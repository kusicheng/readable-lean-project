#include "arithmetic_proof.hpp"

#include <algorithm>
#include <charconv>
#include <limits>
#include <numeric>
#include <set>
#include <stdexcept>

namespace proof {
namespace {

struct Unsupported {};
using Strings = std::vector<std::string>;
struct Context {
    Names names;
    Names assumptions;
    Names abbreviations;
};

std::string formula(const Node& n, const Context& ctx) {
    auto result = checkedFormula(n, ctx.names);
    if (!result) throw Unsupported{};
    for (const auto& [expression, shortName] : ctx.abbreviations) {
        std::size_t pos = 0;
        while ((pos = result->find(expression, pos)) != std::string::npos) {
            result->replace(pos, expression.size(), shortName);
            pos += shortName.size();
        }
    }
    return *result;
}

std::string mathText(const std::string& s) { return "\\(" + s + "\\)"; }

std::string join(const Strings& xs) {
    std::string out;
    for (std::size_t i = 0; i < xs.size(); ++i) {
        if (i) out += i + 1 == xs.size() ? " and " : ", ";
        out += mathText(xs[i]);
    }
    return out;
}

std::string evidenceType(const Node& p, const Context& ctx) {
    if (p.is("p")) return formula(p.at(1), ctx);
    const auto& r = term(p);
    if (r.is("v")) {
        auto found = ctx.assumptions.find(r.at(1).atom);
        if (found != ctx.assumptions.end()) return found->second;
    }
    throw Unsupported{};
}

long long integer(const Node& n) {
    if (head(n) == "OfNat.ofNat") return integer(argument(n, 1));
    if (head(n) == "Int.ofNat") return integer(argument(n, 0));
    if (head(n) == "Neg.neg") {
        auto value = integer(argument(n, 0));
        if (value == std::numeric_limits<long long>::min()) throw Unsupported{};
        return -value;
    }
    const auto& r = term(n);
    if (!r.is("n")) throw Unsupported{};
    const auto& s = r.at(1).atom;
    long long value = 0;
    auto parsed = std::from_chars(s.data(), s.data() + s.size(), value);
    if (parsed.ec != std::errc{} || parsed.ptr != s.data() + s.size() || value < 0)
        throw Unsupported{};
    return value;
}

std::vector<const Node*> list(const Node& n) {
    const Node* tail = head(n) == "Lean.Omega.Coeffs.ofList" ? &argument(n, 0) : &n;
    std::vector<const Node*> entries;
    while (head(*tail) == "List.cons") {
        entries.push_back(&argument(*tail, 1));
        tail = &argument(*tail, 0);
    }
    if (head(*tail) != "List.nil") throw Unsupported{};
    return entries;
}

std::string linearForm(const Node& xs, const Node& vs, const Context& ctx) {
    const auto coefficients = list(xs), values = list(vs);
    std::string result;
    // The kernel's dot product truncates at the shorter list.
    for (std::size_t i = 0; i < std::min(coefficients.size(), values.size()); ++i) {
        long long k = integer(*coefficients[i]);
        if (!k) continue;
        result += result.empty() ? (k < 0 ? "-" : "") : (k < 0 ? " - " : " + ");
        auto operand = formula(*values[i], ctx);
        if ((operand.find(" + ") != std::string::npos || operand.find(" - ") != std::string::npos ||
             operand.front() == '-') && operand.rfind("\\left\\lfloor", 0) != 0)
            operand = "\\left(" + operand + "\\right)";
        if (k < -1 || k > 1) result += std::to_string(k < 0 ? -k : k) + "\\,";
        result += operand;
    }
    return result.empty() ? "0" : result;
}

std::optional<long long> endpoint(const Node& n) {
    if (head(n) == "Option.none") return {};
    if (head(n) == "Option.some") return integer(argument(n, 0));
    throw Unsupported{};
}

struct Interval {
    std::optional<long long> lo, hi;
    std::string describe(const std::string& x) const {
        if (lo && hi && *lo == *hi) return x + " = " + std::to_string(*lo);
        if (lo && hi) return std::to_string(*lo) + " \\le " + x + " \\le " + std::to_string(*hi);
        if (lo) return x + " \\ge " + std::to_string(*lo);
        if (hi) return x + " \\le " + std::to_string(*hi);
        throw Unsupported{};
    }
};

Interval interval(const Node& n) {
    if (head(n) != "Lean.Omega.Constraint.mk") throw Unsupported{};
    return {endpoint(argument(n, 1)), endpoint(argument(n, 0))};
}

struct Bound {
    Interval limits;
    const Node& coefficients;
    std::string expression;
    std::string text;
};

Bound bound(const Node& c, const Node& x, const Node& v, const Context& ctx) {
    const auto limits = interval(c);
    const auto expression = linearForm(x, v, ctx);
    return {limits, x, expression, limits.describe(expression)};
}

// Compare the actual coefficient vectors before and after the checked tidy step.
// Lower bounds round upward and upper bounds downward after fixing the sign.
std::string roundedDivision(const Bound& input, const Bound& output) {
    const auto before = list(input.coefficients), after = list(output.coefficients);
    long long gcd = 0;
    for (const auto* n : before) gcd = std::gcd(gcd, integer(*n));
    if (gcd < 2) return {};
    bool sameSign = true, reversed = true;
    for (std::size_t i = 0; i < std::max(before.size(), after.size()); ++i) {
        const auto a = i < before.size() ? integer(*before[i]) / gcd : 0;
        const auto b = i < after.size() ? integer(*after[i]) : 0;
        sameSign = sameSign && a == b;
        reversed = reversed && -a == b;
    }
    if (!sameSign && !reversed) throw Unsupported{};
    Interval numerators = input.limits;
    if (reversed) {
        std::swap(numerators.lo, numerators.hi);
        if (numerators.lo) numerators.lo = -*numerators.lo;
        if (numerators.hi) numerators.hi = -*numerators.hi;
    }
    Strings bounds;
    bool needsRounding = false;
    for (bool lower : {true, false}) {
        const auto n = lower ? numerators.lo : numerators.hi;
        const auto target = lower ? output.limits.lo : output.limits.hi;
        if (n.has_value() != target.has_value()) throw Unsupported{};
        if (!n) continue;
        const auto remainder = *n % gcd;
        const auto expected = *n / gcd + (lower && remainder > 0) - (!lower && remainder < 0);
        if (*target != expected) throw Unsupported{};
        std::string value = std::to_string(expected);
        if (remainder != 0) {
            needsRounding = true;
            const auto fraction = "\\frac{" + std::to_string(*n) + "}{" + std::to_string(gcd) + "}";
            value = (lower ? "\\left\\lceil" : "\\left\\lfloor") + fraction +
                    (lower ? "\\right\\rceil" : "\\right\\rfloor") + " = " + value;
        }
        bounds.push_back(output.expression + (lower ? " \\ge " : " \\le ") + value);
    }
    const auto divisor = mathText(std::to_string(reversed ? -gcd : gcd));
    if (!needsRounding)
        return "Dividing " + mathText(input.text) + " by " + divisor +
               (reversed ? " reverses the order and gives " : " gives ") + mathText(output.text) + ".";
    return "Divide " + mathText(input.text) + " by " + divisor +
           (reversed ? ", reversing the order. " : ". ") + "Since " + mathText(output.expression) +
           " is integral, " + join(bounds) + ".";
}

// Inspect only the actual premises of the instantiated constraint proof.
// Algebraic transport can contain large typeclass and normalization subtrees.
const Node* inequalityOrigin(const Node& n) {
    const auto op = head(n);
    if (op == "le_of_le_of_eq" || op == "Eq.trans")
        return inequalityOrigin(argument(n, 1));
    if (op == "Int.sub_nonneg_of_le" || op == "Int.add_one_le_of_lt" ||
        op == "Lean.Omega.Int.ofNat_lt_of_lt" || op == "Lean.Omega.Int.ofNat_le_of_le")
        return inequalityOrigin(argument(n, 0));
    if (term(n).is("v") || op == "Nat.emod_pos_of_not_dvd" || op == "Int.lt_mul_ediv_self_add" ||
        op == "Int.ediv_mul_le" || op == "Int.not_le.mp" || op == "Int.lt_of_not_ge" ||
        op == "lt_of_not_ge" || op == "Int.ofNat_zero_le" || op == "Int.ofNat_nonneg" ||
        op == "Nat.lt_of_not_le" || op == "Lean.Omega.Int.lt_of_not_le")
        return &n;
    return nullptr;
}

void omegaSteps(const Node& evidence, const Bound& output, const Context& ctx,
                Strings& lines, bool compact) {
    const auto& result = output.text;
    const auto name = head(evidence);
    const auto& a = term(evidence);
    if (name == "Lean.Omega.Constraint.addInequality_sat" ||
        name == "Lean.Omega.Constraint.addEquality_sat") {
        const auto* source = inequalityOrigin(argument(a, 0));
        // The proof annotation of the final premise relates zero to an internal
        // dot product. The displayed affine expression is its checked expansion.
        if (!source) throw Unsupported{};
        const auto origin = evidenceType(*source, ctx);
        if (origin == result) return;
        const auto sourceRule = head(*source);
        if (sourceRule == "Lean.Omega.Int.lt_of_not_le" || sourceRule == "Nat.lt_of_not_le") {
            const auto premise = evidenceType(argument(*source,0), ctx);
            lines.push_back("From " + mathText(premise) + " we get " + mathText(origin) +
                            ", hence " + mathText(result) + " over the integers.");
            return;
        }
        if (head(*source) == "Nat.emod_pos_of_not_dvd") {
            lines.push_back("Nondivisibility makes the remainder positive, so " + mathText(origin) +
                            ". Writing the remainder as dividend minus divisor times quotient gives " +
                            mathText(result) + ".");
            return;
        }
        if (head(*source) == "Int.lt_mul_ediv_self_add" || head(*source) == "Int.ediv_mul_le") {
            lines.push_back("The quotient bound " + mathText(origin) + " gives " +
                            mathText(result) + " over the integers.");
            return;
        }
        if (!compact)
            lines.push_back("Writing " + mathText(origin) + " as an integer constraint gives " +
                            mathText(result) + ".");
        return;
    }
    if (name == "Lean.Omega.tidy_sat") {
        const auto input = bound(a.at(2), a.at(3), a.at(4), ctx);
        const auto rounding = roundedDivision(input, output);
        const auto* source = head(a.at(5)) == "Lean.Omega.Constraint.addInequality_sat"
            ? inequalityOrigin(argument(a.at(5), 0)) : nullptr;
        const auto sourceFormula = source ? evidenceType(*source, ctx) : std::string{};
        if (source && sourceFormula == result) return;
        if (compact && input.text != result && source) {
            const auto origin = mathText(sourceFormula);
            std::string reason;
            if (head(*source) == "Nat.emod_pos_of_not_dvd")
                reason = "The positive remainder satisfies " + origin +
                         ". Substituting dividend minus divisor times quotient";
            else if (head(*source) == "Int.lt_mul_ediv_self_add" || head(*source) == "Int.ediv_mul_le")
                reason = "Applying the quotient bound " + origin;
            else reason = "Rearranging " + origin;
            if (rounding.empty()) lines.push_back(reason + " gives " + mathText(result) + ".");
            else {
                if (sourceFormula != input.text) lines.push_back(reason + " gives " + mathText(input.text) + ".");
                lines.push_back(rounding);
            }
            return;
        }
        omegaSteps(a.at(5), input, ctx, lines, compact);
        if (!rounding.empty()) lines.push_back(rounding);
        else if (input.text != result && !compact)
            lines.push_back("Rearranging " + mathText(input.text) + " gives " + mathText(result) + ".");
        return;
    }
    if (name == "Lean.Omega.combo_sat'") {
        const auto left = bound(a.at(2), a.at(5), a.at(8), ctx);
        const auto right = bound(a.at(3), a.at(7), a.at(8), ctx);
        omegaSteps(a.at(9), left, ctx, lines, compact);
        omegaSteps(a.at(10), right, ctx, lines, compact);
        if (result == left.text || result == right.text) return;
        lines.push_back("Taking the linear combination of " + mathText(left.text) + " and " +
                        mathText(right.text) + " with respective coefficients " +
                        std::to_string(integer(a.at(4))) + " and " + std::to_string(integer(a.at(6))) +
                        " gives " + mathText(result) + ".");
        return;
    }
    if (name == "Lean.Omega.Constraint.combine_sat'") {
        const auto left = bound(a.at(2), a.at(4), a.at(5), ctx);
        const auto right = bound(a.at(3), a.at(4), a.at(5), ctx);
        omegaSteps(a.at(6), left, ctx, lines, compact);
        omegaSteps(a.at(7), right, ctx, lines, compact);
        if (result == left.text || result == right.text) return;
        if (!compact) lines.push_back("Combining the bounds gives " + mathText(result) + ".");
        else lines.push_back("The two bounds require " + mathText(result) + ".");
        return;
    }
    throw Unsupported{};
}

Strings omega(const Node& p, Context ctx, bool compact) {
    const auto& a = term(p);
    const auto bounds = interval(a.at(2));
    if (!bounds.lo || !bounds.hi || *bounds.lo <= *bounds.hi) throw Unsupported{};
    Strings result;
    for (const auto* atom : list(a.at(5))) {
        if (head(*atom) != "HDiv.hDiv") continue;
        const auto full = formula(*atom, ctx);
        if (full.find("\\left\\lfloor") != 0) continue;
        const auto q = checkedBinderName(ctx.names, "#quotient-" + std::to_string(result.size()), "q");
        result.push_back("Write " + mathText(q + " = " + full) + " for the integer quotient.");
        ctx.abbreviations[full] = q;
    }
    const auto condition = bound(a.at(2), a.at(4), a.at(5), ctx);
    omegaSteps(a.at(6), condition, ctx, result, compact);
    result.push_back("This is impossible because " + mathText(std::to_string(*bounds.lo) +
                     " > " + std::to_string(*bounds.hi)) + ".");
    return result;
}

const std::set<std::string> sumRules = {
    "Linarith.eq_of_eq_of_eq", "Linarith.le_of_eq_of_le", "Linarith.lt_of_eq_of_lt",
    "Linarith.le_of_le_of_eq", "Linarith.add_nonpos", "Linarith.add_lt_of_le_of_neg",
    "Linarith.lt_of_lt_of_eq", "Linarith.add_lt_of_neg_of_le", "Linarith.add_neg"
};

void linearInput(const Node& p, const Context& ctx, Strings& detail) {
    const auto rule = head(p);
    if (term(p).is("v") && ctx.assumptions.count(term(p).at(1).atom)) return;
    if (rule == "neg_neg_of_pos" && head(argument(p, 0)) == "Linarith.zero_lt_one")
        return;
    const auto output = evidenceType(p, ctx);
    if (rule == "Linarith.mul_neg" || rule == "Linarith.mul_nonpos" || rule == "Linarith.mul_eq") {
        const auto& input = argument(p, 1);
        linearInput(input, ctx, detail);
        const auto& positive = argument(p, 0);
        if (!positive.is("p") || head(positive.at(1)) != "LT.lt") throw Unsupported{};
        const auto coefficient = integer(argument(positive.at(1), 0));
        if (coefficient <= 0 || integer(argument(positive.at(1), 1)) != 0) throw Unsupported{};
        detail.push_back("Multiplying " + mathText(evidenceType(input, ctx)) +
                         " by " + std::to_string(coefficient) + " gives " + mathText(output) + ".");
    } else if (rule == "Linarith.sub_nonpos_of_le" || rule == "Linarith.sub_neg_of_lt" ||
               rule == "Linarith.sub_eq_zero_of_eq") {
        linearInput(argument(p, 0), ctx, detail);
        detail.push_back("Subtracting the right side of " + mathText(evidenceType(argument(p, 0), ctx)) +
                         " gives " + mathText(output) + ".");
    } else throw Unsupported{};
}

void summands(const Node& p, const Context& ctx, Strings& terms, Strings& detail) {
    if (sumRules.count(head(p))) {
        summands(argument(p, 1), ctx, terms, detail);
        summands(argument(p, 0), ctx, terms, detail);
        return;
    }
    linearInput(p, ctx, detail);
    terms.push_back(evidenceType(p, ctx));
}

Strings linarith(const Node& p, const Context& ctx, bool compact) {
    const auto& transport = argument(p, 0);
    if (head(transport) != "Eq.mp") throw Unsupported{};
    const auto& summed = argument(transport, 0);
    if (!summed.is("p") || head(summed.at(1)) != "LT.lt" || !transport.is("p") ||
        head(transport.at(1)) != "LT.lt") throw Unsupported{};
    const auto sum = formula(argument(summed.at(1), 1), ctx);
    if (integer(argument(summed.at(1), 0)) != 0 ||
        integer(argument(transport.at(1), 1)) != 0 || integer(argument(transport.at(1), 0)) != 0)
        throw Unsupported{};
    Strings terms, detail;
    summands(summed, ctx, terms, detail);
    Strings lines = compact ? Strings{} : detail;
    lines.push_back("Adding " + join(terms) + " gives " + mathText(sum + " < 0") + ".");
    lines.push_back("The terms on the left cancel, so the inequality would give " +
                    mathText("0 < 0") + ", a contradiction.");
    return lines;
}

Strings explain(const Node& p, const Node& document, Context ctx, bool compact, unsigned depth) {
    if (depth > 20) throw Unsupported{};
    const auto name = head(p);
    if (name == "Lean.Omega.Constraint.not_sat'_of_isImpossible") return omega(p, ctx, compact);
    if (name == "Linarith.lt_irrefl") return linarith(p, ctx, compact);
    if (name == "Linarith.eq_of_not_lt_of_not_gt") {
        Strings lines;
        for (std::size_t i : {1u, 0u}) {
            const auto& excluded = argument(p, i);
            if (head(excluded) != "Not.intro") throw Unsupported{};
            const auto& lambda = term(argument(excluded, 0));
            if (!lambda.is("l")) throw Unsupported{};
            auto inner = ctx;
            const auto premise = formula(lambda.at(3), ctx);
            const auto id = lambda.at(1).atom;
            checkedBinderName(inner.names, id, lambda.at(2).atom);
            inner.assumptions[id] = premise;
            lines.push_back("Suppose " + mathText(premise) + ".");
            const auto branch = explain(lambda.at(4), document, std::move(inner), compact, depth + 1);
            lines.insert(lines.end(), branch.begin(), branch.end());
        }
        lines.push_back("Both strict orderings are impossible, so " + mathText(evidenceType(p, ctx)) + ".");
        return lines;
    }
    if (name == "Decidable.byContradiction" || name == "Classical.byContradiction" ||
        name == "le_of_not_gt" || name == "lt_of_not_ge" || name == "le_of_not_lt") {
        const auto& lambda = term(argument(p, 0));
        if (!lambda.is("l")) throw Unsupported{};
        const auto premise = formula(lambda.at(3), ctx);
        const auto id = lambda.at(1).atom;
        checkedBinderName(ctx.names, id, lambda.at(2).atom);
        ctx.assumptions[id] = premise;
        auto lines = explain(lambda.at(4), document, std::move(ctx), compact, depth + 1);
        lines.insert(lines.begin(), "Suppose for contradiction that " + mathText(premise) + ".");
        return lines;
    }
    if (name == "False.elim") return explain(argument(p, 0), document, std::move(ctx), compact, depth + 1);
    if (document.children.size() > 6) for (const auto& aux : document.at(6).children) {
        if (aux.at(0).atom != name) continue;
        const Node* body = &aux.at(2);
        const auto& app = term(p);
        Context inner;
        for (std::size_t i = 2; i < app.children.size(); ++i) {
            const auto& binder = term(*body);
            if (!binder.is("l")) throw Unsupported{};
            const auto& actual = app.at(i);
            const auto id = binder.at(1).atom;
            if (binder.children.size() > 6 && binder.at(6).atom == "proof") {
                checkedBinderName(inner.names, id, binder.at(2).atom);
                inner.assumptions[id] = evidenceType(actual, ctx);
            } else inner.names[id] = formula(actual, ctx);
            body = &binder.at(4);
        }
        return explain(*body, document, std::move(inner), compact, depth + 1);
    }
    throw Unsupported{};
}
} // namespace

std::optional<std::string> arithmeticProof(const Node& goal, const Names& names,
                                          const Node& step, const Node& document, bool compact) {
    if (step.children.size() <= 4) return {};
    try {
        Context ctx{names, {}, {}};
        for (const auto& local : goal.at(1).children) {
            if (local.at(3).atom != "proof") continue;
            if (auto prop = checkedFormula(local.at(2), names))
                ctx.assumptions[local.at(0).atom] = *prop;
        }
        for (const auto& assignment : step.at(4).children) {
            if (assignment.at(0).atom != goal.at(0).atom) continue;
            auto lines = explain(assignment.at(1), document, ctx, compact, 0);
            std::string result;
            for (const auto& line : lines) result += line + "\n";
            return result;
        }
    } catch (const Unsupported&) {
    } catch (const std::runtime_error&) {
        // Invalid application layout cannot supply a printable certificate.
    }
    return {};
}
} // namespace proof
