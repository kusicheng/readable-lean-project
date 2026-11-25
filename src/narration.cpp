#include "narration.hpp"
#include "paper_links.hpp"
#include "general_proof.hpp"
#include "tactic_proof.hpp"
#include "proof_cost.hpp"

#include <algorithm>
#include <charconv>
#include <cctype>
#include <functional>
#include <map>
#include <ostream>
#include <set>
#include <sstream>
#include <stdexcept>
#include <utility>

namespace proof {
namespace {

std::string join(const std::vector<std::string>& texts) {
    std::string result;
    for (std::size_t i = 0; i < texts.size(); ++i) {
        if (i > 0) result += i == texts.size() - 1 ? " and " : ", ";
        result += texts[i];
    }
    return result;
}

std::string inlineMath(const Math& proposition, const Names& names) {
    return "\\(" + latex(proposition, names) + "\\)";
}

std::string describe(const Statement& signature) {
    Names names;
    std::vector<std::string> variables;
    std::vector<std::string> assumptions;
    for (const auto& parameter : signature.parameters) {
        if (parameter.type.kind == Kind::nat) {
            variables.push_back("\\(" + bindName(names, parameter.id, parameter.hint) + "\\)");
        } else {
            assumptions.push_back(inlineMath(parameter.type, names));
        }
    }
    std::string text;
    if (!variables.empty()) {
        text = "Let " + join(variables) + (variables.size() == 1 ?
            " be a natural number. " : " be natural numbers. ");
    }
    if (!assumptions.empty()) text += "If " + join(assumptions) + ", then ";
    else if (!variables.empty()) text += "Then ";
    return text + inlineMath(signature.conclusion, names) + ".";
}

struct Fact {
    Math claim;
    std::string reference;
    std::string id;
    bool derived = true;
};

struct Scope {
    Names names;
    std::vector<Fact> facts;
    std::map<std::string,const Node*> deferred;

    const Fact* byId(const std::string& id) const {
        const auto found = std::find_if(facts.rbegin(), facts.rend(),
            [&](const Fact& fact) { return fact.id == id; });
        return found == facts.rend() ? nullptr : &*found;
    }

    const Fact* byClaim(const Math& claim) const {
        const auto found = std::find_if(facts.rbegin(), facts.rend(),
            [&](const Fact& fact) { return same(fact.claim, claim); });
        return found == facts.rend() ? nullptr : &*found;
    }
};

struct Earlier {
    std::string name;
    Statement signature;
    std::size_t ordinal;
    std::string role;
    const Node* type;
};

Math instantiatedConclusion(const Node& type, const Substitution& arguments) {
    const Node* body = &type;
    while (body->is("q")) body = &body->at(4);
    return math(*body, arguments);
}

std::size_t binderUses(const Node& expression, const std::string& id) {
    const auto& raw = term(expression);
    if (raw.is("v")) return raw.at(1).atom == id;
    std::size_t count = 0;
    for (const auto& child : raw.children)
        if (child.array) {
            count += binderUses(child, id);
            if (count > 1) break;
        }
    return count;
}

struct Prerequisite {
    std::string name;
    std::string title;
    const Node* type;
    Statement signature;
    bool publicName;
    std::size_t ordinal = 0;
};

using Prerequisites = std::map<std::string, Prerequisite>;

struct Matcher {
    std::size_t parameters;
    std::size_t scrutinees;
    std::vector<std::size_t> alternatives;
    std::size_t equations;
};

using Matchers = std::map<std::string, Matcher>;

std::size_t count(const Node& node) {
    std::size_t value = 0;
    const auto* end = node.atom.data() + node.atom.size();
    const auto parsed = std::from_chars(node.atom.data(), end, value);
    if (!node.isString() || parsed.ec != std::errc{} || parsed.ptr != end)
        throw std::runtime_error("Malformed matcher metadata");
    return value;
}

Matchers readMatchers(const Node& input) {
    Matchers result;
    if (input.children.size() < 3) return result;
    const auto& entries = input.at(2);
    if (!entries.array) throw std::runtime_error("Expected a matcher catalog");
    for (const auto& entry : entries.children) {
        const auto& alternatives = entry.at(3);
        if (!alternatives.array) throw std::runtime_error("Malformed matcher alternatives");
        Matcher info{count(entry.at(1)), count(entry.at(2)), {}, count(entry.at(4))};
        for (const auto& size : alternatives.children) info.alternatives.push_back(count(size));
        result.emplace(entry.at(0).atom, std::move(info));
    }
    return result;
}

std::string prerequisiteTitle(const std::string& name) {
    static const std::map<std::string, std::string> titles = {
        {"funext", "Function extensionality"},
        {"Eq.le", "Equality implies a weak inequality"},
        {"Eq.ge", "Equality implies the reverse weak inequality"},
        {"Finset.sum_fiberwise_of_maps_to", "Summing over the fibers of a map"},
        {"Finset.sum_const", "The sum of a constant"},
        {"Finset.cast_card", "Cardinality as a sum of ones"},
        {"Finset.mem_univ", "Membership in the full set"},
        {"Finset.card_eq_sum_ones", "Cardinality as a sum of ones"},
        {"Finset.card_univ", "Counting all elements of a finite type"},
        {"Finset.prod_comm", "Interchanging two finite products"},
        {"Finset.sum_comm", "Interchanging two finite sums"},
        {"Finset.prod_congr", "Equality of products with equal factors"},
        {"Finset.sum_congr", "Equality of sums with equal summands"},
        {"Nat.instIsStrictOrderedRing", "Strict order on the natural numbers"},
        {"Nat.add_zero", "Adding zero on the right"},
        {"Nat.add_add_add_comm", "Regrouping four summands"},
        {"Nat.add_right_comm", "Interchanging the last two summands"},
        {"Nat.add_le_add_left", "Adding a common left summand preserves order"},
        {"Nat.add_le_add_right", "Adding a common right summand preserves order"},
        {"Nat.add_mul", "A sum times a common factor"},
        {"Nat.le_add_right", "Adding a natural number can only increase a sum"},
        {"Nat.le_refl", "Reflexivity of order"},
        {"Nat.le_trans", "Transitivity of order"},
        {"Nat.le_of_eq", "Equality implies a weak inequality"},
        {"Nat.add_le_add", "Adding two inequalities"},
        {"Nat.succ_le_succ", "Successors preserve order"},
        {"Nat.zero_le", "Natural numbers are nonnegative"},
        {"Nat.lt_of_lt_of_le", "Combining a strict and a weak inequality"},
        {"Nat.pos_of_lt_add_right", "A strict increase requires a positive summand"},
        {"Nat.mul_two", "Doubling by multiplication"},
        {"Nat.mul_le_mul_right", "Multiplying by a common natural number preserves order"},
        {"Nat.dvd_add", "Divisibility of a sum"},
        {"Nat.dvd_add_iff_right", "Divisibility after adding a known multiple"},
        {"Nat.dvd_zero", "Divisibility of zero"},
        {"Nat.left_distrib", "Multiplication distributes over addition"},
        {"Nat.mul_add", "Multiplication distributes over addition"},
        {"Nat.mul_one", "Multiplication by one on the right"},
        {"Nat.mul_succ", "Multiplication by a successor"},
        {"Nat.mul_zero", "Multiplication by zero"},
        {"Nat.one_mul", "Multiplication by one on the left"},
        {"Nat.two_mul", "Doubling by addition"},
    };
    if (const auto title = titles.find(name); title != titles.end()) return title->second;

    // Read conventional algebraic property names without emitting Lean identifiers.
    static const std::map<std::string, std::string> operations = {
        {"add", "Addition"}, {"mul", "Multiplication"},
    };
    static const std::map<std::string, std::string> properties = {
        {"assoc", "associativity"}, {"comm", "commutativity"},
        {"left_comm", "left commutativity"},
    };
    const auto leaf = name.substr(name.find_last_of('.') + 1);
    const auto separator = leaf.find('_');
    if (separator != std::string::npos) {
        const auto operation = operations.find(leaf.substr(0, separator));
        const auto property = properties.find(leaf.substr(separator + 1));
        if (operation != operations.end() && property != properties.end())
            return operation->second + " " + property->second;
    }
    return "Natural-number lemma";
}

// Match premises against the current scope in order, retaining the first complete match.
bool matchPremises(const std::vector<Parameter>& parameters, std::size_t at, const Scope& scope,
                   Substitution& substitutions, std::vector<std::string>& references) {
    if (at == parameters.size()) {
        return std::all_of(substitutions.begin(), substitutions.end(),
            [](const auto& entry) { return entry.second.supported(); });
    }
    const auto& type = parameters[at].type;
    if (type.kind == Kind::nat)
        return matchPremises(parameters, at + 1, scope, substitutions, references);
    for (const auto& fact : scope.facts) {
        auto trial = substitutions;
        if (!match(type, fact.claim, trial)) continue;
        references.push_back(fact.reference);
        if (matchPremises(parameters, at + 1, scope, trial, references)) {
            substitutions = std::move(trial);
            return true;
        }
        references.pop_back();
    }
    return false;
}

std::string theoremReference(std::size_t ordinal, const std::string& role) {
    const auto label = role == "lemma" ? "Lemma" : role == "corollary" ? "Corollary" : "Theorem";
    return numberedReference(std::string(label) + "~","theorem:" + std::to_string(ordinal));
}

// Reserve a line of its own for a substantial formula at the end of a
// theorem. Text-mode centering lets long sums wrap across the available width.
std::string paperStatement(std::string description) {
    const auto math = description.rfind("\\(");
    if (math == std::string::npos || description.size()-math < 96 ||
        description.compare(description.size()-3,3,"\\).")!=0) return description;
    if (math && (math<5 || (description.compare(math-5,5,"Then ")!=0 &&
                           description.compare(math-5,5,"then ")!=0))) return description;
    const auto formula = description.substr(math+2,description.size()-math-5);
    description.resize(math ? math-1 : 0);
    return description + "\n\\begin{center}\n\\(\\displaystyle " + formula + ".\\)\n\\end{center}";
}

void beginResult(std::ostream& out, const std::string& role, const std::string& title,
                 std::size_t ordinal) {
    out << "\\begin{" << role << "}";
    if (!title.empty()) out << "[{" << escapeLatex(title) << "}]";
    out << "\\label{theorem:" << ordinal << "}\n";
}

std::string instanceSuffix(const Statement& signature, const Substitution& substitutions,
                           const Scope& scope, bool chapterStyle, bool omitIdentities) {
    Names formal;
    std::vector<std::string> bindings;
    std::vector<std::string> parameters;
    std::vector<std::string> values;
    for (const auto& parameter : signature.parameters) {
        if (parameter.type.kind != Kind::nat) continue;
        const auto name = bindName(formal, parameter.id, parameter.hint);
        const auto argument = substitutions.find(parameter.id);
        if (argument == substitutions.end() || !argument->second.supported()) continue;
        const auto value = latex(argument->second, scope.names);
        if (omitIdentities && argument->second.kind == Kind::var && name == value) continue;
        if (omitIdentities) {
            bindings.push_back("\\(" + name + " = " + value + "\\)");
            continue;
        }
        if (chapterStyle) {
            parameters.push_back(name);
            values.push_back(value);
        } else {
            bindings.push_back("\\(" + name + " = " + value + "\\)");
        }
    }
    if (!bindings.empty()) return " with " + join(bindings);
    if (parameters.empty()) return "";
    if (parameters.size() == 1)
        return " with its parameter \\(" + parameters.front() + "\\) set to \\(" +
               values.front() + "\\)";
    const auto tuple = [](const std::vector<std::string>& elements) {
        std::string text;
        for (const auto& element : elements) {
            if (!text.empty()) text += ", ";
            text += element;
        }
        return "\\((" + text + ")\\)";
    };
    return " with its parameters " + tuple(parameters) + " set to " + tuple(values);
}

struct RewriteEvidence {
    std::vector<std::string> substitutions;
    std::vector<std::string> equalities;
};

class Narrator {
public:
    Narrator(std::ostream& out, std::ostream& diagnostics, Prerequisites& prerequisites,
             std::vector<const Prerequisite*>& used, const std::vector<Earlier>& earlier,
             const std::map<std::string, std::size_t>& documentTheorems, const Matchers& matchers,
             const Terms& terms, std::size_t threshold, bool chapterStyle, bool paperStyle, bool compact)
        : out_(out), diagnostics_(diagnostics), prerequisites_(prerequisites), used_(used),
          earlier_(earlier), documentTheorems_(documentTheorems), matchers_(matchers),
          terms_(terms), threshold_(threshold), chapterStyle_(chapterStyle), paperStyle_(paperStyle),
          compact_(compact) {}

    bool theorem(const Node& type, const Node& expression, const Statement& signature,
                 std::size_t ordinal, bool main, bool alternateProof, const std::string& role,
                 const std::string& title) {
        if (paperStyle_) beginResult(out_, role, title, ordinal);
        else out_ << "\\begin{theorem}" << (main ? "[Main result]" : "") << "\\label{theorem:"
                  << ordinal << "}\n";
        if (signature.supported()) {
            const auto text = describe(signature);
            out_ << (paperStyle_ ? paperStatement(text) : text) << '\n';
        }
        else {
            const auto checked = paperStyle_ ? describeCheckedStatement(type) : std::nullopt;
            out_ << (checked ? paperStatement(*checked) : "The statement of this theorem could not be rendered.") << '\n';
        }
        out_ << "\\end{" << role << "}\n\n\\begin{proof}\n";
        if (alternateProof) out_ << "\\textit{A separately checked proof is given here.}\n";
        if (signature.supported()) {
            Scope scope;
            Names headerNames;
            Substitution substitutions;
            const Node* currentType = &type;
            const Node* currentProof = &expression;
            bool bindersSupported = true;
            std::vector<std::string> variables;
            for (const auto& parameter : signature.parameters) {
                const auto& lambda = term(*currentProof);
                if (!lambda.is("l")) {
                    pending("missing proof binder");
                    bindersSupported = false;
                    break;
                }
                const auto& id = lambda.at(1).atom;
                if (parameter.type.kind == Kind::nat) {
                    const auto name = bindName(headerNames, parameter.id, parameter.hint);
                    scope.names.emplace(id, name);
                    substitutions.emplace(parameter.id, Math(Kind::var, id));
                    if (!paperStyle_) variables.push_back("\\(" + name + "\\)");
                } else {
                    introduceVariables(variables);
                    const Math claim = math(lambda.at(3));
                    if (!claim.supported()) {
                        pending("unsupported proof-binder domain");
                        bindersSupported = false;
                        break;
                    }
                    if (paperStyle_) scope.facts.push_back({claim, inlineMath(claim, scope.names), id, false});
                    else assume(claim, id, scope, "Assume");
                }
                currentType = &currentType->at(4);
                currentProof = &lambda.at(4);
            }
            if (bindersSupported) {
                introduceVariables(variables);
                prove(*currentProof, math(*currentType, substitutions), scope, true);
            }
        } else {
            pending(paperStyle_ && describeCheckedStatement(type) ?
                    "proof requires a rule outside the elementary narrator" : "unsupported theorem statement");
        }
        if (missing_ != 0) out_ << "\\renewcommand{\\qedsymbol}{}\n";
        out_ << "\\end{proof}\n\n";
        return missing_ == 0;
    }

private:
    std::ostream& out_;
    std::ostream& diagnostics_;
    Prerequisites& prerequisites_;
    std::vector<const Prerequisite*>& used_;
    const std::vector<Earlier>& earlier_;
    const std::map<std::string, std::size_t>& documentTheorems_;
    const Matchers& matchers_;
    const Terms& terms_;
    std::size_t threshold_;
    bool chapterStyle_;
    bool paperStyle_;
    bool compact_;
    std::size_t missing_ = 0;
    std::size_t facts_ = 0;

    void introduceVariables(std::vector<std::string>& variables) {
        if (variables.empty()) return;
        out_ << "Let " << join(variables) << (variables.size() == 1 ?
            " be a natural number.\n" : " be natural numbers.\n");
        variables.clear();
    }

    std::optional<Fact> pending(const std::string& cause) {
        ++missing_;
        diagnostics_ << "  Pending: " << cause << '\n';
        out_ << "An explanation of this step is pending.\n";
        return std::nullopt;
    }

    std::string newTag() { return std::to_string(++facts_); }

    Fact say(const Math& claim, const Scope& scope, const std::string& before,
             bool conclusion, bool citation = false) {
        if (paperStyle_) {
            out_ << before;
            const auto formatted = latex(claim, scope.names);
            const bool comparison = claim.kind == Kind::equal || claim.kind == Kind::lt || claim.kind == Kind::le;
            if (comparison && formatted.size() > 98) {
                const auto sign = claim.kind == Kind::equal ? "=" : claim.kind == Kind::lt ? "<" : "\\le";
                out_ << "\n\\begin{multline*}\n" << latex(claim.parts[0], scope.names) << " \\\\\n"
                     << "{}" << sign << " " << latex(claim.parts[1], scope.names) << ".\n\\end{multline*}\n";
            } else if (claim.complexity() > threshold_)
                out_ << "\n\\[\n" << formatted << ".\n\\]\n";
            else out_ << " " << inlineMath(claim, scope.names) << ".\n";
            return {claim, inlineMath(claim, scope.names), ""};
        }
        const std::string tag = conclusion ? "" : newTag();
        const auto formatted = latex(claim, scope.names);
        out_ << before;
        if (!citation && claim.complexity() > threshold_) {
            if (conclusion) out_ << "\n\\[\n" << formatted << ".\n\\]\n";
            else out_ << "\n\\begin{equation}\\tag{" << tag << "}\n" << formatted
                      << ".\n\\end{equation}\n";
        } else {
            out_ << " \\(" << formatted << "\\)";
            if (!conclusion) out_ << "~(" << tag << ")";
            out_ << ".\n";
        }
        return {claim, conclusion ? "" : "(" + tag + ")", ""};
    }

    void assume(const Math& claim, const std::string& id, Scope& scope, const std::string& before) {
        auto fact = say(claim, scope, before, false);
        fact.id = id;
        scope.facts.push_back(std::move(fact));
    }

    Fact cite(const Math& claim, const Scope& scope, bool conclusion,
              const std::string& reference, const std::vector<std::string>& premises,
              const Math& instance = Math()) {
        if (paperStyle_) {
            const auto explanation = premises.empty() ? "Applying " + reference :
                "Applying " + reference + " to " + join(premises);
            if (instance.supported() && !same(claim, instance)) {
                out_ << explanation << " gives " << inlineMath(instance, scope.names) << ".\n";
                return say(claim, scope, "By the defining equations, this gives", conclusion);
            }
            return say(claim, scope, explanation + " gives", conclusion);
        }
        auto citation = reference;
        if (!premises.empty()) citation += ", using " + join(premises);
        if (!conclusion) return say(claim, scope, "By " + citation + ", we have", false, true);
        out_ << "The claim follows from " << citation << ".\n";
        return {claim, "", ""};
    }

    Fact citeEarlier(const Earlier& earlier, const Math& claim, const Scope& scope, bool conclusion,
                     const Substitution& substitutions, const std::vector<std::string>& premises) {
        auto citation = theoremReference(earlier.ordinal, earlier.role);
        citation += instanceSuffix(earlier.signature, substitutions, scope, chapterStyle_, paperStyle_);
        if (paperStyle_ && conclusion && same(claim,instantiatedConclusion(*earlier.type,substitutions))) {
            out_ << "Apply " << citation;
            if (!premises.empty()) out_ << " using " << join(premises);
            out_ << ".\n";
            return {claim, inlineMath(claim,scope.names), ""};
        }
        if (paperStyle_)
            return cite(claim, scope, conclusion, citation, premises,
                        instantiatedConclusion(*earlier.type, substitutions));
        if (!premises.empty()) citation += ", using " + join(premises);
        if (conclusion) {
            out_ << "The claim follows from " << citation << ".\n";
            return {claim, "", ""};
        }
        const auto tag = "(" + newTag() + ")";
        out_ << "Record the instance of " << citation << " as " << tag << ".\n";
        return {claim, tag, ""};
    }

    std::optional<Fact> obtain(const Node& expression, Scope& scope, const Math* expected = nullptr) {
        const auto& raw = term(expression);
        if (raw.is("v")) {
            if (const auto* existing = scope.byId(raw.at(1).atom)) {
                if (!expected || same(existing->claim, *expected)) return *existing;
                auto fact = say(*expected, scope, "Using " + existing->reference +
                                " and computation, we have", false);
                scope.facts.push_back(fact);
                return fact;
            }
        }
        if (!expected && !expression.is("p")) return pending("missing type of supporting fact");
        const auto claim = expected ? *expected : math(expression.at(1));
        if (const auto* existing = scope.byClaim(claim)) return *existing;
        Scope inner = scope;
        auto fact = prove(expression, claim, inner, false);
        if (fact) scope.facts.push_back(*fact);
        return fact;
    }

    std::optional<Fact> prove(const Node& expression, const Math& claim, Scope& scope,
                              bool conclusion) {
        if (!claim.supported() || !claim.proposition()) return pending("unsupported proposition");

        // A prior theorem with all of its premises in scope wins over any derivation.
        for (const auto& earlier : earlier_) {
            Substitution parameters;
            for (const auto& parameter : earlier.signature.parameters) {
                if (parameter.type.kind == Kind::nat) parameters.emplace(parameter.id, Math());
            }
            if (!match(earlier.signature.conclusion, claim, parameters)) continue;
            std::vector<std::string> premises;
            if (matchPremises(earlier.signature.parameters, 0, scope, parameters, premises))
                return citeEarlier(earlier, claim, scope, conclusion, parameters, premises);
        }
        if (const auto* fact = scope.byClaim(claim)) {
            if (!conclusion) return *fact;
            return say(claim, scope, "From " + fact->reference + ", we conclude", true);
        }

        const auto& raw = term(expression);
        if (paperStyle_ && (raw.is("t") || head(raw) == "letFun")) {
            if (auto fact = boundCalculation(raw, claim, scope)) return fact;
        }
        if (raw.is("t")) return local(raw, claim, scope, conclusion);
        const auto name = head(raw);
        if (paperStyle_ && transitive(raw) && claim.parts.size() == 2) {
            if (auto fact = calculation(raw, claim, scope)) return fact;
        }
        if ((name == "Eq.refl" || name == "rfl") && claim.kind == Kind::equal)
            return say(claim, scope, paperStyle_ ? "Evaluating the two sides gives" :
                       "By computation, we have", conclusion);
        if (name == "id") return prove(argument(raw, 0), claim, scope, conclusion);
        if (name == "letFun") {
            const auto& lambda = term(argument(raw, 0));
            if (!lambda.is("l")) return pending("unsupported local binding");
            return binding(lambda.at(1).atom, lambda.at(2).atom, lambda.at(3),
                           argument(raw, 1), lambda.at(4), claim, scope, conclusion);
        }
        if (name == "of_eq_true" && claim.kind == Kind::equal)
            return simplify(argument(raw, 0), claim, scope, conclusion);
        if (name == "Eq.symm" || name == "Eq.trans" || name == "congrArg")
            return equality(name, raw, claim, scope, conclusion);
        if (name == "Trans.trans" && raw.children.size() == 14 &&
            head(raw.at(8)) == "instTransEq" && claim.kind == Kind::equal)
            return equality("Eq.trans", raw, claim, scope, conclusion);
        if (name == "Eq.mp" || name == "Eq.mpr")
            return transport(raw, claim, scope, conclusion);
        if (name == "Exists.intro") return witness(raw, claim, scope, conclusion);
        if (name == "Exists.elim") return eliminate(raw, claim, scope, conclusion);
        if (const auto matcher = matchers_.find(name); matcher != matchers_.end())
            return matchWitnesses(raw, matcher->second, claim, scope, conclusion);
        if (name == "Iff.intro") return equivalence(raw, claim, scope, conclusion);
        if (name == "Iff.mp" || name == "Iff.mpr")
            return implication(name, raw, claim, scope, conclusion);
        if (name == "Nat.rec" || name == "Nat.recOn" || name == "Nat.recAux")
            return induction(name, raw, claim, scope, conclusion);

        for (const auto& earlier : earlier_) {
            if (name == earlier.name) {
                const auto premises = citePremises(raw, earlier.signature, scope);
                if (!premises) return std::nullopt;
                Substitution substitutions;
                for (std::size_t i = 0; i < earlier.signature.parameters.size(); ++i) {
                    const auto& parameter = earlier.signature.parameters[i];
                    if (parameter.type.kind == Kind::nat)
                        substitutions.emplace(parameter.id, math(raw.at(i + 2)));
                }
                return citeEarlier(earlier, claim, scope, conclusion, substitutions, *premises);
            }
        }
        const auto prerequisite = prerequisites_.find(name);
        if (documentTheorems_.count(name) == 0 && prerequisite != prerequisites_.end() &&
            prerequisite->second.publicName && prerequisite->second.signature.supported()) {
            const auto premises = citePremises(raw, prerequisite->second.signature, scope);
            if (!premises) return std::nullopt;
            auto& entry = prerequisite->second;
            use(entry);
            if (paperStyle_) {
                Substitution arguments;
                for (std::size_t i = 0; i < entry.signature.parameters.size(); ++i) {
                    const auto& parameter = entry.signature.parameters[i];
                    if (parameter.type.kind == Kind::nat)
                        arguments.emplace(parameter.id, math(raw.at(i + 2)));
                }
                return cite(claim, scope, conclusion, paperLink(prerequisiteLabel(name),"\\emph{" + entry.title + "}"), *premises,
                            instantiatedConclusion(*entry.type, arguments));
            }
            return cite(claim, scope, conclusion,
                        numberedReference("Prerequisite~P",prerequisiteLabel(name)), *premises);
        }
        return pending(name.empty() ? "unsupported checked term" : name);
    }

    void use(Prerequisite& rule) {
        if (rule.ordinal != 0) return;
        used_.push_back(&rule);
        rule.ordinal = used_.size();
    }

    static bool transitive(const Node& raw) {
        const auto name = head(raw);
        return name == "Eq.trans" || name == "Nat.le_trans" || name == "Nat.lt_of_lt_of_le" ||
               (name == "Trans.trans" && raw.children.size() == 14 &&
                head(raw.at(8)) == "instTransEq");
    }

    static bool collectsCopies(const Math& sum, const Math& product) {
        if (product.kind != Kind::mul) return false;
        for (std::size_t side = 0; side < 2; ++side) {
            const auto& coefficient = product.parts[side];
            if (coefficient.kind != Kind::numeral) continue;
            const auto& summand = product.parts[1 - side];
            std::vector<const Math*> terms{&sum};
            std::size_t copies = 0;
            bool matched = true;
            while (matched && !terms.empty()) {
                const auto& term = *terms.back();
                terms.pop_back();
                if (same(term, summand)) ++copies;
                else if (term.kind == Kind::add) {
                    terms.push_back(&term.parts[0]);
                    terms.push_back(&term.parts[1]);
                } else matched = false;
            }
            if (matched && copies > 1 && coefficient.value == std::to_string(copies))
                return true;
        }
        return false;
    }

    struct CalculationStep {
        Math right;
        Kind relation;
        std::string reason;
        bool established;
    };

    struct CalculationEvidence {
        std::vector<Prerequisite*> rules;
        std::vector<std::string> premises;
    };

    static std::string calculationActions(const std::vector<CalculationStep>& steps,
                                          std::size_t start, std::size_t end) {
        std::vector<std::string> actions;
        std::vector<std::string> citations;
        auto flush = [&] {
            if (!citations.empty()) {
                actions.push_back("apply " + join(citations) + (citations.size() == 1 ? "" : " in order"));
                citations.clear();
            }
        };
        for (auto i = start; i < end; ++i) {
            const auto& reason = steps[i].reason;
            const bool named = reason.rfind("\\paperlink{theorem:",0) == 0 ||
                (reason.rfind("\\paperlink{premise:",0) == 0 && reason.find("}{\\emph{") != std::string::npos);
            if (named) {
                if (reason.find(" using ") != std::string::npos) {
                    flush();
                    actions.push_back("apply " + reason);
                } else citations.push_back(reason);
                continue;
            }
            flush();
            actions.push_back(reason == "collecting equal summands" ? "collect equal summands" :
                              "use " + reason);
        }
        flush();
        auto instructions = join(actions);
        instructions.front() = static_cast<char>(std::toupper(static_cast<unsigned char>(instructions.front())));
        return instructions + ".";
    }

    std::optional<Fact> boundCalculation(const Node& expr, const Math& claim, Scope scope) {
        const Node* current = &expr;
        while (true) {
            const auto& raw = term(*current);
            const bool direct = raw.is("t");
            if (!direct && head(raw) != "letFun") break;
            const auto& binder = direct ? raw : term(argument(raw, 0));
            if ((!direct && !binder.is("l")) || !math(binder.at(3)).proposition())
                return std::nullopt;
            const auto& rest = binder.at(direct ? 5 : 4);
            const auto& id = binder.at(1).atom;
            // Keep any shared local result as a named fact rather than duplicating its proof.
            if (binderUses(rest, id) > 1) return std::nullopt;
            scope.deferred.emplace(id, direct ? &raw.at(4) : &argument(raw, 1));
            current = &rest;
        }
        if (!transitive(term(*current))) return std::nullopt;
        return calculation(term(*current), claim, scope);
    }

    // A calculation is prepared in full before emission. If a premise needs a proof of
    // its own, the ordinary narrator introduces it in scope and explains its dependencies.
    std::string stepReason(const Node& expression, const Scope& scope,
                           CalculationEvidence& evidence, bool& established) const {
        const auto& raw = term(expression);
        if (raw.is("v")) {
            if (const auto def = scope.deferred.find(raw.at(1).atom); def != scope.deferred.end())
                return stepReason(*def->second, scope, evidence, established);
            const auto* fact = scope.byId(raw.at(1).atom);
            established = fact && fact->derived && fact->reference == inlineMath(fact->claim, scope.names);
            if (!fact) return {};
            if (fact->reference == inlineMath(fact->claim, scope.names))
                return established ? "the preceding relation" : "hypothesis";
            return fact->reference;
        }
        const auto name = head(raw);
        if (name == "Eq.refl" || name == "rfl") return "the defining equations";
        if (name == "congrArg" || name == "Eq.symm" || name == "id" || name == "Nat.le_of_eq")
            return stepReason(argument(raw, 0), scope, evidence, established);

        const Statement* signature = nullptr;
        std::string reason;
        for (const auto& known : earlier_) {
            if (known.name == name) {
                signature = &known.signature;
                reason = theoremReference(known.ordinal, known.role);
                break;
            }
        }
        if (!signature) {
            const auto found = prerequisites_.find(name);
            if (documentTheorems_.count(name) || found == prerequisites_.end() ||
                !found->second.publicName || !found->second.signature.supported()) return {};
            signature = &found->second.signature;
            const auto key = prerequisiteLabel(name);
            reason = compact_ ? paperLink(key,"\\emph{" + found->second.title + "}") :
                numberedReference("Prerequisite~P",key);
            if (compact_ && (name == "Nat.add_le_add_left" || name == "Nat.add_le_add_right"))
                reason = paperLink(key,"monotonicity of addition");
            evidence.rules.push_back(&found->second);
        }
        const auto arguments = raw.is("a") ? raw.children.size() - 2 : 0;
        if (arguments != signature->parameters.size()) return {};
        std::vector<std::string> premises;
        for (std::size_t i = 0; i < arguments; ++i) {
            if (!signature->parameters[i].type.proposition()) continue;
            const auto& premise = raw.at(i + 2);
            const auto& body = term(premise);
            const auto* fact = body.is("v") ? scope.byId(body.at(1).atom) :
                               premise.is("p") ? scope.byClaim(math(premise.at(1))) : nullptr;
            if (fact) {
                premises.push_back(fact->reference);
                continue;
            }
            if (!compact_) return {};
            const Node* applied = &premise;
            if (body.is("v")) {
                const auto def = scope.deferred.find(body.at(1).atom);
                if (def == scope.deferred.end()) return {};
                applied = def->second;
            }
            bool local = false;
            const auto justification = stepReason(*applied, scope, evidence, local);
            if (justification.empty()) return {};
            if (std::any_of(earlier_.begin(), earlier_.end(), [&](const auto& previous) {
                return previous.name == head(*applied);
            }) && applied->is("p")) {
                const auto result = math(applied->at(1));
                if (!result.supported()) return {};
                const auto line = justification + " gives " + inlineMath(result, scope.names) + ".";
                if (std::find(evidence.premises.begin(), evidence.premises.end(), line) == evidence.premises.end())
                    evidence.premises.push_back(line);
            } else if (reason != justification) premises.push_back(justification);
        }
        if (!premises.empty()) reason += (compact_ ? " using " : " applied to ") + join(premises);
        return reason;
    }

    bool collectSteps(const Node& expression, Kind relation, const Math& right,
                      const Scope& scope, std::vector<CalculationStep>& steps,
                      CalculationEvidence& evidence) const {
        const auto& raw = term(expression);
        const auto name = head(raw);
        if (raw.is("v")) {
            if (const auto def = scope.deferred.find(raw.at(1).atom); def != scope.deferred.end())
                return collectSteps(*def->second, relation, right, scope, steps, evidence);
        }
        if (transitive(raw)) {
            const auto middle = math(argument(raw, 3));
            if (!middle.supported() || middle.proposition()) return false;
            const bool strict = name == "Nat.lt_of_lt_of_le";
            return collectSteps(argument(raw, 1), strict ? Kind::lt : relation, middle,
                                scope, steps, evidence) &&
                   collectSteps(argument(raw, 0), strict ? Kind::le : relation, right,
                                scope, steps, evidence);
        }
        if (name == "Nat.le_of_eq" && relation == Kind::le)
            return collectSteps(argument(raw, 0), Kind::equal, right, scope, steps, evidence);
        bool established = false;
        const auto reason = stepReason(raw, scope, evidence, established);
        if (reason.empty()) return false;
        steps.push_back({right, relation, reason, established});
        return true;
    }

    std::optional<Fact> calculation(const Node& raw, const Math& claim, const Scope& scope) {
        if (claim.kind != Kind::equal && claim.kind != Kind::le && claim.kind != Kind::lt)
            return std::nullopt;
        std::vector<CalculationStep> steps;
        CalculationEvidence evidence;
        if (!collectSteps(raw, claim.kind, claim.parts[1], scope, steps, evidence)) return std::nullopt;
        for (auto* rule : evidence.rules) use(*rule);
        for (const auto& line : evidence.premises) out_ << line << '\n';
        if (compact_) {
            const Math* left = &claim.parts[0];
            for (auto& step : steps) {
                if (step.relation == Kind::equal && step.reason.find("\\ref{theorem:") == std::string::npos &&
                    collectsCopies(*left, step.right)) step.reason = "collecting equal summands";
                left = &step.right;
            }
        }
        if (!compact_ && steps.size() >= 2) {
            // Put each reason on the same line as its use whenever the chain fits.
            const auto first = latex(claim.parts[0],scope.names);
            const bool fits = std::all_of(steps.begin(),steps.end(),[&](const CalculationStep& step) {
                const auto visibleReason = step.reason.find(" applied to ");
                return first.size()+latex(step.right,scope.names).size() < 72 &&
                    (visibleReason == std::string::npos || step.reason.size()-visibleReason < 38) &&
                    step.reason.find("\\(") == std::string::npos;
            });
            if (fits) {
                out_ << "\\begin{align*}\n" << first;
                for (std::size_t i=0; i<steps.size(); ++i) {
                    const auto& step = steps[i];
                    out_ << " &" << (step.relation == Kind::le ? "\\le " : step.relation == Kind::lt ? "< " : "= ")
                         << latex(step.right,scope.names) << (i+1 == steps.size() ? "." : "")
                         << " && \\text{by " << step.reason << "}"
                         << (i+1 == steps.size() ? "\n" : " \\\\\n");
                }
                out_ << "\\end{align*}\n";
                return Fact{claim, inlineMath(claim,scope.names), ""};
            }
        }
        // Split unusually wide calculations so each reason stays close to its formula.
        const std::size_t perDisplay = compact_ ? 6 : 1;
        for (std::size_t start = 0; start < steps.size(); start += perDisplay) {
            const auto end = std::min(start + perDisplay, steps.size());
            if (end - start > 1 && std::all_of(steps.begin() + start, steps.begin() + end,
                                               [](const auto& step) { return step.established; })) {
                out_ << "Combining the preceding relations gives";
            } else if (compact_ && end - start > 1) {
                out_ << calculationActions(steps, start, end);
            } else {
                out_ << (start ? "Continuing with " : "Using ");
                for (auto i = start; i < end; ++i) {
                    if (i > start) out_ << ", then ";
                    out_ << steps[i].reason;
                }
                out_ << ", we obtain";
            }
            out_ << "\n\\[\n\\begin{aligned}\n";
            const auto left = latex(start ? steps[start - 1].right : claim.parts[0], scope.names);
            const bool wide = std::any_of(steps.begin() + start, steps.begin() + end, [&](const auto& step) {
                return left.size() + latex(step.right, scope.names).size() > 96;
            });
            if (wide) out_ << "&" << left << " \\\\\n";
            else out_ << left;
            for (auto i = start; i < end; ++i) {
                const auto relation = steps[i].relation;
                out_ << (wide ? " &\\quad {}" : " &")
                     << (relation == Kind::le ? "\\le " : relation == Kind::lt ? "< " : "= ")
                     << latex(steps[i].right, scope.names) << (i + 1 == end ? "." : " \\\\\n");
            }
            out_ << "\n\\end{aligned}\n\\]\n";
        }
        return Fact{claim, inlineMath(claim, scope.names), ""};
    }

    std::optional<std::vector<std::string>> citePremises(const Node& raw,
                                                        const Statement& signature, Scope& scope) {
        const auto count = raw.is("a") ? raw.children.size() - 2 : 0;
        if (count != signature.parameters.size()) {
            pending("partially or dependently applied theorem");
            return std::nullopt;
        }
        std::vector<std::string> references;
        for (std::size_t i = 0; i < count; ++i) {
            if (!signature.parameters[i].type.proposition()) continue;
            const auto& proof = raw.at(i + 2);
            if (paperStyle_ && proof.is("p") && (head(proof) == "Eq.refl" || head(proof) == "rfl")) {
                const auto equality = math(proof.at(1));
                if (equality.kind == Kind::equal && same(equality.parts[0], equality.parts[1])) continue;
            }
            const auto fact = obtain(proof, scope);
            if (!fact) return std::nullopt;
            references.push_back(fact->reference);
        }
        return references;
    }

    std::optional<Fact> local(const Node& raw, const Math& claim, Scope& scope, bool conclusion) {
        return binding(raw.at(1).atom, raw.at(2).atom, raw.at(3), raw.at(4), raw.at(5),
                       claim, scope, conclusion);
    }

    std::optional<Fact> binding(const std::string& id, const std::string& hint, const Node& domain,
                                const Node& expression, const Node& body, const Math& claim,
                                Scope& scope, bool conclusion) {
        const auto type = math(domain);
        if (type.kind == Kind::nat) {
            const auto value = math(expression);
            if (!value.supported()) return pending("unsupported local definition");
            const auto local = bindName(scope.names, id, hint);
            out_ << "Set \\(" << local << " = " << latex(value, scope.names) << "\\).\n";
        } else {
            Scope inner = scope;
            auto fact = prove(expression, type, inner, false);
            if (fact) {
                fact->id = id;
                scope.facts.push_back(*fact);
            }
        }
        return prove(body, claim, scope, conclusion);
    }

    std::optional<Fact> equality(const std::string& name, const Node& raw, const Math& claim,
                                 Scope& scope, bool conclusion) {
        if (name == "Eq.trans") {
            // The checked chain retains its middle expression even when reflexivity
            // has reduced a defining equation to an uninformative reflexive type.
            const Math middle = math(argument(raw, 3));
            const bool useEndpoints = paperStyle_ && claim.kind == Kind::equal && middle.supported();
            const Math left = useEndpoints ? Math(Kind::equal, {}, {}, {claim.parts[0], middle}) : Math();
            const Math right = useEndpoints ? Math(Kind::equal, {}, {}, {middle, claim.parts[1]}) : Math();
            const auto first = obtain(argument(raw, 1), scope, useEndpoints ? &left : nullptr);
            const auto second = obtain(argument(raw, 0), scope, useEndpoints ? &right : nullptr);
            if (!first || !second) return std::nullopt;
            return say(claim, scope, "Combining " + first->reference + " and " +
                       second->reference + " gives", conclusion);
        }
        const auto fact = obtain(argument(raw, 0), scope);
        if (!fact) return std::nullopt;
        if (name == "Eq.symm")
            return say(claim, scope, "Reversing the equality in " + fact->reference + " gives", conclusion);
        const auto& function = term(argument(raw, 1));
        std::string operation = "Applying the same function to both sides of ";
        std::string finish = " gives";
        if (function.is("l") && head(function.at(3)) == "Nat") {
            Names names = scope.names;
            const auto variable = bindName(names, function.at(1).atom, function.at(2).atom);
            const auto value = math(function.at(4));
            if (value.supported() && !value.proposition() && value.kind != Kind::nat) {
                operation = "Applying \\(" + variable + " \\mapsto " + latex(value, names) +
                            "\\) to both sides of ";
                if (paperStyle_ && fact->claim.kind == Kind::equal && claim.kind == Kind::equal &&
                    (!same(applyPredicate(function, fact->claim.parts[0]), claim.parts[0]) ||
                     !same(applyPredicate(function, fact->claim.parts[1]), claim.parts[1])))
                    finish = " and simplifying gives";
            }
        }
        return say(claim, scope, operation + fact->reference + finish, conclusion);
    }

    std::optional<Fact> transport(const Node& raw, const Math& claim, Scope& scope, bool conclusion) {
        const auto* rewrite = &argument(raw, 1);
        while (head(*rewrite) == "id") rewrite = &argument(*rewrite, 0);
        const auto equality = obtain(head(*rewrite) == "congrArg" ? argument(*rewrite, 0) : *rewrite,
                                     scope);
        const auto original = obtain(argument(raw, 0), scope);
        if (!equality || !original) return std::nullopt;
        return say(claim, scope, "Rewriting " + original->reference + " using " +
                   equality->reference + " gives", conclusion);
    }

    std::optional<Fact> witness(const Node& raw, const Math& claim, Scope& scope, bool conclusion) {
        if (claim.kind != Kind::exists && claim.kind != Kind::divides)
            return pending("unsupported witness statement");
        const auto choice = math(argument(raw, 1));
        if (!choice.supported()) return pending("unsupported witness");
        const auto& evidence = argument(raw, 0);
        if (claim.kind == Kind::divides) {
            const Math condition(Kind::equal, {}, {}, {claim.parts[1],
                Math(Kind::mul, {}, {}, {claim.parts[0], choice})});
            return concludeWitness(condition, evidence, choice, claim, scope, conclusion);
        }
        return concludeWitness(Math(), evidence, choice, claim, scope, conclusion);
    }

    std::optional<Fact> concludeWitness(const Math& condition, const Node& evidence,
                                       const Math& choice, const Math& claim,
                                       Scope& scope, bool conclusion) {
        const auto fact = obtain(evidence, scope, condition.supported() ? &condition : nullptr);
        if (!fact) return std::nullopt;
        return say(claim, scope, "With " + escapeLatex(terms_.witness) + " " +
                   inlineMath(choice, scope.names) +
                   ", " + fact->reference + " shows that", conclusion);
    }

    bool chooseWitness(const Node*& branch, const Node& premise, Scope& scope) {
        const auto& lambda = term(*branch);
        if (!lambda.is("l") || head(lambda.at(3)) != "Nat" || !term(lambda.at(4)).is("l")) {
            pending("unsupported witness elimination");
            return false;
        }
        const auto& hypothesis = term(lambda.at(4));
        const auto property = math(hypothesis.at(3));
        if (!property.supported() || !property.proposition()) {
            pending("unsupported witness condition");
            return false;
        }
        const auto existential = obtain(premise, scope);
        if (!existential) return false;
        if (existential->claim.kind != Kind::divides && existential->claim.kind != Kind::exists) {
            pending("unsupported witness premise");
            return false;
        }
        const auto choice = bindName(scope.names, lambda.at(1).atom, lambda.at(2).atom);
        assume(property, hypothesis.at(1).atom, scope, "By " + existential->reference +
               ", choose a natural number \\(" + choice + "\\) such that");
        branch = &hypothesis.at(4);
        return true;
    }

    std::optional<Fact> witnessBranch(const Node* body, const std::vector<const Node*>& premises,
                                      const Math& claim, Scope& scope, bool conclusion) {
        Scope inner = scope;
        if (!conclusion) out_ << (paperStyle_ ? "\\begin{proofstep}\n" : "\\begin{quote}\n");
        std::optional<Fact> branch;
        if (std::all_of(premises.begin(), premises.end(), [&](const Node* premise) {
            return chooseWitness(body, *premise, inner);
        })) branch = prove(*body, claim, inner, true);
        if (!conclusion) out_ << (paperStyle_ ? "\\end{proofstep}\n" : "\\end{quote}\n");
        if (!branch) return std::nullopt;
        if (conclusion) return branch;
        return say(claim, scope, "The witness argument establishes", false);
    }

    std::optional<Fact> eliminate(const Node& raw, const Math& claim, Scope& scope, bool conclusion) {
        return witnessBranch(&argument(raw, 0), {&argument(raw, 1)}, claim, scope, conclusion);
    }

    std::optional<Fact> matchWitnesses(const Node& raw, const Matcher& matcher, const Math& claim,
                                       Scope& scope, bool conclusion) {
        const auto available = raw.children.size();
        if (!raw.is("a") || matcher.parameters >= available || matcher.scrutinees >= available ||
            matcher.scrutinees == 0 || matcher.alternatives.size() != 1 || matcher.equations != 0 ||
            matcher.alternatives.front() != 2 * matcher.scrutinees ||
            available != 4 + matcher.parameters + matcher.scrutinees)
            return pending("unsupported generated match");
        std::vector<const Node*> premises;
        for (std::size_t i = 0; i < matcher.scrutinees; ++i)
            premises.push_back(&raw.at(3 + matcher.parameters + i));
        return witnessBranch(&argument(raw, 0), premises, claim, scope, conclusion);
    }

    bool rewriteReasons(const Node& certificate, Scope& scope, RewriteEvidence& evidence) {
        const auto name = head(certificate);
        if (name == "Eq.refl" || name == "rfl" || name == "eq_self") return true;
        if (name == "Eq.trans" || name == "congr") {
            const auto first = rewriteReasons(argument(certificate, 1), scope, evidence);
            const auto second = rewriteReasons(argument(certificate, 0), scope, evidence);
            return first && second;
        }
        if (name == "Eq.symm" || name == "congrArg" || name == "id")
            return rewriteReasons(argument(certificate, 0), scope, evidence);
        if (name == "congrFun")
            return rewriteReasons(argument(certificate, 1), scope, evidence);
        const auto fact = obtain(certificate, scope);
        if (!fact) return false;
        if (fact->claim.kind != Kind::equal) {
            pending("unsupported simplification certificate");
            return false;
        }
        auto& references = term(certificate).is("v") ? evidence.substitutions : evidence.equalities;
        if (std::find(references.begin(), references.end(), fact->reference) == references.end())
            references.push_back(fact->reference);
        return true;
    }

    std::optional<Fact> simplify(const Node& certificate, const Math& claim, Scope& scope,
                                 bool conclusion) {
        RewriteEvidence evidence;
        if (!rewriteReasons(certificate, scope, evidence)) return std::nullopt;
        std::vector<std::string> actions;
        if (!evidence.substitutions.empty())
            actions.push_back("substituting from " + join(evidence.substitutions));
        if (!evidence.equalities.empty()) actions.push_back("applying " + join(evidence.equalities));
        const auto reason = actions.empty() ? "By computation, we have" : "By " + join(actions) +
                            ", we obtain";
        return say(claim, scope, reason, conclusion);
    }

    std::optional<Fact> equivalence(const Node& raw, const Math& claim, Scope& scope, bool conclusion) {
        if (claim.kind != Kind::iff) return pending("unsupported equivalence statement");
        out_ << "We prove both implications.\n\\begin{description}\n";
        bool complete = true;
        for (std::size_t i = 0; i < 2; ++i) {
            Scope direction = scope;
            const auto& lambda = term(argument(raw, 1 - i));
            out_ << (i == 0 ? "\\item[Forward implication.] " : "\\item[Reverse implication.] ");
            if (!lambda.is("l")) {
                pending("unsupported implication binder");
                complete = false;
                continue;
            }
            assume(claim.parts[i], lambda.at(1).atom, direction, "Assume");
            if (!prove(lambda.at(4), claim.parts[1 - i], direction, true)) complete = false;
        }
        out_ << "\\end{description}\n";
        if (!complete) return std::nullopt;
        if (!conclusion) return say(claim, scope, "The two implications establish", false);
        out_ << "This proves the equivalence.\n";
        return Fact{claim, "", ""};
    }

    std::optional<Fact> implication(const std::string& name, const Node& raw, const Math& claim,
                                    Scope& scope, bool conclusion) {
        const auto equivalence = obtain(argument(raw, 1), scope);
        const auto premise = obtain(argument(raw, 0), scope);
        if (!equivalence || !premise) return std::nullopt;
        return say(claim, scope, std::string("The ") + (name == "Iff.mp" ? "forward" : "reverse") +
                   " implication in " + equivalence->reference + ", applied to " +
                   premise->reference + ", gives", conclusion);
    }

    std::optional<Fact> induction(const std::string& name, const Node& raw, const Math& claim,
                                  Scope& scope, bool conclusion) {
        const auto& motive = argument(raw, 3);
        const bool subjectFirst = name == "Nat.recOn";
        const auto subject = math(argument(raw, subjectFirst ? 2 : 0));
        const auto& zero = argument(raw, subjectFirst ? 1 : 2);
        const auto& step = term(argument(raw, subjectFirst ? 0 : 1));
        if (subject.kind != Kind::var || !step.is("l") || !term(step.at(4)).is("l"))
            return pending("unsupported induction form");
        const auto& hypothesis = term(step.at(4));
        const Math index(Kind::var, step.at(1).atom);
        const Math successor(Kind::add, {}, {}, {index, Math(Kind::numeral, "1")});
        const auto base = applyPredicate(motive, Math(Kind::numeral, "0"));
        const auto next = applyPredicate(motive, successor);
        const auto assumed = math(hypothesis.at(3));
        if (!base.supported() || !next.supported() || !assumed.supported())
            return pending("unsupported induction predicate");

        const bool inductive = !paperStyle_ || binderUses(hypothesis.at(4), hypothesis.at(1).atom);
        out_ << (inductive ? "We proceed by induction on " : "We distinguish the zero and successor cases for ")
             << inlineMath(subject, scope.names) << ".\n\\begin{description}\n"
             << (inductive ? "\\item[Base case.] " : "\\item[Zero case.] ");
        if (!paperStyle_) out_ << "We must show " << inlineMath(base, scope.names) << ".\n";
        Scope baseScope = scope;
        const auto baseResult = prove(zero, base, baseScope, true);

        Scope successorScope = scope;
        const auto variable = bindName(successorScope.names, index.value, step.at(2).atom);
        out_ << (inductive ? "\\item[Inductive step.] " : "\\item[Successor case.] ")
             << "Let \\(" << variable << "\\) be a natural number.\n";
        if (inductive) {
            const auto hypothesisName = "the " + escapeLatex(terms_.inductionHypothesis);
            assume(assumed, hypothesis.at(1).atom, successorScope, "As " + hypothesisName + ", assume");
            if (paperStyle_) successorScope.facts.back().reference = hypothesisName;
        }
        if (!paperStyle_) out_ << "We must show " << inlineMath(next, successorScope.names) << ".\n";
        const auto stepResult = prove(hypothesis.at(4), next, successorScope, true);
        out_ << "\\end{description}\n";
        if (!baseResult || !stepResult) return std::nullopt;
        if (!conclusion) return say(claim, scope, inductive ? "Induction proves" : "Both cases give", false);
        if (inductive) out_ << "This completes the induction.\n";
        return Fact{claim, "", ""};
    }
};

} // namespace

Result writeDocument(const Node& input, std::ostream& output, std::ostream& diagnostics,
                     std::size_t threshold, const Chapter* chapter) {
    const auto& records = input.at(0);
    const auto& library = input.at(1);
    if (!records.array || records.children.empty() || !library.array)
        throw std::runtime_error("Expected ordered theorem records and a prerequisite catalog");

    const bool paper = chapter && chapter->paper;
    Prerequisites prerequisites;
    const auto matchers = readMatchers(input);
    for (const auto& record : library.children) {
        const auto& name = record.at(0).atom;
        auto title = prerequisiteTitle(name);
        if (paper && title == "Natural-number lemma") title = escapeLatex(declarationTitle(name));
        if (paper && record.children.size()>3) {
            const auto conventional = documentedTitle(record.at(3).atom);
            if (!conventional.empty()) title = escapeLatex(conventional);
        }
        if (chapter) {
            const auto override = chapter->prerequisiteTitles.find(name);
            if (override != chapter->prerequisiteTitles.end()) title = escapeLatex(override->second);
        }
        prerequisites.emplace(name, Prerequisite{name, title, &record.at(1), statement(record.at(1)),
                                                  record.at(2).atom == "public"});
    }
    std::map<std::string, std::size_t> documentTheorems;
    const auto ordered = orderTheorems(input, chapter);
    for (const auto* record : ordered)
        documentTheorems.emplace(record->at(0).atom, documentTheorems.size() + 1);
    std::vector<Earlier> earlier;
    std::map<std::string, std::string> earlierReferences;
    Result result;
    std::ostringstream definitions;
    DefinitionRules definedRules;
    std::set<std::string> externalPremises;
    std::map<std::string, const Selection*> selections;
    if (paper) {
        result.incompleteDefinitions = writePaperDefinitions(definitions,input,*chapter,definedRules);
        for (const auto& group : chapter->sections)
            for (const auto& selection : group.theorems)
                selections.emplace(selection.theorem, &selection);
    }
    std::vector<const Prerequisite*> used;
    std::ostringstream body;
    const Terms defaults;
    std::size_t sectionIndex = 0;
    std::size_t nextSection = 0;
    const Section* section = nullptr;
    for (const auto* item : ordered) {
        if (chapter && result.theorems == nextSection) {
            const auto* previous = section;
            section = &chapter->sections.at(sectionIndex++);
            nextSection += section->theorems.size();
            writeSectionHeading(body,*section,previous);
            if (!section->introduction.empty())
                body << escapeLatex(section->introduction) << "\n\n";
        }
        const auto& record = *item;
        const auto& name = record.at(0).atom;
        const auto signature = statement(record.at(1));
        const auto alternateName = selectedAlternate(record);
        diagnostics << name;
        if (!alternateName.empty()) {
            ++result.alternates;
            diagnostics << " (alternate: " << alternateName << ')';
        }
        diagnostics << '\n';
        const std::string role = paper ? selections.at(name)->role : "theorem";
        const std::string title = paper ? selections.at(name)->title : "";
        const auto usedBefore = used.size();
        std::ostringstream rendered, messages;
        const auto cost = paper ? measureProof(record.at(2), &input, chapter->proofWeights) : ProofCost{};
        const bool compact = paper && cost.compactAt(chapter->proofBudget);
        if (paper) diagnostics << "  " << cost.describe() << (compact ? " (compact)\n" : " (expanded)\n");
        Narrator narrator(rendered, messages, prerequisites, used, earlier, documentTheorems,
                          matchers, chapter ? chapter->terms : defaults, threshold, chapter != nullptr,
                          paper, compact);
        ++result.theorems;
        bool complete = narrator.theorem(record.at(1), record.at(2), signature, result.theorems,
                                         section && section->main == name, !alternateName.empty(),
                                         role, title);
        if (!complete && paper) {
            const auto description = describeCheckedStatement(record.at(1));
            std::set<std::string> candidates;
            std::optional<std::string> proof;
            std::string arithmeticCosts;
            if (description) {
                proof = tacticProof(record, input, earlierReferences, candidates, compact,
                                   chapter->proofBudget, chapter->proofWeights, &arithmeticCosts);
                if (!proof) {
                    std::string failure;
                    proof = generalProof(record, input, earlierReferences, definedRules, candidates, compact, &failure);
                    if (!proof && !failure.empty()) messages << "  General proof: " << failure << '\n';
                }
            }
            const bool printable = std::all_of(candidates.begin(), candidates.end(), [&](const auto& key) {
                const auto it = prerequisites.find(key);
                return it != prerequisites.end() && it->second.publicName &&
                       (it->second.signature.supported() || describeCheckedStatement(*it->second.type));
            });
            if (proof && printable) {
                while (used.size() > usedBefore) {
                    prerequisites.at(used.back()->name).ordinal = 0;
                    used.pop_back();
                }
                rendered.str("");
                messages.str("");
                messages << arithmeticCosts;
                beginResult(rendered, role, title, result.theorems);
                rendered << paperStatement(*description) << "\n\\end{" << role << "}\n\n\\begin{proof}\n";
                if (!alternateName.empty())
                    rendered << "\\textit{A separately checked proof is given here.}\n";
                rendered << *proof << "\n\\end{proof}\n\n";
                externalPremises.insert(candidates.begin(), candidates.end());
                complete = true;
            }
        }
        body << rendered.str();
        diagnostics << messages.str();
        if (complete) {
            if (signature.supported()) earlier.push_back({name, signature, result.theorems, role, &record.at(1)});
            earlierReferences.emplace(name, theoremReference(result.theorems, role));
        } else ++result.incomplete;
    }

    const std::string proofText = body.str();
    output << "\\documentclass{article}\n"
           << "\\usepackage{amsmath,amssymb,amsthm}\n" << documentLinks;
    if (paper)
        output << "\\newtheoremstyle{paperresult}{8pt}{5pt}{\\normalfont\\raggedright}{}"
                  "{\\bfseries}{.}{\\newline}{}\n\\theoremstyle{paperresult}\n";
    // amsthm defers the heading until it chooses a page. Attach the PDF
    // destination to the printed name so it moves with that heading.
    output << "\\newtheorem{theorem}{\\paperresultname{Theorem}}\n\\newcounter{paperpremise}\n";
    if (paper)
        output << "\\newtheorem{lemma}[theorem]{\\paperresultname{Lemma}}\n"
               << "\\newtheorem{corollary}[theorem]{\\paperresultname{Corollary}}\n"
               << "\\newcounter{definingequation}\n"
               << "\\newenvironment{proofstep}{\\par\\smallskip"
                  "\\ifdim\\leftskip<3em\\relax\\advance\\leftskip by 1em\\relax\\fi"
                  "\\noindent\\ignorespaces}{\\par\\smallskip}\n"
               << "\\setlength{\\textwidth}{6.5in}\n\\setlength{\\oddsidemargin}{0in}\n"
               << "\\AddToHook{env/proof/begin}{\\raggedright}\n"
               << "\\setlength{\\emergencystretch}{\\linewidth}\n"
               << "\\title{" << escapeLatex(chapter->title) << "}\n\\author{}\n\\date{}\n";
    output << "\\begin{document}\n";
    if (chapter) {
        if (chapter->paper) {
            output << "\\maketitle\n";
            if (!chapter->introduction.empty())
                output << "\\begin{abstract}\n" << escapeLatex(chapter->introduction)
                       << "\n\\end{abstract}\n\n";
            const auto definitionText = definitions.str();
            const auto usesClone = [&](const Prerequisite* p) {
                return containsConstant(*p->type,"SimpleGraph.replaceVertex");
            };
            if (proofText.find("\\operatorname{clone}(")!=std::string::npos ||
                definitionText.find("\\operatorname{clone}(")!=std::string::npos ||
                std::any_of(used.begin(),used.end(),usesClone) ||
                std::any_of(externalPremises.begin(),externalPremises.end(),[&](const auto& name) {
                    return usesClone(&prerequisites.at(name));
                }))
                output << "\\paragraph{Vertex cloning.} In \\(\\operatorname{clone}(G,s,t)\\), "
                          "vertex \\(t\\) takes the neighbors of \\(s\\) in \\(G\\), excluding \\(t\\) itself. "
                          "All edges away from \\(t\\) are preserved.\n\n";
            output << definitionText;
        } else {
            output << "\\section*{" << escapeLatex(chapter->title) << "}\n\n";
            if (!chapter->introduction.empty())
                output << escapeLatex(chapter->introduction) << "\n\n";
        }
        if (!chapter->glossary.empty()) {
            output << "\\subsection*{Glossary}\n\\begin{description}\n";
            for (const auto& entry : chapter->glossary)
                output << "\\item[{\\normalfont\\bfseries " << escapeLatex(entry.first) << "}] "
                       << escapeLatex(entry.second) << '\n';
            output << "\\end{description}\n\n";
        }
    } else {
        output << "\\section*{Proofs in elementary number theory}\n\n";
    }
    if (!used.empty() || !externalPremises.empty()) {
        output << "\\subsection*{Prerequisites}\n\\begin{description}\n";
        for (const auto& name : externalPremises) {
            auto& prerequisite = prerequisites.at(name);
            if (!prerequisite.ordinal) {
                used.push_back(&prerequisite);
                prerequisite.ordinal = used.size();
            }
        }
        for (const auto* prerequisite : used) {
            const auto key = prerequisiteLabel(prerequisite->name);
            output << "\\item[\\paperlineanchor{" << key << "}"
                   << paperLink(key,"P" + std::to_string(prerequisite->ordinal) + ".")
                   << "] \\refstepcounter{paperpremise}\\label{" << key << "}";
            output << "\\textbf{" << prerequisite->title << ".} ";
            if (prerequisite->signature.supported()) output << describe(prerequisite->signature);
            else output << *describeCheckedStatement(*prerequisite->type);
            output << '\n';
        }
        output << "\\end{description}\n\n";
    }
    output << proofText << "\\end{document}\n";
    return result;
}

} // namespace proof
