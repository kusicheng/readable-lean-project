#include "narration.hpp"

#include <algorithm>
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
};

struct Scope {
    Names names;
    std::vector<Fact> facts;

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
};

struct Prerequisite {
    std::string title;
    Statement signature;
    bool publicName;
    std::size_t ordinal = 0;
};

using Prerequisites = std::map<std::string, Prerequisite>;

std::string prerequisiteTitle(const std::string& name) {
    static const std::map<std::string, std::string> titles = {
        {"Nat.dvd_add", "Divisibility of a sum"},
        {"Nat.dvd_zero", "Divisibility of zero"},
        {"Nat.mul_succ", "Multiplication by a successor"},
        {"Nat.mul_zero", "Multiplication by zero"},
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

std::string theoremReference(std::size_t ordinal) {
    return "Theorem~\\ref{theorem:" + std::to_string(ordinal) + "}";
}

std::vector<std::string> instances(const Statement& signature, const Substitution& substitutions,
                                   const Scope& scope) {
    Names formal;
    std::vector<std::string> bindings;
    for (const auto& parameter : signature.parameters) {
        if (parameter.type.kind != Kind::nat) continue;
        const auto name = bindName(formal, parameter.id, parameter.hint);
        const auto argument = substitutions.find(parameter.id);
        if (argument != substitutions.end() && argument->second.supported())
            bindings.push_back("\\(" + name + " = " + latex(argument->second, scope.names) + "\\)");
    }
    return bindings;
}

void theoremDependencies(const Node& expression, const std::map<std::string, const Node*>& records,
                         std::set<std::string>& dependencies) {
    const auto& raw = term(expression);
    if (raw.is("c")) {
        const auto& name = raw.at(1).atom;
        if (records.count(name) != 0) dependencies.insert(name);
    } else {
        for (const auto& child : raw.children) {
            if (child.array) theoremDependencies(child, records, dependencies);
        }
    }
}

std::vector<const Node*> orderTheorems(const Node& records) {
    std::map<std::string, const Node*> byName;
    for (const auto& record : records.children) {
        if (!byName.emplace(record.at(0).atom, &record).second)
            throw std::runtime_error("Duplicate theorem in document");
    }
    std::set<std::string> visited;
    std::set<std::string> active;
    std::vector<const Node*> ordered;
    std::function<void(const Node&)> visit = [&](const Node& record) {
        const auto& name = record.at(0).atom;
        if (visited.count(name) != 0) return;
        if (!active.insert(name).second) throw std::runtime_error("Cyclic theorem dependency");
        std::set<std::string> dependencies;
        theoremDependencies(record.at(2), byName, dependencies);
        for (const auto& candidate : records.children) {
            if (dependencies.count(candidate.at(0).atom) != 0) visit(candidate);
        }
        active.erase(name);
        visited.insert(name);
        ordered.push_back(&record);
    };
    for (const auto& record : records.children) visit(record);
    return ordered;
}

class Narrator {
public:
    Narrator(std::ostream& out, std::ostream& diagnostics, Prerequisites& prerequisites,
             std::vector<const Prerequisite*>& used, const std::vector<Earlier>& earlier,
             const std::map<std::string, std::size_t>& documentTheorems, std::size_t threshold)
        : out_(out), diagnostics_(diagnostics), prerequisites_(prerequisites), used_(used),
          earlier_(earlier), documentTheorems_(documentTheorems), threshold_(threshold) {}

    bool theorem(const Node& type, const Node& expression, const Statement& signature,
                 std::size_t ordinal) {
        out_ << "\\begin{theorem}\\label{theorem:" << ordinal << "}\n";
        if (signature.supported()) out_ << describe(signature) << '\n';
        else out_ << "The statement of this theorem could not be rendered.\n";
        out_ << "\\end{theorem}\n\n\\begin{proof}\n";
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
                    variables.push_back("\\(" + name + "\\)");
                } else {
                    introduceVariables(variables);
                    const Math claim = math(lambda.at(3));
                    assume(claim, id, scope, "Assume");
                }
                currentType = &currentType->at(4);
                currentProof = &lambda.at(4);
            }
            if (bindersSupported) {
                introduceVariables(variables);
                prove(*currentProof, math(*currentType, substitutions), scope, true);
            }
        } else {
            pending("unsupported theorem statement");
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
    std::size_t threshold_;
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
              const std::string& reference, const std::vector<std::string>& premises) {
        auto citation = reference;
        if (!premises.empty()) citation += ", using " + join(premises);
        if (!conclusion) return say(claim, scope, "By " + citation + ", we have", false, true);
        out_ << "The claim follows from " << citation << ".\n";
        return {claim, "", ""};
    }

    Fact citeEarlier(const Earlier& earlier, const Math& claim, const Scope& scope, bool conclusion,
                     const Substitution& substitutions, const std::vector<std::string>& premises) {
        auto citation = theoremReference(earlier.ordinal);
        const auto bindings = instances(earlier.signature, substitutions, scope);
        if (!bindings.empty()) citation += " with " + join(bindings);
        if (!premises.empty()) citation += ", using " + join(premises);
        if (conclusion) {
            out_ << "The claim follows from " << citation << ".\n";
            return {claim, "", ""};
        }
        const auto tag = "(" + newTag() + ")";
        out_ << "Record the instance of " << citation << " as " << tag << ".\n";
        return {claim, tag, ""};
    }

    std::optional<Fact> obtain(const Node& expression, Scope& scope) {
        const auto& raw = term(expression);
        if (raw.is("v")) {
            if (const auto* existing = scope.byId(raw.at(1).atom)) return *existing;
        }
        if (!expression.is("p")) return pending("missing type of supporting fact");
        const auto claim = math(expression.at(1));
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
        if (raw.is("t")) return local(raw, claim, scope, conclusion);
        const auto name = head(raw);
        if (name == "Eq.refl") return say(claim, scope, "By computation, we have", conclusion);
        if (name == "Eq.symm" || name == "Eq.trans" || name == "congrArg")
            return equality(name, raw, claim, scope, conclusion);
        if (name == "Eq.mp" || name == "Eq.mpr")
            return transport(raw, claim, scope, conclusion);
        if (name == "Exists.intro") return witness(raw, claim, scope, conclusion);
        if (name == "Exists.elim") return eliminate(raw, claim, scope, conclusion);
        if (name == "Nat.rec" || name == "Nat.recOn")
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
            if (entry.ordinal == 0) {
                used_.push_back(&entry);
                entry.ordinal = used_.size();
            }
            return cite(claim, scope, conclusion,
                        "Prerequisite~P" + std::to_string(entry.ordinal), *premises);
        }
        return pending(name.empty() ? "unsupported checked term" : name);
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
            const auto fact = obtain(raw.at(i + 2), scope);
            if (!fact) return std::nullopt;
            references.push_back(fact->reference);
        }
        return references;
    }

    std::optional<Fact> local(const Node& raw, const Math& claim, Scope& scope, bool conclusion) {
        const auto& id = raw.at(1).atom;
        const auto type = math(raw.at(3));
        if (type.kind == Kind::nat) {
            const auto value = math(raw.at(4));
            if (!value.supported()) return pending("unsupported local definition");
            const auto local = bindName(scope.names, id, raw.at(2).atom);
            out_ << "Set \\(" << local << " = " << latex(value, scope.names) << "\\).\n";
        } else {
            Scope inner = scope;
            auto fact = prove(raw.at(4), type, inner, false);
            if (fact) {
                fact->id = id;
                scope.facts.push_back(*fact);
            }
        }
        return prove(raw.at(5), claim, scope, conclusion);
    }

    std::optional<Fact> equality(const std::string& name, const Node& raw, const Math& claim,
                                 Scope& scope, bool conclusion) {
        if (name == "Eq.trans") {
            const auto first = obtain(argument(raw, 1), scope);
            const auto second = obtain(argument(raw, 0), scope);
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
        if (function.is("l") && head(function.at(3)) == "Nat") {
            Names names = scope.names;
            const auto variable = bindName(names, function.at(1).atom, function.at(2).atom);
            const auto value = math(function.at(4));
            if (value.supported() && !value.proposition() && value.kind != Kind::nat)
                operation = "Applying \\(" + variable + " \\mapsto " + latex(value, names) +
                            "\\) to both sides of ";
        }
        return say(claim, scope, operation + fact->reference + " gives", conclusion);
    }

    std::optional<Fact> transport(const Node& raw, const Math& claim, Scope& scope, bool conclusion) {
        const auto& rewrite = argument(raw, 1);
        const auto equality = obtain(head(rewrite) == "congrArg" ? argument(rewrite, 0) : rewrite,
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
        const auto fact = obtain(argument(raw, 0), scope);
        if (!fact) return std::nullopt;
        return say(claim, scope, "With witness " + inlineMath(choice, scope.names) +
                   ", " + fact->reference + " shows that", conclusion);
    }

    std::optional<Fact> eliminate(const Node& raw, const Math& claim, Scope& scope, bool conclusion) {
        const auto& lambda = term(argument(raw, 0));
        if (!lambda.is("l") || !term(lambda.at(4)).is("l"))
            return pending("unsupported witness elimination");
        const auto& hypothesis = term(lambda.at(4));
        const auto property = math(hypothesis.at(3));
        if (!property.supported() || !property.proposition()) return pending("unsupported witness condition");
        const auto existential = obtain(argument(raw, 1), scope);
        if (!existential) return std::nullopt;
        Scope inner = scope;
        const auto choice = bindName(inner.names, lambda.at(1).atom, lambda.at(2).atom);
        if (!conclusion) out_ << "\\begin{quote}\n";
        assume(property, hypothesis.at(1).atom, inner, "By " + existential->reference +
               ", choose a natural number \\(" + choice + "\\) such that");
        const auto branch = prove(hypothesis.at(4), claim, inner, true);
        if (!conclusion) out_ << "\\end{quote}\n";
        if (!branch) return std::nullopt;
        if (conclusion) return branch;
        return say(claim, scope, "The witness argument establishes", false);
    }

    std::optional<Fact> induction(const std::string& name, const Node& raw, const Math& claim,
                                  Scope& scope, bool conclusion) {
        const auto& motive = argument(raw, 3);
        const auto subject = math(argument(raw, name == "Nat.rec" ? 0 : 2));
        const auto& zero = argument(raw, name == "Nat.rec" ? 2 : 1);
        const auto& step = term(argument(raw, name == "Nat.rec" ? 1 : 0));
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

        out_ << "We proceed by induction on " << inlineMath(subject, scope.names) << ".\n"
             << "\\begin{description}\n\\item[Base case.] We must show "
             << inlineMath(base, scope.names) << ".\n";
        Scope baseScope = scope;
        const auto baseResult = prove(zero, base, baseScope, true);

        Scope successorScope = scope;
        const auto variable = bindName(successorScope.names, index.value, step.at(2).atom);
        out_ << "\\item[Inductive step.] Let \\(" << variable << "\\) be a natural number.\n";
        assume(assumed, hypothesis.at(1).atom, successorScope, "As the induction hypothesis, assume");
        out_ << "We must show " << inlineMath(next, successorScope.names) << ".\n";
        const auto stepResult = prove(hypothesis.at(4), next, successorScope, true);
        out_ << "\\end{description}\n";
        if (!baseResult || !stepResult) return std::nullopt;
        if (!conclusion) return say(claim, scope, "Induction proves", false);
        out_ << "This completes the induction.\n";
        return Fact{claim, "", ""};
    }
};

} // namespace

Result writeDocument(const Node& input, std::ostream& output, std::ostream& diagnostics,
                     std::size_t threshold) {
    const auto& records = input.at(0);
    const auto& library = input.at(1);
    if (!records.array || records.children.empty() || !library.array)
        throw std::runtime_error("Expected ordered theorem records and a prerequisite catalog");

    Prerequisites prerequisites;
    for (const auto& record : library.children) {
        const auto& name = record.at(0).atom;
        prerequisites.emplace(name, Prerequisite{prerequisiteTitle(name), statement(record.at(1)),
                                                  record.at(2).atom == "public"});
    }
    std::map<std::string, std::size_t> documentTheorems;
    const auto ordered = orderTheorems(records);
    for (const auto* record : ordered)
        documentTheorems.emplace(record->at(0).atom, documentTheorems.size() + 1);
    std::vector<Earlier> earlier;
    std::vector<const Prerequisite*> used;
    std::ostringstream body;
    Result result;
    for (const auto* item : ordered) {
        const auto& record = *item;
        const auto& name = record.at(0).atom;
        const auto signature = statement(record.at(1));
        diagnostics << name << '\n';
        Narrator narrator(body, diagnostics, prerequisites, used, earlier, documentTheorems,
                          threshold);
        ++result.theorems;
        if (narrator.theorem(record.at(1), record.at(2), signature, result.theorems))
            earlier.push_back({name, signature, result.theorems});
        else
            ++result.incomplete;
    }

    output << "\\documentclass{article}\n"
           << "\\usepackage{amsmath,amssymb,amsthm}\n"
           << "\\newtheorem{theorem}{Theorem}\n"
           << "\\begin{document}\n"
           << "\\section*{Proofs in elementary number theory}\n\n";
    if (!used.empty()) {
        output << "\\subsection*{Prerequisites}\n\\begin{description}\n";
        for (const auto* prerequisite : used) {
            output << "\\item[P" << prerequisite->ordinal << ".] "
                   << "\\textbf{" << prerequisite->title << ".} "
                   << describe(prerequisite->signature) << '\n';
        }
        output << "\\end{description}\n\n";
    }
    output << body.str() << "\\end{document}\n";
    return result;
}

} // namespace proof
