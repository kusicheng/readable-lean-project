#include "tactic_proof.hpp"
#include "arithmetic_proof.hpp"
#include "chapter.hpp"

#include <algorithm>
#include <sstream>

namespace proof {
namespace {

// Compare checked syntax including implicit arguments. Binder IDs in two
// serializations of the same expression can differ; display names are irrelevant.
bool equalExpr(const Node& left, const Node& right, Names bound = {}) {
    const auto& a = term(left);
    const auto& b = term(right);
    if (!a.array || !b.array || a.children.empty() || b.children.empty() ||
        a.at(0).atom != b.at(0).atom) return false;
    if (a.is("v")) {
        const auto mapped = bound.find(a.at(1).atom);
        return (mapped == bound.end() ? a.at(1).atom : mapped->second) == b.at(1).atom;
    }
    if (a.is("c") || a.is("n") || a.is("s")) return a.at(1).atom == b.at(1).atom;
    if (a.is("l") || a.is("q") || a.is("t")) {
        if (!equalExpr(a.at(3), b.at(3), bound)) return false;
        if (a.is("t") && !equalExpr(a.at(4), b.at(4), bound)) return false;
        bound[a.at(1).atom] = b.at(1).atom;
        const auto body = a.is("t") ? 5u : 4u;
        return equalExpr(a.at(body), b.at(body), std::move(bound));
    }
    if (a.is("proj"))
        return a.at(1).atom == b.at(1).atom && a.at(2).atom == b.at(2).atom &&
               equalExpr(a.at(3), b.at(3), bound);
    if (!a.is("a") || a.children.size() != b.children.size()) return false;
    for (std::size_t i = 1; i < a.children.size(); ++i)
        if (!equalExpr(a.at(i), b.at(i), bound)) return false;
    return true;
}

const Node& locals(const Node& goal) { return goal.at(1); }
const Node& target(const Node& goal) { return goal.at(2); }
const std::string& id(const Node& goal) { return goal.at(0).atom; }

Names namesOf(const Node& goal) {
    Names names;
    for (const auto& local : locals(goal).children)
        checkedBinderName(names, local.at(0).atom, local.at(1).atom);
    return names;
}

std::optional<std::string> inlineFormula(const Node& expr, const Names& names) {
    const auto rendered = checkedFormula(expr, names);
    if (!rendered) return std::nullopt;
    return "\\(" + *rendered + "\\)";
}

bool proofLocal(const Node& local) { return local.at(3).atom == "proof"; }

bool sameState(const Node& a, const Node& b) {
    if (id(a) != id(b) || !equalExpr(target(a), target(b)) ||
        locals(a).children.size() != locals(b).children.size()) return false;
    for (std::size_t i = 0; i < locals(a).children.size(); ++i) {
        const auto& x = locals(a).at(i);
        const auto& y = locals(b).at(i);
        if (x.at(0).atom != y.at(0).atom || x.at(3).atom != y.at(3).atom ||
            !equalExpr(x.at(2), y.at(2))) return false;
    }
    return true;
}

bool originalGoal(const Node& goal, const Node& theoremType) {
    Names mapped;
    const Node* rest = &theoremType;
    for (const auto& local : locals(goal).children) {
        if (!rest->is("q") || !equalExpr(rest->at(3), local.at(2), mapped)) return false;
        mapped[rest->at(1).atom] = local.at(0).atom;
        rest = &rest->at(4);
    }
    return equalExpr(*rest, target(goal), std::move(mapped));
}

// Check the precise pointwise obligation left by extensionality, including
// its quantifier and the membership instance used on each side.
bool pointwiseEquality(const Node& parent, const Node& child) {
    const auto& eq = target(parent);
    const auto& pointwise = target(child);
    const auto& outer = locals(parent).children;
    const auto& inner = locals(child).children;
    if (head(eq) != "Eq" || !eq.is("a") || eq.children.size() != 5 ||
        inner.size() != outer.size()+1 || inner.back().at(3).atom != "value") return false;
    for (std::size_t i=0; i<outer.size(); ++i)
        if (outer[i].at(0).atom != inner[i].at(0).atom || outer[i].at(3).atom != inner[i].at(3).atom ||
            !equalExpr(outer[i].at(2),inner[i].at(2))) return false;
    const auto& domain = inner.back().at(2);
    const auto& variable = inner.back().at(0).atom;
    const auto& carrier = eq.at(2);
    const auto appliedToVariable = [&](const Node& app,const Node& function) {
        if (!app.is("a") || !argument(app,0).is("v") || argument(app,0).at(1).atom != variable)
            return false;
        if (!function.is("a")) return app.children.size()==3 && equalExpr(app.at(1),function);
        if (app.children.size() != function.children.size()+1) return false;
        for (std::size_t i=1; i<function.children.size(); ++i)
            if (!equalExpr(app.at(i),function.at(i))) return false;
        return true;
    };
    if (carrier.is("q"))
        return equalExpr(carrier.at(3),domain) && head(pointwise) == "Eq" &&
            pointwise.children.size()==5 && appliedToVariable(pointwise.at(3),eq.at(3)) &&
            appliedToVariable(pointwise.at(4),eq.at(4));
    const auto container = head(carrier);
    if ((container != "Finset" && container != "Set") || !carrier.is("a") ||
        carrier.children.size() != 3 || !equalExpr(argument(carrier,0),domain) ||
        head(pointwise) != "Iff" || pointwise.children.size() != 4) return false;
    const auto membership = [&](const Node& expr, const Node& set) {
        return head(expr) == "Membership.mem" && expr.children.size()==7 &&
            head(expr.at(4)) == container+".instMembership" && equalExpr(expr.at(2),domain) &&
            equalExpr(expr.at(3),carrier) && equalExpr(expr.at(5),set) &&
            expr.at(6).is("v") && expr.at(6).at(1).atom == variable;
    };
    return membership(pointwise.at(2),eq.at(3)) && membership(pointwise.at(3),eq.at(4));
}

struct Step {
    const Node* goal;
    const Node* event = nullptr;
    std::vector<std::size_t> children{};
};

std::optional<std::vector<Step>> proofTree(const Node& trace, const Node& theoremType) {
    // The adapter certifies the root by matching the entire declaration body's source span.
    if (trace.children.size() < 3 || !trace.at(2).array || trace.at(2).children.size() != 1)
        return std::nullopt;
    const auto& root = trace.at(2).at(0).atom;
    std::vector<Step> tree;
    std::map<std::string, std::size_t> open;
    for (const auto& event : trace.at(1).children) {
        const auto& before = event.at(1).children;
        const auto& after = event.at(2).children;
        if (tree.empty()) {
            const auto it = std::find_if(before.begin(), before.end(),
                [&](const auto& goal) { return id(goal) == root; });
            if (it == before.end()) continue;
            if (!originalGoal(*it, theoremType)) return std::nullopt;
            tree.push_back({&*it});
            open.emplace(root, 0);
        }
        std::vector<const Node*> changed;
        std::vector<const Node*> produced;
        for (const auto& goal : before) {
            if (std::none_of(after.begin(), after.end(), [&](const Node& x) { return sameState(goal, x); }))
                changed.push_back(&goal);
        }
        if (changed.empty()) continue;
        const auto found = open.find(id(*changed.front()));
        if (found == open.end()) continue; // A macro can expose nested, already-covered transitions.
        if (changed.size() != 1 || !sameState(*tree[found->second].goal, *changed.front()))
            return std::nullopt;
        for (const auto& goal : after) {
            if (std::none_of(before.begin(), before.end(), [&](const Node& x) { return sameState(goal, x); }))
                produced.push_back(&goal);
        }
        const auto parent = found->second;
        open.erase(found);
        tree[parent].event = &event;
        for (const auto* goal : produced) {
            if (!open.emplace(id(*goal), tree.size()).second) return std::nullopt;
            tree[parent].children.push_back(tree.size());
            tree.push_back({goal});
        }
    }
    if (tree.empty() || !open.empty()) return std::nullopt;
    return tree;
}

std::string joined(const std::vector<std::string>& values) {
    std::string text;
    for (std::size_t i = 0; i < values.size(); ++i) {
        if (i) text += i + 1 == values.size() ? " and " : ", ";
        text += values[i];
    }
    return text;
}

bool reflexive(const Node& expr) {
    const auto name = head(expr);
    const auto& raw = term(expr);
    const bool natOrder = name == "Nat.le" || (name == "LE.le" && raw.children.size() == 6 &&
        head(raw.at(2)) == "Nat" && head(raw.at(3)) == "instLENat");
    return name == "True" || ((name == "Eq" || name == "Iff" || natOrder) &&
           equalExpr(argument(expr, 1), argument(expr, 0)));
}

bool naturalDifferenceBound(const Node& expr) {
    const auto& raw = term(expr);
    if (head(raw) != "Nat.le" && !(head(raw) == "LE.le" && raw.children.size() == 6 &&
        head(raw.at(2)) == "Nat" && head(raw.at(3)) == "instLENat")) return false;
    const auto& lhs = term(argument(raw, 1));
    const auto name = head(lhs);
    if (name == "HSub.hSub" && lhs.children.size() == 8) {
        const auto& instance = lhs.at(5);
        if (head(lhs.at(2)) != "Nat" || head(lhs.at(3)) != "Nat" || head(lhs.at(4)) != "Nat" ||
            head(instance) != "instHSub" || head(argument(instance, 0)) != "instSubNat") return false;
    } else if (name != "Nat.sub" || lhs.children.size() != 4) return false;
    return equalExpr(argument(lhs, 1), argument(raw, 0));
}

struct Evidence {
    const Node* proposition;
    std::string reference;
    std::set<std::string> external{};
    std::vector<std::string> derivation{};
};

// Recover the identities on the changed arguments first. The proof also
// contains larger congruence certificates, which obscure these elementary substitutions.
bool replacements(const Node& before, const Node& after, const std::vector<Evidence>& known,
                  std::vector<const Evidence*>& selected) {
    if (equalExpr(before, after)) return true;
    const auto& a = term(before);
    const auto& b = term(after);
    if (a.is("a") && b.is("a") && a.children.size() == b.children.size()) {
        const auto start = selected.size();
        std::size_t i = 1;
        for (; i < a.children.size(); ++i)
            if (!replacements(a.at(i), b.at(i), known, selected)) break;
        if (i == a.children.size()) return true;
        selected.resize(start);
    }
    for (const auto& item : known) {
        const auto rule = head(*item.proposition);
        if (rule != "Eq" && rule != "Iff") continue;
        const auto& x = argument(*item.proposition, 1);
        const auto& y = argument(*item.proposition, 0);
        if ((equalExpr(a, x) && equalExpr(b, y)) || (equalExpr(a, y) && equalExpr(b, x))) {
            selected.push_back(&item);
            return true;
        }
    }
    return false;
}

class TacticWriter {
public:
    TacticWriter(const Node& input, const std::map<std::string,std::string>& earlier,
                 bool compact, std::size_t budget, const ProofWeights& weights)
        : input_(input), earlier_(earlier), compact_(compact), budget_(budget), weights_(weights) {
        for (const auto& record : input.at(0).children) selected_.insert(record.at(0).atom);
        for (const auto& record : input.at(1).children)
            if (record.at(2).atom == "public") library_.emplace(record.at(0).atom, &record.at(1));
    }

    std::optional<std::string> render(const std::vector<Step>& tree) {
        if (!write(tree, 0)) return std::nullopt;
        return out_.str();
    }

    std::set<std::string> used;
    std::string arithmeticCosts;

private:
    const Node& input_;
    const std::map<std::string,std::string>& earlier_;
    bool compact_;
    std::size_t budget_;
    const ProofWeights& weights_;
    std::map<std::string,const Node*> library_;
    std::set<std::string> selected_;
    std::ostringstream out_;

    std::optional<Evidence> support(const Node& fact, const Node& goal, const Names& names) const {
        const auto origin = fact.at(0).atom;
        const auto name = fact.at(1).atom;
        Evidence item{&fact.at(2), {}};
        if (origin == "reflexivity" && ((name == "Eq.refl" && head(fact.at(2)) == "Eq") ||
            (name == "Iff.rfl" && head(fact.at(2)) == "Iff"))) {
            item.reference = "the defining equations";
            return item;
        }
        if (origin == "local") {
            for (const auto& local : locals(goal).children) {
                if (local.at(0).atom != name || !proofLocal(local)) continue;
                const auto statement = inlineFormula(local.at(2), names);
                if (!statement) return std::nullopt;
                item.reference = "the hypothesis " + *statement;
                return item;
            }
            return std::nullopt;
        }
        if (origin != "theorem") return std::nullopt;
        if (const auto prior = earlier_.find(name); prior != earlier_.end())
            item.reference = prior->second;
        else if (library_.count(name) && !selected_.count(name) &&
                 describeCheckedStatement(*library_.at(name))) {
            item.reference = "Prerequisite~P\\ref{" + prerequisiteLabel(name) + "}";
            item.external.insert(name);
        } else return std::nullopt;
        return item;
    }

    std::vector<Evidence> facts(const Step& step, const Names& names) const {
        std::vector<Evidence> known;
        for (const auto& local : locals(*step.goal).children) {
            if (!proofLocal(local)) continue;
            const auto prop = inlineFormula(local.at(2), names);
            if (prop) known.push_back({&local.at(2), "the hypothesis " + *prop});
        }
        const auto& candidates = step.event->at(3).children;
        std::set<const Node*> consumed;
        bool advanced = true;
        while (advanced) {
            advanced = false;
            for (const auto& candidate : candidates) {
                if (consumed.count(&candidate) || candidate.children.size() < 4 || !candidate.at(3).array ||
                    !inlineFormula(candidate.at(2), names) ||
                    std::any_of(known.begin(), known.end(), [&](const auto& fact) {
                        return equalExpr(*fact.proposition, candidate.at(2));
                    })) continue;
                auto fact = support(candidate, *step.goal, names);
                if (!fact) continue;
                std::vector<std::string> premises;
                std::set<std::string> included;
                bool complete = true;
                for (const auto& premise : candidate.at(3).children) {
                    const auto result = std::find_if(known.begin(), known.end(), [&](const auto& x) {
                        return equalExpr(*x.proposition, premise);
                    });
                    if (result == known.end()) { complete = false; break; }
                    const auto prop = inlineFormula(premise, names);
                    if (!prop) { complete = false; break; }
                    premises.push_back(*prop);
                    fact->external.insert(result->external.begin(), result->external.end());
                    for (const auto& line : result->derivation)
                        if (included.insert(line).second) fact->derivation.push_back(line);
                    if (result->reference.rfind("the hypothesis ", 0) != 0) {
                        const auto line = "By " + result->reference + ", we have " + *prop + ".";
                        if (included.insert(line).second) fact->derivation.push_back(line);
                    }
                }
                if (!complete) continue;
                if (!premises.empty()) fact->reference += " applied to " + joined(premises);
                known.push_back(std::move(*fact));
                consumed.insert(&candidate);
                advanced = true;
            }
        }
        return known;
    }

    void use(const Evidence& fact) {
        used.insert(fact.external.begin(), fact.external.end());
        std::set<std::string> printed;
        for (const auto& line : fact.derivation)
            if (printed.insert(line).second) out_ << line << '\n';
    }

    std::optional<std::string> rewrite(const Node& before, const Node& after,
                                       const std::vector<Evidence>& known, const Names& names) {
        std::vector<const Evidence*> rules;
        if (!replacements(before, after, known, rules) || rules.empty()) return std::nullopt;
        std::vector<std::string> references;
        std::set<const Evidence*> emitted;
        for (const auto* rule : rules) {
            if (!emitted.insert(rule).second) continue;
            use(*rule);
            if (!compact_ && rule->reference.rfind("the hypothesis ", 0) != 0) {
                const auto prop = inlineFormula(*rule->proposition, names);
                if (!prop) return std::nullopt;
                out_ << "By " << rule->reference << ", we have " << *prop << ".\n";
            }
            if (std::find(references.begin(), references.end(), rule->reference) == references.end())
                references.push_back(rule->reference);
        }
        return joined(references);
    }

    bool introduce(const Node& parent, const Node& child, const Names& names) {
        for (const auto& local : locals(child).children) {
            const auto existing = std::find_if(locals(parent).children.begin(), locals(parent).children.end(),
                [&](const auto& old) { return old.at(0).atom == local.at(0).atom; });
            if (existing != locals(parent).children.end() && equalExpr(existing->at(2), local.at(2))) continue;
            const auto type = inlineFormula(local.at(2), names);
            if (!type) return false;
            if (proofLocal(local)) out_ << "Assume " << *type << ".\n";
            else out_ << "Fix \\(" << names.at(local.at(0).atom) << "\\) in " << *type << ".\n";
        }
        return true;
    }

    bool terminal(const Node& goal, const std::string& kind, const Names& names,
                  const std::vector<Evidence>& known) {
        const auto& targetExpr = target(goal);
        const auto prop = inlineFormula(targetExpr, names);
        if (!prop) return false;
        for (const auto& item : known) {
            if (!equalExpr(*item.proposition, targetExpr)) continue;
            use(item);
            if (item.reference == "the hypothesis " + *prop)
                out_ << "This is the hypothesis " << *prop << ".\n";
            else out_ << "By " << item.reference << ", we obtain " << *prop << ".\n";
            return true;
        }
        const auto name = head(targetExpr);
        for (const auto& fact : known) {
            if (head(*fact.proposition) == "False") {
                use(fact);
                out_ << "By " << fact.reference << ", this case is impossible.\n";
                return true;
            }
            const auto& neg = term(*fact.proposition);
            const auto* denied = head(neg) == "Not" ? &argument(neg, 0) :
                (neg.is("q") && head(neg.at(4)) == "False") ? &neg.at(3) : nullptr;
            if (!denied) continue;
            for (const auto& affirmed : known) {
                if (!equalExpr(*denied, *affirmed.proposition)) continue;
                use(fact);
                use(affirmed);
                out_ << "The statements supplied by " << fact.reference << " and " << affirmed.reference
                     << " contradict each other. This case is impossible.\n";
                return true;
            }
        }
        if (reflexive(targetExpr) || (kind == "rfl" && (name == "Eq" || name == "Iff"))) {
            out_ << ((name == "Nat.le" || name == "LE.le") ? "By reflexivity of order, " :
                     "By definition, ") << *prop << ".\n";
            return true;
        }
        if (kind == "simp" && naturalDifferenceBound(targetExpr)) {
            out_ << "Subtracting a natural number cannot increase the original value, so " << *prop << ".\n";
            return true;
        }
        if ((kind == "rw" || kind == "simp") && (name == "Eq" || name == "Iff")) {
            const auto& lhs = argument(targetExpr, 1);
            const auto& rhs = argument(targetExpr, 0);
            if (const auto reason = rewrite(lhs, rhs, known, names)) {
                out_ << "Substitution using " << *reason << " gives " << *prop << ".\n";
                return true;
            }
        }
        if (kind == "rw" || kind == "simp") {
            for (const auto& item : known) {
                const auto source = inlineFormula(*item.proposition, names);
                if (!source) continue;
                if (const auto reason = rewrite(*item.proposition, targetExpr, known, names)) {
                    use(item);
                    out_ << "Starting from " << item.reference << ", substitution using " << *reason
                         << " gives " << *prop << ".\n";
                    return true;
                }
            }
        }
        return false;
    }

    bool apply(const std::vector<Step>& tree, const Step& step, const Names& names,
               const std::vector<Evidence>& known, const std::string& prop) {
        for (const auto& candidate : step.event->at(3).children) {
            if (candidate.children.size() < 4 || !candidate.at(3).array ||
                !equalExpr(candidate.at(2), target(*step.goal))) continue;
            const auto rule = support(candidate, *step.goal, names);
            if (!rule) continue;
            std::set<std::size_t> needed;
            std::vector<const Evidence*> available;
            std::vector<std::string> premises;
            bool complete = true;
            for (const auto& premise : candidate.at(3).children) {
                const auto printed = inlineFormula(premise, names);
                if (!printed) { complete = false; break; }
                premises.push_back(*printed);
                const auto child = std::find_if(step.children.begin(), step.children.end(), [&](auto index) {
                    return equalExpr(premise, target(*tree.at(index).goal));
                });
                if (child != step.children.end()) { needed.insert(*child); continue; }
                const auto inScope = std::find_if(known.begin(), known.end(), [&](const auto& item) {
                    return equalExpr(*item.proposition, premise);
                });
                if (inScope == known.end()) { complete = false; break; }
                available.push_back(&*inScope);
            }
            if (!complete || needed.size() != step.children.size()) continue;
            for (const auto* item : available) use(*item);
            for (auto child : step.children) {
                const auto& next = *tree.at(child).goal;
                if (!introduce(*step.goal, next, namesOf(next)) || !write(tree, child)) return false;
            }
            use(*rule);
            out_ << "Applying " << rule->reference << " to " << joined(premises)
                 << " gives " << prop << ".\n";
            return true;
        }
        return false;
    }

    bool write(const std::vector<Step>& tree, std::size_t index) {
        const auto& step = tree.at(index);
        const auto& goal = *step.goal;
        const auto names = namesOf(goal);
        const auto kind = step.event->at(0).atom;
        const auto known = facts(step, names);
        if (step.children.empty()) {
            if (terminal(goal, kind, names, known)) return true;
            if ((kind == "omega" || kind == "linarith") && step.event->children.size() > 4) {
                for (const auto& assignment : step.event->at(4).children) {
                    if (assignment.at(0).atom != id(goal)) continue;
                    const auto cost = measureProof(assignment.at(1), &input_, weights_);
                    const bool compactArithmetic = cost.compactAt(budget_);
                    if (auto proof = arithmeticProof(goal, names, *step.event, input_, compactArithmetic)) {
                        arithmeticCosts += "  Arithmetic step: " + cost.describe() +
                            (compactArithmetic ? " (compact)\n" : " (expanded)\n");
                        out_ << *proof << '\n';
                        return true;
                    }
                }
            }
            return false;
        }
        const auto prop = inlineFormula(target(goal), names);
        if (!prop) return false;
        if (kind == "apply") return apply(tree, step, names, known, *prop);
        if (kind == "ext" && step.children.size() == 1) {
            const auto nextIndex = step.children.front();
            const auto& next = *tree.at(nextIndex).goal;
            if (!pointwiseEquality(goal,next)) return false;
            const auto& leaf = tree.at(nextIndex);
            const auto& variable = locals(next).children.back();
            if (leaf.children.empty() && leaf.event->at(0).atom == "exact") {
                for (const auto& evidence : leaf.event->at(3).children) {
                    if (evidence.at(0).atom != "local" || !equalExpr(evidence.at(2),target(next))) continue;
                    for (const auto& local : locals(goal).children) {
                        const auto& quantified = local.at(2);
                        if (local.at(0).atom != evidence.at(1).atom || !quantified.is("q") ||
                            !equalExpr(quantified.at(3),variable.at(2)) ||
                            !equalExpr(quantified.at(4),target(next),
                                       {{quantified.at(1).atom,variable.at(0).atom}})) continue;
                        const bool functions = target(goal).at(2).is("q");
                        out_ << (functions ? "By hypothesis the functions agree at every argument. " :
                                             "By hypothesis the two sets have the same elements. ")
                             << "Extensionality gives " << *prop << ".\n";
                        return true;
                    }
                }
            }
            const auto names = namesOf(next);
            const auto pointwise = inlineFormula(target(next),names);
            if (!pointwise || !introduce(goal,next,names)) return false;
            out_ << "By extensionality it suffices to show " << *pointwise << ".\n";
            return write(tree,nextIndex);
        }
        if (kind == "simp" || kind == "rw") {
            if (step.children.size() != 1) return false;
            const auto& child = *tree.at(step.children.front()).goal;
            if (locals(goal).children.size() != locals(child).children.size()) return false;
            for (std::size_t i = 0; i < locals(goal).children.size(); ++i) {
                const auto& prior = locals(goal).at(i);
                const auto& fresh = locals(child).at(i);
                if (prior.at(3).atom != fresh.at(3).atom) return false;
                if (!proofLocal(prior) && prior.at(0).atom != fresh.at(0).atom) return false;
                if (equalExpr(prior.at(2), fresh.at(2))) continue;
                if (!proofLocal(prior)) return false;
                const auto original = inlineFormula(prior.at(2), names);
                const auto rewritten = inlineFormula(fresh.at(2), namesOf(child));
                const auto rule = rewrite(prior.at(2), fresh.at(2), known, names);
                if (!original || !rewritten || !rule) return false;
                out_ << "Rewriting the hypothesis " << *original << " using " << *rule
                     << " gives " << *rewritten << ".\n";
            }
            const auto reduced = inlineFormula(target(child), names);
            if (!reduced) return false;
            if (equalExpr(target(goal), target(child))) return write(tree, step.children.front());
            if (const auto reason = rewrite(target(goal), target(child), known, names)) {
                out_ << "Substituting by " << *reason << " reduces the claim to " << *reduced << ".\n";
                return write(tree, step.children.front());
            }
            return false;
        }
        const bool branches = kind == "induction" || kind == "cases";
        if (!branches && kind != "intro" && kind != "constructor") return false;
        if (kind == "constructor" && head(target(goal)) != "And" && head(target(goal)) != "Iff")
            return false;
        if (compact_ && kind == "constructor" && head(target(goal)) == "And" && step.children.size() == 2) {
            std::vector<const Evidence*> evidence;
            std::vector<std::string> premises;
            for (auto child : step.children) {
                const auto& branch = tree.at(child);
                if (!branch.children.empty()) break;
                const auto needed = std::find_if(known.begin(), known.end(), [&](const auto& fact) {
                    return equalExpr(*fact.proposition, target(*branch.goal));
                });
                if (needed == known.end()) break;
                evidence.push_back(&*needed);
                premises.push_back(needed->reference);
            }
            if (premises.size() == 2) {
                for (const auto* item : evidence) use(*item);
                out_ << "Together, " << joined(premises) << " give " << *prop << ".\n";
                return true;
            }
        }
        if (kind == "cases" && compact_) out_ << "Consider the following cases.\n";
        else if (branches)
            out_ << (kind == "induction" ? "We use induction to prove " : "We distinguish cases to prove ")
                 << *prop << ".\n";
        else if (kind == "constructor")
            out_ << (head(target(goal)) == "Iff" ? "We prove both implications.\n" : "We prove both claims.\n");
        for (const auto child : step.children) {
            const auto& next = *tree.at(child).goal;
            if (branches || step.children.size() > 1) out_ << "\\begin{proofstep}\n";
            const auto names = namesOf(next);
            if (!introduce(goal, next, names)) return false;
            if (branches && !compact_) {
                const auto claim = inlineFormula(target(next), names);
                if (!claim) return false;
                out_ << "In this case we must show " << *claim << ".\n";
            }
            if (!write(tree, child)) return false;
            if (branches || step.children.size() > 1) out_ << "\\end{proofstep}\n";
        }
        if (branches) out_ << (kind == "induction" ? "This proves the assertion by induction.\n" :
                                                    "The cases exhaust the possibilities.\n");
        return true;
    }
};

} // namespace

std::optional<std::string> tacticProof(const Node& record, const Node& input,
    const std::map<std::string,std::string>& earlierReferences, std::set<std::string>& externalPremises,
    bool compact, std::size_t budget, const ProofWeights& weights, std::string* arithmeticCosts) {
    if (input.children.size() < 6 || !input.at(5).array) return std::nullopt;
    for (const auto& trace : input.at(5).children) {
        if (trace.at(0).atom != record.at(0).atom) continue;
        const auto tree = proofTree(trace, record.at(1));
        if (!tree) return std::nullopt;
        TacticWriter writer(input, earlierReferences, compact, budget, weights);
        auto proof = writer.render(*tree);
        if (proof) {
            externalPremises.insert(writer.used.begin(), writer.used.end());
            if (arithmeticCosts) *arithmeticCosts = std::move(writer.arithmeticCosts);
        }
        return proof;
    }
    return std::nullopt;
}

} // namespace proof
