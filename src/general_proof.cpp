#include "general_proof.hpp"
#include "auxiliary_lemmas.hpp"
#include "nat_below.hpp"
#include "ring_equality.hpp"
#include "paper_links.hpp"
#include "positive_denominator.hpp"
#include "checked_calculation.hpp"
#include "record_equality.hpp"
#include "indexed_record_equality.hpp"
#include "tree_below.hpp"
#include "chapter.hpp"

#include <algorithm>
#include <charconv>
#include <sstream>
#include <stdexcept>

namespace proof {
namespace {

struct Context {
    Names names;
    Names statementToProofBinders;
    std::map<std::string, std::string> assumptions;
    std::map<std::string, const Node*> hypothesisTypes;
    std::set<std::string> provedFacts;
    std::string inductionHypothesis;
    std::string wellFoundedHypothesis;
};

const Node* chosenPredicate(const Node& expr, const std::string& proofId) {
    if (expr.is("a") && expr.children.size()==5 && head(expr)=="Classical.choose") {
        const auto& evidence = term(argument(expr,0));
        const auto& predicate = term(argument(expr,1));
        if (evidence.is("v") && evidence.at(1).atom==proofId && predicate.is("l"))
            return &predicate;
    }
    for (const auto& child : expr.children) {
        if (child.array)
            if (const auto* result = chosenPredicate(child,proofId)) return result;
    }
    return nullptr;
}

// Introduce a chosen witness immediately after the assertion that supplies it.
// The same local proof identifies the choice throughout its dependent scope.
void introduceChosenWitness(const Node& body, const Node& type, const std::string& proofId,
                            Context& ctx, std::ostream& out) {
    const auto name = head(type);
    if (name!="Exists" && name!="Finset.Nonempty" && name!="Set.Nonempty") return;
    const auto* predicate = chosenPredicate(body,proofId);
    if (!predicate) return;
    const std::string key = "#chosen-witness:" + proofId;
    auto names = ctx.names;
    const auto witness = checkedBinderName(names,key,predicate->at(2).atom);
    names[predicate->at(1).atom] = witness;
    const auto property = checkedFormula(predicate->at(4),names);
    if (!property) return;
    ctx.names[key] = witness;
    out << "Fix \\(" << witness << "\\) such that \\(" << *property << "\\).\n";
}

// Data in a library instance can include a closed operation such as (a,b) ↦ a+b.
// A captured local or an embedded proof needs its own explanation.
bool closedInstanceData(const Node& n, const std::set<std::string>& bound = {}) {
    if (n.is("c")) return n.children.size()<3 || n.at(2).atom!="proof";
    if (n.is("n") || n.is("s")) return true;
    if (n.is("v")) return bound.count(n.at(1).atom)!=0;
    if (n.is("l")) {
        if (!closedInstanceData(n.at(3),bound)) return false;
        auto inner = bound;
        inner.insert(n.at(1).atom);
        return closedInstanceData(n.at(4),inner);
    }
    return n.is("a") && std::all_of(n.children.begin()+1,n.children.end(),
        [&](const Node& argument) { return closedInstanceData(argument,bound); });
}

// Only these closed library instances and their superclass proofs may be
// folded into a natural-number subtraction step.
bool naturalOrderInstance(const Node& evidence) {
    const auto& raw = term(evidence);
    if (raw.is("c"))
        return head(raw) == "Nat.instOrderedSub" || head(raw) == "Nat.instIsOrderedAddMonoid" ||
               head(raw) == "Nat.instIsOrderedCancelAddMonoid";
    static const std::map<std::string,std::vector<std::size_t>> projections{
        {"IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT",{4,6}},
        {"IsCancelAdd.toIsLeftCancelAdd",{4}}, {"IsOrderedCancelAddMonoid.toIsCancelAdd",{5}},
        {"contravariant_lt_of_covariant_le",{5}}, {"IsOrderedAddMonoid.toAddLeftMono",{5}}
    };
    const auto it = projections.find(head(raw));
    if (!raw.is("a") || it==projections.end() || raw.children.size()!=it->second.back()+1 ||
        !raw.at(2).is("c") || head(raw.at(2))!="Nat") return false;
    std::vector<const Node*> premises;
    if (!proofArguments(raw,premises) || premises.size()!=it->second.size()) return false;
    for (std::size_t i=0; i<premises.size(); ++i)
        if (premises[i]!=&raw.at(it->second[i]) || !naturalOrderInstance(*premises[i])) return false;
    for (std::size_t i=2; i<raw.children.size(); ++i)
        if (std::find(premises.begin(),premises.end(),&raw.at(i))==premises.end() &&
            !closedInstanceData(raw.at(i))) return false;
    return true;
}

std::string attribute(const Node& node, std::size_t i) {
    return i < node.children.size() ? node.at(i).atom : "";
}

std::optional<std::string> formula(const Node& expr, const Context& ctx);

// Delimiter sizing and optional line breaks do not change a displayed formula.
std::string withoutLayout(std::string math) {
    for (const std::string token : {"\\left", "\\right", "\\allowbreak{}"}) {
        std::size_t pos = 0;
        while ((pos=math.find(token,pos))!=std::string::npos) {
            const auto next = pos + token.size();
            if (next < math.size() && ((math[next]>='a' && math[next]<='z') ||
                                      (math[next]>='A' && math[next]<='Z'))) pos = next;
            else math.erase(pos,token.size());
        }
    }
    return math;
}

bool endsWithFormula(const std::string& proof, const std::string& formula) {
    const auto text = withoutLayout(proof);
    const auto ending = withoutLayout(formula) + ".\n";
    return text.size() >= ending.size() && text.compare(text.size()-ending.size(),ending.size(),ending)==0;
}

struct Rule {
    std::string reason;
    bool branches = false;
};

struct RewriteReasons {
    std::vector<std::string> sources;
    std::vector<std::string> bijections;
    std::size_t identities = 0;
    std::size_t arguments = 0;
};

// These NormNum certificates reduce natural numerals by definition. A local
// equality or a nonnumerical lemma must take the ordinary proof-writing path.
bool numeralEvidence(const Node& expr) {
    const auto& raw = term(expr);
    const auto name = head(raw);
    if (name == "Eq.refl" || name == "rfl") return true;
    if (name != "Mathlib.Meta.NormNum.isNat_ofNat" && name != "Mathlib.Meta.NormNum.isNat_add" &&
        name != "Mathlib.Meta.NormNum.isNat_mul") return false;
    std::vector<const Node*> premises;
    return proofArguments(raw,premises) && std::all_of(premises.begin(),premises.end(),[](const Node* premise) {
        return numeralEvidence(*premise);
    });
}

std::optional<std::string> numericalRewrite(const Node& raw) {
    if (head(raw) != "Mathlib.Meta.NormNum.IsNat.to_eq" || raw.children.size() != 9 ||
        head(raw.at(2)) != "Nat" || !raw.at(4).is("n") ||
        (head(raw.at(8)) != "Eq.refl" && head(raw.at(8)) != "rfl")) return {};
    const auto instance = head(raw.at(3));
    if (instance != "Nat.instAddMonoidWithOne" && instance != "Mathlib.Meta.NormNum.instAddMonoidWithOneNat")
        return {};
    const auto& computation = term(raw.at(7));
    if (numeralEvidence(computation)) return "evaluation of natural-number arithmetic";
    if (head(computation) != "Mathlib.Meta.NormNum.isNat_natDiv" || computation.children.size() != 10 ||
        !computation.at(4).is("n") || !computation.at(5).is("n") || !computation.at(6).is("n")) return {};
    std::vector<const Node*> premises;
    if (!proofArguments(computation,premises) ||
        !std::all_of(premises.begin(),premises.end(),[](const Node* premise) { return numeralEvidence(*premise); }))
        return {};
    const auto& dividend = computation.at(4).at(1).atom;
    const auto& divisor = computation.at(5).at(1).atom;
    const auto& quotient = computation.at(6).at(1).atom;
    if (divisor == "0")
        return "the natural-number division convention \\(" + dividend + "\\mathbin{\\mathrm{div}}0 = 0\\)";
    return "the quotient \\(\\left\\lfloor\\frac{" + dividend + "}{" + divisor + "}\\right\\rfloor = " + quotient + "\\)";
}

// Lean can retain an immediately-applied local lambda in a checked proof,
// particularly in the congruence evidence produced by simplification.
std::optional<Node> instantiate(const Node& function, const Node& raw, bool signature = false,
                                std::optional<std::size_t> domainAt = std::nullopt) {
    std::map<std::string,const Node*> values;
    const Node* body = &function;
    std::size_t i = 2;
    for (; raw.is("a") && i<raw.children.size(); ++i) {
        if (!body->is(signature ? "q" : "l")) {
            if (domainAt) return {};
            break;
        }
        if (domainAt == i) { body = &body->at(3); break; }
        values.emplace(body->at(1).atom, &raw.at(i));
        body = &body->at(4);
    }
    if (domainAt && (i != *domainAt || i >= raw.children.size())) return {};
    auto reduced = *body;
    const auto substitute = [&](auto&& self, Node& node) -> void {
        if (node.is("v")) {
            const auto it = values.find(node.at(1).atom);
            if (it != values.end()) node = *it->second;
        } else if (node.is("a") && node.at(1).is("v") && values.count(node.at(1).at(1).atom)) {
            // Argument proof roles belong to the applied head, not the bare replacement.
            Node& fn = node.children[1];
            auto replacement = *values.at(fn.at(1).atom);
            if ((replacement.is("c") || replacement.is("v")) && fn.children.size() >= 5) {
                replacement.children.resize(5);
                std::copy(fn.children.begin()+2, fn.children.begin()+5, replacement.children.begin()+2);
            } else if (replacement.is("a") && fn.children.size() >= 5 &&
                       (replacement.at(1).is("c") || replacement.at(1).is("v")) &&
                       replacement.at(1).children.size() >= 5) {
                // For example, substituting membership in a fixed set for P
                // in P(x) fills the second object slot of the original relation.
                const auto offset = replacement.children.size()-2;
                auto& head = replacement.children[1];
                head.children[2] = fn.at(2);
                for (std::size_t k : {3u,4u})
                    for (auto slot : fn.at(k).children) {
                        std::size_t index = 0;
                        const auto end = slot.atom.data()+slot.atom.size();
                        const auto parsed = std::from_chars(slot.atom.data(),end,index);
                        if (parsed.ec != std::errc{} || parsed.ptr != end || index >= node.children.size()-2)
                            throw std::runtime_error("Invalid argument position in checked application");
                        slot.atom = std::to_string(offset+index);
                        head.children[k].children.push_back(std::move(slot));
                    }
                for (std::size_t j=2;j<node.children.size();++j) {
                    self(self,node.children[j]);
                    replacement.children.push_back(std::move(node.children[j]));
                }
                node = std::move(replacement);
                return;
            }
            fn = std::move(replacement);
            for (std::size_t i=2;i<node.children.size();++i) self(self,node.children[i]);
        } else for (auto& child : node.children) if (child.array) self(self,child);
    };
    substitute(substitute,reduced);
    if (!domainAt && raw.is("a") && i < raw.children.size()) {
        // A lambda can return another function. Lean flattens the entire call
        // into one application, so keep the operands after the lambda telescope.
        // The annotation describes the unapplied function, not its final result.
        if (reduced.is("p")) reduced = Node(reduced.at(2));
        if (signature || !reduced.is("a")) return std::nullopt;
        reduced.children.reserve(reduced.children.size() + raw.children.size() - i);
        auto& fn = reduced.children[1];
        if ((!fn.is("c") && !fn.is("v")) || fn.children.size() < 5) return std::nullopt;
        for (; i<raw.children.size(); ++i) {
            const auto& arg = raw.at(i);
            const auto& r = term(arg);
            const auto& applied = r.is("a") ? term(r.at(1)) : r;
            const auto role = arg.is("p") ? "proof" :
                (applied.is("c") || applied.is("v")) ? attribute(applied,2) :
                (r.is("l") || r.is("q")) ? attribute(r,7) : r.is("n") ? "value" : r.is("s") ? "type" : "";
            if (role.empty()) return std::nullopt;
            if (role == "proof") {
                Node slot;
                slot.atom = std::to_string(reduced.children.size()-2);
                fn.children[4].children.push_back(std::move(slot));
            }
            reduced.children.push_back(arg);
        }
    }
    return reduced;
}

std::optional<Node> betaContract(const Node& raw) {
    if (!raw.is("a") || !raw.at(1).is("l")) return std::nullopt;
    return instantiate(raw.at(1), raw);
}

// Proof annotations sometimes retain an applied dependent lambda inside an
// operand. Substitution can erase a proof argument irrelevant to its value.
void reduceForDisplay(Node& node, unsigned& remaining) {
    if (!remaining || !node.array || node.is("c") || node.is("v")) return;
    if (auto reduced = betaContract(node)) {
        --remaining;
        node = std::move(*reduced);
        reduceForDisplay(node,remaining);
        return;
    }
    for (auto& child : node.children) if (child.array) reduceForDisplay(child,remaining);
}

std::optional<std::string> formula(const Node& expr, const Context& ctx) {
    auto text = checkedFormula(expr,ctx.names);
    if (!text) {
        auto reduced = expr;
        unsigned remaining = 200;
        reduceForDisplay(reduced,remaining);
        if (remaining < 200) text = checkedFormula(reduced,ctx.names);
    }
    if (text) *text = "\\(" + *text + "\\)";
    return text;
}

// Lean's alias command can inline the kernel proof of an earlier theorem.
// Match the term and its specialized type, allowing fresh bound variable IDs.
bool sameKernelTerm(const Node& a, const Node& b, const Names& bound = {}) {
    const auto& l = term(a);
    const auto& r = term(b);
    if (!l.array || !r.array || l.at(0).atom != r.at(0).atom) return false;
    if (l.is("c") || l.is("s") || l.is("n")) return l.at(1).atom == r.at(1).atom;
    if (l.is("v")) {
        if (auto it=bound.find(l.at(1).atom); it!=bound.end()) return it->second == r.at(1).atom;
        return l.at(1).atom == r.at(1).atom && std::none_of(bound.begin(),bound.end(),
            [&](const auto& entry) { return entry.second == r.at(1).atom; });
    }
    if (l.is("l") || l.is("q") || l.is("t")) {
        if (!sameKernelTerm(l.at(3),r.at(3),bound)) return false;
        if (l.is("t") && !sameKernelTerm(l.at(4),r.at(4),bound)) return false;
        auto inner = bound;
        inner[l.at(1).atom] = r.at(1).atom;
        return sameKernelTerm(l.at(l.is("t") ? 5 : 4),r.at(r.is("t") ? 5 : 4),inner);
    }
    if (l.is("proj"))
        return l.at(1).atom == r.at(1).atom && l.at(2).atom == r.at(2).atom &&
               sameKernelTerm(l.at(3),r.at(3),bound);
    if (!l.is("a") || l.children.size() != r.children.size()) return false;
    for (std::size_t i=1; i<l.children.size(); ++i)
        if (!sameKernelTerm(l.at(i),r.at(i),bound)) return false;
    return true;
}

// The motive of a recursor gives its result type even when a proof occurs in
// function position and therefore has no separate proposition annotation.
std::optional<Node> recursorConclusion(const Node& raw, const std::string& name) {
    if (!raw.is("a") || raw.children.size()<7 || !raw.at(4).is("l")) return {};
    std::vector<std::size_t> indices;
    std::size_t arity;
    if (name == "Eq.rec") { indices={6,7}; arity=6; }
    else if (name == "Eq.ndrec") { indices={6}; arity=6; }
    else if (name == "Eq.casesOn") { indices={5,6}; arity=6; }
    else if (name == "HEq.casesOn") { indices={5,6,7}; arity=7; }
    else if (name == "And.casesOn" || name == "Exists.casesOn") { indices={5}; arity=5; }
    else return {};
    if (raw.children.size()<arity+2) return {};
    Node app;
    app.array = true;
    app.children = {raw.at(0),raw.at(4)};
    for (auto index : indices) app.children.push_back(raw.at(index));
    auto result = instantiate(raw.at(4),app);
    if (!result || raw.children.size() == arity+2) return result;
    app.children.resize(2);
    app.children.insert(app.children.end(),raw.children.begin()+arity+2,raw.children.end());
    return instantiate(*result,app,true);
}

std::optional<Node> logicalConclusion(const Node& raw, const std::string& name) {
    if (!raw.is("a")) return {};
    const auto str = [](const char* s) { Node n; n.atom=s; return n; };
    const auto tuple = [](std::vector<Node> xs) { Node n; n.array=true; n.children=std::move(xs); return n; };
    const auto arity = raw.children.size()-2;
    if (name == "Exists.intro" && arity == 4) {
        const auto exists = tuple({str("c"),str("Exists"),str("prop"),tuple({str("1")}),tuple({})});
        return tuple({str("a"),exists,raw.at(2),raw.at(3)});
    }
    const char* connective = nullptr;
    if (name == "And.intro" && arity == 4) connective = "And";
    if (name == "Iff.intro" && arity == 4) connective = "Iff";
    if ((name == "Or.inl" || name == "Or.inr") && arity == 3) connective = "Or";
    if (connective) {
        const auto op = tuple({str("c"),str(connective),str("prop"),tuple({str("0"),str("1")}),tuple({})});
        return tuple({str("a"),op,raw.at(2),raw.at(3)});
    }
    const auto eq = tuple({str("c"),str("Eq"),str("prop"),tuple({str("1"),str("2")}),tuple({})});
    if (name == "propext" && arity == 3) {
        // An unannotated application of the axiom has type P = Q in Prop.
        // The ordinary rule below still has to derive its equivalence proof.
        std::vector<const Node*> proofs;
        if (!proofArguments(raw,proofs) || proofs.size()!=1 || proofs.front()!=&raw.at(4)) return {};
        return tuple({str("a"),eq,tuple({str("s"),str("0")}),raw.at(2),raw.at(3)});
    }
    const Node* left;
    const Node* right;
    if ((name == "Eq.refl" || name == "rfl") && arity == 2) left=right=&raw.at(3);
    else if (name == "Eq.trans" && arity == 6) { left=&raw.at(3); right=&raw.at(5); }
    else if (name == "Eq.symm" && arity == 4) { left=&raw.at(4); right=&raw.at(3); }
    else return {};
    return tuple({str("a"),eq,raw.at(2),*left,*right});
}

const std::map<std::string, Rule> rules = {
    {"Eq.refl", {"By definition"}}, {"rfl", {"By definition"}},
    {"Eq.symm", {"Reversing the equality"}}, {"Eq.trans", {"Chaining the equalities"}},
    {"Eq.mp", {"Substituting along the equality"}}, {"Eq.mpr", {"Substituting along the equality"}},
    {"Eq.rec", {"Substituting equals"}}, {"Eq.ndrec", {"Substituting equals"}},
    {"Eq.recOn", {"Substituting equals"}}, {"Eq.casesOn", {"Substituting equals"}},
    {"Eq.ndrecOn", {"Substituting equals"}}, {"Eq.subst", {"Substituting equals"}},
    {"HEq.casesOn", {"Substituting along the heterogeneous equality"}},
    {"cast", {"Transporting the result along the equality"}},
    {"HEq.refl", {"By reflexivity"}}, {"HEq.rfl", {"By reflexivity"}},
    {"Trans.trans", {"By transitivity of the displayed relations"}},
    {"Function.comp", {"Composing these implications"}},
    {"Quot.ind", {"Every element of the quotient has a representative", true}},
    {"Quotient.ind", {"Every element of the quotient has a representative", true}},
    {"Prod.casesOn", {"Every ordered pair has two components", true}},
    {"Finset.casesOn", {"A finite set is represented by a multiset without repetitions", true}},
    {"Subtype.casesOn", {"Using the underlying element and its defining property", true}},
    {"Fin.casesOn", {"Using the natural number and its upper bound", true}},
    {"dite", {"The proposition or its negation holds", true}},
    {"ite", {"The proposition or its negation holds", true}},
    {"congrArg", {"Applying the same function to equal arguments"}},
    {"congrFun", {"Evaluating the equal functions at the same argument"}},
    {"congr", {"By congruence"}}, {"propext", {"By propositional extensionality"}},
    {"funext", {"By function extensionality"}}, {"True.intro", {"By the definition of truth"}},
    {"False.elim", {"The contradiction rules out this case"}},
    {"absurd", {"The assertion contradicts its negation"}},
    {"isEmptyElim", {"The putative element belongs to an empty type"}},
    {"And.intro", {"Combining the two conclusions"}}, {"And.left", {"Taking the first conjunct"}},
    {"And.right", {"Taking the second conjunct"}}, {"And.elim", {"Using the two conjuncts"}},
    {"Or.inl", {"The first alternative suffices"}}, {"Or.inr", {"The second alternative suffices"}},
    {"Or.elim", {"The two alternatives exhaust the cases", true}},
    {"Or.casesOn", {"The two alternatives exhaust the cases", true}},
    {"Iff.intro", {"Together the two implications give the equivalence", true}},
    {"Iff.mp", {"By the forward implication"}}, {"Iff.mpr", {"By the reverse implication"}},
    {"Iff.trans", {"Chaining the equivalences"}}, {"Iff.symm", {"Reversing the equivalence"}},
    {"Exists.intro", {"This witness proves existence"}}, {"Exists.elim", {"Using the existential hypothesis", true}},
    {"Nonempty.intro", {"This element witnesses nonemptiness"}},
    {"Exists.casesOn", {"Using the existential hypothesis", true}},
    {"And.casesOn", {"Using the two conjuncts", true}},
    {"Decidable.casesOn", {"The proposition and its negation exhaust the cases", true}},
    {"Classical.byContradiction", {"The contrary assumption leads to a contradiction", true}},
    {"Decidable.byContradiction", {"The contrary assumption leads to a contradiction", true}},
    {"Classical.byCases", {"The two cases are exhaustive", true}},
    {"Decidable.byCases", {"The two cases are exhaustive", true}},
    {"Nat.rec", {"By induction on the natural number", true}},
    {"Nat.recOn", {"By induction on the natural number", true}},
    {"Nat.recAux", {"By induction on the natural number", true}},
    {"Nat.strongRecOn", {"By strong induction on the natural number", true}},
    {"Nat.caseStrongRecOn", {"By strong induction on the natural number", true}},
    {"Nat.case_strong_induction_on", {"By strong induction on the natural number", true}},
    {"Nat.casesAuxOn", {"The zero and successor cases exhaust the natural numbers", true}},
    {"Nat.one_pos", {"Zero is less than one"}},
    {"Finset.strongDownwardInductionOn", {"By descending induction under the cardinality bound", true}},
    {"Finset.strongInductionOn", {"By strong induction on strict subsets", true}},
    {"Nat.decreasingInduction'", {"By downward induction through this interval", true}},
    {"List.rec", {"By induction on the list", true}},
    {"List.recOn", {"By induction on the list", true}},
    {"Bool.rec", {"The two Boolean cases are exhaustive", true}},
    {"Bool.casesOn", {"The two Boolean cases are exhaustive", true}},
    {"id", {"By the preceding argument"}}
};

const std::set<std::string> equalityEliminators = {
    "Eq.mp", "Eq.mpr", "Eq.rec", "Eq.ndrec", "Eq.recOn", "Eq.ndrecOn", "Eq.casesOn", "Eq.subst",
    "HEq.casesOn", "HEq.rec", "HEq.ndrec", "cast"
};

// Equality elimination may have a motive that depends on an equality proof.
// Its reflexive case then binds equalities between proofs. Check every premise
// in that scope and retain the external equalities used by the substitution.
template<class Cite>
bool equalityEvidence(const Node& expr, const Context& ctx, std::set<std::string> local,
                      std::vector<std::string>& sources, Cite& cite) {
    const auto& raw = term(expr);
    if (auto reduced = betaContract(raw)) return equalityEvidence(*reduced,ctx,std::move(local),sources,cite);
    if (raw.is("l")) {
        if (attribute(raw,6) == "proof") local.insert(raw.at(1).atom);
        return equalityEvidence(raw.at(4),ctx,std::move(local),sources,cite);
    }
    const auto& fn = raw.is("a") ? raw.at(1) : raw;
    if (fn.is("v")) {
        const auto& id = fn.at(1).atom;
        if (!local.count(id)) {
            const auto it = ctx.assumptions.find(id);
            if (it == ctx.assumptions.end()) return false;
            if (std::find(sources.begin(),sources.end(),it->second) == sources.end())
                sources.push_back(it->second);
        }
    } else {
        static const std::set<std::string> congruence = {
            "Eq.refl", "rfl", "HEq.refl", "HEq.rfl", "Eq.trans", "Eq.symm", "congr", "congrArg", "congrFun",
            "id", "eq_of_heq", "heq_of_eq", "funext", "propext", "Lean.Meta.FastSubsingleton.elim",
            "Lean.Meta.instFastSubsingletonDecidable", "Lean.Meta.instFastSubsingletonForall"
        };
        const auto name = head(raw);
        std::string principle;
        if (!equalityEliminators.count(name) && !congruence.count(name)) {
            auto reference = cite(name);
            if (!reference) return false;
            principle = *reference;
        } else if (name == "funext" || name == "Lean.Meta.instFastSubsingletonForall")
            principle = "function extensionality";
        else if (name == "propext") principle = "propositional extensionality";
        if (name == "Lean.Meta.instFastSubsingletonDecidable")
            principle = "uniqueness of a decision for a fixed proposition";
        if (!principle.empty() && std::find(sources.begin(),sources.end(),principle) == sources.end())
            sources.push_back(principle);
    }
    std::vector<const Node*> premises;
    if (!proofArguments(raw,premises)) return false;
    for (const auto* premise : premises)
        if (!equalityEvidence(*premise,ctx,local,sources,cite)) return false;
    return true;
}

class ProofWriter {
public:
    ProofWriter(const Node& input, const std::map<std::string,std::string>& earlier,
                const DefinitionRules& definitions, bool compact, const std::map<std::string,std::string>& auxiliary)
        : earlier_(earlier), compact_(compact), definitions_(definitions), auxiliary_(auxiliary) {
        for (const auto& [name,equation] : definitions)
            signatures_.emplace(name,equation.type);
        for (const auto& record : input.at(0).children) {
            selected_.insert(record.at(0).atom);
            signatures_.emplace(record.at(0).atom, &record.at(1));
            if (earlier.count(record.at(0).atom)) earlierProofs_.emplace_back(&record);
        }
        for (const auto& record : input.at(1).children)
            if (record.at(2).atom == "public") {
                library_.emplace(record.at(0).atom, &record);
                signatures_.emplace(record.at(0).atom, &record.at(1));
            }
        if (input.children.size() > 6)
            for (const auto& helper : input.at(6).children)
                if (!definitions.count(helper.at(0).atom)) {
                    helpers_.emplace(helper.at(0).atom, &helper.at(2));
                    if (auxiliary::incompatibleConclusion(helper)) invalidHelpers_.insert(helper.at(0).atom);
                    if (auxiliary.count(helper.at(0).atom)) signatures_.emplace(helper.at(0).atom,&helper.at(1));
                }
        if (input.children.size() > 2)
            for (const auto& matcher : input.at(2).children)
                matchers_.emplace(matcher.at(0).atom, &matcher);
        if (input.children.size() > 7)
            for (const auto& recursor : input.at(7).children)
                recursors_.emplace(recursor.at(0).atom, &recursor);
        if (input.children.size() > 9)
            for (const auto& ctor : input.at(9).children) {
                if (attribute(ctor,3)=="object") objectConstructors_.emplace(ctor.at(0).atom,&ctor);
                else {
                    propertyConstructors_.emplace(ctor.at(0).atom,&ctor);
                    signatures_.emplace(ctor.at(0).atom,&ctor.at(1));
                }
            }
    }

    std::optional<std::string> render(const Node& record) {
        Context ctx;
        if (!derive(record.at(2), &record.at(1), ctx, false)) return std::nullopt;
        return prose_.str();
    }
    std::set<std::string> used;
    std::string failure;

private:
    const std::map<std::string,std::string>& earlier_;
    bool compact_;
    const DefinitionRules& definitions_;
    const std::map<std::string,std::string>& auxiliary_;
    std::map<std::string,const Node*> library_;
    std::map<std::string,const Node*> signatures_;
    std::map<std::string,const Node*> helpers_;
    std::set<std::string> invalidHelpers_;
    std::map<std::string,const Node*> matchers_;
    std::map<std::string,const Node*> recursors_;
    std::map<std::string,const Node*> propertyConstructors_;
    std::map<std::string,const Node*> objectConstructors_;
    std::vector<const Node*> earlierProofs_;
    std::set<std::string> expanding_;
    std::set<std::string> selected_;
    std::ostringstream prose_;
    bool fail(std::string reason) { failure = std::move(reason); return false; }

    struct RecordCase {
        Node object;
        const Node* branch;
        std::vector<std::size_t> data;
    };

    static std::optional<Node> applyMotive(const Node& motive, const Node& value) {
        Node call;
        call.array = true;
        call.children = {motive.at(0),motive,value};
        call.children[0].atom = "a";
        return instantiate(motive,call);
    }

    static bool recordEqualityCase(const Node& elimination, const Node& conclusion) {
        const auto& motive = term(elimination.at(4));
        if (!motive.is("l") || !term(motive.at(4)).is("l")) return false;
        Node args;
        args.array = true;
        args.children = {elimination.at(0),motive,elimination.at(5),elimination.at(6)};
        const auto target = instantiate(motive,args);
        if (!target) return false;
        args.children.resize(2);
        for (std::size_t i : {8u,9u}) {
            if (!elimination.at(i).is("p")) return false;
            args.children.push_back(elimination.at(i));
            const auto expected = instantiate(*target,args,true,args.children.size()-1);
            if (!expected || !sameKernelTerm(*expected,elimination.at(i).at(1))) return false;
        }
        const auto result = instantiate(*target,args,true);
        return result && sameKernelTerm(*result,conclusion);
    }

    static bool recordTransportArguments(const Node& transfer, const Node& conclusion,
                                         const record_equality::Locals& locals) {
        const auto& motive = term(transfer.at(4));
        const auto target = applyMotive(motive,transfer.at(6));
        const auto baseType = applyMotive(motive,transfer.at(3));
        if (!target || !baseType) return false;
        // The minor premise may introduce dependent fields and their proofs.
        // Compare their domains at the original field value before using them.
        const Node* expected = &*baseType;
        const Node* minor = &transfer.at(5);
        Names bound;
        while (expected->is("q") && minor->is("l")) {
            if (!sameKernelTerm(expected->at(3),minor->at(3),bound)) return false;
            bound[expected->at(1).atom] = minor->at(1).atom;
            expected = &expected->at(4);
            minor = &minor->at(4);
        }
        if (expected->is("q") || !minor->is("p")) return false;
        Node args;
        args.array = true;
        args.children = {transfer.at(0),transfer.at(1)};
        for (std::size_t i=8;i<transfer.children.size();++i) {
            const auto* actual = record_equality::localType(transfer.at(i),locals);
            args.children.push_back(transfer.at(i));
            const auto expected = instantiate(*target,args,true,args.children.size()-1);
            if (!actual || !expected || !sameKernelTerm(*expected,*actual)) return false;
        }
        const auto result = instantiate(*target,args,true);
        return result && sameKernelTerm(*result,conclusion);
    }

    // The adapter certifies that the sole alternative binds the constructor
    // fields in order. Instantiate the catalog signature to check each binder.
    std::optional<RecordCase> openRecordCase(const Node& raw, const Node& info, const Node& spec,
                                             const Node& type, record_equality::Locals& locals) const {
        if (!raw.is("a") || raw.children.size()<5 || !raw.at(1).is("c") || info.children.size()!=6 ||
            info.at(1).atom!=std::to_string(raw.children.size()-5) || info.at(2).atom!="1" ||
            info.at(3).children.size()!=1 || info.at(4).atom!="0" ||
            info.at(3).at(0).atom!=std::to_string(spec.at(2).children.size())) return {};
        RecordCase result{raw,nullptr,{}};
        auto& obj = result.object;
        obj.children.resize(2);
        obj.children[1].children[1].atom = spec.at(0).atom;
        if (type.is("a"))
            obj.children.insert(obj.children.end(),type.children.begin()+2,type.children.end());
        const auto& motive = term(argument(raw,2));
        if (!motive.is("l") || !sameKernelTerm(type,motive.at(3))) return {};
        const Node* binder = &term(argument(raw,0));
        for (std::size_t i=0; i<spec.at(2).children.size(); ++i) {
            if (!binder->is("l")) return {};
            const auto& role = binder->at(6);
            Node ref;
            ref.array = true;
            ref.children = {binder->at(0),binder->at(1),role};
            ref.children.front().atom = "v";
            obj.children.push_back(std::move(ref));
            const auto domain = instantiate(spec.at(1),obj,true,obj.children.size()-1);
            const Node* parameter = &spec.at(1);
            for (std::size_t n=2; n+1<obj.children.size() && parameter->is("q"); ++n) parameter=&parameter->at(4);
            if (!domain || !parameter->is("q") || attribute(*parameter,6)!=role.atom ||
                !sameKernelTerm(*domain,binder->at(3))) return {};
            if (role.atom=="value" || role.atom=="prop" || role.atom=="type") result.data.push_back(i);
            else if (role.atom!="proof") return {};
            locals[binder->at(1).atom] = &binder->at(3);
            binder = &binder->at(4);
        }
        const auto built = instantiate(spec.at(1),obj,true);
        if (!built || !sameKernelTerm(*built,type)) return {};
        const auto branchType = applyMotive(motive,obj);
        if (!branchType) return {};
        const Node* expected = &*branchType;
        const Node* body = binder;
        Names bound;
        while (body->is("l") && expected->is("q")) {
            if (!sameKernelTerm(expected->at(3),body->at(3),bound)) return {};
            bound[expected->at(1).atom] = body->at(1).atom;
            body = &body->at(4);
            expected = &expected->at(4);
        }
        if (!body->is("p") || !sameKernelTerm(*expected,body->at(1),bound)) return {};
        result.branch=binder;
        return result;
    }

    bool recordEquality(const Node& expr, const Node& claim, Context ctx) {
        const auto& raw = term(expr);
        const auto matcher = matchers_.find(head(raw));
        if (matcher==matchers_.end() || matcher->second->children.size()!=6 || !claim.is("q") ||
            !raw.is("a") || raw.children.size()<5) return false;
        const auto& info = *matcher->second;
        const auto entry = objectConstructors_.find(info.at(5).atom);
        if (entry==objectConstructors_.end()) return false;
        const auto& spec = *entry->second;
        const auto& type = claim.at(3);
        const auto& subject = argument(raw,1);
        if (!subject.is("v") || !ctx.names.count(subject.at(1).atom)) return false;
        record_equality::Locals locals;
        const auto first = openRecordCase(raw,info,spec,type,locals);
        if (!first || first->data.empty()) return false;
        const auto applied = applyMotive(term(argument(raw,2)),subject);
        if (!applied || !sameKernelTerm(*applied,claim)) return false;
        const auto& secondBinder = term(*first->branch);
        if (!secondBinder.is("l") || !sameKernelTerm(secondBinder.at(3),type)) return false;
        const auto& secondMatch = term(secondBinder.at(4));
        if (!secondMatch.is("a") || head(secondMatch)!=head(raw) || secondMatch.children.size()<5 ||
            !argument(secondMatch,1).is("v") || argument(secondMatch,1).at(1).atom!=secondBinder.at(1).atom) return false;
        const auto second = openRecordCase(secondMatch,info,spec,type,locals);
        if (!second || second->data!=first->data) return false;
        const auto inner = applyMotive(term(argument(secondMatch,2)),argument(secondMatch,1));
        if (!inner || !secondBinder.at(4).is("p") || !sameKernelTerm(*inner,secondBinder.at(4).at(1))) return false;

        // Compare the complete projected equalities on the statement and on
        // the two decomposed records. Matching field names alone is insufficient.
        checkedBinderName(ctx.names,claim.at(1).atom,claim.at(2).atom);
        const auto params = type.is("a") ? type.children.size()-2 : 0;
        const auto projection = [&](const Node& expr, const std::string& name, const Node& object) {
            if (!expr.is("a") || head(expr)!=name || expr.children.size()!=params+3 ||
                !sameKernelTerm(argument(expr,0),object)) return false;
            for (std::size_t i=0;i<params;++i)
                if (!sameKernelTerm(expr.at(i+2),type.at(i+2))) return false;
            return true;
        };
        Node other = subject;
        other.children[1] = claim.at(1);
        const Node* statement = &claim.at(4);
        const Node* branch = second->branch;
        std::vector<record_equality::Field> data;
        std::vector<std::string> equalityIds;
        Node projected=first->object;
        std::vector<std::string> equations;
        for (auto i : first->data) {
            if (!statement->is("q") || !branch->is("l") || attribute(*statement,6)!="proof" ||
                attribute(*branch,6)!="proof") return false;
            const auto& before = statement->at(3);
            const auto& after = branch->at(3);
            const auto name = head(type)+"."+spec.at(2).at(i).atom;
            if (!record_equality::call(before,"Eq",3) || !record_equality::call(after,"Eq",3) ||
                !projection(before.at(3),name,subject) || !projection(before.at(4),name,other) ||
                !projection(after.at(3),name,first->object) || !projection(after.at(4),name,second->object)) return false;
            const auto math = formula(before,ctx);
            if (!math) return false;
            equations.push_back(*math);
            data.push_back({name,&first->object.at(params+2+i),&second->object.at(params+2+i)});
            equalityIds.push_back(branch->at(1).atom);
            projected.children[params+2+i]=before.at(3);
            locals[branch->at(1).atom] = &branch->at(3);
            statement = &statement->at(4);
            branch = &branch->at(4);
        }
        if (!record_equality::call(*statement,"Eq",3) || !sameKernelTerm(statement->at(2),type) ||
            !sameKernelTerm(statement->at(3),subject) || !sameKernelTerm(statement->at(4),other) ||
            !branch->is("p") || !record_equality::call(branch->at(1),"Eq",3) ||
            !sameKernelTerm(branch->at(1).at(2),type) || !sameKernelTerm(branch->at(1).at(3),first->object) ||
            !sameKernelTerm(branch->at(1).at(4),second->object)) return false;
        std::optional<std::string> indexEquality;
        if (!record_equality::transports(*branch,data,type,first->object,locals,
                [](const Node& a,const Node& b) { return sameKernelTerm(a,b); },
                recordEqualityCase,recordTransportArguments)) {
            record_equality::IndexedEvidence evidence(spec,signatures_,
                [](const Node& a,const Node& b) { return sameKernelTerm(a,b); },betaContract,
                [](const Node& binder,const Node& value) {
                    Node app;
                    app.array=true;
                    app.children={binder.at(0),binder,value};
                    app.children[0].atom="a";
                    return instantiate(binder,app,true);
                });
            const auto index=evidence.check(*branch,first->object,locals,equalityIds);
            if (!index) return false;
            // Express the checked index equation using projections of the
            // original record, whose variables the reader has already seen.
            const auto equation=instantiate(spec.at(1),projected,true,*index);
            if (!equation || !(indexEquality=formula(*equation,ctx))) return false;
        }
        const auto result = formula(*statement,ctx);
        if (!result) return false;
        prose_ << "Compare the two records field by field. ";
        if (indexEquality) prose_ << "Use the defining equality " << *indexEquality << " to rewrite their common index. ";
        for (std::size_t i=0; i<equations.size(); ++i)
            prose_ << (i==0 ? "By hypothesis, " : i+1==equations.size() ? " and " : ", ") << equations[i];
        prose_ << ". ";
        if (data.size()!=spec.at(2).children.size())
            prose_ << "After substitution, the remaining fields prove the same propositions. "
                      "Any two proofs of the same proposition are equal by proof irrelevance. ";
        prose_ << "The records therefore satisfy " << *result << ".\n";
        return true;
    }

    // The constructor fields and their types come from the checked declaration.
    // Include proof parameters before the fields, even when they have no heading.
    bool proveFields(const Node& spec, const Node& raw, const Context& ctx, bool object) {
        const auto& fields = spec.at(2).children;
        if (!raw.is("a") || fields.empty() || fields.size() > raw.children.size()-2) return false;
        const auto start = raw.children.size() - fields.size();
        std::vector<const Node*> premises;
        if (!proofArguments(raw,premises)) return false;
        for (std::size_t i=2; i<raw.children.size(); ++i) {
            const bool proof = std::find(premises.begin(),premises.end(),&raw.at(i)) != premises.end();
            if (!proof && object && i>=start) {
                if (!witnessObligations(raw.at(i),ctx)) return false;
                continue;
            }
            if (!proof && i<start) continue;
            if (!proof) return fail("missing proof of a structure field");
            auto domain = instantiate(spec.at(1),raw,true,i);
            if (!domain) return fail("unavailable structure field type");
            if (i>=start) {
                static const std::map<std::string,std::string> labels{
                    {"refl","Reflexivity"}, {"symm","Symmetry"}, {"trans","Transitivity"},
                    {"isClique","Clique property"}, {"card_eq","Cardinality"},
                    {"map_rel_iff'","Preservation and reflection of the relation"},
                    {"left_inv","Left inverse"}, {"right_inv","Right inverse"}};
                const auto& key = fields[i-start].atom;
                const auto label = labels.find(key);
                const auto title = label == labels.end() ? declarationTitle(key) : label->second;
                prose_ << "\\par\\smallskip\\noindent\\emph{" << escapeLatex(title) << ".}\\enspace\n";
            }
            if (!derive(raw.at(i),&*domain,ctx,true)) return false;
        }
        return true;
    }

    bool witnessObligations(const Node& witness, const Context& ctx) {
        const auto& value = term(witness);
        if (value.is("l")) {
            const Node* body = &value;
            while (body->is("l")) body = &term(body->at(4));
            // A function can construct a new certified element at each input.
            // Open its binders only if there is an actual obligation to explain.
            std::vector<const Node*> proofs;
            if (!body->is("a") || !proofArguments(*body,proofs) || proofs.empty()) return true;
            auto inner = ctx;
            for (const Node* lambda=&value; lambda!=body; lambda=&term(lambda->at(4)))
                if (!introduce(*lambda,nullptr,inner,true)) return false;
            return witnessObligations(*body,inner);
        }
        const auto it = objectConstructors_.find(head(value));
        if (it!=objectConstructors_.end()) return proveFields(*it->second,value,ctx,true);
        // Earlier exports have no constructor catalog. Even then, an explicit
        // proof argument of a constructed witness must be justified.
        if (!value.is("a")) return true;
        const auto& fn = value.at(1);
        if (!fn.is("c") || attribute(fn,2)!="value") return true;
        std::vector<const Node*> proofs;
        if (!proofArguments(value,proofs)) return false;
        for (const auto* proof : proofs) {
            if (!derive(*proof,nullptr,ctx,true)) return false;
        }
        return true;
    }

    std::string recordWitness(const Node& witness, const std::string& rendered, const Node& type,
                              const Context& ctx) const {
        const auto& value = term(witness);
        const auto entry = objectConstructors_.find(head(value));
        // Retain dedicated mathematical notation for pairs, isomorphisms and
        // other structures. Give a field description for the generic constructor.
        const auto marker = rendered.find("\\mathord{:}mk}");
        if (entry==objectConstructors_.end() || !value.is("a") || marker==std::string::npos ||
            rendered.rfind("\\(\\operatorname{",0)!=0 || rendered.find('(' ,2)<marker) return rendered;
        const auto& fields = entry->second->at(2).children;
        if (fields.size()>value.children.size()-2) return rendered;
        const auto target = formula(type,ctx);
        std::vector<const Node*> proofs;
        if (!target || !proofArguments(value,proofs)) return rendered;
        std::vector<std::string> descriptions;
        for (std::size_t i=0;i<fields.size();++i) {
            const auto& arg = value.at(value.children.size()-fields.size()+i);
            if (std::find(proofs.begin(),proofs.end(),&arg)!=proofs.end()) continue;
            const auto content = formula(arg,ctx);
            if (!content) return rendered;
            auto label = declarationTitle(fields[i].atom);
            if (!label.empty() && label[0]>='A' && label[0]<='Z') label[0]+='a'-'A';
            descriptions.push_back(escapeLatex(label) + " " + *content);
        }
        std::string result = "an element of " + *target;
        for (std::size_t i=0;i<descriptions.size();++i)
            result += (i==0 ? " with " : i+1==descriptions.size() ? " and " : ", ") + descriptions[i];
        return result;
    }

    // For a classical decision on a relation, name the relation and the
    // justification instead of printing the elaborator's instance wrapper.
    bool classicalDecision(const Node& witness, const Node& type, const Context& ctx) {
        const auto& app = term(witness);
        if (head(app)!="inferInstance" || app.children.size()!=4 ||
            head(type)!="DecidableRel" || type.children.size()!=5 ||
            !sameKernelTerm(app.at(2),type)) return false;
        const auto& left = term(app.at(3));
        if (!left.is("l") || !term(left.at(4)).is("l")) return false;
        const auto& right = term(left.at(4));
        const auto& decision = term(right.at(4));
        if (head(decision)!="Classical.propDecidable" || decision.children.size()!=3) return false;
        const auto& claim = term(decision.at(2));
        if (!claim.is("a") || claim.children.size()<4) return false;
        const auto& a = argument(claim,1);
        const auto& b = argument(claim,0);
        if (!a.is("v") || a.at(1).atom!=left.at(1).atom ||
            !b.is("v") || b.at(1).atom!=right.at(1).atom) return false;
        const auto relation = formula(type.at(4),ctx);
        if (!relation) return false;
        prose_ << "By excluded middle, the relation " << *relation << " is decidable for each pair.\n";
        return true;
    }

    // Branches precede the object in some recursors and follow it in others.
    // Use Lean's branch positions, including branches that introduce no binders.
    bool eliminate(const Node& info, const Node& raw, const Context& ctx, const std::string& goal) {
        if (!raw.is("a") || info.children.size() != 6) return false;
        const auto argumentAt = [&](const Node& slot) -> const Node* {
            std::size_t pos = 0;
            const auto end = slot.atom.data() + slot.atom.size();
            const auto parsed = std::from_chars(slot.atom.data(), end, pos);
            return parsed.ec == std::errc{} && parsed.ptr == end && pos < raw.children.size()-2
                ? &raw.at(pos+2) : nullptr;
        };
        const auto* object = argumentAt(info.at(4));
        const auto& ctors = info.at(2).children;
        const auto& slots = info.at(3).children;
        if (!object || slots.size() != ctors.size()) return false;
        std::vector<const Node*> premises;
        if (!proofArguments(raw, premises)) return false;
        std::set<const Node*> branches;
        for (const auto& slot : slots) {
            const auto* branch = argumentAt(slot);
            if (!branch || std::find(premises.begin(),premises.end(),branch) == premises.end()) return false;
            branches.insert(branch);
        }
        for (const auto* premise : premises)
            if (!branches.count(premise) && !derive(*premise,nullptr,ctx,true)) return false;
        const auto subject = formula(object->is("p") ? object->at(1) : *object, ctx);
        if (!subject) return false;
        const bool pair = info.at(1).atom == "PSigma" && ctors.size() == 1 &&
                          ctors.front().atom == "PSigma.mk" && info.at(5).atom == "cases";
        if (pair) prose_ << "Write the pair " << *subject << " in terms of its two components.\n";
        else prose_ << (info.at(5).atom == "recursion" ? "Proceed by induction on " : "Consider the possible forms of ")
                    << *subject << ".\n";
        for (std::size_t i=0; i<slots.size(); ++i) {
            if (!pair) prose_ << "\\emph{" << escapeLatex(declarationTitle(ctors[i].atom)) << " case.}\n";
            prose_ << "\\begin{proofstep}\n";
            if (!derive(*argumentAt(slots[i]),nullptr,ctx,true)) return false;
            prose_ << "\\end{proofstep}\n";
        }
        prose_ << "This proves " << goal << ".\n";
        return true;
    }

    enum class Matched { none, witnesses, subtype };

    // A single-constructor proposition can be unpacked into its fields in a
    // pattern match. Check the actual constructor telescope: the branch count
    // and its binder names alone do not establish what the fields mean.
    std::optional<bool> unpackProperty(const Node& raw, const Node& expected, const Context& ctx) {
        const auto matcher = matchers_.find(head(raw));
        if (matcher == matchers_.end() || !raw.is("a") || raw.children.size() < 5) return {};
        const auto& info = *matcher->second;
        if (info.children.size() != 6 || info.at(1).atom != std::to_string(raw.children.size()-5) ||
            info.at(2).atom != "1" || info.at(3).children.size() != 1 || info.at(4).atom != "0") return {};
        const auto& subject = argument(raw,1);
        const auto* type = evidenceType(subject,ctx);
        const auto& motive = term(argument(raw,2));
        if (!type || !motive.is("l") || attribute(motive,6) != "proof" ||
            !sameKernelTerm(*type,motive.at(3)) || !sameKernelTerm(expected,motive.at(4))) return {};
        const auto family = head(*type);
        const auto ctor = propertyConstructors_.find(info.at(5).atom);
        if (ctor == propertyConstructors_.end()) return {};
        const auto* spec = ctor->second;
        const Node* result = &spec->at(1);
        while (result->is("q")) result = &result->at(4);
        const auto& fields = spec->at(2).children;
        if (head(*result) != family || fields.empty() ||
            info.at(3).at(0).atom != std::to_string(fields.size())) return {};

        // Apply the structure parameters, then each branch variable, to
        // obtain the exact type of the next field, including dependencies.
        Node args;
        args.array = true;
        args.children = {raw.at(0), raw.at(1)};
        const auto& target = term(*type);
        if (target.is("a"))
            args.children.insert(args.children.end(),target.children.begin()+2,target.children.end());
        auto inner = ctx;
        const Node* branch = &term(argument(raw,0));
        std::vector<std::string> facts;
        for (std::size_t i=0; i<fields.size(); ++i) {
            if (!branch->is("l") || attribute(*branch,6) != "proof") return {};
            Node var;
            var.array = true;
            var.children = {raw.at(0),branch->at(1),branch->at(6)};
            var.children[0].atom = "v";
            args.children.push_back(std::move(var));
            const auto domain = instantiate(spec->at(1),args,true,args.children.size()-1);
            if (!domain || !sameKernelTerm(*domain,branch->at(3)) || !introduce(*branch,nullptr,inner,false))
                return {};
            const auto& id = branch->at(1).atom;
            facts.push_back(inner.assumptions.at(id));
            inner.provedFacts.insert(id);
            branch = &branch->at(4);
        }
        const auto constructed = instantiate(spec->at(1),args,true);
        const auto* conclusion = evidenceType(*branch,inner);
        if (!constructed || !sameKernelTerm(*constructed,*type) ||
            !conclusion || !sameKernelTerm(*conclusion,expected)) return {};
        const auto& source = term(subject);
        const auto claim = formula(*type,ctx);
        if (!claim) return {};
        if (source.is("v") && ctx.assumptions.count(source.at(1).atom)) {
            prose_ << (ctx.provedFacts.count(source.at(1).atom) ? "Unpacking the result " : "Unpacking the hypothesis ")
                   << *claim << " gives ";
        } else {
            if (!derive(subject,type,ctx,true)) return false;
            prose_ << "Unpacking this property gives ";
        }
        for (std::size_t i=0; i<facts.size(); ++i)
            prose_ << (i==0 ? "" : i+1==facts.size() ? " and " : ", ") << facts[i];
        prose_ << ".\n";

        // Two fields used verbatim as the two conjuncts need no second
        // display. Check their identifiers, positions and the And premises.
        const auto& body = term(*branch);
        if (facts.size()==2 && head(body)=="And.intro" && body.children.size()==6 &&
            head(expected)=="And" && expected.children.size()==4) {
            const auto& first = term(argument(raw,0));
            const auto& second = term(first.at(4));
            std::vector<const Node*> premises;
            if (proofArguments(body,premises) && premises==std::vector<const Node*>{&body.at(4),&body.at(5)} &&
                body.at(4).is("v") && body.at(4).at(1).atom==first.at(1).atom &&
                body.at(5).is("v") && body.at(5).at(1).atom==second.at(1).atom &&
                sameKernelTerm(body.at(2),first.at(3)) && sameKernelTerm(body.at(3),second.at(3)) &&
                sameKernelTerm(body.at(2),expected.at(2)) && sameKernelTerm(body.at(3),expected.at(3))) {
                prose_ << "This proves the conjunction.\n";
                return true;
            }
        }
        return derive(*branch,&expected,std::move(inner),true);
    }

    Matched witnessMatch(const std::string& name, const Node& raw, const Context& ctx) const {
        const auto it = matchers_.find(name);
        if (it == matchers_.end() || !raw.is("a")) return Matched::none;
        const auto& info = *it->second;
        if (raw.children.size()<5 || info.at(1).atom != std::to_string(raw.children.size()-5) ||
            info.at(2).atom != "1" || info.at(3).children.size() != 1 || info.at(4).atom != "0" ||
            !term(argument(raw,0)).is("l")) return Matched::none;
        const auto& scrutinee = argument(raw,1);
        const auto& motive = term(argument(raw,2));
        const Node* type = motive.is("l") ? &motive.at(3) : nullptr;
        if (scrutinee.is("p")) type = &scrutinee.at(1);
        else if (scrutinee.is("v")) {
            const auto it = ctx.hypothesisTypes.find(scrutinee.at(1).atom);
            if (it != ctx.hypothesisTypes.end()) type = it->second;
        }
        if (!type) return Matched::none;
        const auto key = head(*type);
        if ((key == "Subtype" || key == "Set.Elem") && info.at(3).at(0).atom == "2") return Matched::subtype;
        if (key == "Exists" || key == "And" || key == "Finset.Nonempty") return Matched::witnesses;
        if (key == "Set.Nonempty" && type->is("a") && type->children.size()==4 &&
            info.at(3).at(0).atom=="2") {
            // Unfolding nonemptiness of s supplies x and a proof of x ∈ s.
            // In particular a different set or membership relation cannot justify this case.
            const auto& item=term(argument(raw,0));
            const auto& field=term(item.at(4));
            if (!field.is("l") || attribute(item,6)!="value" || attribute(field,6)!="proof" ||
                !sameKernelTerm(item.at(3),type->at(2))) return Matched::none;
            const auto& membership=term(field.at(3));
            std::vector<const Node*> proofs;
            if (head(membership)=="Membership.mem" && membership.children.size()==7 &&
                head(membership.at(4))=="Set.instMembership" && membership.at(4).children.size()==3 &&
                sameKernelTerm(membership.at(4).at(2),type->at(2)) &&
                sameKernelTerm(membership.at(5),type->at(3)) && membership.at(6).is("v") &&
                membership.at(6).at(1).atom==item.at(1).atom && proofArguments(raw,proofs) &&
                proofs==std::vector<const Node*>{&argument(raw,1),&argument(raw,0)}) return Matched::witnesses;
        }
        return Matched::none;
    }

    bool unpackSubtype(const Node& raw, const std::string& goal, Context ctx) {
        const auto& value = term(argument(raw,0));
        const auto& property = term(value.at(4));
        const auto item = formula(argument(raw,1),ctx);
        if (!item || attribute(value,6) != "value" || !property.is("l") || attribute(property,6) != "proof")
            return fail("unrecognized subtype constructor fields");
        if (!introduce(value,nullptr,ctx,false) || !introduce(property,nullptr,ctx,false)) return false;
        prose_ << "Let \\(" << ctx.names.at(value.at(1).atom) << "\\) be the underlying element of " << *item
               << ". Its defining property gives " << ctx.assumptions.at(property.at(1).atom) << ".\n";
        if (!derive(property.at(4),nullptr,std::move(ctx),true)) return false;
        prose_ << "This proves " << goal << ".\n";
        return true;
    }

    // A single alternative may bind the discriminants themselves. Applying
    // its checked branch to those values is valid when the instantiated
    // proposition is exactly the requested one, including dependent arguments.
    std::optional<Node> directMatcherBranch(const Node& raw, const Node& expected) const {
        const auto entry = matchers_.find(head(raw));
        if (entry == matchers_.end() || !raw.is("a")) return {};
        const auto& info = *entry->second;
        if (info.at(3).children.size() != 1 || info.at(4).atom != "0") return {};
        auto index = [](const std::string& text) -> std::optional<std::size_t> {
            std::size_t n = 0;
            const auto end = text.data()+text.size();
            const auto parsed = std::from_chars(text.data(),end,n);
            if (parsed.ec != std::errc{} || parsed.ptr != end) return {};
            return n;
        };
        const auto params=index(info.at(1).atom), fields=index(info.at(2).atom);
        if (!params || !fields || !*fields || *params >= raw.children.size() ||
            *fields >= raw.children.size() || info.at(3).at(0).atom != info.at(2).atom) return {};
        const auto first = 3+*params, branch = first+*fields;
        if (branch >= raw.children.size()) return {};
        const auto& alternative = term(raw.at(branch));
        const Node* target = &term(raw.at(first-1));
        const Node* binder = &alternative;
        Names matching;
        const auto args = *fields+raw.children.size()-branch-1;
        for (std::size_t i=0;i<args;++i) {
            if (!binder->is("l") || !target->is(i<*fields ? "l" : "q") ||
                !sameKernelTerm(binder->at(3),target->at(3),matching)) return {};
            matching[binder->at(1).atom] = target->at(1).atom;
            binder = &binder->at(4);
            target = &target->at(4);
        }
        Node call;
        call.array = true;
        call.children = {raw.at(0),alternative};
        call.children.insert(call.children.end(),raw.children.begin()+first,raw.children.begin()+branch);
        call.children.insert(call.children.end(),raw.children.begin()+branch+1,raw.children.end());
        auto result = instantiate(alternative,call);
        if (!result || !result->is("p") || !sameKernelTerm(result->at(1),expected)) return {};
        return result;
    }

    template<class Use>
    bool useHelper(const std::string& name, const Node& raw, Use use) {
        if (invalidHelpers_.count(name)) return fail("incompatible proof conclusion for " + name);
        if (helpers_.at(name)->is("u"))
            return fail("unavailable proof for " + name + ": " + attribute(*helpers_.at(name),1));
        if (!expanding_.insert(name).second) return fail("recursive helper " + name);
        const auto instantiated = instantiate(*helpers_.at(name),raw);
        const bool ok = instantiated ? use(*instantiated) : fail("could not instantiate proof helper " + name);
        expanding_.erase(name);
        return ok;
    }

    // A checked generic lemma can replace expansion at this call only after
    // its arguments have been matched against the same dependent telescope.
    std::optional<bool> applyAuxiliary(const Node& expr, const Node* expected, const Context& ctx,
                                       std::vector<std::string>* rewrite) {
        const auto& raw = term(expr);
        const auto name = head(raw);
        const auto entry = auxiliary_.find(name);
        if (entry==auxiliary_.end()) return {};
        const auto& signature = *signatures_.at(name);
        const auto result = instantiate(signature,raw,true);
        const auto agrees = [&](const Node& left,const Node& right) {
            const auto same = [&](const Node& a,const Node& b) {
                return sameKernelTerm(a,b) || sameKernelTerm(a,b,ctx.statementToProofBinders);
            };
            if (same(left,right)) return true;
            // Specializing P in P(x) to a lambda can leave an applied lambda
            // in the signature while Lean has already reduced it in the goal.
            // Accept only equality of the resulting terms, including instances.
            auto reducedLeft = left;
            auto reducedRight = right;
            unsigned leftBudget = 200, rightBudget = 200;
            reduceForDisplay(reducedLeft,leftBudget);
            reduceForDisplay(reducedRight,rightBudget);
            return (leftBudget<200 || rightBudget<200) && same(reducedLeft,reducedRight);
        };
        if (!result) return {};
        if ((expected && !agrees(*expected,*result)) || (expr.is("p") && !agrees(expr.at(1),*result)))
            return fail("unmatched conclusion of auxiliary lemma " + name);
        const auto conclusion = formula(*result,ctx);
        if (!conclusion) return {};
        std::vector<const Node*> classified, proofs;
        if (!proofArguments(raw,classified)) return {};
        std::vector<Node> domains;
        std::vector<std::string> conditions;
        const Node* binder = &signature;
        for (std::size_t i=2;raw.is("a") && i<raw.children.size();++i) {
            if (!binder->is("q")) return {};
            const auto& arg = raw.at(i);
            if (attribute(*binder,6)=="proof") {
                auto domain = instantiate(signature,raw,true,i);
                const auto* actual = evidenceType(arg,ctx);
                if (!domain || !actual) return {};
                if (!agrees(*domain,*actual)) return fail("unmatched premise of auxiliary lemma " + name);
                const auto condition = formula(*domain,ctx);
                if (!condition) return {};
                proofs.push_back(&arg);
                domains.push_back(std::move(*domain));
                conditions.push_back(*condition);
            }
            binder = &binder->at(4);
        }
        if (proofs!=classified) return {};
        // Failed evidence invalidates this derivation; it must never become
        // a citation solely because the generic lemma has a proof.
        for (std::size_t i=0;i<proofs.size();++i)
            if (!derive(*proofs[i],&domains[i],ctx,true)) return false;
        for (std::size_t i=2;raw.is("a") && i<raw.children.size();++i)
            if (std::find(proofs.begin(),proofs.end(),&raw.at(i))==proofs.end() &&
                !witnessObligations(raw.at(i),ctx)) return false;
        auto reason = entry->second + specialization(name,raw,ctx);
        for (std::size_t i=0;i<conditions.size();++i)
            reason += (i==0 ? " (using " : " and ") + conditions[i];
        if (!conditions.empty()) reason += ")";
        if (rewrite) {
            if (std::find(rewrite->begin(),rewrite->end(),reason)==rewrite->end()) rewrite->push_back(reason);
        } else prose_ << "By " << reason << ", we obtain " << *conclusion << ".\n";
        return true;
    }

    std::string specialization(const std::string& name, const Node& app, const Context& ctx,
                               bool showGivenObjects = false) const {
        const auto it = signatures_.find(name);
        if (!app.is("a") || it == signatures_.end()) return {};
        Names names;
        const Node* binder = it->second;
        std::string parameters;
        for (std::size_t i=2; i<app.children.size() && binder->is("q"); ++i) {
            const auto& arg = app.at(i);
            const auto formal = checkedBinderName(names,binder->at(1).atom,binder->at(2).atom);
            const bool explicitValue = attribute(*binder,5) == "explicit" && attribute(*binder,6) != "proof";
            const bool specializedType = attribute(*binder,6) == "type" && !arg.is("v");
            const bool wholeCarrier = head(arg) == "Finset.univ" || head(arg) == "Set.univ";
            if (explicitValue || specializedType || wholeCarrier) {
                auto actual = checkedFormula(arg,ctx.names);
                if (actual && (*actual != formal || (showGivenObjects && explicitValue))) {
                    parameters += parameters.empty() ? " with " : " and ";
                    // The formal belongs to the cited result. A local namesake
                    // can also occur in the conclusion, outside the argument.
                    const bool localNamesake = std::any_of(ctx.names.begin(),ctx.names.end(),
                        [&](const auto& local) { return local.second == formal; });
                    if (*actual == formal) parameters += "the given \\(" + *actual + "\\)";
                    else if (localNamesake && attribute(*binder,6) == "type")
                        parameters += "\\(" + *actual + "\\) as its type parameter \\(" + formal + "\\)";
                    else if (localNamesake)
                        parameters += "\\(" + *actual + "\\) in place of its parameter \\(" + formal + "\\)";
                    else parameters += "\\(" + formal + " = " + *actual + "\\)";
                }
            }
            binder = &binder->at(4);
        }
        return parameters;
    }

    // A cited lemma can take a transported object as an ordinary argument.
    // Its equality proofs are then underneath that argument, outside the
    // lemma's own list of proof premises.
    bool explainArgumentTransports(const Node& app, const Context& ctx) {
        std::vector<const Node*> explained;
        const auto isTransport = [](const Node& raw) {
            if (!raw.is("a") || raw.children.size()!=6 || attribute(raw.at(1),2)!="value") return false;
            const auto name = head(raw);
            if (name!="Eq.mp" && name!="Eq.mpr" && name!="cast") return false;
            std::vector<const Node*> proofs;
            return proofArguments(raw,proofs) && proofs.size()==1 && proofs.front()==&raw.at(4);
        };
        const auto visit = [&](auto&& self, const Node& raw) -> bool {
            if (!raw.is("a")) return true;
            if (isTransport(raw)) {
                if (std::any_of(explained.begin(),explained.end(),[&](const Node* prior) {
                    return sameKernelTerm(raw,*prior);
                })) return true;
                std::vector<const Node*> chain;
                const Node* original = &raw;
                while (isTransport(*original)) {
                    chain.push_back(original);
                    original = &term(original->at(5));
                }
                if (!self(self,*original)) return false;
                for (auto it=chain.rbegin();it!=chain.rend();++it) {
                    const Node* reason = &(*it)->at(4);
                    // Congruence lifts an index equality to an equality of
                    // whole types. Present the equality the reader needs.
                    while (head(term(*reason))=="congrArg" && term(*reason).children.size()==8)
                        reason = &argument(term(*reason),0);
                    const auto& proof = term(*reason);
                    std::vector<const Node*> premises;
                    if (reason->is("p") && proofArguments(proof,premises) && premises.empty()) {
                        const auto equality = formula(reason->at(1),ctx);
                        const auto source = equality ? citation(head(proof)) : std::nullopt;
                        if (source) {
                            prose_ << "By " << *source << specialization(head(proof),proof,ctx,true)
                                   << ", we obtain " << *equality << ".\n";
                            continue;
                        }
                    }
                    if (!derive(*reason,nullptr,ctx,true)) return false;
                }
                const auto object = formula(*original,ctx);
                const auto target = formula(raw.at(head(raw)=="Eq.mpr" ? 2 : 3),ctx);
                if (!object || !target) return fail("unrendered type transport in an argument");
                prose_ << "After substitution, " << *object << " has type " << *target << ".\n";
                explained.push_back(&raw);
                return true;
            }
            const auto& fn = raw.at(1);
            if ((!fn.is("c") && !fn.is("v")) || fn.children.size()<4 || !fn.at(3).array) return true;
            for (const auto& slot : fn.at(3).children) {
                std::size_t i = 0;
                const auto end = slot.atom.data()+slot.atom.size();
                const auto parsed = std::from_chars(slot.atom.data(),end,i);
                if (parsed.ec!=std::errc{} || parsed.ptr!=end || i>=raw.children.size()-2)
                    return fail("invalid checked argument position");
                if (!self(self,raw.at(i+2))) return false;
            }
            return true;
        };
        return visit(visit,app);
    }

    std::optional<std::string> citation(const std::string& name) {
        if (auto it = earlier_.find(name); it != earlier_.end()) return it->second;
        if (auto it = definitions_.find(name); it != definitions_.end()) return it->second.reference;
        const auto it = library_.find(name);
        if (it == library_.end() || selected_.count(name) || !describeCheckedStatement(it->second->at(1)))
            return std::nullopt;
        used.insert(name);
        return prerequisiteReference(*it->second);
    }

    std::optional<std::string> cardinalityBijection(const Node& app, const Context& ctx) const {
        if (head(app)!="Fintype.card_congr" || app.children.size()!=7) return {};
        const auto endpoint = [&](const Node& type) -> std::optional<std::string> {
            if (head(type)!="Sigma" || type.children.size()!=4 || !term(type.at(3)).is("l"))
                return formula(type,ctx);
            const auto& fiber = term(type.at(3));
            auto inner = ctx;
            const auto x = checkedBinderName(inner.names,fiber.at(1).atom,fiber.at(2).atom);
            const auto domain = formula(type.at(2),ctx);
            if (!domain) return {};
            const std::string pairs = "the pairs with first component \\(" + x + "\\) in " + *domain +
                                      " and second component in ";
            const auto& family = term(fiber.at(4));
            if (head(family)=="Sum" && family.children.size()==4) {
                const auto left=formula(family.at(2),inner), right=formula(family.at(3),inner);
                if (left && right) return pairs + "the disjoint union of " + *left + " and " + *right;
            }
            const auto members = formula(family,inner);
            return members ? std::optional<std::string>(pairs + *members) : std::nullopt;
        };
        const auto from=endpoint(app.at(2)), to=endpoint(app.at(3));
        const auto& map=term(app.at(6));
        const auto object=formula(map,ctx);
        if (!from || !to || !object) return {};
        std::string detail;
        if (map.is("a") && map.at(1).is("c") && map.at(1).children.size()>=5 && map.at(1).at(3).children.empty()) {
            // An equivalence can take only implicit arguments. Show its actual
            // carrier even when the ordinary expression printer shows just its name.
            for (std::size_t i=2; i<map.children.size(); ++i) {
                const auto& param=term(map.at(i));
                if (attribute(param.is("a") ? param.at(1) : param,2)!="type") continue;
                if (const auto carrier=formula(param,ctx))
                    detail += (detail.empty() ? " specialized to " : " and ") + *carrier;
            }
        }
        std::vector<std::string> assumptions;
        const auto collect = [&](auto&& self,const Node& value) -> void {
            if (value.is("v")) {
                const auto it=ctx.assumptions.find(value.at(1).atom);
                if (it!=ctx.assumptions.end() && std::find(assumptions.begin(),assumptions.end(),it->second)==assumptions.end())
                    assumptions.push_back(it->second);
            } else if (value.is("a")) {
                for (std::size_t i=2; i<value.children.size(); ++i) self(self,term(value.at(i)));
            }
        };
        collect(collect,map);
        for (std::size_t i=0; i<assumptions.size(); ++i) detail += (i ? " and " : " using ") + assumptions[i];
        return "The supplied bijection " + *object + detail + " maps " + *from + " onto " + *to + ".";
    }

    // A cited equality used in reverse needs one sentence. Keep a nontrivial
    // auxiliary proof on the ordinary path so its argument is still visible.
    bool citeReversedEquality(const Node& raw, const Context& ctx, const std::string& goal) {
        if (head(raw)!="Eq.symm" || raw.children.size()!=6) return false;
        const auto& equality = term(argument(raw,0));
        std::vector<const Node*> premises;
        if (!proofArguments(equality,premises)) return false;
        std::vector<std::string> conditions;
        for (const auto* premise : premises) {
            const auto& value = term(*premise);
            if (!value.is("v")) return false;
            const auto it = ctx.assumptions.find(value.at(1).atom);
            if (it==ctx.assumptions.end()) return false;
            if (std::find(conditions.begin(),conditions.end(),it->second)==conditions.end())
                conditions.push_back(it->second);
        }
        const auto name = head(equality);
        if (name=="Fintype.card_congr") return false;
        auto source = citation(name);
        if (!source) return false;
        prose_ << "Using " << *source << specialization(name,equality,ctx) << " in reverse";
        if (!conditions.empty()) {
            prose_ << " under ";
            for (std::size_t i=0;i<conditions.size();++i) {
                if (i) prose_ << (i+1==conditions.size() ? " and " : ", ");
                prose_ << conditions[i];
            }
        }
        prose_ << " gives " << goal << ".\n";
        return true;
    }

    std::optional<std::string> inlinedEarlier(const Node& proof, const Context& ctx) const {
        const auto& raw = term(proof);
        if (!proof.is("p") || !raw.is("a") || !raw.at(1).is("l")) return {};
        const auto* fn = &raw.at(1);
        for (std::size_t i=2; i<raw.children.size(); ++i) {
            if (!fn->is("l") || attribute(*fn,6) == "proof") return {};
            fn = &fn->at(4);
        }
        for (const auto* record : earlierProofs_) {
            if (!sameKernelTerm(record->at(2),raw.at(1))) continue;
            const auto specialized = instantiate(record->at(1),raw,true);
            if (specialized && sameKernelTerm(*specialized,proof.at(1))) {
                const auto& name = record->at(0).atom;
                return earlier_.at(name) + specialization(name,raw,ctx);
            }
        }
        return {};
    }

    std::optional<std::string> naturalMeasure(const Node& proj, const Context& ctx) const {
        if (!proj.is("proj") || proj.at(1).atom != "WellFoundedRelation" ||
            proj.at(2).atom != "1" || attribute(proj,4) != "proof") return {};
        const auto& inverse = term(proj.at(3));
        if (head(inverse) != "invImage" || inverse.children.size() != 6 || head(inverse.at(3)) != "Nat") return {};
        const auto& order = term(inverse.at(5));
        if (head(order) != "instWellFoundedRelationOfSizeOf" || order.children.size() != 4 ||
            head(order.at(2)) != "Nat" || head(order.at(3)) != "instSizeOfNat") return {};
        return formula(inverse.at(4),ctx);
    }

    // A measure relation reduces to the standard strict order on the two
    // natural-number measures. Keep the direction and both operands.
    static bool sameDecrease(const Node& expected, const Node& actual) {
        if (sameKernelTerm(expected,actual)) return true;
        if (!expected.is("a") || expected.children.size()!=4 ||
            !record_equality::call(actual,"LT.lt",4) || head(actual.at(2))!="Nat" ||
            head(actual.at(3))!="instLTNat") return false;
        const auto& rel = expected.at(1);
        if (!rel.is("proj") || rel.at(1).atom!="WellFoundedRelation" || rel.at(2).atom!="0") return false;
        const auto& inverse = term(rel.at(3));
        if (!record_equality::call(inverse,"invImage",4) || head(inverse.at(3))!="Nat") return false;
        const auto& order = inverse.at(5);
        if (!record_equality::call(order,"instWellFoundedRelationOfSizeOf",2) ||
            head(order.at(2))!="Nat" || head(order.at(3))!="instSizeOfNat") return false;
        const auto& measure = term(inverse.at(4));
        if (!measure.is("l")) return false;
        const auto a=applyMotive(measure,expected.at(2)), b=applyMotive(measure,expected.at(3));
        return a && b && sameKernelTerm(*a,actual.at(4)) && sameKernelTerm(*b,actual.at(5));
    }

    bool typedDecrease(const Node& expr, const Node& expected, const Context& ctx) const {
        if (expr.is("p") && !sameDecrease(expected,expr.at(1))) return false;
        const auto& raw = term(expr);
        if (raw.is("v")) {
            const auto* actual = evidenceType(raw,ctx);
            return actual && sameDecrease(expected,*actual);
        }
        if (record_equality::call(raw,"id",2))
            return sameDecrease(expected,raw.at(2)) && typedDecrease(raw.at(3),expected,ctx);
        if (record_equality::call(raw,"Eq.mpr",4) || record_equality::call(raw,"Eq.mp",4)) {
            const bool reverse = head(raw)=="Eq.mpr";
            const auto* cert = evidenceType(raw.at(4),ctx);
            return cert && record_equality::call(*cert,"Eq",3) && sameKernelTerm(cert->at(3),raw.at(2)) &&
                   sameKernelTerm(cert->at(4),raw.at(3)) && sameDecrease(expected,raw.at(reverse ? 2 : 3)) &&
                   typedDecrease(raw.at(5),raw.at(reverse ? 3 : 2),ctx);
        }
        const Node* signature=raw.is("a") && raw.at(1).is("v") ? evidenceType(raw.at(1),ctx) : nullptr;
        const auto sig=signatures_.find(head(raw));
        if (!signature && sig!=signatures_.end()) signature=sig->second;
        if (!signature) return false;
        const auto actual=instantiate(*signature,raw,true);
        return actual && sameDecrease(expected,*actual);
    }

    bool recursiveInstance(const Node& call, const Context& ctx, std::string& result) {
        const auto* signature=evidenceType(call.at(1),ctx);
        if (!signature || call.children.size()!=4) return fail("invalid arguments to the induction hypothesis");
        const auto domain=instantiate(*signature,call,true,3);
        const auto conclusion=instantiate(*signature,call,true);
        std::vector<const Node*> premises;
        if (!domain || !conclusion || !proofArguments(call,premises) || premises!=std::vector<const Node*>{&call.at(3)} ||
            !typedDecrease(call.at(3),*domain,ctx)) return fail("unverified decrease in the recursive call");
        const auto smaller=formula(call.at(2),ctx), fact=formula(*conclusion,ctx);
        if (!smaller || !fact || !derive(call.at(3),&*domain,ctx,true)) return false;
        prose_ << "Apply the induction hypothesis to " << *smaller << " to obtain " << *fact << ".\n";
        result=*fact;
        return true;
    }

    template<class Same>
    bool proofInputMatches(const Node& parent, std::size_t slot, const Node& fact, const Context& ctx, Same same) const {
        if (parent.is("p") && slot==2) return same(parent.at(1),fact);
        if (!parent.is("a") || slot<2) return false;
        const auto sig=signatures_.find(head(parent));
        const auto* signature=parent.at(1).is("v") ? evidenceType(parent.at(1),ctx) : nullptr;
        if (!signature && sig!=signatures_.end()) signature=sig->second;
        if (signature) {
            const auto type=instantiate(*signature,parent,true,slot);
            if (type) return same(*type,fact);
        }
        if (record_equality::call(parent,"And.intro",4) && (slot==4 || slot==5))
            return same(parent.at(slot-2),fact);
        if (!record_equality::call(fact,"Eq",3) || !same(fact.at(2),parent.at(2))) return false;
        if (record_equality::call(parent,"Eq.trans",6) && (slot==6 || slot==7))
            return same(fact.at(3),parent.at(slot-3)) && same(fact.at(4),parent.at(slot-2));
        if (record_equality::call(parent,"Eq.symm",4) && slot==5)
            return same(fact.at(3),parent.at(3)) && same(fact.at(4),parent.at(4));
        if (record_equality::call(parent,"congrArg",6) && slot==7)
            return same(fact.at(3),parent.at(4)) && same(fact.at(4),parent.at(5));
        return false;
    }

    bool treeInduction(const Node& raw, const Node& cert, const Node& expected, Context ctx) {
        const auto required=[&](const Node& parent,std::size_t slot,const Node& fact) {
            return proofInputMatches(parent,slot,fact,ctx,
                [](const Node& a,const Node& b) { return sameKernelTerm(a,b); });
        };
        const auto branches=tree_below::open(raw,cert,expected,
            [](const Node& a,const Node& b) { return sameKernelTerm(a,b); },applyMotive,required);
        if (!branches) return fail("unverified branch or subtree hypothesis in tree induction");
        const auto subject=formula(raw.at(4),ctx);
        const auto goal=formula(expected,ctx);
        if (!subject || !goal) return fail("unrendered tree induction goal");
        prose_ << "Use structural induction on the tree " << *subject << " to prove " << *goal << ".\n"
               << "\\par\\smallskip\\noindent\\emph{Empty tree.}\\enspace\n";
        const auto& base=term(*branches->leaf);
        const auto& baseType=branches->leaf->at(1);
        const auto baseGoal=formula(*branches->leafGoal,ctx);
        if (head(base)=="Eq.refl" || head(base)=="rfl") {
            if (!baseGoal || base.children.size()!=4 || !record_equality::call(baseType,"Eq",3) ||
                !sameKernelTerm(baseType.at(2),base.at(2)) || !sameKernelTerm(baseType.at(3),base.at(3)) ||
                !sameKernelTerm(baseType.at(4),base.at(3)))
                return fail("unverified reflexivity in the empty-tree case");
            prose_ << "Evaluating the defining equations gives " << *baseGoal << ".\n";
        } else if (!derive(*branches->leaf,nullptr,ctx,true)) return false;
        const auto label=checkedBinderName(ctx.names,branches->label->at(1).atom,"a");
        std::vector<std::string> names, facts;
        for (std::size_t i=0;i<2;++i) {
            const auto tree=checkedBinderName(ctx.names,branches->children[i]->at(1).atom,i ? "r" : "l");
            const auto fact=formula(branches->hypotheses[i],ctx);
            if (!fact) return false;
            names.push_back("\\("+tree+"\\)");
            facts.push_back(*fact);
            ctx.hypothesisTypes[branches->ids[i]]=&branches->hypotheses[i];
            ctx.assumptions[branches->ids[i]]=*fact;
            ctx.provedFacts.insert(branches->ids[i]);
        }
        prose_ << "\\par\\smallskip\\noindent\\emph{Node.}\\enspace "
               << "For a node with label \\(" << label << "\\), let " << names[0] << " and " << names[1]
               << " be the left and right subtrees. "
               << "Their induction hypotheses give " << facts[0] << " and " << facts[1] << ".\n";
        if (!derive(branches->nodeProof,nullptr,std::move(ctx),true)) return false;
        prose_ << "These cases establish " << *goal << ".\n";
        return true;
    }

    const Node* evidenceType(const Node& value, const Context& ctx) const {
        if (value.is("p")) return &value.at(1);
        if (value.is("v")) {
            const auto it = ctx.hypothesisTypes.find(value.at(1).atom);
            if (it != ctx.hypothesisTypes.end()) return it->second;
        }
        const auto name = head(value);
        if (name == "id" && value.children.size() == 4) return &value.at(2);
        if ((name == "Eq.mp" || name == "Eq.mpr") && value.children.size() == 6)
            return &value.at(name == "Eq.mp" ? 3 : 2);
        if (value.is("proj") && value.at(1).atom == "And" &&
            (value.at(2).atom == "0" || value.at(2).atom == "1")) {
            const auto* type = evidenceType(value.at(3),ctx);
            if (type && head(*type) == "And" && term(*type).children.size() == 4)
                return &argument(*type,value.at(2).atom == "0" ? 1 : 0);
        }
        return nullptr;
    }

    // Proof terms have no mathematical value notation. An equality between
    // them can still be stated when both inhabitants prove the same proposition.
    std::optional<std::string> proofIdentity(const Node& expr, const Context& ctx) const {
        const bool heterogeneous=record_equality::call(expr,"HEq",4);
        if (!heterogeneous && !record_equality::call(expr,"Eq",3)) return {};
        if (heterogeneous && !sameKernelTerm(expr.at(2),expr.at(4))) return {};
        const auto* left=evidenceType(expr.at(3),ctx);
        const auto* right=evidenceType(argument(expr,0),ctx);
        if (!left || !right || !sameKernelTerm(*left,expr.at(2)) || !sameKernelTerm(*right,expr.at(2)))
            return {};
        const auto common=formula(expr.at(2),ctx);
        if (!common) return {};
        return "the two proofs of " + *common + " agree";
    }

    bool conjunct(const Node& projection, const Context& ctx, std::string& result) {
        const auto& whole = projection.at(3);
        const auto* type = evidenceType(whole,ctx);
        if (!type || head(*type) != "And" || term(*type).children.size() != 4) return false;
        const bool first = projection.at(2).atom == "0";
        if (!first && projection.at(2).atom != "1") return false;
        const auto part = formula(argument(*type,first ? 1 : 0),ctx);
        if (!part || !derive(whole,type,ctx,true)) return false;
        prose_ << "Taking the " << (first ? "first" : "second") << " conjunct gives " << *part << ".\n";
        result = *part;
        return true;
    }

    // A conjunct may itself state a universally quantified implication.
    // Lean projections have no argument-slot metadata. Obtain each premise
    // from its actual binder, specializing dependent premises in order.
    bool applyConjunct(const Node& raw, const Node* expected, const Context& ctx) {
        const auto& projection=raw.at(1);
        const auto* signature=evidenceType(projection,ctx);
        if (!signature) return fail("unavailable conjunct type");
        const auto conclusion=instantiate(*signature,raw,true);
        if (!conclusion || (expected && !sameKernelTerm(*conclusion,*expected) &&
            !sameKernelTerm(*expected,*conclusion,ctx.statementToProofBinders)))
            return fail("unrecognized conclusion of a conjunct");
        const auto goal=formula(*conclusion,ctx);
        if (!goal) return fail("unrendered conclusion of a conjunct");
        std::string fact;
        if (!conjunct(projection,ctx,fact)) return false;
        const Node* binder=signature;
        std::vector<std::string> objects;
        for (std::size_t i=2;i<raw.children.size();++i) {
            if (!binder->is("q")) return fail("extra argument to a conjunct");
            const auto& item=raw.at(i);
            if (attribute(*binder,6)=="proof") {
                const auto domain=instantiate(*signature,raw,true,i);
                if (!domain) return fail("unavailable premise of a conjunct");
                const auto* actual=evidenceType(item,ctx);
                if (actual && !sameKernelTerm(*actual,*domain)) return fail("mismatched premise of a conjunct");
                if (!derive(item,&*domain,ctx,true)) return false;
            } else {
                const auto object=formula(item,ctx);
                if (!object || !witnessObligations(item,ctx)) return false;
                objects.push_back(*object);
            }
            binder=&binder->at(4);
        }
        prose_ << "Applying this conjunct";
        for (std::size_t i=0;i<objects.size();++i) prose_ << (i==0 ? " to " : ", ") << objects[i];
        prose_ << " gives " << *goal << ".\n";
        return true;
    }

    static bool appliedConjunct(const Node& raw) {
        if (!raw.is("a") || raw.children.size()<3) return false;
        const auto& fn=raw.at(1);
        return fn.is("proj") && fn.at(1).atom=="And" && attribute(fn,4)=="proof";
    }

    bool rewriteEvidence(const Node& expr, const Context& ctx, RewriteReasons& evidence) {
        auto& reasons = evidence.sources;
        const auto& raw = term(expr);
        if (ring_equality::certificate(expr) && ring_equality::terms(expr.at(1))) {
            const std::string reason="expanding the products and collecting like terms";
            if (std::find(reasons.begin(),reasons.end(),reason)==reasons.end()) reasons.push_back(reason);
            return true;
        }
        if (raw.is("a") && raw.at(1).is("v") && raw.at(1).at(1).atom==ctx.wellFoundedHypothesis) {
            std::string fact;
            if (!recursiveInstance(raw,ctx,fact)) return false;
            reasons.push_back(fact);
            return true;
        }
        if (raw.is("proj") && attribute(raw,4) == "proof") {
            std::string reason;
            if (const auto measure = naturalMeasure(raw,ctx))
                reason = "well-foundedness of strict descent under the natural-number measure " + *measure;
            else if (raw.at(1).atom != "And" || !conjunct(raw,ctx,reason))
                return fail("unsupported proof projection " + raw.at(1).atom + "." + raw.at(2).atom);
            if (std::find(reasons.begin(),reasons.end(),reason) == reasons.end()) reasons.push_back(reason);
            return true;
        }
        if (auto reduced = betaContract(raw)) return rewriteEvidence(*reduced,ctx,evidence);
        const auto name = head(raw);
        if (name == "Lean.opaqueId" && raw.is("a") && raw.children.size() == 4 &&
            attribute(raw.at(1),2) == "proof")
            return rewriteEvidence(raw.at(3),ctx,evidence);
        if (auto applied=applyAuxiliary(expr,nullptr,ctx,&reasons)) return *applied;
        if (helpers_.count(name)) return useHelper(name,raw,[&](const Node& proof) {
            return rewriteEvidence(proof,ctx,evidence);
        });
        if (equalityEliminators.count(name)) {
            std::vector<std::string> sources;
            const auto previous = used;
            auto cite = [&](const std::string& theorem) { return citation(theorem); };
            if (equalityEvidence(expr,ctx,{},sources,cite)) {
                sources.push_back("substitution of equals");
                for (const auto& source : sources)
                    if (std::find(reasons.begin(),reasons.end(),source) == reasons.end()) reasons.push_back(source);
                return true;
            }
            used = previous;
        }
        std::string reason;
        if (auto map=cardinalityBijection(raw,ctx); map && !earlier_.count(name)) {
            if (auto source=citation(name)) {
                if (std::find(evidence.bijections.begin(),evidence.bijections.end(),*map)==evidence.bijections.end()) {
                    evidence.bijections.push_back(*map);
                    prose_ << *map << " By " << *source << ", the two finite types have equal cardinality.\n";
                    ++evidence.identities;
                }
                return true;
            }
        }
        if (auto arithmetic = numericalRewrite(raw)) {
            if (std::find(reasons.begin(),reasons.end(),*arithmetic) == reasons.end())
                reasons.push_back(*arithmetic);
            return true;
        }
        if (raw.is("l") || raw.is("t") || appliedConjunct(raw) || name == "letFun" || name == "WellFounded.fix" ||
            nat_below::certified(raw,matchers_) || tree_below::certificate(raw,matchers_) ||
            name == "Exists.intro" || name == "Nonempty.intro" || name == "And.intro" ||
            name == "Or.inl" || name == "Or.inr" || name == "Iff.intro") {
            prose_ << "The substitution uses the following argument.\n\\begin{proofstep}\n";
            if (!derive(expr,nullptr,ctx,true)) return false;
            prose_ << "\\end{proofstep}\n";
            const Node* conclusion = &expr;
            while (term(*conclusion).is("l") || term(*conclusion).is("t")) {
                const auto& binding = term(*conclusion);
                conclusion = &binding.at(binding.is("l") ? 4 : 5);
            }
            if (conclusion->is("p") && head(conclusion->at(1)) == "Eq") ++evidence.identities;
            else ++evidence.arguments;
            return true;
        }
        std::vector<const Node*> premises;
        if (!proofArguments(raw, premises)) return false;
        const auto& fn = raw.is("a") ? raw.at(1) : raw;
        if (fn.is("v")) {
            const auto it = ctx.assumptions.find(fn.at(1).atom);
            if (it == ctx.assumptions.end()) return false;
            reason = it->second;
        } else {
            static const std::set<std::string> plumbing{
                "Eq.trans", "Eq.refl", "rfl", "Eq.symm", "congr", "congrArg", "congrFun",
                "propext", "eq_self", "of_eq_true", "eq_true", "eq_true_intro", "id",
                "Eq.mp", "Eq.mpr", "Eq.rec", "Eq.ndrec", "Eq.recOn", "Eq.casesOn", "Eq.ndrecOn",
                "Eq.subst", "HEq.refl", "HEq.rfl", "cast", "True.intro"
            };
            if (!plumbing.count(name)) {
                auto source = citation(name);
                if (!source) return fail("unavailable rewriting premise " +
                    (name.empty() ? "[" + raw.at(0).atom + "]" : name));
                reason = *source;
                const bool productEndpoint = name=="Finset.prod_range_succ";
                if ((productEndpoint || name=="Finset.sum_range_succ") && raw.children.size()==6 && expr.is("p")) {
                    const auto& equation = term(expr.at(1));
                    const auto& index = raw.at(5);
                    const auto endpoint = applyMotive(term(raw.at(4)),index);
                    if (endpoint && head(equation)=="Eq" && equation.children.size()==5) {
                        const auto& rhs = argument(equation,0);
                        if (head(rhs)==(productEndpoint ? "HMul.hMul" : "HAdd.hAdd") &&
                            rhs.children.size()==8 && sameKernelTerm(*endpoint,argument(rhs,0))) {
                            const auto at = formula(index,ctx);
                            const auto value = formula(*endpoint,ctx);
                            if (at && value)
                                reason += std::string(" (the final ") + (productEndpoint ? "factor" : "summand") +
                                          " at index " + *at + " is " + *value + ")";
                        }
                    }
                }
                // A direct hypothesis licenses this lemma application. Keep
                // the condition with its citation when grouping several rewrites.
                std::vector<std::string> conditions;
                std::vector<const Node*> otherPremises;
                for (const Node* premise : premises) {
                    const auto& value = term(*premise);
                    if (value.is("v")) {
                        const auto local = ctx.assumptions.find(value.at(1).atom);
                        if (local == ctx.assumptions.end()) return false;
                        if (std::find(conditions.begin(),conditions.end(),local->second) == conditions.end())
                            conditions.push_back(local->second);
                    } else otherPremises.push_back(premise);
                }
                for (std::size_t i=0; i<conditions.size(); ++i)
                    reason += (i ? " and " : " (using ") + conditions[i];
                if (!conditions.empty()) reason += ")";
                premises = std::move(otherPremises);
            }
        }
        if (!reason.empty() && std::find(reasons.begin(), reasons.end(), reason) == reasons.end())
            reasons.push_back(reason);
        for (const auto* premise : premises)
            if (!rewriteEvidence(*premise, ctx, evidence)) return false;
        return true;
    }

    bool showDenominatorStep(const Node& cert, const Node& originalType, const Context& ctx,
                             const std::string& goal, RewriteReasons* evidence) {
        const auto same = [](const Node& left, const Node& right) { return sameKernelTerm(left,right); };
        if (const auto step = denominator::explain(cert,originalType,ctx.names,ctx.hypothesisTypes,same,betaContract)) {
            // The ordinary traversal above has verified the full certificate.
            // Only describe the intermediate bound when its sources occur in that traversal.
            std::vector<std::string> origins;
            const auto usedBefore = used;
            const auto recognized = [&](const std::string& name) -> std::optional<std::string> {
                auto reference = citation(name);
                if (reference && !evidence) return reference;
                if (reference) {
                    for (const auto& reason : evidence->sources)
                        if (reason==*reference || (name==step->rule && reason==*reference+" (using "+step->witness+")"))
                            return reference;
                }
                return {};
            };
            for (const auto& name : step->origins) {
                if (const auto ref=recognized(name)) origins.push_back(*ref);
            }
            const auto rule=recognized(step->rule);
            if (rule && origins.size()==step->origins.size()) {
                if (origins.empty()) prose_ << "Over " << step->domain << ", the preceding bound is ";
                else {
                    prose_ << "Applying ";
                    for (std::size_t i=0; i<origins.size(); ++i) {
                        if (i) prose_ << (i+1==origins.size() ? " and " : ", ");
                        prose_ << origins[i];
                    }
                    prose_ << " to the preceding bound gives the inequality over " << step->domain << " ";
                }
                prose_ << "\\(\\displaystyle " << step->quotient << "\\).\n"
                       << "Since \\(" << step->positivity << "\\), multiplying by the denominator preserves the order. "
                       << "By " << *rule << ", this gives " << step->cleared << ".\n";
                if (!evidence) return false;
                // Keep every residual source besides the cited steps and
                // their closed, standard rational order-instance proofs.
                std::vector<std::string> covered=origins, hierarchy;
                covered.push_back(*rule);
                covered.push_back(*rule+" (using "+step->witness+")");
                denominator::structuralRules(cert,hierarchy);
                for (const auto& name : hierarchy) {
                    if (const auto ref=recognized(name)) covered.push_back(*ref);
                }
                auto& sources=evidence->sources;
                sources.erase(std::remove_if(sources.begin(),sources.end(),[&](const std::string& source) {
                    return std::find(covered.begin(),covered.end(),source)!=covered.end();
                }),sources.end());
                if (sources.empty() && !evidence->identities && !evidence->arguments &&
                    withoutLayout(step->cleared)==withoutLayout(goal)) return true;
            } else used=usedBefore;
        }
        return false;
    }

    static void finishRewrite(std::ostream& out, RewriteReasons& evidence,
                              const std::string& conclusion, bool preceding) {
        auto& reasons = evidence.sources;
        const auto group = [&](std::size_t count, const char* singular, const char* plural) {
            if (count == 1) reasons.push_back(std::string("the ") + singular + " established above");
            if (count > 1) reasons.push_back("the " + (count == 2 ? "two" : std::to_string(count)) +
                                             " " + plural + " established above");
        };
        group(evidence.identities, "identity", "identities");
        group(evidence.arguments, "auxiliary result", "auxiliary results");
        out << (reasons.empty() ? "Simplifying by definition" : "Rewriting with ");
        for (std::size_t i=0; i<reasons.size(); ++i) {
            if (i) out << (i+1 == reasons.size() ? " and " : ", ");
            out << reasons[i];
        }
        out << (preceding ? " in the preceding result gives " : " gives ") << conclusion << ".\n";
    }

    // Equivalence of two equations alone does not authorize rewriting their
    // operands. Require congruence in a context with a fixed right-hand side.
    static bool leftCongruence(const Node& cert, const Node& before, const Node& after) {
        const Node* proof = &term(cert);
        const Node* equality = cert.is("p") ? &term(cert.at(1)) : nullptr;
        if (head(*proof)=="id" && proof->children.size()==4) {
            equality=&term(proof->at(2));
            proof=&term(proof->at(3));
        }
        // The adapter exports the checked type at the use site. This retains
        // Lean's conversion of operation instances between the motive and goal.
        if (!equality || head(*equality)!="Eq" || equality->children.size()!=5 ||
            !sameKernelTerm(equality->at(3),before) || !sameKernelTerm(equality->at(4),after)) return false;
        if (head(*proof)!="congrArg" || proof->children.size()!=8) return false;
        const auto& motive = term(proof->at(6));
        return motive.is("l") && head(motive.at(4))=="Eq" && term(motive.at(4)).children.size()==5 &&
               sameKernelTerm(argument(motive.at(4),0),argument(before,0));
    }

    // A sequence of rewrites on the left of an equality is a calculation.
    // Check the unchanged target and the closing reflexivity before printing
    // the intermediate expressions in the order a reader would calculate them.
    std::optional<bool> leftCalculation(const Node& proof, const Node& expected, const Context& ctx) {
        if (earlier_.empty() || head(expected)!="Eq" || term(expected).children.size()!=5) return {};
        const Node* current = &proof;
        const Node* equation = &expected;
        std::vector<std::pair<const Node*,std::string>> steps;
        bool citesEarlier = false;
        for (;;) {
            const auto& app = term(*current);
            const auto rule = head(app);
            if ((rule!="Eq.mpr" && rule!="Eq.mp") || app.children.size()!=6) break;
            const auto& from = app.at(rule=="Eq.mpr" ? 2 : 3);
            const auto& to = app.at(rule=="Eq.mpr" ? 3 : 2);
            const bool sameSource = sameKernelTerm(*equation,from) ||
                (steps.empty() && sameKernelTerm(*equation,from,ctx.statementToProofBinders));
            if (!sameSource || head(to)!="Eq" || term(to).children.size()!=5 ||
                !sameKernelTerm(term(from).at(2),term(to).at(2)) ||
                !sameKernelTerm(argument(from,0),argument(to,0)) ||
                !leftCongruence(app.at(4),app.at(2),app.at(3))) return {};
            auto a = checkedFormula(argument(from,1),ctx.names);
            auto b = checkedFormula(argument(to,1),ctx.names);
            if (!a || !b || *a==*b) return {};
            // Replace only the right operand when printing a step. The checked
            // equality printer supplies the necessary relation precedence.
            auto step = term(from);
            step.children[4] = argument(to,1);
            const auto display = formula(step,ctx);
            if (!display) return {};
            steps.emplace_back(&app.at(4),*display);
            if (!citesEarlier) {
                const auto local = [&](auto&& self,const Node& n) -> bool {
                    if (n.is("c")) return earlier_.count(n.at(1).atom)!=0;
                    return std::any_of(n.children.begin(),n.children.end(),[&](const Node& child) {
                        return child.array && self(self,child);
                    });
                };
                citesEarlier = local(local,app.at(4));
            }
            equation = &to;
            current = &app.at(5);
        }
        const auto& base = term(*current);
        if (!citesEarlier || steps.size()<2 || (head(base)!="Eq.refl" && head(base)!="rfl") ||
            base.children.size()!=4 || !sameKernelTerm(base.at(2),term(*equation).at(2)) ||
            !sameKernelTerm(base.at(3),argument(*equation,0)) ||
            !sameKernelTerm(argument(*equation,0),argument(*equation,1))) return {};
        for (const auto& [certificate,identity] : steps) {
            RewriteReasons evidence;
            if (!rewriteEvidence(*certificate,ctx,evidence)) return false;
            finishRewrite(prose_,evidence,identity,false);
        }
        return true;
    }

    bool simplify(const Node& cert, const Node* original, const Node* originalType,
                  const std::string& goal, Context ctx, bool sameProposition = false) {
        auto oldUsed = used;
        RewriteReasons evidence;
        std::vector<const Node*> transformations{&cert};
        const Node* base = original;
        const Node* type = originalType;
        while (compact_ && base) {
            const auto& app = term(*base);
            const auto rule = head(app);
            if ((rule!="Eq.mp" && rule!="Eq.mpr") || app.children.size()!=6) break;
            transformations.push_back(&app.at(4));
            type = &app.at(rule=="Eq.mp" ? 2 : 3);
            base = &app.at(5);
        }
        const auto start = base ? head(*base) : "";
        const bool reflexive = compact_ && type && (start=="Eq.refl" || start=="rfl" || start=="Iff.rfl") &&
            (head(*type)=="Eq" || head(*type)=="Iff") &&
            sameKernelTerm(argument(*type,1),argument(*type,0));
        if (!reflexive) transformations.resize(1);
        const auto beforeRewrites = prose_.tellp();
        for (auto it=transformations.rbegin(); it!=transformations.rend(); ++it) {
            if (!rewriteEvidence(**it, ctx, evidence)) {
                used = std::move(oldUsed);
                return false;
            }
        }
        const bool preceding = original && !reflexive;
        // The enclosed proof already establishes the identical proposition.
        // Validate the equality evidence above before dropping its unused citation.
        if (preceding && sameProposition && prose_.tellp()==beforeRewrites) {
            used = std::move(oldUsed);
            return derive(*original,originalType,ctx,true);
        }
        bool justPrintedEquation = false;
        if (preceding) {
            const auto beforeOriginal = prose_.tellp();
            if (!derive(*original,originalType,ctx,true)) return false;
            if (originalType && head(*originalType)=="Eq") {
                const auto originalFormula = formula(*originalType,ctx);
                if (originalFormula && withoutLayout(*originalFormula)==withoutLayout(goal)) {
                    justPrintedEquation = endsWithFormula(prose_.str().substr(static_cast<std::size_t>(beforeOriginal)),goal);
                }
            }
        }
        if (preceding && originalType && showDenominatorStep(cert,*originalType,ctx,goal,&evidence)) return true;
        finishRewrite(prose_,evidence,justPrintedEquation ? "the same displayed equality" : goal,preceding);
        return true;
    }

    // A reflexivity proof may be annotated "x = x" even when the actual
    // base case is "x = f(0)". The motive at zero supplies the statement.
    std::string knownBaseValue(const Node& witness, const Context& ctx) const {
        const Node* value = &witness;
        if (head(witness) == "Nat.cast" && witness.children.size() == 5 &&
            head(witness.at(2)) == "Int" && head(witness.at(3)) == "instNatCastInt")
            value = &witness.at(4);
        for (const auto* earlier : earlierProofs_) {
            const auto& equality = term(earlier->at(1));
            if (head(equality) != "Eq" || equality.children.size() != 5 ||
                !sameKernelTerm(equality.at(3),*value)) continue;
            const auto& right = equality.at(4);
            if (!right.is("n") && !(head(right) == "OfNat.ofNat" && right.children.size() == 5 &&
                head(right.at(2)) == "Nat" && right.at(3).is("n") && head(right.at(4)) == "instOfNatNat")) continue;
            if (const auto result = formula(right,ctx))
                return " Their common value is " + *result + " by " + earlier_.at(earlier->at(0).atom) + ".";
        }
        return {};
    }

    // The ordinary and strong principles order the index and the two
    // branches differently. In both step lambdas the second binder is the
    // induction hypothesis, independently of the name supplied by the author.
    bool naturalInduction(const Node& index, const Node& motive, const Node& base,
                          const Node& successor, const Context& ctx, const std::string& goal, bool strong) {
        const auto subject = formula(index,ctx);
        if (!subject) return fail("unrendered induction variable");
        const auto& hypothesis = term(term(successor).at(4));
        const std::string method = strong ? "strong induction" : "induction";
        prose_ << "Proceed by " << method << " on " << *subject
               << ".\n\\emph{Base case.}\n\\begin{proofstep}\n";
        const auto& evidence = term(base);
        std::optional<std::string> baseGoal;
        if (motive.is("l") && head(evidence) == "Eq.refl" && evidence.children.size() == 4) {
            auto zero = ctx;
            zero.names[motive.at(1).atom] = "0";
            baseGoal = formula(motive.at(4),zero);
        }
        if (baseGoal)
            prose_ << "At zero, " << *baseGoal << " holds by definition."
                   << (head(motive.at(4)) == "Eq" ? knownBaseValue(evidence.at(3),ctx) : "") << "\n";
        else if (!derive(base,nullptr,ctx,true)) return false;
        prose_ << "\\end{proofstep}\n\\emph{Successor step.}\n\\begin{proofstep}\n";
        auto branch = ctx;
        branch.inductionHypothesis = hypothesis.at(1).atom;
        if (!derive(successor,nullptr,std::move(branch),true)) return false;
        prose_ << "\\end{proofstep}\nBy " << method << ", " << goal << ".\n";
        return true;
    }

    bool introduce(const Node& binder, const Node* type, Context& ctx, bool narrate) {
        const auto& id = binder.at(1).atom;
        const auto hint = type && type->is("q") ? type->at(2).atom : binder.at(2).atom;
        const auto role = attribute(binder,6);
        const auto kind = attribute(binder,5);
        // The type and value trees open binders independently.
        const auto variable = checkedBinderName(ctx.names, id, hint);
        bindCheckedAddition(ctx.names,binder,variable);
        if (type && type->is("q")) {
            ctx.names[type->at(1).atom] = variable;
            ctx.statementToProofBinders[type->at(1).atom] = id;
            bindCheckedAddition(ctx.names,*type,variable);
        }
        if (role == "proof") {
            auto hypothesis = formula(binder.at(3), ctx);
            if (!hypothesis) hypothesis=proofIdentity(binder.at(3),ctx);
            if (!hypothesis) return false;
            ctx.assumptions[id] = *hypothesis;
            ctx.hypothesisTypes[id] = &binder.at(3);
            const bool induction = id==ctx.inductionHypothesis || (hint=="ih" && binder.at(3).is("q"));
            if (induction) ctx.inductionHypothesis = id;
            if (narrate) prose_ << (induction ? "Assume as induction hypothesis that " : "Assume ")
                                << *hypothesis << ".\n";
        } else if (narrate && kind != "instance" && kind != "instImplicit") {
            const auto domain = formula(binder.at(3), ctx);
            if (!domain) return false;
            prose_ << "Fix \\(" << variable << "\\) in " << *domain << ".\n";
        }
        return true;
    }

    bool derive(const Node& expr, const Node* expected, Context ctx, bool narrateBinders) {
        if (deriveStep(expr,expected,std::move(ctx),narrateBinders)) return true;
        if (failure.empty()) {
            const auto& raw = term(expr);
            const auto name = head(raw);
            failure = "unexplained proof step " + (name.empty() ? "[" + raw.at(0).atom + "]" : name);
        }
        return false;
    }

    std::optional<bool> subtractNaturalSummand(const Node& expr, const Node& expected, const Context& ctx,
                                               const std::string& goal) {
        const auto& raw = term(expr);
        const auto name = head(raw);
        const bool forward = name=="eq_tsub_of_add_eq";
        if (!forward && name!="tsub_eq_of_eq_add" && name!="tsub_eq_of_eq_add_rev") return {};
        if (!raw.is("a") || raw.children.size()!=12 || !library_.count(name) || selected_.count(name)) return {};
        const char* standard[] = {"Nat","Nat.instPartialOrder","Nat.instAddCommSemigroup","instSubNat"};
        for (std::size_t i=0; i<4; ++i)
            if (!raw.at(i+2).is("c") || head(raw.at(i+2))!=standard[i]) return {};
        std::vector<const Node*> arguments;
        if (!proofArguments(raw,arguments) || arguments!=std::vector<const Node*>{&raw.at(6),&raw.at(10),&raw.at(11)} ||
            !naturalOrderInstance(raw.at(6)) || !naturalOrderInstance(raw.at(10))) return {};

        const auto& result = expr.is("p") ? expr.at(1) : expected;
        if (&result!=&expected && !sameKernelTerm(expected,result) &&
            !sameKernelTerm(expected,result,ctx.statementToProofBinders)) return {};
        const auto* premise = evidenceType(raw.at(11),ctx);
        if (!premise || !denominator::call(*premise,"Eq",3) || !denominator::call(result,"Eq",3) ||
            head(premise->at(2))!="Nat" || head(result.at(2))!="Nat") return {};
        const auto& sum = premise->at(forward ? 3 : 4);
        const auto& total = premise->at(forward ? 4 : 3);
        const auto& difference = result.at(forward ? 4 : 3);
        const auto& remainder = result.at(forward ? 3 : 4);
        if (!denominator::call(sum,"HAdd.hAdd",6) || !denominator::call(difference,"HSub.hSub",6) ||
            !denominator::hierarchy(difference.at(5),"Nat",{"instHSub"},"instSubNat")) return {};
        if (!denominator::hierarchy(sum.at(5),"Nat",{"instHAdd"},"instAddNat") &&
            !denominator::hierarchy(sum.at(5),"Nat",{"instHAdd","AddCommMagma.toAdd","AddCommSemigroup.toAddCommMagma"},
                                    "Nat.instAddCommSemigroup")) return {};
        const auto& removed = difference.at(7);
        const bool left = name=="tsub_eq_of_eq_add_rev";
        if (!sameKernelTerm(total,difference.at(6)) || !sameKernelTerm(sum.at(left ? 6 : 7),removed) ||
            !sameKernelTerm(sum.at(left ? 7 : 6),remainder) || !sameKernelTerm(total,raw.at(forward ? 8 : 7)) ||
            !sameKernelTerm(removed,raw.at(forward ? 9 : 8)) || !sameKernelTerm(remainder,raw.at(forward ? 7 : 9))) return {};
        const auto amount = formula(removed,ctx);
        const auto source = citation(name);
        if (!amount || !source) return {};

        // Validate the same two instance proofs as the detailed edition.
        // Their internal citations belong only to that detailed rendering.
        std::ostringstream details;
        details.swap(prose_);
        std::set<std::string> earlierUses;
        earlierUses.swap(used);
        const bool checked = derive(raw.at(6),nullptr,ctx,true) && derive(raw.at(10),nullptr,ctx,true);
        earlierUses.swap(used);
        details.swap(prose_);
        if (!checked || !derive(raw.at(11),premise,ctx,true)) return false;
        prose_ << "Subtracting " << *amount << " from both sides gives " << goal << " by " << *source << ".\n";
        return true;
    }

    bool deriveStep(const Node& expr, const Node* expected, Context ctx, bool narrateBinders) {
        const auto& raw = term(expr);
        if (!expected && expr.is("p")) expected = &expr.at(1);
        if (ring_equality::certificate(expr) && expected &&
            (sameKernelTerm(*expected,expr.at(1)) || sameKernelTerm(*expected,expr.at(1),ctx.statementToProofBinders))) {
            std::vector<const Node*> indeterminates;
            if (const auto terms=ring_equality::terms(expr.at(1), &indeterminates)) {
                if (*terms>3 && !indeterminates.empty() && indeterminates.size()<=8) {
                    std::vector<std::string> quantities;
                    for (const auto* quantity:indeterminates) {
                        const auto displayed=formula(*quantity,ctx);
                        if (!displayed) break;
                        quantities.push_back(*displayed);
                    }
                    if (quantities.size()==indeterminates.size()) {
                        prose_ << "Treat ";
                        for (std::size_t i=0;i<quantities.size();++i)
                            prose_ << (i==0 ? "" : i+1==quantities.size() ? " and " : ", ") << quantities[i];
                        prose_ << (quantities.size()==1 ? " as an indeterminate. " : " as indeterminates. ");
                    }
                }
                if (*terms==0) prose_ << "Expanding and collecting like terms reduces both sides to zero.\n";
                else prose_ << "Expanding and collecting like terms gives the same "
                            << (*terms==1 ? "term" : std::to_string(*terms)+" terms") << " on both sides.\n";
                return true;
            }
        }
        if (appliedConjunct(raw)) return applyConjunct(raw,expected,ctx);
        if (raw.is("proj") && attribute(raw,4) == "proof") {
            if (const auto measure = naturalMeasure(raw,ctx)) {
                prose_ << "A descending chain would make the natural-number measure " << *measure
                       << " strictly decrease at each step, so the relation is well-founded.\n";
                return true;
            }
            std::string fact;
            if (raw.at(1).atom == "And") return conjunct(raw,ctx,fact);
            const auto& pair = term(raw.at(3));
            if (raw.at(1).atom == "PSigma" && raw.at(2).atom == "1" && head(pair) == "PSigma.mk" &&
                pair.children.size() == 6) return derive(argument(pair,0),expected,std::move(ctx),narrateBinders);
            return fail("unsupported proof projection " + raw.at(1).atom + "." + raw.at(2).atom);
        }
        if (auto reduced = betaContract(raw))
            return derive(*reduced, expected, std::move(ctx), narrateBinders);
        if (head(raw) == "letFun" && raw.is("a")) {
            if (raw.children.size() != 6) return fail("unrecognized application of a local binding");
            const auto& continuation = term(argument(raw,0));
            if (!continuation.is("l")) return fail("unrecognized local binding");
            Node binding;
            binding.array = true;
            Node tag;
            tag.atom = "t";
            binding.children = {tag,continuation.at(1),continuation.at(2),continuation.at(3),
                                argument(raw,1),continuation.at(4)};
            return derive(binding, expected, std::move(ctx), narrateBinders);
        }
        if (raw.is("l")) {
            // A proof of a defined predicate can introduce a fresh argument
            // after all the binders printed in the statement are exhausted.
            const bool newArgument = !expected || !expected->is("q");
            if (!introduce(raw, expected, ctx, narrateBinders || newArgument)) return false;
            if (attribute(raw,6)=="proof")
                introduceChosenWitness(raw.at(4),raw.at(3),raw.at(1).atom,ctx,prose_);
            const auto* rest = expected && expected->is("q") ? &expected->at(4) : nullptr;
            return derive(raw.at(4), rest, std::move(ctx), narrateBinders);
        }
        if (raw.is("t")) {
            const auto& id = raw.at(1).atom;
            const auto& value = term(raw.at(4));
            const auto& valueHead = value.is("a") ? term(value.at(1)) : value;
            if (raw.at(4).is("p") || ((valueHead.is("v") || valueHead.is("c")) && attribute(valueHead,2) == "proof")
                || (value.is("l") && attribute(value,7) == "proof")) {
                if (!derive(raw.at(4), &raw.at(3), ctx, true)) return false;
                const auto fact = formula(raw.at(3), ctx);
                if (!fact) return false;
                ctx.assumptions[id] = *fact;
                ctx.hypothesisTypes[id] = &raw.at(3);
                ctx.provedFacts.insert(id);
                introduceChosenWitness(raw.at(5),raw.at(3),id,ctx,prose_);
            } else {
                const auto value = formula(raw.at(4), ctx);
                if (!value) return false;
                const auto name = checkedBinderName(ctx.names, id, raw.at(2).atom);
                prose_ << "Set \\(" << name << "\\) equal to " << *value << ".\n";
                if (!witnessObligations(raw.at(4),ctx)) return false;
            }
            return derive(raw.at(5), expected, std::move(ctx), narrateBinders);
        }
        if (raw.is("v")) {
            const auto it = ctx.assumptions.find(raw.at(1).atom);
            if (it == ctx.assumptions.end()) return false;
            if (ctx.inductionHypothesis == raw.at(1).atom) prose_ << "Use the induction hypothesis";
            else if (ctx.provedFacts.count(raw.at(1).atom)) prose_ << "Use the previously proved fact " << it->second;
            else prose_ << "Use the hypothesis " << it->second;
            const auto goal = expected ? formula(*expected,ctx) : std::nullopt;
            const auto hypothesisType = ctx.hypothesisTypes.find(raw.at(1).atom);
            const bool identical = expected && hypothesisType != ctx.hypothesisTypes.end() &&
                                   sameKernelTerm(*hypothesisType->second,*expected);
            if (goal && !identical && withoutLayout(*goal) != withoutLayout(it->second))
                prose_ << ", which simplifies to " << *goal;
            prose_ << ".\n";
            return true;
        }
        if (!raw.is("a") && !raw.is("c")) return false;
        const auto& fn = raw.is("a") ? raw.at(1) : raw;
        const auto name = head(raw);
        if (raw.is("a") && fn.is("v") && fn.at(1).atom==ctx.wellFoundedHypothesis) {
            std::string fact;
            return recursiveInstance(raw,ctx,fact);
        }
        if (name == "Nonempty.intro" && (!raw.is("a") || raw.children.size() != 4))
            return fail("missing nonemptiness witness");
        if (nat_below::certified(raw,matchers_) && expected) {
            auto same = [&](const Node& a,const Node& b) {
                return sameKernelTerm(a,b) || sameKernelTerm(b,a,ctx.statementToProofBinders);
            };
            auto apply = [&](const Node& motive,const Node& value) {
                Node app;
                app.array = true;
                app.children = {raw.at(0),motive,value};
                return instantiate(motive,app);
            };
            auto checkProof = [&](const Node& proof) {
                const auto& use=term(proof);
                const auto signature=signatures_.find(head(use));
                if (signature==signatures_.end()) return true; // The ordinary derivation checks local proofs.
                const auto actual=instantiate(*signature->second,use,true);
                return actual && same(*actual,proof.at(1));
            };
            auto required = [&](const Node& parent,std::size_t slot,const Node& fact) {
                return proofInputMatches(parent,slot,fact,ctx,[&](const Node& a,const Node& b) {
                    if (same(a,b)) return true;
                    Node left=a, right=b;
                    nat_below::normalizeAddition(left);
                    nat_below::normalizeAddition(right);
                    return same(left,right);
                });
            };
            const auto branches=nat_below::branches(raw,*expected,same,apply,checkProof,required);
            const auto goal=formula(*expected,ctx);
            if (!branches || !goal) return fail("unsupported course-of-values induction branch");
            return naturalInduction(raw.at(3),raw.at(2),*branches->base,branches->successor,ctx,*goal,false);
        }
        if (const auto* cases=tree_below::certificate(raw,matchers_); cases && expected)
            return treeInduction(raw,*cases,expr.is("p") ? expr.at(1) : *expected,std::move(ctx));
        if (name == "Lean.opaqueId" && raw.is("a") && raw.children.size() == 4 &&
            attribute(fn,2) == "proof")
            return derive(raw.at(3),&raw.at(2),std::move(ctx),narrateBinders);
        if (expected) {
            if (auto branch = directMatcherBranch(raw,*expected))
                return derive(*branch,expected,std::move(ctx),narrateBinders);
            if (expr.is("p") && matchers_.count(name) &&
                (sameKernelTerm(*expected,expr.at(1)) ||
                 sameKernelTerm(*expected,expr.at(1),ctx.statementToProofBinders)) &&
                recordEquality(expr,expr.at(1),ctx)) return true;
        }
        if (auto applied=applyAuxiliary(expr,expected,ctx,nullptr)) return *applied;
        if (helpers_.count(name)) return useHelper(name,raw,[&](const Node& proof) {
            return derive(proof,expected,ctx,narrateBinders);
        });
        std::optional<Node> inferredType;
        if (!expected && name=="WellFounded.fix" && (raw.children.size()==7 || raw.children.size()==8)) {
            const auto& motive=term(raw.at(3));
            if (motive.is("l")) {
                if (raw.children.size()==8) inferredType=applyMotive(motive,raw.at(7));
                else {
                    inferredType=motive;
                    inferredType->children[0].atom="q";
                }
                if (inferredType) expected=&*inferredType;
            }
        }
        if (!expected && (name == "Eq.mp" || name == "Eq.mpr") && raw.children.size() == 6)
            expected = &raw.at(name == "Eq.mp" ? 3 : 2);
        if (!expected && (name == "False.elim" || name == "id") && raw.children.size() == 4)
            expected = &raw.at(2);
        if (!expected && (name == "dite" || name == "ite") && raw.children.size() == 7)
            expected = &raw.at(2);
        if (!expected) {
            const auto signature = signatures_.find(name);
            const Node* type = signature != signatures_.end() ? signature->second : nullptr;
            if (fn.is("v")) {
                const auto local = ctx.hypothesisTypes.find(fn.at(1).atom);
                if (local != ctx.hypothesisTypes.end()) type = local->second;
            }
            if (type) {
                inferredType = instantiate(*type,raw,true);
                if (inferredType) expected = &*inferredType;
            }
        }
        if (!expected) {
            inferredType = recursorConclusion(raw,name);
            if (!inferredType) inferredType = logicalConclusion(raw,name);
            if (inferredType) expected = &*inferredType;
        }
        auto goal = expected ? formula(*expected,ctx) : std::nullopt;
        if (!goal && expected) goal=proofIdentity(*expected,ctx);
        if (!goal && (name == "HEq.refl" || name == "HEq.rfl") && raw.children.size() == 4) {
            std::vector<const Node*> premises;
            if (!proofArguments(raw,premises)) return false;
            const auto& item = raw.at(3);
            if (std::find(premises.begin(),premises.end(),&item) != premises.end()) {
                if (const auto prop = formula(raw.at(2),ctx))
                    goal = "the same proof of " + *prop + " on both sides of the heterogeneous equality";
            } else if (const auto val = formula(item,ctx))
                goal = *val + " heterogeneously equal to itself";
        }
        if (!goal) return fail("unrendered conclusion of " + name);
        if (compact_ && name=="id" && raw.children.size()==4) {
            std::vector<const Node*> arguments;
            if (proofArguments(raw,arguments) && arguments.size()==1 && arguments.front()==&raw.at(3)) {
                const auto start = prose_.tellp();
                if (!derive(raw.at(3),&raw.at(2),ctx,true)) return false;
                if (!endsWithFormula(prose_.str().substr(static_cast<std::size_t>(start)),*goal))
                    prose_ << "By the preceding argument, we obtain " << *goal << ".\n";
                return true;
            }
        }
        if (compact_ && expected)
            if (auto subtracted=subtractNaturalSummand(expr,*expected,ctx,*goal)) return *subtracted;
        if (compact_ && citeReversedEquality(raw,ctx,*goal)) return true;
        if (auto map=cardinalityBijection(raw,ctx); map && !earlier_.count(name)) {
            if (auto source=citation(name)) {
                prose_ << *map << " By " << *source << ", their cardinalities satisfy " << *goal << ".\n";
                return true;
            }
        }
        if (name == "Trans.trans" && expected) {
            const auto steps = calculationSteps(raw,*expected);
            if (!steps.empty()) {
                for (std::size_t i=0; i<steps.size(); ++i) {
                    prose_ << "\\par\\smallskip\\noindent\\emph{Equality " << i+1 << ".}\\enspace\n";
                    if (!derive(*steps[i],&steps[i]->at(1),ctx,true)) return false;
                }
                prose_ << "\\par Combining these equalities gives " << *goal << ".\n";
                return true;
            }
        }
        if ((name == "Iff.mpr" || name == "Iff.mp") && raw.children.size() == 5) {
            if (const auto source = inlinedEarlier(raw.at(4),ctx)) {
                prose_ << "Apply the " << (name == "Iff.mp" ? "forward" : "reverse")
                       << " implication of " << *source;
                if (narrateBinders) prose_ << " to obtain " << *goal;
                prose_ << ".\n";
                return true;
            }
        }
        if (compact_ && name == "of_eq_true" && raw.is("a"))
            return simplify(argument(raw,0), nullptr, nullptr, *goal, ctx);
        const bool transport = (name == "Eq.mp" || name == "Eq.mpr") && raw.children.size() == 6;
        const auto* originalType = transport ? &raw.at(name == "Eq.mp" ? 2 : 3) : nullptr;
        if (compact_ && transport) {
            if (expected)
                if (auto calculation=leftCalculation(raw,*expected,ctx)) return *calculation;
            const auto displayed = sameKernelTerm(raw.at(2),raw.at(3)) ? formula(*originalType,ctx) : std::nullopt;
            const bool unchanged = displayed && withoutLayout(*displayed)==withoutLayout(*goal);
            return simplify(argument(raw,1), &argument(raw,0), originalType, *goal, ctx, unchanged);
        }
        std::string reason;
        bool branches = false;
        if (name == "WellFounded.fix" && (raw.children.size() == 8 || raw.children.size() == 7)) {
            // Its step is ∀ x, (∀ y, R y x → C y) → C x.
            const auto& step = term(raw.at(6));
            if (!step.is("l") || !term(step.at(4)).is("l") || attribute(term(step.at(4)),6) != "proof")
                return fail("unrecognized well-founded induction step");
            if (raw.children.size()==7) {
                const auto& motive=term(raw.at(3));
                const auto& recur=term(step.at(4));
                const auto& smaller=recur.at(3);
                const Node* pointwise=expr.is("p") ? &expr.at(1) : expected;
                const auto goalAt=[&](const Node& binder,const Node& claim) {
                    if (motive.is("l"))
                        return sameKernelTerm(motive.at(3),raw.at(2)) &&
                               sameKernelTerm(motive.at(4),claim,{{motive.at(1).atom,binder.at(1).atom}});
                    return (motive.is("v") || motive.is("c")) && claim.is("a") && claim.children.size()==3 &&
                           sameKernelTerm(claim.at(1),motive) && claim.at(2).is("v") &&
                           claim.at(2).at(1).atom==binder.at(1).atom;
                };
                if (!pointwise || !pointwise->is("q") || (expected!=pointwise && expected &&
                    !sameKernelTerm(*expected,*pointwise,ctx.statementToProofBinders)) ||
                    !sameKernelTerm(pointwise->at(3),raw.at(2)) ||
                    !sameKernelTerm(step.at(3),raw.at(2)) || !smaller.is("q") || !smaller.at(4).is("q") ||
                    !sameKernelTerm(smaller.at(3),raw.at(2)) || !goalAt(*pointwise,pointwise->at(4)))
                    return fail("unverified pointwise conclusion of well-founded recursion");
                const auto& decrease=smaller.at(4).at(3);
                if (!decrease.is("a") || decrease.children.size()!=4 || !sameKernelTerm(decrease.at(1),raw.at(4)) ||
                    !decrease.at(2).is("v") || decrease.at(2).at(1).atom!=smaller.at(1).atom ||
                    !decrease.at(3).is("v") || decrease.at(3).at(1).atom!=step.at(1).atom ||
                    !goalAt(smaller,smaller.at(4).at(4)) || !recur.at(4).is("p") ||
                    !goalAt(step,recur.at(4).at(1)))
                    return fail("unverified smaller-case hypothesis of well-founded recursion");
                const auto* wellFounded=evidenceType(raw.at(5),ctx);
                if (!wellFounded || !record_equality::call(*wellFounded,"WellFounded",2) ||
                    !sameKernelTerm(wellFounded->at(2),raw.at(2)) || !sameKernelTerm(wellFounded->at(3),raw.at(4)))
                    return fail("missing well-foundedness of the recursion relation");
                ctx.wellFoundedHypothesis=recur.at(1).atom;
                ctx.inductionHypothesis=ctx.wellFoundedHypothesis;
            }
            if (!derive(raw.at(5),nullptr,ctx,true)) return false;
            prose_ << "Proceed by well-founded induction to prove " << *goal << ". For an arbitrary element we may assume "
                   << "the claim for each strictly smaller element.\n\\begin{proofstep}\n";
            if (!derive(raw.at(6),nullptr,ctx,true)) return false;
            prose_ << "\\end{proofstep}\nThe induction gives " << *goal << ".\n";
            return true;
        }
        const auto matched = witnessMatch(name,raw,ctx);
        if (matched == Matched::subtype) return unpackSubtype(raw,*goal,ctx);
        if (matched == Matched::none && expected) {
            // The declaration and its proof open their binders independently.
            // The checked annotation shares its local identifiers with the branch.
            const auto& claim = expr.is("p") ? expr.at(1) : *expected;
            if (auto unpacked = unpackProperty(raw,claim,ctx)) return *unpacked;
        }
        const bool unpack = matched == Matched::witnesses;
        const auto rule = rules.find(name);
        const auto earlier = earlier_.find(name);
        if (earlier != earlier_.end())
            reason = "By " + earlier->second + specialization(name,raw,ctx);
        else if (rule != rules.end()) {
            reason = rule->second.reason;
            branches = rule->second.branches;
            if (name == "isEmptyElim" && raw.children.size() == 6) {
                const auto object = formula(raw.at(5),ctx);
                const auto type = formula(raw.at(2),ctx);
                if (!object || !type) return fail("unrendered witness of the empty type");
                reason = "The element " + *object + " cannot belong to the empty type " + *type;
            }
        } else if (const auto ctor = propertyConstructors_.find(name); ctor != propertyConstructors_.end()) {
            if (!proveFields(*ctor->second,raw,ctx,false)) return false;
            prose_ << "These properties establish " << *goal << ".\n";
            return true;
        } else if (const auto it = recursors_.find(name); it != recursors_.end()) {
            return eliminate(*it->second,raw,ctx,*goal);
        } else if (unpack) {
            reason = "Using the witnesses and their properties";
            branches = true;
        } else if (const auto eq=definitions_.find(name); eq!=definitions_.end()) {
            reason = "By " + eq->second.reference;
        } else if (library_.count(name) && !selected_.count(name)) {
            if (!describeCheckedStatement(library_.at(name)->at(1))) return fail("unrendered prerequisite " + name);
            reason = "By " + prerequisiteReference(*library_.at(name)) + specialization(name,raw,ctx);
            used.insert(name);
        } else if (fn.is("v") && ctx.assumptions.count(fn.at(1).atom)) {
            reason = fn.at(1).atom == ctx.inductionHypothesis ? "Applying the induction hypothesis" :
                "Applying the hypothesis " + ctx.assumptions.at(fn.at(1).atom);
        } else return fail("unexplained rule " + name);
        if (raw.is("a")) {
            if (!explainArgumentTransports(raw,ctx)) return false;
            const bool strongNat = name == "Nat.caseStrongRecOn" || name == "Nat.case_strong_induction_on";
            if (earlier == earlier_.end() && raw.children.size() == 6 && (strongNat || name == "Nat.recAux")) {
                const auto& step = term(raw.at(strongNat ? 5 : 4));
                if (step.is("l") && term(step.at(4)).is("l") && attribute(term(step.at(4)),6) == "proof")
                    return naturalInduction(raw.at(strongNat ? 3 : 5),term(raw.at(2)),
                                            raw.at(strongNat ? 4 : 3),raw.at(strongNat ? 5 : 4),
                                            ctx,*goal,strongNat);
            }
            if (name == "Finset.strongDownwardInductionOn" && raw.children.size() >= 8) {
                const auto set = formula(raw.at(5),ctx);
                const auto bound = formula(raw.at(3),ctx);
                if (!set || !bound) return fail("unrendered downward induction parameters");
                prose_ << "Use descending induction starting at " << *set << " with cardinality at most " << *bound
                       << ". The induction hypothesis applies to each strict superset within that bound.\n";
            }
            if (name == "Nat.decreasingInduction'" && raw.children.size() == 8) {
                const auto lower = formula(raw.at(2),ctx), upper = formula(raw.at(3),ctx);
                if (!lower || !upper) return fail("unrendered induction interval");
                prose_ << "Start at " << *upper << " and work downward to " << *lower
                       << ". Each step uses the result for the next larger integer.\n";
            }
            if (name == "Finset.strongInductionOn" && raw.children.size() >= 6) {
                const auto set = formula(raw.at(4),ctx);
                if (!set) return fail("unrendered induction set");
                prose_ << "Use strong induction on " << *set
                       << ", assuming the claim for every strict subset in the induction step.\n";
            }
            if (name == "Exists.intro" || name == "Nonempty.intro") {
                const auto& witness = argument(raw,name == "Exists.intro" ? 1 : 0);
                const auto& value = term(witness);
                if (witness.is("p") || (value.is("v") && ctx.assumptions.count(value.at(1).atom))) {
                    const auto property = witness.is("p") ? formula(witness.at(1),ctx) :
                        std::optional<std::string>(ctx.assumptions.at(value.at(1).atom));
                    if (!property) return false;
                    prose_ << "The construction requires evidence that " << *property << ".\n";
                } else if (!(name=="Exists.intro" && classicalDecision(witness,raw.at(2),ctx))) {
                    const auto choice = formula(witness,ctx);
                    if (!choice) return fail("unrendered existential witness");
                    const auto description = recordWitness(witness,*choice,raw.at(2),ctx);
                    if (description==*choice) prose_ << "Choose the witness " << *choice << ".\n";
                    else prose_ << "Construct " << description << ".\n";
                    if (!witnessObligations(witness,ctx)) return false;
                }
            }
            std::vector<const Node*> premises;
            if (!proofArguments(raw, premises)) return false;
            if (name == "Function.comp") std::reverse(premises.begin(), premises.end());
            if (name == "Nat.decreasingInduction'" && raw.children.size() == 8 && premises.size() == 3 &&
                premises[0] == &raw.at(5) && premises[1] == &raw.at(6) && premises[2] == &raw.at(7))
                std::rotate(premises.begin(),premises.begin()+1,premises.end());
            if (name == "dite" || name == "ite") {
                const auto condition = formula(raw.at(3),ctx);
                if (!condition) return false;
                prose_ << "Distinguish whether " << *condition << " holds.\n";
            }
            const bool twoBounds = name=="le_antisymm" && library_.count(name) && raw.children.size()==8 &&
                premises==std::vector<const Node*>{&raw.at(6),&raw.at(7)} &&
                !term(raw.at(6)).is("v") && !term(raw.at(7)).is("v");
            for (const auto* premise : premises) {
                const auto& child = *premise;
                const auto& value = term(child);
                if (twoBounds)
                    prose_ << "\\par\\smallskip\\noindent\\emph{" << (premise==premises.front() ? "Upper" : "Lower")
                           << " bound.}\\enspace\n";
                if (earlier != earlier_.end() && value.is("v") &&
                    ctx.assumptions.count(value.at(1).atom)) continue;
                const bool subproof = term(child).is("l");
                const bool natCase = name == "Nat.casesAuxOn" && raw.children.size() >= 6 &&
                                     (premise == &raw.at(4) || premise == &raw.at(5));
                if (natCase) prose_ << (premise == &raw.at(4) ? "In the zero case,\n" :
                    "In the successor case,\n") << "\\begin{proofstep}\n";
                else if (subproof) prose_ << (unpack ? "Take the witnesses from the preceding result.\n" :
                    branches ? "Consider the following case.\n" :
                    "For the required implication, argue as follows.\n") << "\\begin{proofstep}\n";
                const auto* required = transport && premise == &argument(raw,0) ? originalType : nullptr;
                if (name == "Iff.intro" && raw.children.size() == 6 && value.is("l")) {
                    auto branch = ctx;
                    const auto& conclusion = raw.at(premise == &raw.at(4) ? 3 : 2);
                    if (!introduce(value,nullptr,branch,true) ||
                        !derive(value.at(4),&conclusion,std::move(branch),true)) return false;
                } else if (!derive(child, required, ctx, true)) return false;
                if (subproof || natCase) prose_ << "\\end{proofstep}\n";
            }
            if (twoBounds) prose_ << "\\par\\smallskip\\noindent ";
        }
        if (!compact_ && transport && originalType)
            showDenominatorStep(argument(raw,1),*originalType,ctx,*goal,nullptr);
        if (earlier != earlier_.end() && !narrateBinders) {
            prose_ << "Apply " << earlier->second << specialization(name,raw,ctx) << ".\n";
            return true;
        }
        const bool sentence = reason.rfind("The ",0) == 0 || reason.rfind("This ",0) == 0 ||
            reason.rfind("Every ",0) == 0 || reason.rfind("Together ",0) == 0;
        prose_ << reason << (sentence ? ". Hence " : ", we obtain ") << *goal << ".\n";
        return true;
    }
};

} // namespace

std::optional<std::string> generalProof(const Node& record, const Node& input,
    const std::map<std::string, std::string>& earlierReferences,
    const DefinitionRules& definitions, std::set<std::string>& externalPremises, bool compact, std::string* failure,
    std::size_t resultNumber) {
    std::map<std::string,std::string> references;
    std::vector<auxiliary::Lemma> lemmas;
    if (compact && resultNumber) {
        for (const auto* helper : auxiliary::repeated(record,input,definitions)) {
            if (auxiliary::incompatibleConclusion(*helper)) continue;
            const auto statement = describeCheckedStatement(helper->at(1));
            if (!statement) continue;
            ProofWriter subproof(input,earlierReferences,definitions,compact,references);
            auto body = subproof.render(*helper);
            if (!body || std::count(body->begin(),body->end(),'\n')<6) continue;
            auto link = auxiliary::reference(resultNumber,lemmas.size()+1);
            references.emplace(helper->at(0).atom,link);
            lemmas.push_back({*statement,std::move(*body),std::move(subproof.used),link});
        }
    }
    ProofWriter writer(input, earlierReferences, definitions, compact, references);
    auto proof = writer.render(record);
    if (proof) {
        externalPremises.insert(writer.used.begin(), writer.used.end());
        if (!lemmas.empty()) return auxiliary::assemble(std::move(*proof),lemmas,resultNumber,externalPremises);
    }
    else if (failure) *failure = writer.failure;
    return proof;
}

} // namespace proof
