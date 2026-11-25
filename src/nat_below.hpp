#pragma once

#include "expressions.hpp"
#include <algorithm>

namespace proof::nat_below {

inline bool call(const Node& n, const char* name, std::size_t arity) {
    return n.is("a") && n.children.size()==arity+2 && head(n)==name;
}

inline bool binder(const Node& n, const char* tag) {
    return n.is(tag) && n.children.size()>=8;
}

inline bool local(const Node& n, const Node& binding) {
    return n.is("v") && n.at(1).atom==binding.at(1).atom;
}

inline bool containsLocal(const Node& n, const Node& binding) {
    return local(n,binding) || std::any_of(n.children.begin(),n.children.end(),
        [&](const Node& child) { return child.array && containsLocal(child,binding); });
}

inline bool zero(const Node& n) {
    const auto literal=[](const Node& v) { return v.is("n") && v.at(1).atom=="0"; };
    return literal(n) || (n.is("c") && head(n)=="Nat.zero") ||
        (call(n,"OfNat.ofNat",3) && head(n.at(2))=="Nat" && literal(n.at(3)) &&
         call(n.at(4),"instOfNatNat",1) && literal(n.at(4).at(2)));
}

// The recursion table for k+1 has P(k) in its first field. A use of its
// tail would require an earlier induction hypothesis, beyond ordinary induction.
inline bool replacePredecessor(Node& n, const Node& history) {
    if (n.is("proj") && n.children.size()==5 && n.at(1).atom=="PProd" && n.at(2).atom=="0" &&
        n.at(4).atom=="proof" && local(n.at(3),history)) {
        Node ih=n.at(3);
        ih.children[2].atom="proof";
        n=std::move(ih);
        return true;
    }
    return !local(n,history) && std::all_of(n.children.begin(),n.children.end(),
        [&](Node& child) { return !child.array || replacePredecessor(child,history); });
}

using Catalog = std::map<std::string,const Node*>;

inline bool certified(const Node& raw, const Catalog& matchers) {
    if (!call(raw,"Nat.brecOn",3)) return false;
    const auto& step=term(raw.at(4));
    if (!binder(step,"l") || !binder(step.at(4),"l")) return false;
    const auto& match=term(step.at(4).at(4));
    const auto it=matchers.find(head(match));
    if (it==matchers.end() || it->second->children.size()!=6) return false;
    const auto& info=it->second->at(5);
    return info.is("natCases") && info.children.size()==3 && info.at(1).atom=="Nat.zero" &&
        info.at(2).atom=="Nat.succ";
}

struct Branches {
    const Node* base;
    Node successor;
};

// Recover ordinary induction only when both original proofs have the right
// specialization of the motive and the supplied history flows to that match.
template<class Same, class Apply, class CheckProof>
std::optional<Branches> branches(const Node& raw, const Node& conclusion, Same same, Apply apply,
                                 CheckProof checkProof) {
    const auto& motive=raw.at(2);
    const auto& step=term(raw.at(4));
    const auto& history=step.at(4);
    const auto& match=term(history.at(4));
    if (!binder(motive,"l") || head(motive.at(3))!="Nat" || head(step.at(3))!="Nat" ||
        !match.is("a") || match.children.size()!=7 || !local(match.at(3),step) ||
        !local(match.at(6),history)) return {};
    const auto below=[&](const Node& type) {
        return call(type,"Nat.below",2) && same(type.at(2),motive);
    };
    const auto goalAt=[&](const Node& index,const Node& goal) {
        auto wanted=apply(motive,index);
        return wanted && same(*wanted,goal);
    };
    const auto branchGoal=[&](const Node& branch,const Node& index) {
        if (!branch.at(4).is("p") || !checkProof(branch.at(4))) return false;
        const auto& actual=branch.at(4).at(1);
        if (goalAt(index,actual)) return true;
        if (branch.children.size()!=9) return false;
        const auto& witness=branch.at(8);
        return witness.is("inductionCase") && witness.children.size()==3 &&
            same(actual,witness.at(1)) && goalAt(index,witness.at(2));
    };
    if (!below(history.at(3)) || !local(history.at(3).at(3),step) ||
        !goalAt(raw.at(3),conclusion)) return {};
    const auto& family=match.at(2);
    if (!binder(family,"l") || head(family.at(3))!="Nat" || !binder(family.at(4),"q")) return {};
    const auto& premise=family.at(4);
    if (!below(premise.at(3)) || !local(premise.at(3).at(3),family) ||
        !goalAt(premise.at(3).at(3),premise.at(4))) return {};

    const auto& base=match.at(4);
    const auto& succ=match.at(5);
    if (!binder(base,"l") || head(base.at(3))!="Unit" || !binder(base.at(4),"l") ||
        !binder(succ,"l") || head(succ.at(3))!="Nat" || !binder(succ.at(4),"l")) return {};
    const auto& atZero=base.at(4);
    const auto& atSuccessor=succ.at(4);
    if (!below(atZero.at(3)) || !zero(atZero.at(3).at(3)) || !below(atSuccessor.at(3))) return {};
    const auto& nextIndex=atSuccessor.at(3).at(3);
    if (!call(nextIndex,"Nat.succ",1) || !local(nextIndex.at(2),succ) ||
        !branchGoal(atZero,atZero.at(3).at(3)) || !branchGoal(atSuccessor,nextIndex) ||
        containsLocal(atZero.at(4),base) || containsLocal(atZero.at(4),atZero)) return {};
    auto hypothesis=apply(motive,nextIndex.at(2));
    if (!hypothesis) return {};
    Branches result{&atZero.at(4),succ};
    auto& ih=result.successor.children[4];
    ih.children[3]=std::move(*hypothesis);
    ih.children[6].atom="proof";
    if (!replacePredecessor(ih.children[4],atSuccessor)) return {};
    return result;
}

} // namespace proof::nat_below
