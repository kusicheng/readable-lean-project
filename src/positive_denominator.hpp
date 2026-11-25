#pragma once

#include "expressions.hpp"
#include <algorithm>

namespace proof::denominator {

struct Step {
    std::vector<std::string> origins;
    std::string rule, quotient, positivity, witness, cleared, domain;
};

inline bool call(const Node& expression, const char* name, std::size_t arity) {
    const auto& raw = term(expression);
    return raw.is("a") && raw.children.size()==arity+2 && head(raw)==name;
}

// simp and the order lemmas may select the same standard multiplication or
// inversion through different superclass projections. Match the full paths,
// including their carrier, so a different installed operation stays distinct.
inline bool hierarchy(const Node& instance, const std::string& carrier,
                      std::initializer_list<const char*> path, const char* base) {
    const Node* current=&instance;
    for (const char* projection : path) {
        if (!call(*current,projection,2) || head(current->at(2))!=carrier) return false;
        current=&current->at(3);
    }
    return current->is("c") && head(*current)==base;
}

inline bool standardMul(const Node& instance,const std::string& carrier) {
    if (carrier=="Rat") return hierarchy(instance,carrier,{"instHMul"},"Rat.instMul") ||
        hierarchy(instance,carrier,{"instHMul","Distrib.toMul","NonUnitalNonAssocSemiring.toDistrib",
            "NonAssocSemiring.toNonUnitalNonAssocSemiring","Semiring.toNonAssocSemiring"},"Rat.semiring") ||
        hierarchy(instance,carrier,{"instHMul","MulZeroClass.toMul","MulZeroOneClass.toMulZeroClass",
            "MonoidWithZero.toMulZeroOneClass","GroupWithZero.toMonoidWithZero","CommGroupWithZero.toGroupWithZero"},
            "Rat.commGroupWithZero");
    if (carrier!="NNRat") return false;
    return hierarchy(instance,carrier,{"instHMul","Distrib.toMul","NonUnitalNonAssocSemiring.toDistrib",
               "NonAssocSemiring.toNonUnitalNonAssocSemiring","Semiring.toNonAssocSemiring",
               "DivisionSemiring.toSemiring","Semifield.toDivisionSemiring"},"NNRat.instSemifield") ||
           hierarchy(instance,carrier,{"instHMul","MulZeroClass.toMul","MulZeroOneClass.toMulZeroClass",
               "MonoidWithZero.toMulZeroOneClass","GroupWithZero.toMonoidWithZero",
               "CommGroupWithZero.toGroupWithZero","Semifield.toCommGroupWithZero"},"NNRat.instSemifield");
}

inline bool ordinaryNumerals(const Node& expression) {
    const auto& raw=term(expression);
    if (call(raw,"OfNat.ofNat",3)) {
        const auto carrier=head(raw.at(2));
        if (carrier=="Rat" || carrier=="NNRat") return isStandardRationalNumeral(raw,carrier);
        if (carrier!="Nat" || !raw.at(3).is("n") || !call(raw.at(4),"instOfNatNat",1) ||
            !raw.at(4).at(2).is("n")) return false;
        return raw.at(3).at(1).atom==raw.at(4).at(2).at(1).atom;
    }
    if (raw.is("a")) {
        for (std::size_t i=2;i<raw.children.size();++i)
            if (!ordinaryNumerals(raw.at(i))) return false;
    } else if (raw.is("l")) return ordinaryNumerals(raw.at(4));
    return true;
}

template<class Same>
bool sameScalar(const Node& a,const Node& b,const std::string& carrier,Same same) {
    if (same(a,b)) return true;
    const auto& x=term(a); const auto& y=term(b);
    if (call(x,"Inv.inv",3) && call(y,"Inv.inv",3))
        return head(x.at(2))==carrier && same(x.at(2),y.at(2)) && same(x.at(4),y.at(4)) &&
               isStandardRationalInverse(x.at(3),carrier) && isStandardRationalInverse(y.at(3),carrier);
    if (!call(x,"HMul.hMul",6) || !call(y,"HMul.hMul",6)) return false;
    for (std::size_t i=2;i<=4;++i)
        if (head(x.at(i))!=carrier || !same(x.at(i),y.at(i))) return false;
    return standardMul(x.at(5),carrier) && standardMul(y.at(5),carrier) &&
           sameScalar(x.at(6),y.at(6),carrier,same) && sameScalar(x.at(7),y.at(7),carrier,same);
}

template<class Same>
bool sameBound(const Node& a,const Node& b,Same same) {
    if (same(a,b)) return true;
    if (!call(a,"LE.le",4) || !call(b,"LE.le",4)) return false;
    const auto& x=term(a); const auto& y=term(b);
    const auto carrier=head(x.at(2));
    return same(x.at(2),y.at(2)) && isStandardRationalOrder(x,carrier) && isStandardRationalOrder(y,carrier) &&
           sameScalar(x.at(4),y.at(4),carrier,same) && sameScalar(x.at(5),y.at(5),carrier,same);
}

// These closed superclass applications discharge the order-instance premises
// of rational denominator clearing and natural-cast monotonicity. Never
// collapse a chain rooted in a local assumption or an unfamiliar theorem.
inline bool rationalHierarchy(const Node& proof, std::vector<std::string>& names) {
    const auto& raw=term(proof);
    const auto name=head(raw);
    if (raw.is("c") && (name=="instIsStrictOrderedRingNNRat" || name=="NNRat.instCharZero" ||
                         name=="Rat.instIsStrictOrderedRing" || name=="Rat.instCharZero")) {
        names.push_back(name);
        return true;
    }
    if (name!="PosMulReflectLE.toPosMulReflectLT" && name!="PosMulStrictMono.toPosMulReflectLE" &&
        name!="IsStrictOrderedRing.toPosMulStrictMono" && name!="IsOrderedAddMonoid.toAddLeftMono" &&
        name!="IsOrderedRing.toIsOrderedAddMonoid" && name!="IsStrictOrderedRing.toIsOrderedRing" &&
        name!="IsStrictOrderedRing.toZeroLEOneClass") return false;
    std::vector<const Node*> premises;
    if (!raw.is("a") || (head(raw.at(2))!="NNRat" && head(raw.at(2))!="Rat") || !proofArguments(raw,premises) || premises.size()!=1 ||
        !rationalHierarchy(*premises.front(),names)) return false;
    names.push_back(name);
    return true;
}

inline void structuralRules(const Node& expression, std::vector<std::string>& names) {
    if (!expression.array || expression.children.empty()) return;
    const auto& raw=term(expression);
    std::vector<std::string> chain;
    if (rationalHierarchy(raw,chain)) {
        names.insert(names.end(),chain.begin(),chain.end());
        return;
    }
    if (raw.is("a")) {
        for (std::size_t i=1;i<raw.children.size();++i) structuralRules(raw.at(i),names);
    } else if (raw.is("l")) structuralRules(raw.at(4),names);
}

// A conventional rational numerator may be written without its natural cast.
// Leave custom instances explicit. These projections lead to the standard
// nonnegative rational semifield in Mathlib.
inline const Node& scalar(const Node& expression) {
    const auto& raw = term(expression);
    if (!call(raw,"Nat.cast",3) || head(raw.at(2))!="NNRat") return raw;
    return hierarchy(raw.at(3),"NNRat",{"AddMonoidWithOne.toNatCast", "AddCommMonoidWithOne.toAddMonoidWithOne",
            "NonAssocSemiring.toAddCommMonoidWithOne", "Semiring.toNonAssocSemiring",
            "DivisionSemiring.toSemiring", "Semifield.toDivisionSemiring"},"NNRat.instSemifield") ? raw.at(4) : raw;
}

// Collect only the actual rules at the leaves of a congruence proof.
// A rule with further side conditions stays on the ordinary narrative path.
inline bool collectOrigins(const Node& proof, std::vector<std::string>& origins) {
    const auto& raw = term(proof);
    if (!raw.is("a") && !raw.is("c")) return false;
    const auto name = head(raw);
    std::vector<const Node*> premises;
    if (!proofArguments(raw,premises)) return false;
    if (name=="Eq.refl" || name=="rfl") return premises.empty();
    if (name=="Eq.trans" || name=="congrArg" || name=="congrFun" || name=="congr") {
        for (const Node* premise : premises)
            if (!collectOrigins(*premise,origins)) return false;
        return true;
    }
    if (!premises.empty() || name.empty()) return false;
    if (std::find(origins.begin(),origins.end(),name)==origins.end()) origins.push_back(name);
    return true;
}

// Follow whole-proposition equality links forward from the supplied bound.
// A rewrite under a negation, implication, or other context does not establish
// the rewritten subproposition as a separate fact.
template<class Same, class Beta>
std::optional<Step> explain(const Node& certificate, const Node& original, const Names& names,
                            const std::map<std::string,const Node*>& hypothesisTypes, Same same, Beta beta) {
    if (!certificate.is("p") || !call(certificate.at(1),"Eq",3)) return {};
    const auto& equality = term(certificate.at(1));
    if (!call(original,"LE.le",4) ||
        !isStandardRationalOrder(original,head(term(original).at(2))) ||
        !sameBound(original,equality.at(3),same)) return {};
    struct Link { const Node& proof; const Node& before; const Node& after; };
    std::vector<Link> pending{{certificate,equality.at(3),equality.at(4)}};
    Step step;
    while (!pending.empty()) {
        const auto link = pending.back();
        pending.pop_back();
        const auto& proof = term(link.proof);
        if (call(proof,"Eq.trans",6)) {
            if (!same(link.before,proof.at(3)) || !same(link.after,proof.at(5))) return {};
            pending.push_back({proof.at(7),proof.at(4),link.after});
            pending.push_back({proof.at(6),link.before,proof.at(4)});
            continue;
        }
        const auto reduced = beta(proof);
        const auto& ext = reduced ? term(*reduced) : proof;
        if (!call(ext,"propext",3)) {
            if (!collectOrigins(proof,step.origins)) return {};
            continue;
        }
        const auto& law = term(ext.at(4));
        const auto name = head(law);
        if (name!=u8"mul_inv_le_iff₀'" || law.children.size()!=10 ||
            !sameBound(link.before,ext.at(2),same) || !sameBound(link.after,ext.at(3),same)) return {};
        const auto& lhs = term(link.before);
        const auto& rhs = term(link.after);
        if (!call(lhs,"LE.le",4) || !call(rhs,"LE.le",4)) return {};
        const auto& product = term(lhs.at(4));
        const auto& cleared = term(rhs.at(5));
        if (!call(product,"HMul.hMul",6) || !call(cleared,"HMul.hMul",6) ||
            !call(product.at(7),"Inv.inv",3)) return {};
        const auto carrier=head(law.at(2));
        const bool group = carrier=="Rat" ? hierarchy(law.at(3),carrier,{},"Rat.commGroupWithZero") :
            hierarchy(law.at(3),carrier,{"Semifield.toCommGroupWithZero"},"NNRat.instSemifield");
        const bool order = carrier=="Rat" ? hierarchy(law.at(4),carrier,{},"Rat.instPartialOrder") :
            hierarchy(law.at(4),carrier,{"SemilatticeInf.toPartialOrder","Lattice.toSemilatticeInf",
                "DistribLattice.toLattice","instDistribLatticeOfLinearOrder"},"instNNRatLinearOrder");
        if (!group || !order || !isStandardRationalOrder(lhs,carrier) || !isStandardRationalOrder(rhs,carrier) ||
            !standardMul(product.at(5),carrier) || !standardMul(cleared.at(5),carrier) ||
            !isStandardRationalInverse(term(product.at(7)).at(3),carrier)) return {};
        const Node& bound=law.at(6), &numerator=law.at(7), &divisor=law.at(8);
        if (!ordinaryNumerals(bound) || !ordinaryNumerals(numerator) || !ordinaryNumerals(divisor)) return {};
        if (!same(numerator,product.at(6)) || !same(divisor,term(product.at(7)).at(4)) ||
            !same(bound,lhs.at(5)) || !same(numerator,rhs.at(4)) ||
            !same(divisor,cleared.at(6)) || !same(bound,cleared.at(7))) return {};
        const auto& witness = law.at(9);
        const Node* positivity = witness.is("p") ? &witness.at(1) : nullptr;
        if (!positivity && witness.is("v")) {
            const auto it = hypothesisTypes.find(witness.at(1).atom);
            if (it!=hypothesisTypes.end()) positivity = it->second;
        }
        if (!positivity || !call(*positivity,"LT.lt",4)) return {};
        const auto& strict = term(*positivity);
        const auto& zero = term(strict.at(4));
        if (!same(strict.at(2),law.at(2)) || !same(strict.at(5),divisor) ||
            !isStandardRationalOrder(strict,carrier) || !isStandardRationalZero(zero,carrier)) return {};
        auto n=checkedFormula(scalar(numerator),names), d=checkedFormula(scalar(divisor),names),
             a=checkedFormula(scalar(bound),names), positive=checkedFormula(strict,names),
             result=checkedFormula(rhs,names);
        if (!n || !d || !a || !positive || !result) return {};
        step.rule = name;
        step.domain = carrier == "NNRat" ? "the nonnegative rationals" : "the rationals";
        step.quotient = "\\frac{" + *n + "}{" + *d + "} \\le " + *a;
        step.positivity = "0 < " + *d;
        step.witness = "\\(" + *positive + "\\)";
        step.cleared = "\\(" + *result + "\\)";
        return step;
    }
    return {};
}

} // namespace proof::denominator
