#pragma once

#include "expressions.hpp"

#include <algorithm>
#include <charconv>
#include <cstdint>
#include <iterator>

namespace proof::ring_equality {

using Monomial = std::vector<std::size_t>;
using Polynomial = std::map<Monomial, std::int64_t>;

// These bounds only limit which calculations get a compact explanation.
// The square of the coefficient bound fits a signed 64-bit intermediate.
constexpr std::int64_t coefficientLimit = 1000000000;
constexpr std::size_t termLimit = 128;

inline bool accumulate(Polynomial& result, const Monomial& key, std::int64_t increment) {
    const auto coefficient = result[key] + increment;
    if (coefficient < -coefficientLimit || coefficient > coefficientLimit) return false;
    if (coefficient) result[key] = coefficient;
    else result.erase(key);
    return result.size() <= termLimit;
}

inline bool sameAtom(const Node& left, const Node& right) {
    // The lists of visible arguments and proof premises describe a constant
    // at a call site. Its identity, arguments and binder IDs determine the term.
    if (left.is("v") || left.is("c") || left.is("n"))
        return right.is(left.at(0).atom.c_str()) && left.at(1).atom == right.at(1).atom;
    if (left.is("proj"))
        return right.is("proj") && left.at(1).atom==right.at(1).atom &&
            left.at(2).atom==right.at(2).atom && sameAtom(left.at(3),right.at(3));
    if (!left.is("a") || !right.is("a") || left.children.size()!=right.children.size()) return false;
    for (std::size_t i=1;i<left.children.size();++i)
        if (!sameAtom(left.at(i),right.at(i))) return false;
    return true;
}

// The interchange format omits universe levels. Only intern local variables,
// their applications and known monomorphic natural-number operations. Two
// arbitrary universe-polymorphic constants could print identically here.
inline bool naturalAtom(const Node& value) {
    if (value.is("v") || value.is("n")) return true;
    if (value.is("proj") && value.children.size()>=4 && value.at(1).atom=="Fin" && value.at(2).atom=="0")
        return naturalAtom(value.at(3));
    if (!value.is("a")) return false;
    const auto name=head(value);
    if (value.at(1).is("v"))
        return std::all_of(value.children.begin()+2,value.children.end(),naturalAtom);
    if (name=="Fin.val" && value.children.size()==4)
        return naturalAtom(value.at(2)) && naturalAtom(value.at(3));
    if (name=="OfNat.ofNat" && value.children.size()==5 && head(value.at(2))=="Nat") {
        const auto& instance=value.at(4);
        return value.at(3).is("n") && instance.is("a") && instance.children.size()==3 &&
            head(instance)=="instOfNatNat" && sameAtom(value.at(3),instance.at(2));
    }
    if (name=="HAdd.hAdd" || name=="HSub.hSub" || name=="HMul.hMul") {
        const std::string op=name=="HAdd.hAdd" ? "Add" : name=="HSub.hSub" ? "Sub" : "Mul";
        if (value.children.size()!=8) return false;
        const auto& instance=value.at(5);
        for (std::size_t i=2;i<5;++i) if (!value.at(i).is("c") || head(value.at(i))!="Nat") return false;
        return instance.is("a") && instance.children.size()==4 && head(instance)=="instH"+op &&
            head(instance.at(2))=="Nat" && instance.at(3).is("c") && head(instance.at(3))=="inst"+op+"Nat" &&
            naturalAtom(value.at(6)) && naturalAtom(value.at(7));
    }
    if (name!="Nat.succ" && name!="Nat.centralBinom" && name!="Nat.choose" && name!="Nat.factorial" &&
        name!="Nat.add" && name!="Nat.mul" && name!="Nat.sub" && name!="Nat.pow") return false;
    return std::all_of(value.children.begin()+2,value.children.end(),naturalAtom);
}

class Normalizer {
public:
    std::vector<const Node*> indeterminates() const {
        std::vector<const Node*> results;
        for (const auto& atom:atoms_) results.push_back(atom.key);
        return results;
    }

    std::optional<Polynomial> expand(const Node& expression) {
        if (++operations_ > 16000) return {};
        const auto name=head(expression);
        if (expression.is("a") && name=="OfNat.ofNat") {
            if (!isStandardRationalNumeral(expression,"Rat")) return {};
            const Node& index=expression.at(3);
            const auto& digits=index.is("n") ? index.at(1).atom : index.at(3).at(1).atom;
            std::int64_t value=0;
            const auto parsed=std::from_chars(digits.data(),digits.data()+digits.size(),value);
            if (parsed.ec!=std::errc{} || parsed.ptr!=digits.data()+digits.size() ||
                value<0 || value>coefficientLimit) return {};
            return value ? Polynomial{{{},value}} : Polynomial{};
        }
        if (name=="HAdd.hAdd" || name=="HSub.hSub" || name=="HMul.hMul") {
            const std::string op=name=="HAdd.hAdd" ? "Add" : name=="HSub.hSub" ? "Sub" : "Mul";
            if (!expression.is("a") || expression.children.size()!=8 ||
                !rational(expression.at(2)) || !rational(expression.at(3)) || !rational(expression.at(4))) return {};
            const auto& instance=expression.at(5);
            if (!instance.is("a") || instance.children.size()!=4 || head(instance)!="instH"+op ||
                !rational(instance.at(2)) || !isStandardRationalStructure(instance.at(3),op)) return {};
            auto a=expand(expression.at(6)), b=expand(expression.at(7));
            if (!a || !b) return {};
            if (op!="Mul") {
                for (const auto& [key,k]:*b)
                    if (!accumulate(*a,key,op=="Sub" ? -k : k)) return {};
                return a;
            }
            Polynomial product;
            for (const auto& [x,m]:*a) for (const auto& [y,n]:*b) {
                if (++operations_>16000 || x.size()+y.size()>32) return {};
                Monomial key;
                std::merge(x.begin(),x.end(),y.begin(),y.end(),std::back_inserter(key));
                if (!accumulate(product,key,m*n)) return {};
            }
            return product;
        }
        if (name=="Neg.neg") {
            if (!expression.is("a") || expression.children.size()!=5 || !rational(expression.at(2)) ||
                !isStandardRationalStructure(expression.at(3),"Neg")) return {};
            auto value=expand(expression.at(4));
            if (!value) return {};
            for (auto& entry:*value) entry.second=-entry.second;
            return value;
        }
        // A cast is one indeterminate for each *natural expression*. The
        // instance check permits different superclass paths to the usual cast.
        const bool cast=name=="Nat.cast";
        if (cast && (!expression.is("a") || expression.children.size()!=5 || !rational(expression.at(2)) ||
            !isStandardRationalStructure(expression.at(3),"NatCast"))) return {};
        const auto& key=cast ? expression.at(4) : expression;
        if (cast ? !naturalAtom(key) :
            !(key.is("v") || (key.is("a") && key.at(1).is("v") &&
              std::all_of(key.children.begin()+2,key.children.end(),naturalAtom)))) return {};
        auto it=std::find_if(atoms_.begin(),atoms_.end(),[&](const Atom& atom) {
            return atom.cast==cast && sameAtom(*atom.key,key);
        });
        const auto index=static_cast<std::size_t>(it-atoms_.begin());
        if (it==atoms_.end()) atoms_.push_back({cast,&key});
        return Polynomial{{{index},1}};
    }

private:
    struct Atom { bool cast; const Node* key; };
    std::vector<Atom> atoms_;
    std::size_t operations_=0;
    static bool rational(const Node& value) { return value.is("c") && head(value)=="Rat"; }
};

inline std::optional<std::size_t> terms(const Node& equality, std::vector<const Node*>* indeterminates=nullptr) {
    if (!equality.is("a") || head(equality)!="Eq" || equality.children.size()!=5 ||
        !equality.at(2).is("c") || head(equality.at(2))!="Rat") return {};
    Normalizer normalizer;
    const auto lhs=normalizer.expand(equality.at(3)), rhs=normalizer.expand(equality.at(4));
    if (!lhs || !rhs || *lhs!=*rhs) return {};
    if (indeterminates) *indeterminates=normalizer.indeterminates();
    return lhs->size();
}

inline bool certificate(const Node& expression) {
    const auto& raw=term(expression);
    if (!expression.is("p") || expression.children.size()!=3) return false;
    if (raw.is("ringEquality"))
        return raw.children.size()==2 && raw.at(1).atom=="Mathlib.Tactic.Ring.of_eq";
    if (!raw.is("a") || raw.children.size()!=8 || head(raw)!="Mathlib.Tactic.Ring.of_eq") return false;
    const auto normalization=[](const Node& proof) {
        const auto rule=head(term(proof));
        if (!proof.is("p") || (rule!="Eq.refl" && rule.rfind("Mathlib.Tactic.Ring.",0)!=0)) return false;
        std::vector<const Node*> pending{&proof.at(2)};
        while (!pending.empty()) {
            const auto* current=pending.back();
            pending.pop_back();
            if (current->is("u")) return false;
            for (const auto& child:current->children) if (child.array) pending.push_back(&child);
        }
        return true;
    };
    const auto& equality=expression.at(1);
    const auto provesNormalization=[&](const Node& proof,const Node& operand) {
        if (!normalization(proof)) return false;
        const auto& type=proof.at(1);
        if (!type.is("a") || head(type)!="Eq" || type.children.size()!=5 ||
            !sameAtom(type.at(2),raw.at(2)) || !sameAtom(type.at(4),raw.at(5))) return false;
        if (sameAtom(type.at(3),operand)) return true;
        // The subproof may spell the ring operation via a superclass projection.
        Normalizer normalizer;
        const auto typed=normalizer.expand(type.at(3)), supplied=normalizer.expand(operand);
        return typed && supplied && *typed==*supplied;
    };
    return head(equality)=="Eq" && equality.children.size()==5 && sameAtom(equality.at(2),raw.at(2)) &&
        sameAtom(equality.at(3),raw.at(3)) && sameAtom(equality.at(4),raw.at(4)) &&
        provesNormalization(raw.at(6),raw.at(3)) && provesNormalization(raw.at(7),raw.at(4));
}

} // namespace proof::ring_equality
