#pragma once

#include "expressions.hpp"
#include <algorithm>

namespace proof::paper_titles {

inline bool titleApplication(const Node& n, const char* name, std::size_t arity) {
    return n.is("a") && n.children.size()==arity+2 && head(n)==name;
}

inline bool titleVariable(const Node& n, const std::string& id) {
    return n.is("v") && n.at(1).atom==id;
}

inline bool finiteMembership(const Node& n) {
    return titleApplication(n,"Membership.mem",5) && titleApplication(n.at(4),"Finset.instMembership",1);
}

inline std::string neighborhoodTitle(const Node& claim) {
    const bool equality = titleApplication(claim,"Eq",3);
    if (!equality && !titleApplication(claim,"Iff",2)) return {};
    const auto& left = argument(claim,1);
    const auto* neighborhood = &left;
    const bool underlying = equality && titleApplication(left,"Finset.toSet",2);
    if (underlying) neighborhood = &argument(left,0);
    if (!equality) {
        if (!finiteMembership(left)) return {};
        neighborhood = &argument(left,1);
    }
    const bool incoming = titleApplication(*neighborhood,"Finset.bipartiteBelow",6);
    if (!incoming && !titleApplication(*neighborhood,"Finset.bipartiteAbove",6)) return {};
    if (!equality) return incoming ? "Membership in an incoming neighborhood" : "Membership in an outgoing neighborhood";
    if (underlying) return incoming ? "The underlying set of incoming neighbors" : "The underlying set of outgoing neighbors";
    if (titleApplication(neighborhood->at(4),"Function.swap",4))
        return incoming ? "Incoming neighbors after reversing the relation" : "Outgoing neighbors after reversing the relation";
    return {};
}

inline bool sameTitleVariable(const Node& a, const Node& b) {
    return a.is("v") && titleVariable(b,a.at(1).atom);
}

// Only identify two chosen relations when their complete exported terms
// match, including arguments already supplied to a relation constructor.
inline bool sameTitleTerm(const Node& a, const Node& b) {
    return a.array==b.array && a.atom==b.atom && a.children.size()==b.children.size() &&
           std::equal(a.children.begin(),a.children.end(),b.children.begin(),sameTitleTerm);
}

// Strip exactly "for each x in S" so bounds on a different set, or on a
// different element of the same type, cannot determine the heading.
inline const Node* claimOnSet(const Node& hypothesis, const Node& set) {
    if (!hypothesis.is("q") || !hypothesis.at(4).is("q")) return nullptr;
    const auto& membership = hypothesis.at(4).at(3);
    if (!finiteMembership(membership) || !sameTitleVariable(argument(membership,1),set) ||
        !titleVariable(argument(membership,0),hypothesis.at(1).atom)) return nullptr;
    return &hypothesis.at(4).at(4);
}

struct DegreeBound {
    const Node* relation;
    bool row, strict;
};

inline bool degreeComparison(const Node& expression, bool natural) {
    const bool strict = titleApplication(expression,"LT.lt",4);
    if (!strict && !titleApplication(expression,"LE.le",4)) return false;
    if (natural)
        return head(expression.at(2))=="Nat" && head(expression.at(3))==(strict ? "instLTNat" : "instLENat");
    return titleApplication(expression.at(3),strict ? "Preorder.toLT" : "Preorder.toLE",2);
}

inline std::optional<DegreeBound> degreeBound(const Node& statement, const Node& product,
                                              const Node& opposite, const Node& conclusion,
                                              bool lower, bool natural) {
    const auto& domain = argument(argument(product,1),0);
    for (const Node* q=&statement; q->is("q"); q=&q->at(4)) {
        const auto& hypothesis = q->at(3);
        const auto* claim = claimOnSet(hypothesis,domain);
        if (!claim || !degreeComparison(*claim,natural) ||
            !sameTitleVariable(argument(*claim,lower ? 1 : 0),argument(product,0))) continue;
        const Node* cardinality = &argument(*claim,lower ? 0 : 1);
        if (!natural) {
            // The hypotheses can install a second order or a second additive
            // structure on the very same scalar type.
            if (!sameTitleTerm(argument(claim->at(3),0),argument(conclusion.at(3),0))) continue;
            const auto& monoid = argument(argument(product.at(5),0),0);
            if (!titleApplication(*cardinality,"Nat.cast",3) ||
                !titleApplication(cardinality->at(3),"AddMonoidWithOne.toNatCast",2) ||
                !titleApplication(monoid,"AddMonoidWithOne.toAddMonoid",2) ||
                !sameTitleTerm(argument(cardinality->at(3),0),argument(monoid,0))) continue;
            cardinality = &argument(*cardinality,0);
        }
        if (!titleApplication(*cardinality,"Finset.card",2)) continue;
        const auto& neighbors = argument(*cardinality,0);
        const bool row = titleApplication(neighbors,"Finset.bipartiteAbove",6);
        if ((!row && !titleApplication(neighbors,"Finset.bipartiteBelow",6)) ||
            !sameTitleVariable(neighbors.at(5),opposite) || !titleVariable(neighbors.at(6),hypothesis.at(1).atom))
            continue;
        return DegreeBound{&neighbors.at(4),row,head(*claim)=="LT.lt"};
    }
    return {};
}

// Read the direction from the two incidence neighborhoods. Swapping the
// relation or the sides of its degree bounds changes which part is counted.
inline std::string incidenceBounds(const Node& statement, const Node& conclusion) {
    if (!titleApplication(conclusion,"LE.le",4) && !titleApplication(conclusion,"LT.lt",4)) return {};
    const auto& left = argument(conclusion,1);
    const auto& right = argument(conclusion,0);
    const bool natural = titleApplication(left,"HMul.hMul",6);
    if (!degreeComparison(conclusion,natural)) return {};
    for (const Node* product : {&left,&right}) {
        if (!titleApplication(*product,natural ? "HMul.hMul" : "HSMul.hSMul",6) ||
            !titleApplication(argument(*product,1),"Finset.card",2)) return {};
        const auto& instance = product->at(5);
        if (natural) {
            if (!titleApplication(instance,"instHMul",2) || head(argument(instance,0))!="instMulNat") return {};
        } else if (!titleApplication(instance,"instHSMul",3) ||
                   !titleApplication(argument(instance,0),"AddMonoid.toNatSMul",2)) return {};
    }
    const auto lower = degreeBound(statement,left,argument(argument(right,1),0),conclusion,true,natural);
    const auto upper = degreeBound(statement,right,argument(argument(left,1),0),conclusion,false,natural);
    if (!lower || !upper || !sameTitleTerm(*lower->relation,*upper->relation) || lower->row==upper->row ||
        (lower->strict && upper->strict) || (lower->strict || upper->strict)!=(head(conclusion)=="LT.lt")) return {};
    std::string title = " with a ";
    if (lower->strict || upper->strict) title += "strict ";
    else title += natural ? "natural-number " : "scalar ";
    title += upper->strict ? "upper bound on " : "lower bound on ";
    return title + ((upper->strict ? upper : lower)->row ? "row degrees" : "column degrees");
}

// Both a nonempty fiber and a subsingleton fiber use the same predicate:
// y is in the opposite set and r(x,y) (row), or r(y,x) (column).
struct IncidenceFiber {
    const Node* edge;
    bool row;
};

inline std::optional<IncidenceFiber> incidenceFiber(const Node& predicate, const Node& opposite,
                                                     const std::string& outer) {
    if (!predicate.is("l") || !titleApplication(predicate.at(4),"And",2)) return {};
    const auto& member = argument(predicate.at(4),1);
    const auto& edge = argument(predicate.at(4),0);
    if (!finiteMembership(member) || !sameTitleVariable(argument(member,1),opposite) ||
        !titleVariable(argument(member,0),predicate.at(1).atom) || !edge.is("a") ||
        edge.children.size()<4) return {};
    const auto& inner = predicate.at(1).atom;
    const bool row = titleVariable(argument(edge,1),outer) && titleVariable(argument(edge,0),inner);
    if (!row && !(titleVariable(argument(edge,1),inner) && titleVariable(argument(edge,0),outer))) return {};
    return IncidenceFiber{&edge,row};
}

inline std::string sparseFiberTitle(const Node& statement, const Node& conclusion) {
    if (!titleApplication(conclusion,"LE.le",4) || !degreeComparison(conclusion,true)) return {};
    const auto& left = argument(conclusion,1);
    const auto& right = argument(conclusion,0);
    if (!titleApplication(left,"Finset.card",2) || !titleApplication(right,"Finset.card",2)) return {};
    std::optional<IncidenceFiber> total, unique;
    for (const Node* q=&statement; q->is("q"); q=&q->at(4)) {
        const auto& h = q->at(3);
        const auto* exists = claimOnSet(h,argument(left,0));
        if (exists && titleApplication(*exists,"Exists",2))
            total = incidenceFiber(argument(*exists,0),argument(right,0),h.at(1).atom);
        const auto* sparse = claimOnSet(h,argument(right,0));
        if (sparse && titleApplication(*sparse,"Set.Subsingleton",2) && titleApplication(argument(*sparse,0),"setOf",2))
            unique = incidenceFiber(argument(argument(*sparse,0),0),argument(left,0),h.at(1).atom);
    }
    if (!total || !unique || total->row==unique->row) return {};
    const auto& a = total->edge->children;
    const auto& b = unique->edge->children;
    if (a.size()!=b.size() || !std::equal(a.begin()+1,a.end()-2,b.begin()+1,sameTitleTerm)) return {};
    return total->row ? "Bounding nonempty rows by columns of degree at most one" :
                        "Bounding nonempty columns by rows of degree at most one";
}

} // namespace proof::paper_titles
