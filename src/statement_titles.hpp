#pragma once

#include "incidence_titles.hpp"

namespace proof::paper_titles {

inline bool naturalNumber(const Node& value, const char* digit) {
    return titleApplication(value,"OfNat.ofNat",3) && head(value.at(2))=="Nat" &&
           value.at(3).is("n") && value.at(3).at(1).atom==digit &&
           titleApplication(value.at(4),"instOfNatNat",1) && sameTitleTerm(value.at(3),value.at(4).at(2));
}

inline bool naturalOperation(const Node& value, const char* operation, const char* bridge, const char* instance) {
    return titleApplication(value,operation,6) && head(value.at(2))=="Nat" &&
           head(value.at(3))=="Nat" && head(value.at(4))=="Nat" &&
           titleApplication(value.at(5),bridge,2) && head(value.at(5).at(2))=="Nat" &&
           value.at(5).at(3).is("c") && head(value.at(5).at(3))==instance;
}

inline std::string enumerationTitle(const Node& left, const Node& right) {
    if (titleApplication(left,"catalan",1) && naturalOperation(right,"HDiv.hDiv","instHDiv","Nat.instDiv")) {
        const auto& numerator = argument(right,1);
        const auto& divisor = argument(right,0);
        if (titleApplication(numerator,"Nat.centralBinom",1) && naturalOperation(divisor,"HAdd.hAdd","instHAdd","instAddNat") &&
            sameTitleVariable(argument(left,0),argument(numerator,0)) && sameTitleVariable(argument(left,0),argument(divisor,1)) &&
            naturalNumber(argument(divisor,0),"1"))
            return "The central binomial formula for Catalan numbers";
    }
    if (titleApplication(left,"Finset.card",2) && titleApplication(argument(left,0),"Tree.treesOfNumNodesEq",1) &&
        titleApplication(right,"catalan",1) && sameTitleTerm(argument(argument(left,0),0),argument(right,0)))
        return "The Catalan count for binary trees with a fixed number of nodes";
    if (titleApplication(left,"DyckWord.semilength",1) && titleApplication(right,"Tree.numNodes",2)) {
        const auto& image = argument(right,0);
        if (titleApplication(image,"DFunLike.coe",6) && argument(image,1).is("c") &&
            head(argument(image,1))=="DyckWord.equivTree" && sameTitleVariable(argument(image,0),argument(left,0)))
            return "Semilength equals the node count of the corresponding tree";
    }
    if (titleApplication(left,"Fintype.card",2) && titleApplication(right,"catalan",1)) {
        const auto& subtype = left.at(2);
        if (!titleApplication(subtype,"Subtype",2) || head(subtype.at(2))!="DyckWord") return {};
        const auto& condition = argument(subtype,0);
        if (!condition.is("l") || !titleApplication(condition.at(4),"Eq",3)) return {};
        const auto& measure = argument(condition.at(4),1);
        if (titleApplication(measure,"DyckWord.semilength",1) && titleVariable(argument(measure,0),condition.at(1).atom) &&
            sameTitleTerm(argument(condition.at(4),0),argument(right,0)))
            return "The Catalan count for Dyck words of fixed semilength";
    }
    return {};
}

inline std::string matchingCharacterization(const Node& claim) {
    if (!titleApplication(claim,"Iff",2)) return {};
    const auto& property = argument(claim,1);
    const auto& all = argument(claim,0);
    if (!titleApplication(property,"SimpleGraph.Subgraph.IsMatching",3) || !all.is("q") ||
        !all.at(4).is("q") || !sameTitleTerm(all.at(3),property.at(2))) return {};
    const auto& member = all.at(4).at(3);
    const auto& conclusion = all.at(4).at(4);
    if (!titleApplication(member,"Membership.mem",5) || !titleApplication(member.at(4),"Set.instMembership",1) ||
        !titleVariable(argument(member,0),all.at(1).atom) || !titleApplication(conclusion,"Eq",3) ||
        !naturalNumber(argument(conclusion,0),"1")) return {};
    const auto& vertices = argument(member,1);
    const auto& degree = argument(conclusion,1);
    if (titleApplication(vertices,"SimpleGraph.Subgraph.verts",3) &&
        titleApplication(degree,"SimpleGraph.Subgraph.degree",5) &&
        sameTitleTerm(vertices.at(4),property.at(4)) && sameTitleTerm(degree.at(4),property.at(4)) &&
        titleVariable(degree.at(5),all.at(1).atom))
        return "The degree-one characterization of a matching";
    return {};
}

// The same rule handles arbitrary named sequences exported with a checked
// signature Nat -> Nat -> Nat. Parameter positions come from the equation.
inline std::string sequenceTitle(const Node& equality) {
    const auto& lhs = argument(equality,1);
    const auto& rhs = argument(equality,0);
    if (head(equality.at(2))!="Nat") return {};
    const bool uniform = titleApplication(lhs,"Nat.uniformBell",2);
    const bool multiset = titleApplication(lhs,"Multiset.bell",1);
    if ((uniform || multiset || !lhs.mathSymbol.empty()) &&
        naturalOperation(rhs,"HDiv.hDiv","instHDiv","Nat.instDiv") && head(argument(rhs,1))=="Nat.factorial")
        return uniform ? "Factorial quotient for uniform Bell numbers" :
               multiset ? "Factorial quotient for prescribed block sizes" : "A factorial quotient";
    if (naturalOperation(lhs,"HMul.hMul","instHMul","instMulNat") && titleApplication(rhs,"Nat.factorial",1)) {
        const auto& product = argument(lhs,1);
        if (naturalOperation(product,"HMul.hMul","instHMul","instMulNat")) {
            const auto& factor = argument(product,1);
            if (titleApplication(factor,"Nat.uniformBell",2)) return "Factorial product for uniform Bell numbers";
            if (titleApplication(factor,"Multiset.bell",1)) return "Factorial product for prescribed block sizes";
        }
    }
    if (!lhs.is("a") || lhs.children.size()!=4 || (!uniform && lhs.mathSymbol.empty())) return {};
    const auto& first = lhs.at(2);
    const auto& second = lhs.at(3);
    if (naturalNumber(rhs,"1")) {
        if (naturalNumber(first,"0")) return uniform ? "The value for zero blocks" : "Value at zero in the first parameter";
        if (naturalNumber(second,"0")) return uniform ? "The value for blocks of size zero" : "Value at zero in the second parameter";
        if (naturalNumber(first,"1")) return uniform ? "The value for one block" : "Value at one in the first parameter";
        if (naturalNumber(second,"1")) return uniform ? "The value for singleton blocks" : "Value at one in the second parameter";
    }
    if (titleApplication(rhs,"Finset.prod",5) && titleApplication(argument(rhs,1),"Finset.range",1))
        return uniform ? "Product formula for uniform Bell numbers" : "A finite product formula";
    if (!naturalOperation(rhs,"HMul.hMul","instHMul","instMulNat")) return {};
    for (const std::size_t side : {0u,1u}) {
        const auto& previous = argument(rhs,side);
        if (!previous.is("a") || previous.children.size()!=4 || !sameTitleTerm(lhs.at(1),previous.at(1))) continue;
        for (const std::size_t i : {0u,1u}) {
            const auto& next = argument(lhs,i);
            if (!sameTitleTerm(argument(lhs,1-i),argument(previous,1-i)) ||
                !naturalOperation(next,"HAdd.hAdd","instHAdd","instAddNat") || !naturalNumber(argument(next,0),"1") ||
                !sameTitleTerm(argument(next,1),argument(previous,i))) continue;
            if (uniform && i==1) return "Recurrence for one additional block";
            return i==1 ? "A multiplicative recurrence in the first parameter" : "A multiplicative recurrence in the second parameter";
        }
    }
    return {};
}

inline std::vector<const Node*> proofPremises(const Node& statement) {
    std::vector<const Node*> premises;
    for (const Node* binder = &statement; binder->is("q"); binder = &binder->at(4)) {
        if (binder->children.size() > 6 && binder->at(6).atom == "proof")
            premises.push_back(&binder->at(3));
    }
    return premises;
}

// Identify the same subgraph throughout, including its ambient graph and
// vertex type. A matching hypothesis about another graph cannot name this one.
inline bool matchingPremise(const std::vector<const Node*>& premises, const Node& vertices,
                            const Node& graph, const Node* subgraph, bool perfect) {
    const char* property = perfect ? "SimpleGraph.Subgraph.IsPerfectMatching" : "SimpleGraph.Subgraph.IsMatching";
    return std::any_of(premises.begin(),premises.end(),[&](const Node* premise) {
        return titleApplication(*premise,property,3) && sameTitleTerm(premise->at(2),vertices) &&
               sameTitleTerm(premise->at(3),graph) && (!subgraph || sameTitleTerm(premise->at(4),*subgraph));
    });
}

inline std::string uniquenessTitle(const Node& statement, const Node& equality) {
    const auto& lhs = argument(equality,1);
    const auto& rhs = argument(equality,0);
    if (!lhs.is("v") || !rhs.is("v") || sameTitleVariable(lhs,rhs)) return {};
    const auto premises = proofPremises(statement);
    for (const Node* first : premises) {
        if (!first->is("a") || first->children.size() < 4) continue;
        for (const Node* second : premises) {
            if (!second->is("a") || second->children.size() != first->children.size()) continue;
            // Include the relation, any implicit parameters and the chosen instance.
            if (!std::equal(first->children.begin()+1,first->children.end()-2,
                            second->children.begin()+1,sameTitleTerm)) continue;
            for (const std::size_t varying : {0u,1u}) {
                const auto& fixed = argument(*first,1-varying);
                if (!sameTitleVariable(fixed,argument(*second,1-varying)) ||
                    sameTitleVariable(fixed,lhs) || sameTitleVariable(fixed,rhs) ||
                    !sameTitleVariable(argument(*first,varying),lhs) ||
                    !sameTitleVariable(argument(*second,varying),rhs)) continue;
                if (titleApplication(*first,"SimpleGraph.Subgraph.Adj",5) &&
                    matchingPremise(premises,first->at(2),first->at(3),&first->at(4),false))
                    return varying == 0 ? "Matching edges with the same first endpoint have the same second endpoint" :
                                          "Matching edges with the same second endpoint have the same first endpoint";
                return varying == 0 ? "Uniqueness of the second coordinate for a fixed first coordinate" :
                                      "Uniqueness of the first coordinate for a fixed second coordinate";
            }
        }
    }
    return {};
}

inline std::string parityTitle(const Node& statement, const Node& conclusion) {
    if (!titleApplication(conclusion,"Even",3) || head(conclusion.at(2)) != "Nat" ||
        head(conclusion.at(3)) != "instAddNat") return {};
    const auto& count = argument(conclusion,0);
    const auto premises = proofPremises(statement);
    if (titleApplication(count,"Finset.card",2)) {
        const auto& set = argument(count,0);
        if (!titleApplication(set,"Set.toFinset",3)) return {};
        const auto& vertices = set.at(3);
        if (titleApplication(vertices,"SimpleGraph.Subgraph.verts",3) &&
            matchingPremise(premises,vertices.at(2),vertices.at(3),&vertices.at(4),false))
            return "A matching covers an even number of vertices";
    }
    if (titleApplication(count,"Fintype.card",2)) {
        const auto& carrier = count.at(2);
        if (titleApplication(carrier,"Set.Elem",2)) {
            const auto& component = carrier.at(3);
            if (titleApplication(component,"SimpleGraph.ConnectedComponent.supp",3) &&
                matchingPremise(premises,component.at(2),component.at(3),nullptr,true))
                return "Each connected component of a graph with a perfect matching has even order";
        }
        for (const Node* premise : premises) {
            if (titleApplication(*premise,"SimpleGraph.Subgraph.IsPerfectMatching",3) &&
                sameTitleTerm(carrier,premise->at(2)))
                return "A graph with a perfect matching has an even number of vertices";
        }
    }
    return {};
}

// Read an existential binder and its membership requirement together.
inline const Node* naturalWitnessInSet(const Node& exists, const Node*& set, std::string& witness) {
    if (!titleApplication(exists,"Exists",2) || head(exists.at(2)) != "Nat") return nullptr;
    const auto& predicate = argument(exists,0);
    if (!predicate.is("l") || !titleApplication(predicate.at(4),"And",2)) return nullptr;
    const auto& membership = argument(predicate.at(4),1);
    witness = predicate.at(1).atom;
    if (!titleApplication(membership,"Membership.mem",5) ||
        !titleApplication(membership.at(4),"Set.instMembership",1) ||
        !titleVariable(argument(membership,0),witness)) return nullptr;
    set = &argument(membership,1);
    return &argument(predicate.at(4),0);
}

inline std::string congruentPairTitle(const Node& exists) {
    const Node *firstSet = nullptr, *secondSet = nullptr;
    std::string first, second;
    const auto* inner = naturalWitnessInSet(exists,firstSet,first);
    if (!inner) return {};
    const auto* conditions = naturalWitnessInSet(*inner,secondSet,second);
    if (!conditions || !sameTitleTerm(*firstSet,*secondSet) || !titleApplication(*conditions,"And",2)) return {};
    const auto& less = argument(*conditions,1);
    const auto& congruent = argument(*conditions,0);
    if (titleApplication(less,"LT.lt",4) && head(less.at(3)) == "instLTNat" &&
        titleVariable(argument(less,1),first) && titleVariable(argument(less,0),second) &&
        titleApplication(congruent,"Nat.ModEq",3) && titleVariable(argument(congruent,1),first) &&
        titleVariable(argument(congruent,0),second))
        return "Two distinct elements of a set in the same residue class";
    return {};
}

} // namespace proof::paper_titles
