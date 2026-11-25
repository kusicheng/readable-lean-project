#pragma once

#include "expressions.hpp"
#include <map>

namespace proof::record_equality {

using Locals = std::map<std::string, const Node*>;
using Equal = bool (*)(const Node&, const Node&);

struct Field {
    std::string projection;
    const Node* left;
    const Node* right;
};

inline bool call(const Node& n, const char* name, std::size_t args) {
    return n.is("a") && head(n)==name && n.children.size()==args+2;
}

inline const Node* localType(const Node& value, const Locals& locals) {
    if (!value.is("v")) return nullptr;
    const auto found = locals.find(value.at(1).atom);
    return found==locals.end() ? nullptr : found->second;
}

inline const Node& bind(const Node& branch, Locals& locals) {
    const Node* body = &branch;
    while (term(*body).is("l")) {
        const auto& binder = term(*body);
        locals[binder.at(1).atom] = &binder.at(3);
        body = &binder.at(4);
    }
    return *body;
}

// The structure extensionality tactic eliminates each projected equality,
// transports the remaining fields, and finishes with the constructor equal
// to itself. Check the eliminators and their supplied evidence in this order.
template<class CheckCase, class CheckArguments>
bool transports(const Node& body, const std::vector<Field>& data, const Node& type,
                const Node& leftRecord, Locals locals, Equal same,
                CheckCase checkCase, CheckArguments checkArguments) {
    const Node* evidence = &body;
    for (const auto& field : data) {
        const Node* step = &term(*evidence);
        if (!call(*step,"Eq.casesOn",8) || !evidence->is("p") || !checkCase(*step,evidence->at(1))) return false;
        const auto& left = step->at(3);
        const auto& right = step->at(5);
        const auto& major = step->at(6);
        const auto* equality = localType(major,locals);
        if (!equality || !call(*equality,"Eq",3) || !same(equality->at(2),step->at(2)) ||
            !same(equality->at(3),left) || !same(equality->at(4),right) ||
            head(left)!=field.projection || head(right)!=field.projection ||
            !same(argument(left,0),leftRecord)) return false;
        const auto& refl = term(step->at(8));
        const auto& hrefl = term(step->at(9));
        if (!call(refl,"Eq.refl",2) || !same(refl.at(2),equality->at(2)) || !same(refl.at(3),right) ||
            !call(hrefl,"HEq.refl",2) || !same(hrefl.at(2),*equality) || !same(hrefl.at(3),major)) return false;

        const auto& reverse = term(step->at(7));
        if (!reverse.is("l") || !call(reverse.at(3),"Eq",3) || !same(reverse.at(3).at(3),right) ||
            !same(reverse.at(3).at(4),left)) return false;
        const auto& transfer = term(reverse.at(4));
        if (!transfer.is("a") || head(transfer)!="Eq.ndrec" || transfer.children.size()<8 ||
            !same(transfer.at(2),step->at(2)) || !same(transfer.at(3),*field.left) ||
            !same(transfer.at(6),*field.right) || !term(transfer.at(4)).is("l")) return false;
        const auto& symmetry = term(transfer.at(7));
        if (!call(symmetry,"Eq.symm",4) || !same(symmetry.at(2),transfer.at(2)) ||
            !same(symmetry.at(3),*field.right) || !same(symmetry.at(4),*field.left) ||
            !symmetry.at(5).is("v") || symmetry.at(5).at(1).atom!=reverse.at(1).atom) return false;

        // Arguments after the transport are the still-local fields and
        // equalities. A missing witness may never disappear in a summary.
        if (!reverse.at(4).is("p") || !checkArguments(transfer,reverse.at(4).at(1),locals)) return false;
        evidence = &bind(transfer.at(5),locals);
    }
    const auto& refl = term(*evidence);
    return call(refl,"Eq.refl",2) && same(refl.at(2),type) && same(refl.at(3),leftRecord);
}

} // namespace proof::record_equality
