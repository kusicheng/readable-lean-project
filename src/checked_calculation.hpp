#pragma once

#include "expressions.hpp"

namespace proof {

// Lean elaborates an equality calculation into a tree of Trans.trans calls.
// Keep the actual proof of each link so it can be narrated in its own scope.
inline std::vector<const Node*> calculationSteps(const Node& proof, const Node& conclusion) {
    if (head(conclusion) != "Eq" || term(conclusion).children.size() != 5) return {};
    std::vector<const Node*> steps;
    const auto flatten = [&](auto&& self, const Node& node) -> bool {
        const auto& raw = term(node);
        if (head(raw) != "Trans.trans" || raw.children.size() != 14 || head(raw.at(8)) != "instTransEq") {
            if (!node.is("p")) return false;
            const auto& type = term(node.at(1));
            if (head(type) != "Eq" || type.children.size() != 5) return false;
            steps.push_back(&node);
            return true;
        }
        // instTransEq has one shared middle term. Lean checked both links
        // against it, including any definitional reductions in a link's type.
        for (std::size_t i=5; i<=7; ++i)
            if (head(raw.at(i)) != "Eq") return false;
        return self(self,raw.at(12)) && self(self,raw.at(13));
    };
    if (!flatten(flatten,proof) || steps.size()<3) return {};
    return steps;
}

} // namespace proof
