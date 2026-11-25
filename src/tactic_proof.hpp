#pragma once

#include "expressions.hpp"
#include "proof_cost.hpp"

#include <set>

namespace proof {

std::optional<std::string> tacticProof(const Node& record, const Node& input,
    const std::map<std::string, std::string>& earlierReferences,
    std::set<std::string>& externalPremises, bool compact,
    std::size_t budget, const ProofWeights& weights, std::string* arithmeticCosts = nullptr);

} // namespace proof
