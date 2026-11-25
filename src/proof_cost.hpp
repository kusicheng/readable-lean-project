#pragma once

#include "expressions.hpp"

#include <array>

namespace proof {

using ProofWeights = std::array<std::size_t,6>;
inline constexpr ProofWeights defaultProofWeights{1,1,2,1,4,3};
ProofWeights parseProofWeights(const std::string& text);

struct ProofCost {
    // In order: uses of hypotheses, other rule applications, rewrites,
    // bindings, branches, steps of an arithmetic certificate.
    std::array<std::size_t,6> counts{};
    ProofWeights weights = defaultProofWeights;
    bool available = true;
    bool compactAt(std::size_t budget) const { return !available || total()>budget; }
    std::size_t total() const;
    std::string describe() const;
};

ProofCost measureProof(const Node& proof, const Node* document = nullptr,
                       const ProofWeights& weights = defaultProofWeights);

} // namespace proof
