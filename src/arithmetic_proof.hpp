#pragma once

#include "expressions.hpp"

namespace proof {

// Explain the certificate assigned to a closed arithmetic tactic goal.
// Unsupported certificate forms leave the caller's proof incomplete.
std::optional<std::string> arithmeticProof(const Node& goal, const Names& names,
                                          const Node& step, const Node& document,
                                          bool compact);

} // namespace proof
