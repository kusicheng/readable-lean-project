#pragma once

#include "expressions.hpp"
#include "chapter.hpp"

#include <set>

namespace proof {

// A proof succeeds only when each proof argument of every used rule is
// accounted for. Failed attempts do not register any imported premises.
std::optional<std::string> generalProof(const Node& record, const Node& input,
    const std::map<std::string, std::string>& earlierReferences,
    const DefinitionRules& definitions, std::set<std::string>& externalPremises,
    bool compact = true, std::string* failure = nullptr);

} // namespace proof
