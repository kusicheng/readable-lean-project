#pragma once

#include "chapter.hpp"
#include "expressions.hpp"

#include <iosfwd>

namespace proof {

struct Result {
    std::size_t theorems = 0;
    std::size_t incomplete = 0;
    std::size_t incompleteDefinitions = 0;
    std::size_t alternates = 0;
};

Result writeDocument(const Node& input, std::ostream& output, std::ostream& diagnostics,
                     std::size_t threshold, const Chapter* chapter = nullptr);

} // namespace proof
