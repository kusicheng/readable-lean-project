#pragma once

#include "expressions.hpp"

#include <iosfwd>

namespace proof {

struct Result {
    std::size_t theorems = 0;
    std::size_t incomplete = 0;
};

Result writeDocument(const Node& input, std::ostream& output, std::ostream& diagnostics,
                     std::size_t threshold);

} // namespace proof
