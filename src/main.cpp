#include "narration.hpp"

#include <charconv>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <string>

int main(int argc, char* argv[]) {
    try {
        std::size_t threshold = 5;
        if (argc == 5 && std::string(argv[3]) == "--threshold") {
            const std::string value = argv[4];
            const auto parsed = std::from_chars(value.data(), value.data() + value.size(), threshold);
            if (parsed.ec != std::errc{} || parsed.ptr != value.data() + value.size())
                throw std::runtime_error("The threshold must be a nonnegative integer");
        } else if (argc != 3) {
            std::cerr << "Usage: lean-to-latex INPUT.json OUTPUT.tex [--threshold N]\n";
            return 2;
        }
        std::ifstream input(argv[1], std::ios::binary);
        if (!input) throw std::runtime_error("Cannot read the adapter input");
        const auto checked = proof::readJson(input);
        // Binary mode keeps line endings identical on Windows and Unix.
        std::ofstream output(argv[2], std::ios::binary | std::ios::trunc);
        if (!output) throw std::runtime_error("Cannot open the LaTeX output");
        const auto result = proof::writeDocument(checked, output, std::cerr, threshold);
        output.close();
        if (!output) throw std::runtime_error("Cannot write the LaTeX output");
        std::cerr << result.theorems - result.incomplete << '/' << result.theorems
                  << " proofs complete\n";
        return result.incomplete == 0 ? 0 : 1;
    } catch (const std::exception& error) {
        std::cerr << error.what() << '\n';
        return 2;
    }
}
