#include "narration.hpp"

#include <charconv>
#include <fstream>
#include <iostream>
#include <optional>
#include <sstream>
#include <stdexcept>
#include <string>

int main(int argc, char* argv[]) {
    try {
        if (argc == 3 && std::string(argv[1]) == "--list-chapter") {
            const auto chapter = proof::readChapter(argv[2]);
            for (const auto& section : chapter.sections)
                for (const auto& theorem : section.theorems) std::cout << theorem.request() << '\n';
            return 0;
        }
        if (argc < 3 || argc % 2 == 0) {
            std::cerr << "Usage: lean-to-latex INPUT.json OUTPUT.tex [--threshold N] [--chapter FILE]\n"
                         "       lean-to-latex --list-chapter FILE\n";
            return 2;
        }
        std::size_t threshold = 5;
        std::optional<proof::Chapter> chapter;
        bool thresholdSpecified = false;
        for (int i = 3; i < argc; i += 2) {
            const std::string option = argv[i];
            if (option == "--threshold" && !thresholdSpecified) {
                thresholdSpecified = true;
                const std::string value = argv[i + 1];
                const auto parsed = std::from_chars(value.data(), value.data() + value.size(), threshold);
                if (parsed.ec != std::errc{} || parsed.ptr != value.data() + value.size())
                    throw std::runtime_error("The threshold must be a nonnegative integer");
            } else if (option == "--chapter" && !chapter) {
                chapter = proof::readChapter(argv[i + 1]);
            } else {
                throw std::runtime_error("Unknown or repeated option " + option);
            }
        }
        std::ifstream input(argv[1], std::ios::binary);
        if (!input) throw std::runtime_error("Cannot read the adapter input");
        const auto checked = proof::readJson(input);
        std::ostringstream document;
        const auto result = proof::writeDocument(checked, document, std::cerr, threshold,
                                                 chapter ? &*chapter : nullptr);
        // Binary mode keeps line endings identical on Windows and Unix.
        std::ofstream output(argv[2], std::ios::binary | std::ios::trunc);
        if (!output) throw std::runtime_error("Cannot open the LaTeX output");
        output << document.str();
        output.close();
        if (!output) throw std::runtime_error("Cannot write the LaTeX output");
        std::cerr << result.theorems - result.incomplete << '/' << result.theorems
                  << " proofs complete\n";
        if (result.alternates > 0)
            std::cerr << result.alternates << " separately checked alternate proofs selected\n";
        return result.incomplete == 0 ? 0 : 1;
    } catch (const std::exception& error) {
        std::cerr << error.what() << '\n';
        return 2;
    }
}
