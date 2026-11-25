#include "narration.hpp"

#include <charconv>
#include <fstream>
#include <iostream>
#include <optional>
#include <sstream>
#include <stdexcept>
#include <string>

namespace {
constexpr char usage[] =
    "Usage: lean-to-latex INPUT.json OUTPUT.tex [--chapter FILE | --paper TITLE]\n"
    "       lean-to-latex --list-chapter FILE\n"
    "       lean-to-latex --help\n"
    "\n"
    "  --paper TITLE        Create an article from the checked declarations.\n"
    "  --chapter FILE       Use the sections and selections in a JSON layout.\n"
    "  --list-chapter FILE  Print the declarations selected by a layout.\n"
    "  --threshold N        Set the display threshold for a formula (default 5).\n"
    "  --proof-budget N     Set the detail budget in paper mode (default 24).\n"
    "  --proof-weights KEY=N,...  Override weights for hypothesis, application,\n"
    "                             rewrite, binding, branch, or certificate.\n";
}

int main(int argc, char* argv[]) {
    try {
        if (argc == 2 && (std::string(argv[1]) == "--help" || std::string(argv[1]) == "-h")) {
            std::cout << usage;
            return 0;
        }
        if (argc == 3 && std::string(argv[1]) == "--list-chapter") {
            const auto chapter = proof::readChapter(argv[2]);
            for (const auto& section : chapter.sections)
                for (const auto& theorem : section.theorems) std::cout << theorem.request() << '\n';
            return 0;
        }
        if (argc < 3 || argc % 2 == 0) {
            std::cerr << usage;
            return 2;
        }
        std::size_t threshold = 5;
        std::optional<proof::Chapter> chapter;
        std::optional<std::string> paperTitle;
        std::optional<std::size_t> proofBudget;
        std::optional<proof::ProofWeights> proofWeights;
        bool thresholdSpecified = false;
        for (int i = 3; i < argc; i += 2) {
            const std::string option = argv[i];
            if ((option == "--threshold" && !thresholdSpecified) ||
                (option == "--proof-budget" && !proofBudget)) {
                const std::string value = argv[i + 1];
                std::size_t n;
                const auto parsed = std::from_chars(value.data(), value.data() + value.size(), n);
                if (parsed.ec != std::errc{} || parsed.ptr != value.data() + value.size())
                    throw std::runtime_error(option + " must be a nonnegative integer");
                if (option == "--threshold") { threshold = n; thresholdSpecified = true; }
                else proofBudget = n;
            } else if (option == "--proof-weights" && !proofWeights) {
                proofWeights = proof::parseProofWeights(argv[i+1]);
            } else if (option == "--chapter" && !chapter && !paperTitle) {
                chapter = proof::readChapter(argv[i + 1]);
            } else if (option == "--paper" && !chapter && !paperTitle) {
                paperTitle = argv[i + 1];
            } else {
                throw std::runtime_error("Unknown or repeated option " + option);
            }
        }
        std::ifstream input(argv[1], std::ios::binary);
        if (!input) throw std::runtime_error("Cannot read the adapter input");
        auto checked = proof::readJson(input);
        if (paperTitle) chapter = proof::automaticPaper(checked, *paperTitle);
        if (proofBudget || proofWeights) {
            if (!chapter || !chapter->paper) throw std::runtime_error("Proof detail controls require a paper");
            if (proofBudget) chapter->proofBudget = *proofBudget;
            if (proofWeights) chapter->proofWeights = *proofWeights;
        }
        if (chapter) {
            if (chapter->paper) proof::prepareCheckedNames(checked);
            proof::applyChapterSymbols(checked, *chapter);
            proof::preparePaper(*chapter, checked);
        }
        std::ostringstream document;
        const auto result = proof::writeDocument(checked, document, std::cerr, threshold,
                                                 chapter ? &*chapter : nullptr);
        // Binary mode keeps line endings identical on Windows and Unix.
        std::ofstream output(argv[2], std::ios::binary | std::ios::trunc);
        if (!output) throw std::runtime_error("Cannot open the LaTeX output");
        output << (chapter && chapter->paper ? proof::wrapPaperMath(document.str()) : document.str());
        output.close();
        if (!output) throw std::runtime_error("Cannot write the LaTeX output");
        std::cerr << result.theorems - result.incomplete << '/' << result.theorems
                  << " proofs complete\n";
        if (result.alternates > 0)
            std::cerr << result.alternates << " separately checked alternate proofs selected\n";
        if (result.incompleteDefinitions)
            std::cerr << result.incompleteDefinitions << " definitions have unrendered equations\n";
        return result.incomplete == 0 && !result.incompleteDefinitions ? 0 : 1;
    } catch (const std::exception& error) {
        std::cerr << error.what() << '\n';
        return 2;
    }
}
