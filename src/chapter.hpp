#pragma once

#include "proof_cost.hpp"
#include <filesystem>
#include <iosfwd>
#include <map>
#include <string>
#include <utility>
#include <vector>

namespace proof {

struct Node;

struct DefiningEquation {
    const Node* type;
    std::string reference;
};
using DefinitionRules = std::map<std::string,DefiningEquation>;

struct Selection {
    std::string theorem;
    std::string alternate;
    std::string role;
    std::string title;
    std::string request() const;
};

struct Section {
    std::string title;
    std::string introduction;
    std::vector<Selection> theorems;
    std::string main;
    std::vector<std::string> sourceHeadings{};
};

struct Terms {
    std::string witness = "witness";
    std::string inductionHypothesis = "induction hypothesis";
};

struct Chapter {
    std::string title;
    std::string introduction;
    bool paper = false;
    std::size_t proofBudget = 24;
    ProofWeights proofWeights = defaultProofWeights;
    Terms terms;
    std::map<std::string, std::string> symbols;
    std::map<std::string, std::string> prerequisiteTitles;
    std::vector<std::pair<std::string, std::string>> glossary;
    std::vector<Section> sections;
    bool automaticLayout = false;
};

Chapter readChapter(const std::filesystem::path& path);
std::string selectedAlternate(const Node& record);
std::vector<const Node*> orderTheorems(const Node& document, const Chapter* chapter);
Chapter automaticPaper(const Node& checked, const std::string& title);
void writeSectionHeading(std::ostream& out, const Section& section, const Section* previous);
void preparePaper(Chapter& chapter, const Node& checked);
std::size_t writePaperDefinitions(std::ostream& output, const Node& checked, const Chapter& chapter,
                                  DefinitionRules& rules);
std::string declarationTitle(const std::string& name);
std::string prerequisiteLabel(const std::string& name);
std::string documentedTitle(const std::string& doc);
std::string prerequisiteReference(const Node& libraryEntry);
std::string wrapPaperMath(std::string text);
bool containsConstant(const Node& expression, const std::string& symbol);
void applyChapterSymbols(Node& checked, const Chapter& chapter);
std::string escapeLatex(const std::string& prose);

} // namespace proof
