#pragma once

#include <filesystem>
#include <string>
#include <utility>
#include <vector>

namespace proof {

struct Selection {
    std::string theorem;
    std::string alternate;
    std::string request() const;
};

struct Section {
    std::string title;
    std::string introduction;
    std::vector<Selection> theorems;
    std::string main;
};

struct Terms {
    std::string witness = "witness";
    std::string inductionHypothesis = "induction hypothesis";
};

struct Chapter {
    std::string title;
    std::string introduction;
    Terms terms;
    std::vector<std::pair<std::string, std::string>> glossary;
    std::vector<Section> sections;
};

Chapter readChapter(const std::filesystem::path& path);
std::string escapeLatex(const std::string& prose);

} // namespace proof
