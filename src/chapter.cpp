#include "chapter.hpp"
#include "expressions.hpp"

#include <fstream>
#include <set>
#include <stdexcept>

namespace proof {
namespace {

Node read(const std::filesystem::path& path) {
    std::ifstream input(path, std::ios::binary);
    if (!input) throw std::runtime_error("Cannot read chapter input " + path.string());
    return readJson(input);
}

const Node& member(const Node& node, const char* key) {
    const auto* found = node.lookup(key);
    if (!found) throw std::runtime_error(std::string("Missing chapter field ") + key);
    return *found;
}

std::string prose(const Node& node, const std::string& field) {
    if (!node.isString()) throw std::runtime_error("Expected text for " + field);
    for (unsigned char character : node.atom) {
        if (character < ' ' && character != '\r' && character != '\n' && character != '\t')
            throw std::runtime_error("Invalid text in " + field);
    }
    return node.atom;
}

std::string field(const Node& node, const std::string& key, bool required = false) {
    if (const auto* found = node.lookup(key)) {
        const auto text = prose(*found, key);
        if (!required || text.find_first_not_of(" \t\r\n") != std::string::npos) return text;
    }
    if (required) throw std::runtime_error("Missing or empty " + key);
    return {};
}

void fields(const Node& node, const std::set<std::string>& allowed) {
    if (!node.isObject) throw std::runtime_error("Expected a chapter object");
    for (const auto& entry : node.object) {
        if (allowed.count(entry.first) == 0)
            throw std::runtime_error("Unknown chapter field " + entry.first);
    }
}

Selection selection(const Node& node) {
    if (node.isString()) return {prose(node, "theorem"), {}};
    fields(node, {"theorem", "alternate"});
    return {field(node, "theorem", true), field(node, "alternate", true)};
}

Section section(const Node& node) {
    fields(node, {"title", "introduction", "theorems", "main"});
    Section result{field(node, "title", true), field(node, "introduction"), {},
                   field(node, "main")};
    const auto& theorems = member(node, "theorems");
    if (!theorems.array || theorems.children.empty())
        throw std::runtime_error("A section must list at least one theorem");
    for (const auto& entry : theorems.children)
        result.theorems.push_back(selection(entry));
    if (!result.main.empty() && result.main != result.theorems.back().theorem)
        throw std::runtime_error("The main result must be listed last in its section");
    return result;
}

void checkName(const std::string& name) {
    if (name.empty() || name.find_first_of(" \t\r\n=") != std::string::npos)
        throw std::runtime_error("Invalid theorem selection " + name);
}

} // namespace

std::string Selection::request() const {
    return alternate.empty() ? theorem : theorem + "=" + alternate;
}

Chapter readChapter(const std::filesystem::path& path) {
    const auto root = read(path);
    fields(root, {"title", "introduction", "terminology", "glossary", "sections"});
    Chapter chapter;
    chapter.title = field(root, "title", true);
    chapter.introduction = field(root, "introduction");
    if (const auto* terminology = root.lookup("terminology")) {
        fields(*terminology, {"witness", "induction_hypothesis"});
        if (terminology->lookup("witness"))
            chapter.terms.witness = field(*terminology, "witness", true);
        if (terminology->lookup("induction_hypothesis"))
            chapter.terms.inductionHypothesis = field(*terminology, "induction_hypothesis", true);
    }
    if (const auto* glossary = root.lookup("glossary")) {
        if (!glossary->array) throw std::runtime_error("Expected a glossary array");
        std::set<std::string> terms;
        for (const auto& entry : glossary->children) {
            fields(entry, {"term", "definition"});
            auto term = field(entry, "term", true);
            if (!terms.insert(term).second) throw std::runtime_error("Duplicate glossary term " + term);
            chapter.glossary.emplace_back(std::move(term), field(entry, "definition", true));
        }
    }
    const auto& sections = member(root, "sections");
    if (!sections.array || sections.children.empty())
        throw std::runtime_error("A chapter must list at least one section");
    std::set<std::string> names;
    for (const auto& entry : sections.children) {
        chapter.sections.push_back(entry.isString() ?
            section(read(path.parent_path() / prose(entry, "section file"))) : section(entry));
        const auto& current = chapter.sections.back();
        if (!current.main.empty() && chapter.sections.size() != sections.children.size())
            throw std::runtime_error("The main result must be in the final section");
        for (const auto& selected : current.theorems) {
            checkName(selected.theorem);
            if (!selected.alternate.empty()) checkName(selected.alternate);
            if (!names.insert(selected.theorem).second)
                throw std::runtime_error("Duplicate chapter theorem " + selected.theorem);
        }
    }
    return chapter;
}

std::string escapeLatex(const std::string& prose) {
    std::string escaped;
    for (const char character : prose) {
        switch (character) {
        case '\\': escaped += "\\textbackslash{}"; break;
        case '~': escaped += "\\textasciitilde{}"; break;
        case '^': escaped += "\\textasciicircum{}"; break;
        case '#': case '$': case '%': case '&': case '_': case '{': case '}':
            escaped += '\\';
            escaped += character;
            break;
        case '\r': break;
        default: escaped += character;
        }
    }
    return escaped;
}

} // namespace proof
