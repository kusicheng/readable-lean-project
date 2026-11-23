#pragma once

#include <iosfwd>
#include <map>
#include <optional>
#include <string>
#include <vector>

namespace proof {

struct Node {
    std::string atom;
    std::vector<Node> children;
    bool array = false;
    std::map<std::string, Node> object;
    bool isObject = false;

    const Node& at(std::size_t index) const;
    const Node* lookup(const std::string& key) const;
    bool is(const char* tag) const;
    bool isString() const { return !array && !isObject; }
};

Node readJson(std::istream& input);
const Node& term(const Node& node);
std::string head(const Node& node);
const Node& argument(const Node& node, std::size_t fromEnd);

enum class Kind { unsupported, nat, var, numeral, add, mul, equal, divides, exists, iff };

struct Math {
    Kind kind;
    std::string value;
    std::string hint;
    std::vector<Math> parts;

    explicit Math(Kind kind = Kind::unsupported, std::string value = {},
                  std::string hint = {}, std::vector<Math> parts = {});
    bool supported() const;
    bool proposition() const;
    std::size_t complexity() const;
};

using Substitution = std::map<std::string, Math>;
using Names = std::map<std::string, std::string>;

Math math(const Node& expression, const Substitution& substitutions = {});
Math applyPredicate(const Node& predicate, const Math& argument,
                    const Substitution& substitutions = {});
bool match(const Math& pattern, const Math& target, Substitution& parameters);
bool same(const Math& left, const Math& right);

std::string bindName(Names& names, const std::string& id, const std::string& hint);
std::string latex(const Math& expression, const Names& names);

struct Parameter {
    std::string id;
    std::string hint;
    Math type;
};

struct Statement {
    std::vector<Parameter> parameters;
    Math conclusion;

    bool supported() const;
};

Statement statement(const Node& expression);

} // namespace proof
