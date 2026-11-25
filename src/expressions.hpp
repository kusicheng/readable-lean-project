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
    std::string mathSymbol{};
    std::string checkedName{};

    const Node& at(std::size_t index) const;
    const Node* lookup(const std::string& key) const;
    bool is(const char* tag) const;
    bool isString() const { return !array && !isObject; }
};

Node readJson(std::istream& input);
const Node& term(const Node& node);
std::string head(const Node& node);
const Node& argument(const Node& node, std::size_t fromEnd);
bool proofArguments(const Node& application, std::vector<const Node*>& proofs);
std::string withSuperscript(std::string base, const std::string& exponent);

enum class Kind { unsupported, nat, var, numeral, function, add, mul, power, equal,
                  le, lt, divides, exists, conjunction, iff };

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

// Mathematical presentation of a checked expression. Failure is explicit when
// the expression contains a metavariable, internal term or unknown free binder.
std::optional<std::string> checkedFormula(const Node& expression, const Names& names = {});
// Check the instance argument of Inv.inv, or an entire OfNat zero expression.
bool isStandardRationalInverse(const Node& instance, const std::string& carrier);
bool isStandardRationalZero(const Node& expression, const std::string& carrier);
bool isStandardRationalNumeral(const Node& expression, const std::string& carrier);
bool isStandardRationalOrder(const Node& expression, const std::string& carrier);
std::optional<std::string> describeCheckedStatement(const Node& type);
std::optional<std::string> describeCheckedDefinition(const std::string& fullName,
                                                      const Node& type, const Node& value);
std::string checkedBinderName(Names& names, const std::string& id, const std::string& hint);
// Remember which additive structure governs an unqualified repeated sum on this carrier.
void bindCheckedAddition(Names& names, const Node& binder, const std::string& symbol);
void prepareCheckedNames(Node& document);

} // namespace proof
