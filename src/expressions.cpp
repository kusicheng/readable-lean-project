#include "expressions.hpp"

#include <algorithm>
#include <charconv>
#include <istream>
#include <iterator>
#include <stdexcept>
#include <utility>

namespace proof {
bool proofArguments(const Node& raw, std::vector<const Node*>& proofs) {
    if (raw.is("c") || raw.is("v")) return true;
    if (!raw.is("a")) return false;
    const auto& fn = raw.at(1);
    if (fn.children.size() < 5 || !fn.at(4).array) return false;
    for (const auto& slot : fn.at(4).children) {
        std::size_t i = 0;
        const auto end = slot.atom.data() + slot.atom.size();
        const auto parsed = std::from_chars(slot.atom.data(), end, i);
        if (parsed.ec != std::errc{} || parsed.ptr != end || i >= raw.children.size()-2)
            return false;
        proofs.push_back(&raw.at(i+2));
    }
    return true;
}

std::string withSuperscript(std::string base, const std::string& exponent) {
    // TeX needs a new atom for an additional superscript on a primed symbol.
    if (base.find('^') != std::string::npos) base = "{" + base + "}";
    return base + "^{" + exponent + "}";
}
std::string functionSymbol(const std::string& label) {
    if (label.size()==1) return label;
    std::string words;
    for (std::size_t i=0; i<label.size(); ++i) {
        if (i && label[i-1]>='a' && label[i-1]<='z' && label[i]>='A' && label[i]<='Z') words += "\\,";
        words += label[i];
    }
    return "\\operatorname{" + words + "}";
}

namespace {

class Parser {
public:
    explicit Parser(std::istream& input)
        : source_(std::istreambuf_iterator<char>(input), {}) {}

    Node parse() {
        Node result = value();
        space();
        if (pos_ != source_.size()) invalid();
        return result;
    }

private:
    std::string source_;
    std::size_t pos_ = 0;

    [[noreturn]] void invalid() const {
        throw std::runtime_error("Invalid adapter JSON at byte " + std::to_string(pos_));
    }

    void space() {
        while (pos_ < source_.size() &&
               std::string(" \n\r\t").find(source_[pos_]) != std::string::npos) ++pos_;
    }

    bool take(char character) {
        if (pos_ == source_.size() || source_[pos_] != character) return false;
        ++pos_;
        return true;
    }

    Node value() {
        space();
        if (take('"')) return {quoted(), {}, false, {}, false};
        if (take('{')) return object();
        if (!take('[')) invalid();
        Node result{{}, {}, true, {}, false};
        space();
        if (take(']')) return result;
        do {
            result.children.push_back(value());
            space();
        } while (take(','));
        if (!take(']')) invalid();
        return result;
    }

    Node object() {
        Node result{{}, {}, false, {}, true};
        space();
        if (take('}')) return result;
        do {
            space();
            if (!take('"')) invalid();
            const auto key = quoted();
            space();
            if (!take(':')) invalid();
            if (!result.object.emplace(key, value()).second) invalid();
            space();
        } while (take(','));
        if (!take('}')) invalid();
        return result;
    }

    unsigned hex() {
        unsigned result = 0;
        for (int i = 0; i < 4; ++i) {
            if (pos_ == source_.size()) invalid();
            const char digit = source_[pos_++];
            result *= 16;
            if (digit >= '0' && digit <= '9') result += digit - '0';
            else if (digit >= 'a' && digit <= 'f') result += digit - 'a' + 10;
            else if (digit >= 'A' && digit <= 'F') result += digit - 'A' + 10;
            else invalid();
        }
        return result;
    }

    std::string quoted() {
        std::string result;
        while (pos_ < source_.size()) {
            const auto character = static_cast<unsigned char>(source_[pos_++]);
            if (character == '"') return result;
            if (character < ' ') invalid();
            if (character != '\\') {
                result += static_cast<char>(character);
                continue;
            }
            if (pos_ == source_.size()) invalid();
            const char escape = source_[pos_++];
            switch (escape) {
            case '\\': case '/': case '"': result += escape; break;
            case 'b': result += '\b'; break;
            case 'f': result += '\f'; break;
            case 'n': result += '\n'; break;
            case 'r': result += '\r'; break;
            case 't': result += '\t'; break;
            case 'u': {
                unsigned code = hex();
                if (code >= 0xd800 && code <= 0xdbff) {
                    if (!take('\\') || !take('u')) invalid();
                    const unsigned low = hex();
                    if (low < 0xdc00 || low > 0xdfff) invalid();
                    code = 0x10000 + ((code - 0xd800) << 10) + low - 0xdc00;
                } else if (code >= 0xdc00 && code <= 0xdfff) {
                    invalid();
                }
                // The mathematical display uses ASCII names, so a non-ASCII escape
                // only needs to round-trip for comparing internal names.
                if (code < 0x80) {
                    result += static_cast<char>(code);
                } else if (code < 0x800) {
                    result += static_cast<char>(0xc0 | (code >> 6));
                    result += static_cast<char>(0x80 | (code & 63));
                } else {
                    if (code >= 0x10000) {
                        result += static_cast<char>(0xf0 | (code >> 18));
                        result += static_cast<char>(0x80 | ((code >> 12) & 63));
                    } else {
                        result += static_cast<char>(0xe0 | (code >> 12));
                    }
                    result += static_cast<char>(0x80 | ((code >> 6) & 63));
                    result += static_cast<char>(0x80 | (code & 63));
                }
                break;
            }
            default: invalid();
            }
        }
        invalid();
    }
};

bool number(const std::string& input) {
    return !input.empty() && std::all_of(input.begin(), input.end(),
        [](char c) { return c >= '0' && c <= '9'; });
}

bool unify(const Math& pattern, const Math& target, Substitution& parameters,
           std::map<std::string, std::string>& bound);

bool mentionsBound(const Math& term, const std::map<std::string, std::string>& bound) {
    if (term.kind == Kind::var &&
        std::any_of(bound.begin(), bound.end(),
                    [&](const auto& entry) { return entry.second == term.value; })) return true;
    return std::any_of(term.parts.begin(), term.parts.end(), [&](const Math& part) {
        return mentionsBound(part, bound);
    });
}

bool unify(const Math& pattern, const Math& target, Substitution& parameters,
           std::map<std::string, std::string>& bound) {
    if (pattern.kind == Kind::var) {
        const auto local = bound.find(pattern.value);
        if (local != bound.end())
            return target.kind == Kind::var && target.value == local->second;
        auto parameter = parameters.find(pattern.value);
        if (parameter != parameters.end()) {
            if (target.proposition() || target.kind == Kind::nat || mentionsBound(target, bound))
                return false;
            if (parameter->second.supported()) return same(parameter->second, target);
            parameter->second = target;
            return true;
        }
    }
    if (pattern.kind != target.kind || pattern.parts.size() != target.parts.size()) return false;
    if (pattern.kind == Kind::exists) {
        bound.emplace(pattern.value, target.value);
        const bool result = unify(pattern.parts.front(), target.parts.front(), parameters, bound);
        bound.erase(pattern.value);
        return result;
    }
    if (pattern.value != target.value) return false;
    for (std::size_t i = 0; i < pattern.parts.size(); ++i) {
        if (!unify(pattern.parts[i], target.parts[i], parameters, bound)) return false;
    }
    return true;
}

std::string format(const Math& expression, const Names& names, int enclosing) {
    const auto& parts = expression.parts;
    int precedence = 4;
    std::string rendered;
    switch (expression.kind) {
    case Kind::nat: return "\\mathbb{N}";
    case Kind::var: return names.at(expression.value);
    case Kind::numeral: return expression.value;
    case Kind::function: {
        rendered = functionSymbol(expression.hint);
        if (parts.empty()) return rendered;
        rendered += "(";
        for (std::size_t i = 0; i < parts.size(); ++i) {
            if (i) rendered += ", ";
            rendered += format(parts[i], names, 0);
        }
        return rendered + ")";
    }
    case Kind::power: {
        rendered = withSuperscript(format(parts[0], names, 5),format(parts[1], names, 0));
        return enclosing > 4 ? "(" + rendered + ")" : rendered;
    }
    case Kind::mul: precedence = 3; break;
    case Kind::add: precedence = 2; break;
    case Kind::equal: case Kind::le: case Kind::lt: case Kind::divides: precedence = 1; break;
    case Kind::conjunction:
        rendered = format(parts[0], names, parts[0].kind == Kind::iff || parts[0].kind == Kind::exists) +
                   " \\land " + format(parts[1], names, parts[1].kind == Kind::iff);
        return enclosing > 0 ? "(" + rendered + ")" : rendered;
    case Kind::iff:
        rendered = format(parts[0], names, parts[0].kind == Kind::iff || parts[0].kind == Kind::exists) +
                   " \\iff " + format(parts[1], names, parts[1].kind == Kind::iff);
        return enclosing > 0 ? "(" + rendered + ")" : rendered;
    case Kind::exists: {
        Names inner = names;
        const auto witness = bindName(inner, expression.value, expression.hint);
        rendered = "\\exists " + witness + " \\in \\mathbb{N}\\; (" +
                   format(parts.front(), inner, 0) + ")";
        if (enclosing > 0) return "(" + rendered + ")";
        return rendered;
    }
    default: throw std::runtime_error("Attempted to format an unsupported expression");
    }
    const char* op = " + ";
    if (expression.kind == Kind::mul) op = " \\cdot ";
    if (expression.kind == Kind::equal) op = " = ";
    if (expression.kind == Kind::le) op = " \\le ";
    if (expression.kind == Kind::lt) op = " < ";
    if (expression.kind == Kind::divides) op = " \\mid ";
    // Preserve right nesting for arithmetic, and parenthesize relations used as operands.
    const int left = precedence == 1 ? 2 : precedence;
    rendered = format(parts[0], names, left) + op + format(parts[1], names, precedence + 1);
    return precedence < enclosing ? "(" + rendered + ")" : rendered;
}

} // namespace

const Node& Node::at(std::size_t index) const {
    if (!array || index >= children.size()) throw std::runtime_error("Malformed adapter node");
    return children[index];
}

bool Node::is(const char* tag) const {
    return array && !children.empty() && children.front().isString() && children.front().atom == tag;
}

const Node* Node::lookup(const std::string& key) const {
    const auto entry = object.find(key);
    return entry == object.end() ? nullptr : &entry->second;
}

Node readJson(std::istream& input) { return Parser(input).parse(); }

const Node& term(const Node& node) { return node.is("p") ? node.at(2) : node; }

std::string head(const Node& node) {
    const Node& raw = term(node);
    const Node& function = raw.is("a") ? term(raw.at(1)) : raw;
    return function.is("c") ? function.at(1).atom : "";
}

const Node& argument(const Node& node, std::size_t fromEnd) {
    const Node& raw = term(node);
    if (!raw.is("a") || raw.children.size() < 3 + fromEnd)
        throw std::runtime_error("Missing adapter application argument");
    return raw.at(raw.children.size() - 1 - fromEnd);
}

Math::Math(Kind kind, std::string value, std::string hint, std::vector<Math> parts)
    : kind(kind), value(std::move(value)), hint(std::move(hint)), parts(std::move(parts)) {}

bool Math::supported() const {
    return kind != Kind::unsupported &&
           std::all_of(parts.begin(), parts.end(), [](const Math& part) { return part.supported(); });
}

bool Math::proposition() const {
    return kind == Kind::equal || kind == Kind::le || kind == Kind::lt ||
           kind == Kind::divides || kind == Kind::exists || kind == Kind::iff ||
           kind == Kind::conjunction;
}

std::size_t Math::complexity() const {
    std::size_t size = 1;
    for (const auto& part : parts) size += part.complexity();
    return size;
}

Math math(const Node& expression, const Substitution& substitutions) {
    const Node& raw = term(expression);
    if (raw.is("v")) {
        const auto& id = raw.at(1).atom;
        const auto substitution = substitutions.find(id);
        return substitution == substitutions.end() ? Math(Kind::var, id) : substitution->second;
    }
    if (raw.is("n") && number(raw.at(1).atom)) return Math(Kind::numeral, raw.at(1).atom);
    if (raw.is("t")) {
        auto inner = substitutions;
        inner[raw.at(1).atom] = math(raw.at(4), substitutions);
        return math(raw.at(5), inner);
    }
    const auto name = head(raw);
    if (!raw.mathSymbol.empty()) {
        std::vector<Math> args;
        for (std::size_t i = 2; raw.is("a") && i < raw.children.size(); ++i)
            args.push_back(math(raw.at(i), substitutions));
        return Math(Kind::function, name, raw.mathSymbol, std::move(args));
    }
    if (name == "Nat") return Math(Kind::nat);
    if (name == "Nat.zero") return Math(Kind::numeral, "0");
    if (!raw.is("a")) return Math();
    const Node& function = term(raw.at(1));
    if (function.is("l") && raw.children.size() == 3)
        return applyPredicate(function, math(argument(raw, 0), substitutions), substitutions);
    if (name == "OfNat.ofNat" && raw.children.size() == 5 && head(argument(raw, 2)) == "Nat" &&
        head(argument(raw, 0)) == "instOfNatNat")
        return math(argument(raw, 1), substitutions);
    if (name == "Nat.succ" && raw.children.size() == 3)
        return Math(Kind::add, {}, {},
                    {math(argument(raw, 0), substitutions), Math(Kind::numeral, "1")});
    if (name == "Exists" && raw.children.size() == 4) {
        const Node& predicate = term(argument(raw, 0));
        if (predicate.is("l") && head(predicate.at(3)) == "Nat")
            return Math(Kind::exists, predicate.at(1).atom, predicate.at(2).atom,
                        {math(predicate.at(4), substitutions)});
    }
    if ((name == "Iff" || name == "And") && raw.children.size() == 4) {
        auto left = math(argument(raw, 1), substitutions);
        auto right = math(argument(raw, 0), substitutions);
        if (left.proposition() && right.proposition())
            return Math(name == "And" ? Kind::conjunction : Kind::iff, {}, {},
                        {std::move(left), std::move(right)});
        return Math();
    }
    const auto nativeInstance = [&](const char* instance) {
        return raw.children.size() == 6 && head(raw.at(2)) == "Nat" &&
               head(argument(raw, 2)) == instance;
    };
    const auto homogeneousInstance = [&](const char* wrapper, const char* instance) {
        if (raw.children.size() != 8) return false;
        const auto& resolved = argument(raw, 2);
        return head(raw.at(2)) == "Nat" && head(raw.at(3)) == "Nat" &&
               head(raw.at(4)) == "Nat" && head(resolved) == wrapper &&
               head(argument(resolved, 0)) == instance;
    };
    Kind operation = Kind::unsupported;
    if ((name == "Nat.add" && raw.children.size() == 4) ||
        (name == "Add.add" && nativeInstance("instAddNat")) ||
        (name == "HAdd.hAdd" && homogeneousInstance("instHAdd", "instAddNat")))
        operation = Kind::add;
    if ((name == "Nat.mul" && raw.children.size() == 4) ||
        (name == "Mul.mul" && nativeInstance("instMulNat")) ||
        (name == "HMul.hMul" && homogeneousInstance("instHMul", "instMulNat")))
        operation = Kind::mul;
    if (name == "Eq" && raw.children.size() == 5 && head(argument(raw, 2)) == "Nat")
        operation = Kind::equal;
    if (name == "Dvd.dvd" && nativeInstance("Nat.instDvd"))
        operation = Kind::divides;
    if ((name == "Nat.le" && raw.children.size() == 4) ||
        (name == "LE.le" && nativeInstance("instLENat"))) operation = Kind::le;
    if ((name == "Nat.lt" && raw.children.size() == 4) ||
        (name == "LT.lt" && nativeInstance("instLTNat"))) operation = Kind::lt;
    if (name == "Nat.pow" && raw.children.size() == 4) operation = Kind::power;
    if (name == "HPow.hPow" && raw.children.size() == 8 &&
        head(raw.at(2)) == "Nat" && head(raw.at(3)) == "Nat" && head(raw.at(4)) == "Nat") {
        const auto& instance = raw.at(5);
        if (head(instance) == "instHPow" && head(argument(instance, 0)) == "instPowNat" &&
            head(argument(argument(instance, 0), 0)) == "instNatPowNat") operation = Kind::power;
    }
    if (operation == Kind::unsupported) return Math();
    auto left = math(argument(raw, 1), substitutions);
    auto right = math(argument(raw, 0), substitutions);
    if (left.proposition() || right.proposition() || left.kind == Kind::nat || right.kind == Kind::nat)
        return Math();
    return Math(operation, {}, {}, {std::move(left), std::move(right)});
}

Math applyPredicate(const Node& predicate, const Math& argument, const Substitution& substitutions) {
    const Node& lambda = term(predicate);
    if (!lambda.is("l")) return Math();
    auto inner = substitutions;
    inner[lambda.at(1).atom] = argument;
    return math(lambda.at(4), inner);
}

bool match(const Math& pattern, const Math& target, Substitution& parameters) {
    if (!pattern.supported() || !target.supported()) return false;
    std::map<std::string, std::string> bound;
    return unify(pattern, target, parameters, bound);
}

bool same(const Math& left, const Math& right) {
    Substitution none;
    return match(left, right, none);
}

std::string bindName(Names& names, const std::string& id, const std::string& hint) {
    const auto existing = names.find(id);
    if (existing != names.end()) return existing->second;
    const bool letter = hint.size() == 1 &&
        ((hint.front() >= 'a' && hint.front() <= 'z') ||
         (hint.front() >= 'A' && hint.front() <= 'Z'));
    const std::string base = letter ? hint : "k";
    std::string candidate = base;
    for (unsigned suffix = 1; std::any_of(names.begin(), names.end(),
        [&](const auto& pair) { return pair.second == candidate; }); ++suffix) {
        candidate = base + "_{" + std::to_string(suffix) + "}";
    }
    names.emplace(id, candidate);
    return candidate;
}

std::string latex(const Math& expression, const Names& names) {
    return format(expression, names, 0);
}

bool Statement::supported() const {
    return conclusion.supported() && conclusion.proposition() &&
           std::all_of(parameters.begin(), parameters.end(), [](const Parameter& parameter) {
               return parameter.type.supported() &&
                      (parameter.type.kind == Kind::nat || parameter.type.proposition());
           });
}

Statement statement(const Node& expression) {
    Statement result;
    const Node* current = &expression;
    while (current->is("q")) {
        result.parameters.push_back(
            {current->at(1).atom, current->at(2).atom, math(current->at(3))});
        current = &current->at(4);
    }
    result.conclusion = math(*current);
    return result;
}

} // namespace proof
