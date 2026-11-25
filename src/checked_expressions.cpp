#include "expressions.hpp"

#include <algorithm>
#include <charconv>
#include <map>
#include <set>
#include <utility>

namespace proof {
namespace {

// This printer is independent of theorem-pattern matching. Sharing visual notation
// between two checked types never makes their terms interchangeable as evidence.
struct Unsupported {};
struct Display {
    std::string text;
    int priority = 100;
    std::string within(int context) const {
        return priority < context ? "\\left(" + text + "\\right)" : text;
    }
};

bool asciiLetter(char c) {
    return (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z');
}
bool digit(char c) { return c >= '0' && c <= '9'; }

const std::map<std::string, std::string> greekLetters = {
    {u8"α","\\alpha"}, {u8"β","\\beta"}, {u8"γ","\\gamma"}, {u8"δ","\\delta"},
    {u8"ε","\\varepsilon"}, {u8"η","\\eta"}, {u8"θ","\\theta"}, {u8"ι","\\iota"},
    {u8"κ","\\kappa"}, {u8"λ","\\lambda"}, {u8"μ","\\mu"}, {u8"ν","\\nu"},
    {u8"π","\\pi"}, {u8"ρ","\\rho"}, {u8"σ","\\sigma"}, {u8"τ","\\tau"},
    {u8"φ","\\varphi"}, {u8"χ","\\chi"}, {u8"ω","\\omega"}, {u8"Γ","\\Gamma"},
    {u8"Δ","\\Delta"}, {u8"Θ","\\Theta"}, {u8"Λ","\\Lambda"}, {u8"Σ","\\Sigma"},
    {u8"Φ","\\Phi"}, {u8"Ω","\\Omega"}
};
const std::vector<std::string> subscripts = {
    u8"₀",u8"₁",u8"₂",u8"₃",u8"₄",u8"₅",u8"₆",u8"₇",u8"₈",u8"₉"
};

std::string indexedLetter(const std::string& name) {
    std::string base;
    std::size_t pos = 0;
    if (!name.empty() && asciiLetter(name.front())) {
        base = name.substr(0,1);
        pos = 1;
    } else {
        for (const auto& entry : greekLetters) {
            if (name.compare(0,entry.first.size(),entry.first) == 0) {
                base = entry.second;
                pos = entry.first.size();
                break;
            }
        }
    }
    if (base.empty()) return {};
    std::string index;
    while (pos < name.size()) {
        const auto found = std::find_if(subscripts.begin(),subscripts.end(),[&](const std::string& ch) {
            return name.compare(pos,ch.size(),ch) == 0;
        });
        if (found == subscripts.end()) return {};
        index += static_cast<char>('0' + (found-subscripts.begin()));
        pos += found->size();
    }
    return index.empty() ? base : base + "_{" + index + "}";
}

std::string join(const std::vector<std::string>& items, const std::string& separator) {
    std::string result;
    for (const auto& item : items) {
        if (!result.empty()) result += separator;
        result += item;
    }
    return result;
}

std::string identifier(const std::string& name) {
    if (name.empty() || name.front() == '_' || name.find("._") != std::string::npos)
        throw Unsupported{};
    if (auto shortLabel = indexedLetter(name); !shortLabel.empty()) return shortLabel;
    std::string words;
    for (std::size_t i = 0; i < name.size(); ++i) {
        const char c = name[i];
        if (asciiLetter(c) || digit(c)) {
            if (c >= 'A' && c <= 'Z' && i && name[i-1] >= 'a' && name[i-1] <= 'z')
                words += "\\,";
            words += c;
        } else if (c == '.') words += "\\mathord{:}";
        else if (c == '_') words += "\\,";
        else if (c == '\'') words += "^{\\prime}";
        else throw Unsupported{};
    }
    return "\\operatorname{" + words + "}";
}

// The kernel qualifies private user definitions with the module and a numeric
// private scope. Their declaration suffix still identifies a mathematical object.
std::string publicSpelling(const std::string& name) {
    if (name.rfind("_private.", 0) != 0) return name;
    for (std::size_t start = 9; start < name.size();) {
        const auto end = name.find('.', start);
        if (end == std::string::npos) break;
        if (end > start && std::all_of(name.begin()+start, name.begin()+end, digit))
            return name.substr(end + 1);
        start = end + 1;
    }
    return name;
}

template<class Action>
void visitConstants(Node& node, const Action& visit) {
    if (node.is("c")) { visit(node); return; }
    for (auto& child : node.children)
        if (child.array) visitConstants(child, visit);
}

std::string role(const Node& node, std::size_t position) {
    return node.children.size() > position && node.at(position).isString()
        ? node.at(position).atom : std::string{};
}

bool positiveLevel(const std::string& level) {
    return (level != "0" && !level.empty() && std::all_of(level.begin(),level.end(),digit)) ||
           (level.size() > 2 && level.substr(level.size()-2) == "+1");
}

bool mentions(const Node& n, const std::string& id) {
    if (n.is("v")) return n.at(1).atom == id;
    return std::any_of(n.children.begin(), n.children.end(),
                       [&](const Node& child) { return child.array && mentions(child, id); });
}

std::string binderBase(const std::string& hint) {
    if (auto shortLabel = indexedLetter(hint); !shortLabel.empty()) return shortLabel;
    if (const auto prime = hint.find('\''); prime != std::string::npos &&
        hint.find_first_not_of('\'',prime) == std::string::npos) {
        if (const auto base = indexedLetter(hint.substr(0,prime)); !base.empty())
            return base + "^{" + hint.substr(prime) + "}";
    }
    if (hint.empty() || !asciiLetter(hint.front())) return "x";
    if (hint.size() == 1) return hint;
    if (std::all_of(hint.begin(), hint.end(), [](char c) { return asciiLetter(c) || digit(c); }))
        return "\\mathit{" + hint + "}";
    if (std::all_of(hint.begin()+1, hint.end(), [](char c) { return c == '\''; }))
        return hint.substr(0, 1) + "^{" + std::string(hint.size()-1, '\'') + "}";
    return hint.substr(0, 1);
}

using Args = std::vector<const Node*>;

Args explicitArgs(const Node& raw, bool includeProofs = false) {
    Args result;
    const auto& fn = term(raw.at(1));
    if ((fn.is("c") || fn.is("v")) && fn.children.size() > 3 && fn.at(3).array) {
        const auto add = [&](const Node& entry) {
            std::size_t index = 0;
            const auto* end = entry.atom.data() + entry.atom.size();
            auto parsed = std::from_chars(entry.atom.data(), end, index);
            if (parsed.ec != std::errc{} || parsed.ptr != end || index >= raw.children.size() - 2)
                throw Unsupported{};
            result.push_back(&raw.at(index + 2));
        };
        for (const auto& entry : fn.at(3).children) add(entry);
        // A local family can take a proof as its mathematical argument, e.g. Q(h).
        if ((fn.is("v") || includeProofs) && fn.children.size() > 4 && !fn.at(4).children.empty()) {
            for (const auto& entry : fn.at(4).children) add(entry);
            std::sort(result.begin(),result.end());
        }
    } else if (fn.is("l") || fn.is("v") || !raw.mathSymbol.empty()) {
        // Binding metadata for checked local functions is normally present.
        for (std::size_t i = 2; i < raw.children.size(); ++i) result.push_back(&raw.at(i));
    } else throw Unsupported{};
    return result;
}

Display render(const Node&, const Names&);
Display renderArgument(const Node&, const Names&);

Display call(const Display& fn, const Args& args, const Names& names) {
    if (args.empty()) return fn;
    std::vector<std::string> values;
    for (const auto* arg : args) values.push_back(renderArgument(*arg, names).text);
    return {fn.within(95) + "\\left(" + join(values, ", ") + "\\right)"};
}

// A proof occurring as a function argument is itself a mathematical object.
// Name its constructor or public theorem, and retain the evidence it consumes.
// This is separate from displaying the proposition established by a proof step.
Display renderArgument(const Node& arg, const Names& names) {
    const auto& raw = term(arg);
    const auto& fn = raw.is("a") ? term(raw.at(1)) : raw;
    if (!fn.is("c") || role(fn, 2) != "proof") return render(arg, names);
    const auto& name = fn.at(1).atom;
    if (name.empty() || name.front() == '_' || name.find("._") != std::string::npos)
        throw Unsupported{};
    if (name == "True.intro" && raw.is("c")) return {"\\mathrm{trivial}"};
    const auto count = raw.is("a") ? raw.children.size() - 2 : 0;
    if ((name == "Eq.substr" && count == 6) ||
        ((name == "Eq.mpr_prop" || name == "Eq.mpr_not") && count == 4)) {
        const auto eq = renderArgument(argument(raw,1),names);
        const auto evidence = renderArgument(argument(raw,0),names);
        return {"\\operatorname{transport}^{\\leftarrow}_{" + eq.text + "}(" + evidence.text + ")"};
    }
    if (name == "of_eq_true" && count == 2)
        return {"\\operatorname{transport}^{\\leftarrow}_{" + renderArgument(argument(raw,0),names).text +
                "}(\\mathrm{trivial})"};
    const auto label = identifier(fn.checkedName.empty() ? name : fn.checkedName);
    return raw.is("a") ? call({label}, explicitArgs(raw, true), names) : Display{label};
}

struct Operator { const char* sign; int priority; };
// Parenthesize either nested set operation. Readers use different conventions
// for the precedence of set difference relative to union and intersection.
constexpr int setOperatorPriority = 50;
const std::map<std::string, Operator> binary = {
    {"Iff",{"\\iff",10}}, {"Or",{"\\lor",25}}, {"And",{"\\land",30}},
    {"Eq",{"=",40}}, {"Ne",{"\\ne",40}}, {"LE.le",{"\\le",40}}, {"LT.lt",{"<",40}},
    {"GT.gt",{">",40}}, {"GE.ge",{"\\ge",40}},
    {"Nat.le",{"\\le",40}}, {"Nat.lt",{"<",40}}, {"Int.le",{"\\le",40}}, {"Int.lt",{"<",40}},
    {"Dvd.dvd",{"\\mid",40}}, {"HasSubset.Subset",{"\\subseteq",40}},
    {"HasSSubset.SSubset",{"\\subsetneq",40}}, {"Set.Subset",{"\\subseteq",40}},
    {"Union.union",{"\\cup",setOperatorPriority}}, {"Inter.inter",{"\\cap",setOperatorPriority}},
    {"SDiff.sdiff",{"\\setminus",setOperatorPriority}},
    {"HAdd.hAdd",{"+",60}}, {"Add.add",{"+",60}}, {"Nat.add",{"+",60}}, {"Int.add",{"+",60}},
    {"HSub.hSub",{"-",60}}, {"Sub.sub",{"-",60}}, {"Nat.sub",{"-",60}}, {"Int.sub",{"-",60}},
    {"HMul.hMul",{"\\cdot",70}}, {"Mul.mul",{"\\cdot",70}}, {"Nat.mul",{"\\cdot",70}},
    {"HSMul.hSMul",{"\\mathbin{\\bullet}",70}},
    {"Int.mul",{"\\cdot",70}}, {"HDiv.hDiv",{"/",70}}, {"Div.div",{"/",70}},
    {"HMod.hMod",{"\\bmod",70}}, {"Mod.mod",{"\\bmod",70}}, {"Nat.mod",{"\\bmod",70}},
    {"Bool.and",{"\\land",30}}, {"Bool.or",{"\\lor",25}}, {"Prod",{"\\times",70}},
    {"HAppend.hAppend",{"\\mathbin{\\Vert}",60}}, {"List.append",{"\\mathbin{\\Vert}",60}}
};

Display infix(const Display& l, const Operator& op, const Display& r) {
    const int left = op.priority <= setOperatorPriority ? op.priority + 1 : op.priority;
    return {l.within(left) + " " + op.sign + " " + r.within(op.priority + 1), op.priority};
}

const std::map<std::string, std::string> constants = {
    {"Nat","\\mathbb{N}"}, {"Int","\\mathbb{Z}"}, {"Rat","\\mathbb{Q}"},
    {"NNRat","\\mathbb{Q}_{\\ge 0}"}, {"Real","\\mathbb{R}"}, {"Complex","\\mathbb{C}"}, {"Bool","\\mathbb{B}"},
    {"True","\\mathrm{True}"}, {"False","\\mathrm{False}"}, {"Bool.true","\\mathrm{true}"},
    {"Bool.false","\\mathrm{false}"}, {"Nat.zero","0"}, {"List.nil","\\langle\\,\\rangle"},
    {"EmptyCollection.emptyCollection","\\varnothing"}, {"Finset.empty","\\varnothing"},
    {"Set.empty","\\varnothing"}
};

bool applicationOf(const Node& expression, const char* name, std::size_t arguments);

const Node* membershipRange(const Node& proposition, const std::string& index) {
    const auto& test = term(proposition);
    if (!applicationOf(test,"Membership.mem",5)) return nullptr;
    const auto& instance = test.at(4);
    const auto& element = term(argument(test,0));
    const auto& set = argument(test,1);
    if ((!applicationOf(instance,"Finset.instMembership",1) && !applicationOf(instance,"Set.instMembership",1)) ||
        !element.is("v") || element.at(1).atom != index || mentions(set,index))
        return nullptr;
    return &set;
}

const Node* membershipDomain(const Node& predicate) {
    const auto& lambda = term(predicate);
    if (applicationOf(lambda,"Membership.mem",4) &&
        (applicationOf(lambda.at(4),"Finset.instMembership",1) || applicationOf(lambda.at(4),"Set.instMembership",1)))
        return &argument(lambda,0);
    return lambda.is("l") ? membershipRange(lambda.at(4),lambda.at(1).atom) : nullptr;
}

bool displayedSubtype(const Node& domain) {
    return applicationOf(domain,"Subtype",2) || applicationOf(domain,"Set.Elem",2);
}

// A binder presented as an element of a subset already denotes its underlying
// element in the mathematical notation. Retain a projection for other terms.
void bindCarrier(Names& names, const Node& binder, const std::string& symbol) {
    if (displayedSubtype(binder.at(3))) names["#carrier:" + binder.at(1).atom] = symbol;
}

Display elementsOf(const Node& set, const Names& names) {
    return render(applicationOf(set,"Finset.toSet",2) ? argument(set,0) : set,names);
}

Display subtypeDomain(const Node& carrier, const Node& test, const Names& names) {
    const auto& predicate = term(test);
    if (const auto* set = membershipDomain(predicate)) return elementsOf(*set,names);
    Names inner = names;
    const auto x = predicate.is("l") ? checkedBinderName(inner,predicate.at(1).atom,predicate.at(2).atom)
                                     : checkedBinderName(inner,"#subtype-element","x");
    if (predicate.is("l")) bindCarrier(inner,predicate,x);
    const auto condition = predicate.is("l") ? render(predicate.at(4),inner).text :
                                               render(predicate,names).within(95) + "(" + x + ")";
    return {"\\{" + x + "\\in " + render(carrier,names).text + " \\mid " + condition + "\\}"};
}

Display binder(const Node& raw, const Names& names) {
    const auto& body = raw.at(4);
    const auto id = raw.at(1).atom;
    Names inner = names;
    const auto var = checkedBinderName(inner, id, raw.at(2).atom);
    bindCarrier(inner,raw,var);
    if (raw.is("q") && role(raw,7) == "prop" && raw.at(3).is("s") && positiveLevel(raw.at(3).at(1).atom) &&
        body.is("q") && role(body,5) == "instance" && applicationOf(body.at(3),"Fintype",1)) {
        const auto& carrier = term(argument(body.at(3),0));
        if (carrier.is("v") && carrier.at(1).atom == id) {
            const auto enumeration = checkedBinderName(inner,body.at(1).atom,body.at(2).atom);
            return {"\\forall " + var + "\\text{ with finite enumeration }" + enumeration + ",\\; " +
                    render(body.at(4),inner).text,5};
        }
    }
    const auto domain = render(raw.at(3), names);
    const auto result = render(body, inner);
    if (raw.is("l")) return {var + " \\mapsto " + result.text, 5};
    const auto boundRole = role(raw, 6);
    const bool dependent = mentions(body, id);
    if (role(raw, 7) == "type") {
        if (!dependent) return {domain.within(16) + " \\to " + result.within(15), 15};
        return {"\\Pi_{" + var + "\\, :\\, " + domain.text + "}\\, " + result.text, 5};
    }
    if (boundRole == "proof" && !dependent)
        return {domain.within(21) + " \\implies " + result.within(20), 20};
    return {"\\forall " + var + "\\, :\\, " + domain.text + ",\\; " + result.text, 5};
}

Display aggregate(const std::string& sign, const Node& domain, const Node& predicate,
                  const Names& names) {
    const auto& lambda = term(predicate);
    Names inner = names;
    const bool explicitLambda = lambda.is("l");
    const std::string variable = explicitLambda
        ? checkedBinderName(inner, lambda.at(1).atom, lambda.at(2).atom)
        : checkedBinderName(inner, "#sum-index", "i");
    if (explicitLambda) bindCarrier(inner,lambda,variable);
    const auto body = explicitLambda ? render(lambda.at(4), inner)
        : Display{render(lambda, names).within(95) + "(" + variable + ")"};
    const Node* range = &domain;
    if (applicationOf(domain,"Finset.univ",2) && applicationOf(domain.at(2),"Subtype",2)) {
        if (const auto* set = membershipDomain(argument(domain.at(2),0))) range = set;
    }
    std::string limits = variable + "\\in " + render(*range,names).text;
    if (applicationOf(*range,"Finset.filter",4) && applicationOf(argument(*range,0),"Finset.powerset",2)) {
        const auto& condition = term(range->at(3));
        if (condition.is("l") && applicationOf(condition.at(4),"Finset.Nonempty",2)) {
            const auto& member = term(argument(condition.at(4),0));
            if (member.is("v") && member.at(1).atom == condition.at(1).atom)
                limits = "\\varnothing \\ne " + variable + " \\subseteq " +
                         render(argument(argument(*range,0),0),names).text;
        }
    }
    if (sign == "\\bigcup" || sign == "\\bigcap")
        return {sign + "_{" + limits + "} " + body.within(setOperatorPriority + 1),setOperatorPriority};
    return {sign + "_{" + limits + "}\\left(" + body.text + "\\right)", 75};
}

// The serializer includes both the type index of the intersection/union and
// its lambda's binder type. Collapse a bounded index only when those agree.
bool identicalEncoding(const Node& a, const Node& b) {
    return !a.isObject && !b.isObject && a.array == b.array && a.atom == b.atom &&
           a.children.size() == b.children.size() &&
           std::equal(a.children.begin(),a.children.end(),b.children.begin(),identicalEncoding);
}

Display indexedSet(const Node& expression, const Names& names) {
    const auto key = head(expression);
    const std::string op = key == "Set.iInter" ? "\\bigcap" : "\\bigcup";
    const auto& family = term(argument(expression,0));
    const auto& indexType = argument(expression,1);
    Names inner = names;
    const bool explicitBinder = family.is("l");
    const auto index = explicitBinder ? checkedBinderName(inner,family.at(1).atom,family.at(2).atom) :
                                        checkedBinderName(inner,"#set-index","i");
    if (explicitBinder) {
        bindCarrier(inner,family,index);
        const auto& body = term(family.at(4));
        if (applicationOf(body,key.c_str(),3)) {
            const auto& membership = argument(body,1);
            const auto& branch = term(argument(body,0));
            const auto* range = membershipRange(membership,family.at(1).atom);
            if (range && branch.is("l") && role(branch,6) == "proof" &&
                identicalEncoding(membership,branch.at(3)) && !mentions(branch.at(4),branch.at(1).atom)) {
                return {op + "_{" + index + "\\in " + elementsOf(*range,names).text + "} " +
                        elementsOf(branch.at(4),inner).within(setOperatorPriority+1),setOperatorPriority};
            }
        }
    }
    // In a genuinely proof-dependent family the proof remains a second index.
    const auto separator = explicitBinder && role(family,6) == "proof" ? "\\text{ proving }" : "\\, :\\, ";
    const auto body = explicitBinder ? elementsOf(family.at(4),inner) :
                                      Display{render(family,names).within(95) + "(" + index + ")"};
    return {op + "_{" + index + separator + render(indexType,names).text + "} " +
            body.within(setOperatorPriority+1),setOperatorPriority};
}

bool applicationOf(const Node& expression, const char* name, std::size_t arguments) {
    const auto& raw = term(expression);
    return raw.is("a") && raw.children.size() == arguments + 2 && head(raw) == name;
}

bool hasProofArgument(const Node& application, const char* position) {
    const auto& fn = term(term(application).at(1));
    return fn.children.size() > 4 && fn.at(4).array &&
        std::any_of(fn.at(4).children.begin(), fn.at(4).children.end(),
                    [&](const Node& n) { return n.isString() && n.atom == position; });
}

// Lean can obtain a rational operation through several superclass paths.
// Verify the carrier, source and target of each projection and the library
// instance at the root. Retain the root to identify a locally selected operation.
struct RationalStructure {
    const Node& source;
    bool standard;
};

RationalStructure rationalStructure(const Node& instance, const std::string& carrier, std::string target) {
    static const std::set<std::string> projections{
        "InvOneClass.toInv", "DivInvMonoid.toInv", "DivInvOneMonoid.toInvOneClass",
        "DivisionMonoid.toDivInvOneMonoid", "GroupWithZero.toDivInvMonoid", "GroupWithZero.toDivisionMonoid",
        "DivisionCommMonoid.toDivisionMonoid", "CommGroupWithZero.toDivisionCommMonoid",
        "DivisionSemiring.toGroupWithZero", "Semifield.toDivisionSemiring", "Semifield.toCommGroupWithZero",
        "DivisionRing.toDivisionSemiring", "Field.toSemifield", "Field.toDivisionRing",
        "Zero.toOfNat0", "MulZeroClass.toZero", "NonUnitalNonAssocSemiring.toMulZeroClass",
        "NonAssocSemiring.toNonUnitalNonAssocSemiring", "Semiring.toNonAssocSemiring",
        "DivisionSemiring.toSemiring", "AddZeroClass.toZero", "AddMonoid.toAddZeroClass",
        "AddMonoidWithOne.toAddMonoid", "AddCommMonoidWithOne.toAddMonoidWithOne",
        "NonAssocSemiring.toAddCommMonoidWithOne", "MulZeroOneClass.toMulZeroClass",
        "MonoidWithZero.toMulZeroOneClass", "GroupWithZero.toMonoidWithZero",
        "One.toOfNat1", "AddMonoidWithOne.toOne", "MulOneClass.toOne", "InvOneClass.toOne",
        "MulZeroOneClass.toMulOneClass", "NonAssocSemiring.toMulZeroOneClass", "AddMonoidWithOne.toNatCast",
        "AddGroupWithOne.toAddMonoidWithOne", "Ring.toAddGroupWithOne", "DivisionRing.toRing",
        "CommSemiring.toSemiring", "SubNegMonoid.toAddMonoid", "AddGroup.toSubNegMonoid",
        "NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring",
        "NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring", "NonUnitalCommRing.toNonUnitalNonAssocCommRing",
        "CommRing.toNonUnitalCommRing", "NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring",
        "NonAssocRing.toNonUnitalNonAssocRing", "Ring.toNonAssocRing",
        "Preorder.toLE", "Preorder.toLT", "PartialOrder.toPreorder", "LinearOrder.toPartialOrder",
        "SemilatticeInf.toPartialOrder", "Lattice.toSemilatticeInf", "DistribLattice.toLattice"
    };
    const Node* current = &term(instance);
    if (carrier != "Rat" && carrier != "NNRat") return {*current,false};
    while (current->is("a") && current->children.size() == 4 &&
           current->at(2).is("c") && head(current->at(2)) == carrier) {
        const auto projection = head(*current);
        if (projection == "instDistribLatticeOfLinearOrder" && target == "DistribLattice") {
            target = "LinearOrder";
            current = &term(current->at(3));
            continue;
        }
        if (!projections.count(projection)) break;
        const auto dot = projection.find(".to");
        if (projection.substr(dot + 3) != target) break;
        target = projection.substr(0,dot);
        current = &term(current->at(3));
    }
    const auto base = current->is("c") ? head(*current) : std::string{};
    static const std::map<std::string,std::string> ratStructures{
        {"Inv","Rat.instInv"}, {"Field","Rat.instField"}, {"DivisionRing","Rat.instDivisionRing"},
        {"CommGroupWithZero","Rat.commGroupWithZero"}, {"Semiring","Rat.semiring"}, {"CommSemiring","Rat.commSemiring"},
        {"CommRing","Rat.commRing"}, {"AddMonoid","Rat.addMonoid"}, {"AddGroup","Rat.addGroup"},
        {"LE","Rat.instLE"}, {"LT","Rat.instLT"}, {"PartialOrder","Rat.instPartialOrder"}, {"LinearOrder","Rat.linearOrder"}
    };
    static const std::map<std::string,std::string> nnratStructures{
        {"Inv","NNRat.instInv"}, {"Semifield","NNRat.instSemifield"}, {"LinearOrder","instNNRatLinearOrder"}
    };
    const auto& structures = carrier == "Rat" ? ratStructures : nnratStructures;
    const auto known = structures.find(target);
    const bool standard = known != structures.end() && base == known->second;
    return {*current,standard};
}

// Explicit applications of OfNat can themselves spell their natural index
// using the canonical Nat numeral instance.
std::string naturalLiteral(const Node& index) {
    if (index.is("n")) return index.at(1).atom;
    if (!applicationOf(index,"OfNat.ofNat",3) || !index.at(2).is("c") || head(index.at(2)) != "Nat" ||
        !applicationOf(index.at(4),"instOfNatNat",1)) return {};
    const auto& n = index.at(3);
    const auto& instanceIndex = argument(index.at(4),0);
    return n.is("n") && instanceIndex.is("n") && instanceIndex.at(1).atom == n.at(1).atom ? n.at(1).atom : "";
}

RationalStructure rationalNumeral(const Node& raw, const std::string& carrier) {
    const auto& instance = raw.at(4);
    const auto value = naturalLiteral(raw.at(3));
    if (value.empty()) return {instance,false};
    if (carrier == "Rat" && applicationOf(instance,"Rat.instOfNat",1))
        return {instance,naturalLiteral(argument(instance,0)) == value};
    if (value == "0" || value == "1")
        return rationalStructure(instance,carrier,value == "0" ? "OfNat0" : "OfNat1");
    if (applicationOf(instance,"instOfNatAtLeastTwo",4) && instance.at(2).is("c") &&
        head(instance.at(2)) == carrier && naturalLiteral(instance.at(3)) == value)
        return rationalStructure(instance.at(4),carrier,"NatCast");
    return {instance,false};
}

bool finsetLattice(const Node& semilattice) {
    return applicationOf(semilattice,"Lattice.toSemilatticeInf",2) &&
           applicationOf(argument(semilattice,0),"Finset.instLattice",2);
}

bool finsetTop(const Node& top) {
    const Node* structure = &top;
    for (const char* projection : {"CoheytingAlgebra.toOrderTop","BiheytingAlgebra.toCoheytingAlgebra",
                                   "BooleanAlgebra.toBiheytingAlgebra"}) {
        if (!applicationOf(*structure,projection,2)) return false;
        structure = &argument(*structure,0);
    }
    return applicationOf(*structure,"Finset.booleanAlgebra",3);
}

bool pointwiseOne(const Node& expression, std::size_t arguments = 3) {
    if (!applicationOf(expression,"OfNat.ofNat",arguments)) return false;
    const auto& raw = term(expression);
    const auto& number = term(raw.at(3));
    const auto& instance = raw.at(4);
    if (!number.is("n") || number.at(1).atom != "1" || !applicationOf(instance,"One.toOfNat1",2)) return false;
    const Node* structure = &argument(instance,0);
    if (!applicationOf(*structure,"Pi.instOne",3)) {
        for (const char* base : {"MulOneClass.toOne","Monoid.toMulOneClass","CommMonoid.toMonoid"}) {
            if (!applicationOf(*structure,base,2)) return false;
            structure = &argument(*structure,0);
        }
        if (!applicationOf(*structure,"Pi.commMonoid",3)) return false;
    }
    const auto& choice = term(argument(*structure,0));
    return choice.is("l") && !mentions(choice.at(4),choice.at(1).atom);
}

// The outer constructor certifies that its image has no repetitions. Each
// inner conversion consumes the separate Nodup proof passed to the partial map.
// A multiset powerset on its own may contain repetitions.
const Node* duplicateFreeCandidates(const Node& expression) {
    if (!applicationOf(expression,"Finset.mk",3) || !hasProofArgument(expression,"2")) return nullptr;
    const auto& map = term(argument(expression,1));
    if (!applicationOf(map,"Multiset.pmap",6) || !hasProofArgument(map,"5") ||
        !applicationOf(map.at(2),"Multiset",1) || !applicationOf(map.at(3),"Finset",1) ||
        !applicationOf(map.at(4),"Multiset.Nodup",1) || !applicationOf(map.at(5),"Finset.mk",1))
        return nullptr;
    return &map.at(6);
}

std::string candidateSource(const Node& candidates, const Names& names) {
    const bool sized = applicationOf(candidates,"Multiset.powersetCard",3);
    if (sized || applicationOf(candidates,"Multiset.powerset",2)) {
        const auto& base = argument(candidates,0);
        const std::string source = applicationOf(base,"Finset.val",2)
            ? "the underlying multiset of \\(" + render(argument(base,0),names).text + "\\)"
            : "\\(" + render(base,names).text + "\\)";
        return sized ? "the part of the multiset powerset of " + source +
                       " whose entries have cardinality \\(" + render(argument(candidates,1),names).text + "\\)" :
                       "the multiset powerset of " + source;
    }
    return "the multiset \\(" + render(candidates,names).text + "\\)";
}

bool adjacencyProjection(const Node& field) {
    return field.is("proj") && field.children.size() == 5 && field.at(1).atom == "SimpleGraph" &&
           field.at(2).atom == "0" && role(field,4) == "value";
}

Display adjacency(const Node& graph, const Node* left, const Node* right, const Names& names) {
    const auto graphName = render(graph,names).text;
    if (!left) {
        if (term(graph).is("a")) return {"\\operatorname{Adj}(" + graphName + ")"};
        return {"\\operatorname{Adj}_{" + graphName + "}"};
    }
    const auto relation = render(*left,names).within(41) + " \\sim_{" + graphName + "} ";
    if (right) return {relation + render(*right,names).within(41),40};
    Names inner = names;
    const auto vertex = checkedBinderName(inner,"#adjacency-vertex","v");
    return {vertex + " \\mapsto " + relation + vertex,5};
}

// Graphs on a fixed vertex set are ordered by edge inclusion. A local
// instance on the same type may choose an entirely different ordering.
bool graphLatticeInstance(const Node& instance, const char* direct) {
    static const std::set<std::string> projections{
        "CompleteLattice.toTop","CompleteLattice.toBot","SemilatticeSup.toMax","SemilatticeInf.toMin",
        "Preorder.toLE","PartialOrder.toPreorder","SemilatticeSup.toPartialOrder",
        "Lattice.toSemilatticeSup","Lattice.toSemilatticeInf","ConditionallyCompleteLattice.toLattice",
        "CompleteLattice.toConditionallyCompleteLattice","CompleteAtomicBooleanAlgebra.toCompleteLattice",
        "OmegaCompletePartialOrder.toPartialOrder","CompleteLattice.instOmegaCompletePartialOrder"
    };
    const Node* field = &term(instance);
    while (field->is("a") && field->children.size() == 4 &&
           applicationOf(field->at(2),"SimpleGraph",1) && projections.count(head(*field))) {
        field = &term(argument(*field,0));
    }
    return applicationOf(*field,direct,1) || applicationOf(*field,"SimpleGraph.completeAtomicBooleanAlgebra",1);
}

const Node* emptyMapCodomain(const Node& use) {
    if (!applicationOf(use,"isEmptyElim",4) || !hasProofArgument(use,"1") ||
        role(term(use.at(1)),2) != "value") return nullptr;
    const auto& family = term(use.at(4));
    if (!family.is("l") || mentions(family.at(4),family.at(1).atom)) return nullptr;
    return &family.at(4);
}

Display pairProjection(const Node& pair, bool second, const Names& names) {
    if (applicationOf(pair,"PSigma.mk",4)) return renderArgument(argument(pair,second ? 0 : 1),names);
    return {std::string(second ? "\\pi_2(" : "\\pi_1(") + render(pair,names).text + ")"};
}

// Eliminating a dependent pair evaluates the sole branch on its components.
// Only render a component if the checked branch uses its binder.
std::optional<Display> pairCase(const Node& use, const Node& pair, const Names& names) {
    if (!applicationOf(use,"PSigma.casesOn",5) || role(term(use.at(1)),2) == "proof") return std::nullopt;
    const auto& branch = term(argument(use,0));
    if (!branch.is("l") || !term(branch.at(4)).is("l")) return std::nullopt;
    const auto& second = term(branch.at(4));
    const auto& result = second.at(4);
    Names inner = names;
    if (mentions(result,branch.at(1).atom))
        inner[branch.at(1).atom] = pairProjection(pair,false,names).within(100);
    if (mentions(result,second.at(1).atom))
        inner[second.at(1).atom] = pairProjection(pair,true,names).within(100);
    return render(result,inner);
}

const Node* naturalMeasure(const Node& projection) {
    if (!projection.is("proj") || projection.children.size() != 5 || projection.at(1).atom != "WellFoundedRelation" ||
        projection.at(2).atom != "0" || role(projection,4) != "value") return nullptr;
    const auto& structure = term(projection.at(3));
    if (!applicationOf(structure,"invImage",4) || head(structure.at(3)) != "Nat") return nullptr;
    const auto& order = term(argument(structure,0));
    if (!applicationOf(order,"instWellFoundedRelationOfSizeOf",2) || head(order.at(2)) != "Nat" ||
        !order.at(3).is("c") || head(order.at(3)) != "instSizeOfNat") return nullptr;
    return &argument(structure,1);
}

Display measuredValue(const Node& measure, const Node& subject, const Names& names) {
    const auto& function = term(measure);
    if (!function.is("l"))
        return {render(function,names).within(95) + "(" + render(subject,names).text + ")"};
    const auto& result = term(function.at(4));
    if (applicationOf(result,"PSigma.casesOn",5) && !mentions(argument(result,0),function.at(1).atom)) {
        const auto& pair = term(argument(result,1));
        if (pair.is("v") && pair.at(1).atom == function.at(1).atom) {
            if (const auto value = pairCase(result,subject,names)) return *value;
        }
    }
    Names inner = names;
    inner[function.at(1).atom] = render(subject,names).within(100);
    return render(result,inner);
}

// The inverse of the universal-subtype equivalence packages x with its
// membership proof. Keep that domain change visible even for the full set.
const Node* universalSubtypeInverse(const Node& map) {
    if (!applicationOf(map,"Equiv.symm",3)) return nullptr;
    const auto& forward = term(argument(map,0));
    return applicationOf(forward,"Equiv.subtypeUnivEquiv",3) && hasProofArgument(forward,"2") ? &forward : nullptr;
}

bool fullSetPredicate(const Node& predicate) {
    const auto* set = membershipDomain(predicate);
    return set && (applicationOf(*set,"Finset.univ",2) || applicationOf(*set,"Set.univ",1));
}

Display inSubtype(const Display& x, const Node& carrier, const Node& predicate, const Names& names) {
    if (fullSetPredicate(predicate)) {
        // Just ascribing x its ambient type would erase the packaging that
        // makes it an admissible input to a map defined on the subtype.
        return {"\\left\\langle " + x.text + ",\\; " + x.within(41) + "\\in " +
                render(carrier,names).text + "\\right\\rangle"};
    }
    const auto domain = subtypeDomain(carrier,predicate,names);
    return {"\\left(" + x.text + "\\, :\\, " + domain.text + "\\right)"};
}

Display bijectionEndpoint(const Node& type, const Names& names) {
    if (!applicationOf(type,"Subtype",2) || !fullSetPredicate(type.at(3))) return render(type,names);
    Names inner = names;
    const auto x = checkedBinderName(inner,"#full-subtype-member","v");
    const auto pair = inSubtype({x},type.at(2),type.at(3),inner);
    return {"\\{" + pair.text + "\\mid " + x + "\\in " + render(type.at(2),names).text + "\\}"};
}

Display applyBijection(const Node& map, const Display& x, const Names& names) {
    if (applicationOf(map,"Equiv.trans",5))
        return applyBijection(argument(map,0),applyBijection(argument(map,1),x,names),names);
    if (const auto* forward = universalSubtypeInverse(map))
        return inSubtype(x,forward->at(2),forward->at(3),names);
    if (applicationOf(map,"Equiv.subtypeUnivEquiv",3) && hasProofArgument(map,"2"))
        return {"\\operatorname{val}(" + x.text + ")"};
    return {render(map,names).within(95) + "\\left(" + x.text + "\\right)"};
}

Display render(const Node& input, const Names& names) {
    const Node& raw = term(input);
    if (raw.is("v")) {
        auto it = names.find(raw.at(1).atom);
        if (it == names.end()) throw Unsupported{};
        return {it->second};
    }
    if (raw.is("n")) {
        const auto& digits = raw.at(1).atom;
        if (digits.empty() || !std::all_of(digits.begin(), digits.end(), digit)) throw Unsupported{};
        return {digits};
    }
    if (raw.is("s")) {
        const auto& level = raw.at(1).atom;
        return {level == "0" ? "\\mathsf{Prop}" :
                positiveLevel(level) ? "\\mathsf{Type}" : "\\mathsf{Sort}"};
    }
    if (raw.is("proj")) {
        if (adjacencyProjection(raw)) return adjacency(raw.at(3),nullptr,nullptr,names);
        const auto& index = raw.at(2).atom;
        if (raw.at(1).atom == "PSigma" && (index == "0" || index == "1"))
            return pairProjection(raw.at(3),index == "1",names);
        if (const auto* measure = naturalMeasure(raw))
            return {"\\text{the strict order induced by the natural-valued measure }" + render(*measure,names).text,5};
        if (raw.at(1).atom == "Subtype" && index == "0") {
            const auto& value = term(raw.at(3));
            if (value.is("v")) {
                const auto found = names.find("#carrier:" + value.at(1).atom);
                if (found != names.end()) return {found->second};
            }
            return {"\\operatorname{val}(" + render(value,names).text + ")"};
        }
        if (raw.at(1).atom != "Prod" || (index != "0" && index != "1")) throw Unsupported{};
        if (head(raw.at(3)) == "SimpleGraph.Dart.toProd" &&
            term(raw.at(3)).children.size() == 5)
            return {std::string(index == "0" ? "\\operatorname{tail}(" : "\\operatorname{head}(") +
                    render(argument(raw.at(3), 0), names).text + ")"};
        return {std::string(index == "0" ? "\\pi_1(" : "\\pi_2(") +
                render(raw.at(3), names).text + ")"};
    }
    if (raw.is("l") && role(raw,7) == "value") {
        const auto& use = term(raw.at(4));
        if (const auto* target = emptyMapCodomain(use)) {
            const auto& x = term(argument(use,0));
            if (x.is("v") && x.at(1).atom == raw.at(1).atom && !mentions(*target,raw.at(1).atom))
                return {"\\text{the unique function from the empty type }" + render(raw.at(3),names).text +
                        "\\text{ to }" + render(*target,names).text,5};
        }
    }
    if (raw.is("l") || raw.is("q")) return binder(raw, names);
    if (raw.is("t")) {
        Names inner = names;
        const auto label = checkedBinderName(inner, raw.at(1).atom, raw.at(2).atom);
        return {"\\left. " + render(raw.at(5), inner).text + "\\right|_{" + label + "=" +
                render(raw.at(4), names).text + "}", 90};
    }
    if (!raw.is("a") && !raw.is("c")) throw Unsupported{};
    const auto key = head(raw);
    const bool application = raw.is("a");
    const auto count = application ? raw.children.size() - 2 : 0;
    const auto& fn = application ? term(raw.at(1)) : raw;
    if (application && adjacencyProjection(fn) && (count == 1 || count == 2))
        return adjacency(fn.at(3),&raw.at(2),count == 2 ? &raw.at(3) : nullptr,names);
    if (application && count == 2) {
        if (const auto* measure = naturalMeasure(fn))
            return infix(measuredValue(*measure,raw.at(2),names),{"<",40},measuredValue(*measure,raw.at(3),names));
    }
    const auto last = [&](std::size_t fromEnd = 0) { return render(argument(raw, fromEnd), names); };
    const auto named = [&]() { return identifier(fn.checkedName.empty() ? publicSpelling(key) : fn.checkedName); };
    if (!raw.mathSymbol.empty()) {
        const auto& label = raw.mathSymbol;
        if (!std::all_of(label.begin(), label.end(), asciiLetter)) throw Unsupported{};
        return call({label.size() == 1 ? label : "\\operatorname{" + label + "}"},
                    application ? explicitArgs(raw) : Args{}, names);
    }
    if (auto it = constants.find(key); it != constants.end()) {
        // Polymorphic empty collections may themselves be used as predicates.
        if (!application || (key == "List.nil" && count == 1) ||
            (key == "EmptyCollection.emptyCollection" && count == 2) ||
            ((key == "Set.empty" || key == "Finset.empty") && count == 1))
            return {it->second};
    }
    if (!application) {
        // Only public named mathematical objects can be displayed as symbols.
        if (role(raw, 2).empty() || role(raw, 2) == "proof") throw Unsupported{};
        return {named()};
    }
    // In the original protocol a partially applied operator does not carry the
    // positions of its type, instance and object arguments. Its old renderer
    // recognizes only exact, known signatures. Never infer operands from a tail.
    if (fn.is("c") && (fn.children.size() <= 3 || !fn.at(3).array)) {
        const auto known = math(raw);
        if (!known.supported()) throw Unsupported{};
        return {latex(known,names)};
    }
    const auto args = explicitArgs(raw);
    const auto arity = [&](std::size_t n) { return args.size() == n; };
    const auto arg = [&](std::size_t i) { return render(*args.at(i), names); };
    if ((key == "Eq.mp" || key == "Eq.mpr" || key == "cast") && count == 4 &&
        role(fn,2) == "value" && arity(1) && hasProofArgument(raw,"2")) {
        // Consecutive changes of type preserve the represented object. Show
        // its final type even when this expression occurs outside a proof.
        const Node* source = &term(argument(raw,0));
        while (source->is("a") && source->children.size() == 6 &&
               (head(*source) == "Eq.mp" || head(*source) == "Eq.mpr" || head(*source) == "cast") &&
               role(source->at(1),2) == "value" && hasProofArgument(*source,"2"))
            source = &term(argument(*source,0));
        const auto target = render(raw.at(key == "Eq.mpr" ? 2 : 3),names);
        return {"\\left(" + render(*source,names).text + "\\, :\\, " + target.text + "\\right)"};
    }
    if (key == "SimpleGraph.Iso.comp" && count == 8 && arity(2))
        return infix(arg(0),{"\\circ",70},arg(1));
    if (key == "SimpleGraph.Iso.symm" && count == 5 && arity(1))
        return {withSuperscript(arg(0).within(81),"-1"),80};
    if (key == "Equiv" && count == 2 && arity(2))
        return {"\\operatorname{Bij}\\left(" + bijectionEndpoint(*args[0],names).text + ", " +
                bijectionEndpoint(*args[1],names).text + "\\right)"};
    if (key == "DFunLike.coe" && count == 6 && arity(2) &&
        applicationOf(raw.at(2),"Equiv",2) && applicationOf(raw.at(5),"Equiv.instFunLike",2))
        return applyBijection(*args[0],arg(1),names);
    if (key == "Equiv.trans" && count == 5 && arity(2)) {
        if (universalSubtypeInverse(*args[0])) {
            Names inner = names;
            const auto x = checkedBinderName(inner,"#bijection-input","x");
            return {x + "\\mapsto " + applyBijection(raw,{x},inner).text,5};
        }
        return infix(arg(1),{"\\circ",70},arg(0));
    }
    if (key == "Equiv.symm" && count == 3 && arity(1)) {
        if (universalSubtypeInverse(raw)) {
            Names inner = names;
            const auto x = checkedBinderName(inner,"#subtype-input","x");
            return {x + "\\mapsto " + applyBijection(raw,{x},inner).text,5};
        }
        return {withSuperscript(arg(0).within(81),"-1"),80};
    }
    if (key == "Equiv.subtypeUnivEquiv" && count == 3 && hasProofArgument(raw,"2")) {
        Names inner = names;
        const auto x = checkedBinderName(inner,"#subtype-input","x");
        return {x + "\\in " + subtypeDomain(raw.at(2),raw.at(3),names).text +
                "\\mapsto \\operatorname{val}(" + x + ")",5};
    }
    if (key == "RelIso.mk" && count == 6 && arity(1) && hasProofArgument(raw,"5")) {
        const bool graphs = applicationOf(raw.at(4),"SimpleGraph.Adj",2) &&
                            applicationOf(raw.at(5),"SimpleGraph.Adj",2);
        return {std::string(graphs ? "\\text{the graph isomorphism with vertex map }" :
                                     "\\text{the relation isomorphism with underlying map }") + arg(0).within(6),5};
    }
    if (key == "Fin.val" && count == 2 && arity(1)) {
        if (applicationOf(*args[0],"Fin.mk",3) && hasProofArgument(*args[0],"2"))
            return render(argument(*args[0],1),names);
        return {"\\operatorname{val}(" + arg(0).text + ")"};
    }
    if (key == "PSigma" && count == 2) {
        const auto& family = term(argument(raw,0));
        Names inner = names;
        const auto x = family.is("l") ? checkedBinderName(inner,family.at(1).atom,family.at(2).atom) :
                                       checkedBinderName(inner,"#pair-first","x");
        const auto& result = family.is("l") ? term(family.at(4)) : family;
        const auto& fnResult = result.is("a") ? term(result.at(1)) : result;
        const bool proposition = family.is("l") &&
            (((fnResult.is("c") || fnResult.is("v")) && role(fnResult,2) == "prop") ||
             (result.is("q") && role(result,7) == "prop"));
        const auto y = checkedBinderName(inner,"#pair-second",proposition ? "h" : "y");
        const auto fiber = family.is("l") ? render(family.at(4),inner).text :
                                           render(family,names).within(95) + "(" + x + ")";
        return {"\\{(" + x + ", " + y + ")\\mid " + x + "\\, :\\, " + last(1).text +
                ",\\; " + y + (proposition ? "\\text{ proves }" : "\\, :\\, ") + fiber + "\\}"};
    }
    if (key == "PSigma.mk" && count == 4)
        return {"\\langle " + renderArgument(argument(raw,1),names).text + ", " +
                renderArgument(argument(raw,0),names).text + "\\rangle"};
    if ((key == "PSigma.fst" || key == "PSigma.snd") && count == 3)
        return pairProjection(argument(raw,0),key == "PSigma.snd",names);
    if (key == "PSigma.casesOn" && count == 5) {
        if (const auto value = pairCase(raw,argument(raw,1),names)) return *value;
    }
    if ((key == "Classical.choose" || key == "Exists.choose") && count == 3 && role(fn,2) != "proof" &&
        hasProofArgument(raw,"2")) {
        const auto& evidence = term(raw.at(4));
        if (evidence.is("v")) {
            // A proof may already have selected a name for this witness in its
            // current scope. Each occurrence using that existential shares it.
            const auto found = names.find("#chosen-witness:" + evidence.at(1).atom);
            if (found != names.end()) return {found->second};
        }
        return {"\\text{the fixed choice from }" + subtypeDomain(raw.at(2),raw.at(3),names).text,5};
    }
    if ((key == "Classical.arbitrary" || key == "Classical.choice") && count == 2 && role(fn,2) != "proof" &&
        hasProofArgument(raw,"1"))
        return {"\\text{a fixed element of }" + render(raw.at(2),names).within(6),5};
    if (key == "isEmptyElim") {
        if (const auto* target = emptyMapCodomain(raw))
            return {"\\operatorname{empty\\,map}_{" + render(raw.at(2),names).text + "\\to " +
                    render(*target,names).text + "}(" + last().text + ")"};
    }
    if (key == "HEq" && count == 4) {
        // Proof irrelevance identifies the inhabitants of each proposition.
        // The propositions on the two sides can nevertheless be different.
        if (hasProofArgument(raw,"1") && hasProofArgument(raw,"3"))
            return {"\\text{the proof of }" + render(raw.at(2),names).within(41) +
                    "\\text{ agrees under transport with the proof of }" + render(raw.at(4),names).within(41),40};
        const auto operand = [&](const Node& type, const Node& value) {
            return "\\left(" + renderArgument(value,names).text + "\\, :\\, " + render(type,names).text + "\\right)";
        };
        return {operand(raw.at(2),raw.at(3)) + "\\text{ is heterogeneously equal to }" +
                operand(raw.at(4),raw.at(5)),40};
    }
    if ((key == "IsOrderedCancelAddMonoid" || key == "IsOrderedAddMonoid") && count == 3 && arity(1))
        return {std::string(key == "IsOrderedCancelAddMonoid" ? "\\text{translation preserves and reflects order on }" :
                           "\\text{translation preserves order on }") + arg(0).text, 40};
    if (key == "IsStrictOrderedRing" && count == 3 && arity(1))
        return {arg(0).text + "\\text{ is a strictly ordered semiring}", 40};
    if (key == "IsRefl" && count == 2 && arity(2))
        return {arg(1).within(41) + "\\text{ is reflexive on }" + arg(0).text,40};
    if ((key == "Relator.LeftTotal" || key == "Relator.RightTotal" ||
         key == "Relator.LeftUnique" || key == "Relator.RightUnique") && count == 3 && arity(1)) {
        Names inner = names;
        const auto a = checkedBinderName(inner,"#relation-left","a");
        const auto b = checkedBinderName(inner,"#relation-right","b");
        const auto left = last(2).text, right = last(1).text;
        const auto relation = arg(0).within(95);
        const auto applies = [&](const std::string& x, const std::string& y) {
            return relation + "(" + x + ", " + y + ")";
        };
        const auto each = [](const std::string& x, const std::string& type) {
            return "\\forall " + x + "\\, :\\, " + type + ",\\; ";
        };
        if (key == "Relator.LeftTotal")
            return {each(a,left) + "\\exists " + b + "\\, :\\, " + right + ",\\; " + applies(a,b),5};
        if (key == "Relator.RightTotal")
            return {each(b,right) + "\\exists " + a + "\\, :\\, " + left + ",\\; " + applies(a,b),5};
        const bool leftUnique = key == "Relator.LeftUnique";
        const auto c = checkedBinderName(inner,"#relation-alternative",leftUnique ? "a'" : "b'");
        const auto fixed = leftUnique ? each(b,right) : each(a,left);
        const auto varying = leftUnique ? a : b;
        return {fixed + each(varying + ", " + c,leftUnique ? left : right) +
                applies(a,b) + " \\land " + (leftUnique ? applies(c,b) : applies(a,c)) +
                " \\implies " + varying + " = " + c,5};
    }
    if (key == "Nonempty" && count == 1 &&
        (applicationOf(raw.at(2),"SimpleGraph.Iso",4) || applicationOf(raw.at(2),"SimpleGraph.Embedding",4))) {
        const auto& map = raw.at(2);
        const auto from = render(argument(map,1),names);
        const auto to = render(argument(map,0),names);
        if (head(map) == "SimpleGraph.Iso") return infix(from,{"\\cong",40},to);
        return {from.within(41) + "\\text{ is isomorphic to an induced subgraph of }" + to.within(41),40};
    }
    if ((key == "Nonempty" || key == "IsEmpty" || key == "Set.Infinite" || key == "Subsingleton") && arity(1)) {
        const auto adjective = key == "Nonempty" ? " is nonempty" : key == "IsEmpty" ? " is empty" : key == "Set.Infinite" ?
            " is infinite" : " has at most one element";
        return {arg(0).within(41) + "\\text{" + adjective + "}", 40};
    }
    if (key == "OrderDual" && count == 1) return {withSuperscript(arg(0).within(81),"\\mathrm{op}"),80};
    if (key == "Nat.ModEq" && count == 3 && arity(3))
        return {arg(1).within(41) + " \\equiv " + arg(2).within(41) + " \\pmod{" + arg(0).text + "}",40};
    if (key == "Inv.inv" && count == 3 && arity(1) && raw.at(2).is("c")) {
        const auto carrier = head(raw.at(2));
        if (carrier == "Rat" || carrier == "NNRat") {
            const auto structure = rationalStructure(raw.at(3),carrier,"Inv");
            if (!structure.standard)
                return {"\\operatorname{inv}_{" + render(structure.source,names).text + "}\\left(" + last().text + "\\right)"};
            return {"\\mathord{\\frac{1}{" + last().text + "}}"};
        }
    }
    if (key == "Nat.cast" && count == 3 && head(raw.at(3)) == "AddMonoidWithOne.toNatCast")
        return {"\\operatorname{cast}_{" + render(raw.at(2), names).text + "}\\left(" + last().text + "\\right)"};
    if ((key == "Nat.cast" && count == 3 && head(raw.at(2)) == "Int") ||
        (key == "Int.ofNat" && count == 1)) return last();
    if (key == "HDiv.hDiv" && arity(2) && count == 6 &&
        (head(raw.at(2)) == "Int" || head(raw.at(2)) == "Nat") &&
        head(*args[1]) == "OfNat.ofNat") {
        const auto& d = term(argument(*args[1], 1));
        if (d.is("n") && d.at(1).atom.find_first_not_of('0') != std::string::npos)
            return {"\\left\\lfloor\\frac{" + arg(0).text + "}{" + arg(1).text + "}\\right\\rfloor"};
    }
    if (count >= 2 && applicationOf(raw.at(2),"SimpleGraph",1)) {
        if (count == 4 && arity(2)) {
            if (key == "Max.max" && graphLatticeInstance(raw.at(3),"SimpleGraph.instMax"))
                return infix(arg(0),{"\\cup",setOperatorPriority},arg(1));
            if (key == "Min.min" && graphLatticeInstance(raw.at(3),"SimpleGraph.instMin"))
                return infix(arg(0),{"\\cap",setOperatorPriority},arg(1));
            if (key == "LE.le" && graphLatticeInstance(raw.at(3),"SimpleGraph.instLE"))
                return infix(arg(0),{"\\subseteq",40},arg(1));
        }
        if (count == 2 && ((key == "Top.top" && graphLatticeInstance(raw.at(3),"SimpleGraph.instTop")) ||
                          (key == "Bot.bot" && graphLatticeInstance(raw.at(3),"SimpleGraph.instBot")))) {
            const auto vertices = render(argument(raw.at(2),0),names).text;
            return {std::string(key == "Top.top" ? "\\operatorname{complete\\,graph}(" :
                                                   "\\operatorname{edgeless\\,graph}(") + vertices + ")"};
        }
    }
    const auto operation = binary.find(key);
    if (count == 4 && arity(2) && raw.at(2).is("c") && (head(raw.at(2)) == "Rat" || head(raw.at(2)) == "NNRat") &&
        (key == "LT.lt" || key == "GT.gt" || key == "LE.le" || key == "GE.ge")) {
        const auto order = rationalStructure(raw.at(3),head(raw.at(2)),key == "LT.lt" || key == "GT.gt" ? "LT" : "LE");
        if (!order.standard) {
            const std::string sign = std::string(operation->second.sign) + "_{" + render(order.source,names).text + "}";
            return infix(arg(0),{sign.c_str(),40},arg(1));
        }
    }
    if (operation != binary.end() || key == "Membership.mem") {
        const bool membership = key == "Membership.mem";
        const auto op = membership ? Operator{"\\in",40} : operation->second;
        if (arity(2)) return membership ? infix(arg(1),op,arg(0)) : infix(arg(0),op,arg(1));
        if (arity(1) || arity(0)) {
            Names inner = names;
            const auto x = checkedBinderName(inner,"#binary-left","x");
            const auto y = checkedBinderName(inner,"#binary-right","y");
            const auto left = arity(1) ? arg(0) : Display{x};
            auto result = membership ? infix({y},op,left) : infix(left,op,{y});
            return {(arity(1) ? "" : x + " \\mapsto ") + y + " \\mapsto " + result.text,5};
        }
    }
    if (key == "OfNat.ofNat" && count == 3) {
        const auto carrier = head(raw.at(2));
        if (raw.at(2).is("c") && (carrier == "Rat" || carrier == "NNRat")) {
            const auto numeral = rationalNumeral(raw,carrier);
            if (!numeral.standard)
                return {"\\operatorname{numeral}_{" + render(numeral.source,names).text + "}(" + last(1).text + ")"};
        }
        return last(1);
    }
    if (key == "OfNat.ofNat" && count == 4 && pointwiseOne(raw,4)) return {"1"};
    if (key == "Nat.succ" && count == 1) return infix(last(), {"+",60}, {"1"});
    if ((key == "Nat.pow" || key == "HPow.hPow" || key == "Pow.pow") && arity(2))
        return {withSuperscript(arg(0).within(81),arg(1).text),80};
    if ((key == "Not" || key == "Bool.not") && arity(1)) {
        const auto& expr = term(*args[0]);
        if (key == "Not" && applicationOf(expr,"SimpleGraph.CliqueFree",3))
            return {render(argument(expr,1),names).within(41) + "\\text{ contains a clique of size }" +
                    render(argument(expr,0),names).within(41),40};
        if (head(expr) == "Membership.mem" && expr.children.size() == 7)
            return infix(render(argument(expr,0),names), {"\\notin",40}, render(argument(expr,1),names));
        return {"\\neg " + arg(0).within(41),35};
    }
    if (key == "Neg.neg" && arity(1)) return {"-" + arg(0).within(76),75};
    if ((key == "Exists" || key == "ExistsUnique") && count == 2) {
        const auto& predicate = term(argument(raw, 0));
        Names inner = names;
        const bool lambda = predicate.is("l");
        const auto var = lambda ? checkedBinderName(inner,predicate.at(1).atom,predicate.at(2).atom)
                                : checkedBinderName(inner,"#existential-witness","x");
        if (lambda) bindCarrier(inner,predicate,var);
        const auto body = lambda ? render(predicate.at(4),inner).text
                                 : render(predicate,names).within(95) + "(" + var + ")";
        if (lambda && role(predicate,6) == "proof") {
            if (key == "Exists" && !mentions(predicate.at(4),predicate.at(1).atom))
                return infix(last(1),{"\\land",30},render(predicate.at(4),inner));
            return {std::string(key == "Exists" ? "\\exists " : "\\exists! ") + var +
                    "\\text{ proving }" + last(1).within(41) + ",\\; " + body,5};
        }
        return {std::string(key == "Exists" ? "\\exists " : "\\exists! ") + var + "\\, :\\, " +
                last(1).text + ",\\; " + body, 5};
    }
    if ((key == "Iff.mp" || key == "Iff.mpr") && count == 4)
        return {"{" + last(1).within(95) + "}" + (key == "Iff.mp" ? "_{\\rightarrow}" : "_{\\leftarrow}") +
                "\\left(" + last().text + "\\right)"};
    if ((key == "Finset" || key == "Set") && count == 1) {
        const auto symbol = key == "Finset" ? "\\mathcal{P}_{\\mathrm{fin}}" : "\\mathcal{P}";
        return {std::string(symbol) + "(" + last().text + ")"};
    }
    if (key == "Set.Elem" && count == 2 && arity(1)) return elementsOf(*args[0],names);
    if (key == "Subtype" && count == 2 && arity(1)) return subtypeDomain(raw.at(2),raw.at(3),names);
    if (key == "Subtype.val" && count == 3 && arity(1)) {
        const auto& value = term(*args[0]);
        if (value.is("v")) {
            const auto found = names.find("#carrier:" + value.at(1).atom);
            if (found != names.end()) return {found->second};
        }
        if (applicationOf(value,"Subtype.mk",4) && hasProofArgument(value,"3"))
            return render(argument(value,1),names);
        return {"\\operatorname{val}(" + arg(0).text + ")"};
    }
    if (key == "Subtype.mk" && count == 4 && hasProofArgument(raw,"3"))
        return inSubtype(last(1),raw.at(2),raw.at(3),names);
    if ((key == "Fin" || key == "List" || key == "Multiset" || key == "SimpleGraph") && count == 1)
        return {identifier(key) + "(" + last().text + ")"};
    if ((key == "Finset.card" || key == "Fintype.card" ||
         key == "Multiset.card") && arity(1) && count == 2)
        return {"\\left|" + arg(0).text + "\\right|"};
    // ncard is zero on infinite sets, unlike the usual cardinal of an arbitrary set.
    if (key == "Set.ncard" && arity(1) && count == 2)
        return {"\\operatorname{ncard}(" + arg(0).text + ")"};
    if (key == "Nat.choose" && arity(2))
        return {"\\binom{" + arg(0).text + "}{" + arg(1).text + "}"};
    if (key == "List.length" && arity(1)) return {"\\operatorname{length}(" + arg(0).text + ")"};
    if ((key == "Finset.sum" || key == "Finset.prod") && arity(2))
        return aggregate(key == "Finset.sum" ? "\\sum" : "\\prod", *args[0], *args[1], names);
    if (key == "Finset.biUnion" && count == 5 && arity(2))
        return aggregate("\\bigcup",*args[0],*args[1],names);
    if ((key == "Set.iInter" || key == "Set.iUnion") && count == 3 && arity(1))
        return indexedSet(raw,names);
    if ((key == "Finset.inf" || key == "Finset.inf'") && count == 6 && arity(2) &&
        applicationOf(raw.at(2),"Finset",1) && finsetLattice(raw.at(4)) &&
        (key == "Finset.inf" ? finsetTop(raw.at(5)) : hasProofArgument(raw,"4")))
        return aggregate("\\bigcap",*args[0],*args[1],names);
    if (key == "HasCompl.compl" && count == 3 && arity(1)) {
        const auto& instance = raw.at(3);
        if ((applicationOf(raw.at(2),"Set",1) && applicationOf(instance,"Set.instHasCompl",1)) ||
            (applicationOf(raw.at(2),"Finset",1) && applicationOf(instance,"BooleanAlgebra.toHasCompl",2) &&
             applicationOf(argument(instance,0),"Finset.booleanAlgebra",3)))
            return {withSuperscript(elementsOf(*args[0],names).within(81),"\\mathrm c"),80};
    }
    if (key == "Set.indicator" && count == 6 && arity(3)) {
        const auto domain = elementsOf(*args[0],names).text;
        if (pointwiseOne(*args[1])) return {"\\mathbf{1}_{" + domain + "}(" + arg(2).text + ")"};
        const auto x = arg(2).text;
        return {"\\begin{cases}" + arg(1).within(95) + "(" + x + ") & " + x + "\\in " + domain +
                "\\\\ 0 & " + x + "\\notin " + domain + "\\end{cases}"};
    }
    if ((key == "Finset.bipartiteAbove" || key == "Finset.bipartiteBelow") && count == 6 && arity(3))
        return {std::string("N^{") + (key == "Finset.bipartiteAbove" ? "+" : "-") +
                "}_{" + arg(0).text + ", " + arg(1).text + "}(" + arg(2).text + ")"};
    if (key == "Finset.range" && arity(1)) {
        Names inner = names;
        const auto index = checkedBinderName(inner, "#range-index", "i");
        return {"\\{" + index + "\\in\\mathbb{N}\\mid " + index + "<" + last().text + "\\}"};
    }
    if (key == "Finset.univ" && count == 2) return last(1);
    if (key == "Set.univ" && count == 1) return last();
    if ((key == "Singleton.singleton" || key == "Finset.singleton" || key == "Set.singleton") && arity(1))
        return {"\\{" + arg(0).text + "\\}"};
    if ((key == "Insert.insert" || key == "Finset.insert" || key == "Set.insert") && arity(2))
        return infix({"\\{" + arg(0).text + "\\}"}, {"\\cup",setOperatorPriority}, arg(1));
    if ((key == "Finset.powerset" || key == "Set.powerset") && arity(1))
        return {"\\mathcal P(" + arg(0).text + ")"};
    if (key == "Finset.powersetCard" && arity(2))
        return {"\\mathcal P_{" + arg(0).text + "}(" + arg(1).text + ")"};
    if (key == "Finset.ssubsets" && arity(1))
        return {"\\operatorname{proper\\,subsets}(" + arg(0).text + ")"};
    if (key == "Multiset.powerset" && arity(1))
        return {"\\operatorname{multiset\\,powerset}(" + arg(0).text + ")"};
    if (key == "Multiset.powersetCard" && arity(2))
        return {"\\operatorname{multiset\\,powerset}_{" + arg(0).text + "}(" + arg(1).text + ")"};
    if (key == "Multiset.pmap" && count == 6 && arity(2) && hasProofArgument(raw,"5"))
        return {"\\operatorname{multiset\\,map}_{" + render(raw.at(4),names).text + "}(" +
                arg(0).text + ", " + arg(1).text + ")"};
    if (key == "Finset.mk" && count == 1) return {"\\operatorname{as\\,finite\\,set}"};
    if (key == "Finset.mk" && count == 3 && arity(1) && hasProofArgument(raw,"2")) {
        if (const Node* candidates = duplicateFreeCandidates(raw)) {
            Names inner = names;
            const auto element = checkedBinderName(inner,"#multiset-entry","u");
            return {"\\left\\{\\operatorname{as\\,finite\\,set}(" + element + ") \\mid " + element +
                    "\\in " + render(*candidates,names).text + "\\right\\}"};
        }
        return {"\\operatorname{as\\,finite\\,set}(" + arg(0).text + ")"};
    }
    if (key == "Finset.erase" && arity(2))
        return infix(arg(0), {"\\setminus",setOperatorPriority}, {"\\{" + arg(1).text + "\\}"});
    if (key == "Finset.toSet" && count == 1)
        return {"\\operatorname{underlying\\,set}"};
    if (key == "Finset.toSet" && arity(1))
        return {"\\operatorname{underlying\\,set}(" + arg(0).text + ")"};
    if (key == "Set.toFinset" && arity(1))
        return {"\\operatorname{as\\,finite\\,set}(" + arg(0).text + ")"};
    if (key == "Finset.val" && arity(1))
        return {"\\operatorname{underlying\\,multiset}(" + arg(0).text + ")"};
    if ((key == "Set.setOf" || key == "setOf") && arity(1)) {
        const auto& predicate = term(argument(raw,0));
        if (predicate.is("l")) {
            Names inner = names;
            const auto var = checkedBinderName(inner,predicate.at(1).atom,predicate.at(2).atom);
            return {"\\{" + var + "\\in " + render(predicate.at(3),names).text + " \\mid " +
                    render(predicate.at(4),inner).text + "\\}"};
        }
    }
    if ((key == "Set.image" || key == "Finset.image" || key == "Set.preimage") && arity(2)) {
        auto map = arg(0).within(95);
        if (key=="Set.preimage") map = withSuperscript(map,"-1");
        return {map + "\\left[" + arg(1).text + "\\right]"};
    }
    if (key == "Set.InjOn" && arity(2))
        return {arg(0).within(41) + "\\text{ is injective on }" + arg(1).text,40};
    if (key == "Set.SurjOn" && arity(3))
        return {arg(2).within(41) + "\\subseteq " + arg(0).within(95) +
                "\\left[" + arg(1).text + "\\right]",40};
    if ((key == "List.Nodup" || key == "Multiset.Nodup") && arity(1))
        return {arg(0).within(41) + "\\text{ has no repeated elements}",40};
    if ((key == "List.Nodup" || key == "Multiset.Nodup") && count == 1 && arity(0))
        return {"\\operatorname{no\\,repetitions}"};
    if (key == "List.reverse" && arity(1)) return {"\\operatorname{reverse}(" + arg(0).text + ")"};
    if ((key == "Finset.Nonempty" || key == "Set.Nonempty") && arity(1))
        return {arg(0).within(41) + "\\ne\\varnothing",40};
    if ((key == "Finset.Nontrivial" || key == "Set.Nontrivial") && count == 2 && arity(1))
        return {arg(0).within(41) + "\\text{ contains two distinct elements}",40};
    if ((key == "Function.Injective" || key == "Function.Surjective" ||
         key == "Function.Bijective") && arity(1)) {
        const auto adjective = key == "Function.Injective" ? "injective" :
                               key == "Function.Surjective" ? "surjective" : "bijective";
        return {arg(0).within(41) + "\\text{ is " + adjective + "}",40};
    }
    if ((key == "List.map" || key == "List.filter" || key == "Finset.filter") && arity(2)) {
        const auto& predicate = term(*args[0]);
        const bool lambda = predicate.is("l");
        Names inner = names;
        const auto var = lambda ? checkedBinderName(inner,predicate.at(1).atom,predicate.at(2).atom)
                                : checkedBinderName(inner,"#comprehension-variable","x");
        const auto body = lambda ? render(predicate.at(4),inner).text
                                 : render(predicate,names).within(95) + "(" + var + ")";
        const auto range = var + "\\in " + render(*args[1],names).text;
        if (key == "Finset.filter") return {"\\{" + range + " \\mid " + body + "\\}"};
        if (key == "List.filter") return {"\\langle " + range + " \\mid " + body + "\\rangle"};
        return {"\\langle " + body + " \\mid " + range + "\\rangle"};
    }
    if (key == "SimpleGraph.Adj" && !args.empty() && args.size() <= 3 && count == args.size()+1)
        return adjacency(*args[0],args.size() >= 2 ? args[1] : nullptr,arity(3) ? args[2] : nullptr,names);
    if (key == "SimpleGraph.replaceVertex" && count==5 && arity(3))
        return {"\\operatorname{clone}(" + arg(0).text + ", " + arg(1).text + ", " + arg(2).text + ")"};
    if (key == "SimpleGraph.mk" && count == 4 && arity(1) && hasProofArgument(raw,"2") && hasProofArgument(raw,"3")) {
        const auto graph = "\\text{the graph on }" + render(raw.at(2),names).text;
        const auto& relation = term(*args[0]);
        if (relation.is("l") && term(relation.at(4)).is("l")) {
            const auto& second = term(relation.at(4));
            Names inner = names;
            const auto v = checkedBinderName(inner,relation.at(1).atom,relation.at(2).atom);
            const auto w = checkedBinderName(inner,second.at(1).atom,second.at(2).atom);
            return {graph + "\\text{ in which }" + v + "\\text{ and }" + w +
                    "\\text{ are adjacent exactly when }" + render(second.at(4),inner).text,5};
        }
        return {graph + "\\text{ with adjacency relation }" + arg(0).within(6),5};
    }
    if (key == "SimpleGraph.CliqueFree" && count == 3 && arity(2))
        return {arg(0).within(41) + "\\text{ contains no clique of size }" + arg(1).within(41),40};
    if (key == "SimpleGraph.IsClique" && count == 3 && arity(2))
        return {elementsOf(*args[1],names).within(41) + "\\text{ is a clique in }" + arg(0).within(41),40};
    if (key == "SimpleGraph.IsNClique" && count == 4 && arity(3))
        return {arg(2).within(41) + "\\text{ is a clique of size }" + arg(1).within(41) +
                "\\text{ in }" + arg(0).within(41),40};
    // Both Mathlib constructions take their graph and parameter implicitly,
    // recovered by Lean from a Turan-maximality proof. Keep them in the paper.
    if (((key == "SimpleGraph.IsTuranMaximal.setoid" && count == 6) ||
         (key == "SimpleGraph.IsTuranMaximal.finpartition" && count == 7)) &&
        arity(0) && hasProofArgument(raw,"5")) {
        const auto label = count == 6 ? "\\operatorname{nonadjacency\\,relation}" :
                                        "\\operatorname{nonadjacency\\,partition}";
        return {label + std::string("(") + render(raw.at(4),names).text + ", " + render(raw.at(6),names).text + ")"};
    }
    if (key == "Finpartition.ofSetoid" && count == 5 && arity(1))
        return {"\\text{the partition into equivalence classes of }" + arg(0).within(6),5};
    if (key == "Setoid.mk" && count == 3 && arity(1) && hasProofArgument(raw,"2"))
        return {"\\text{the equivalence relation }" + arg(0).within(6) +
                "\\text{ on }" + render(raw.at(2),names).text,5};
    if (key == "Setoid.r" && count >= 2 && count <= 4 && arity(count-2)) {
        const auto relation = render(raw.at(3),names);
        if (count == 2) return relation;
        if (count == 4) return {arg(0).within(41) + " \\sim_{" + relation.text + "} " + arg(1).within(41),40};
        Names inner = names;
        const auto y = checkedBinderName(inner,"#related-element","y");
        return {y + "\\mapsto " + arg(0).within(41) + " \\sim_{" + relation.text + "} " + y,5};
    }
    if (key == "SimpleGraph.Dart" && arity(1))
        return {"\\operatorname{oriented\\,edges}(" + arg(0).text + ")"};
    if (key == "SimpleGraph.Dart.symm" && arity(1))
        return {"\\operatorname{reverse}(" + arg(0).text + ")"};
    if (key == "SimpleGraph.dartOfNeighborSet" && (arity(2) || arity(3))) {
        if (arity(3))
            return {"\\operatorname{dart}_{" + arg(0).text + "}(" + arg(1).text + ", " + arg(2).text + ")"};
        Names inner = names;
        const auto w = checkedBinderName(inner, "#neighbor", "w");
        return {w + "\\mapsto\\operatorname{dart}_{" + arg(0).text + "}(" + arg(1).text + ", " + w + ")",5};
    }
    if (key == "SimpleGraph.support" && arity(1))
        return {"\\operatorname{supp}(" + arg(0).text + ")"};
    if (key == "SimpleGraph.degree" || key == "SimpleGraph.neighborFinset" ||
        key == "SimpleGraph.neighborSet") {
        if (args.size() == 2) return {std::string(key == "SimpleGraph.degree" ? "\\deg" : "N") +
            "_{" + render(*args[0], names).text + "}(" + render(*args[1], names).text + ")"};
    }
    if (key == "SimpleGraph.edgeFinset" || key == "SimpleGraph.edgeSet") {
        if (args.size() == 1) return {"E(" + render(*args[0], names).text + ")"};
    }
    if (key == "Prod.mk" && arity(2)) return {"\\left(" + arg(0).text + ", " + arg(1).text + "\\right)"};
    if ((key == "Prod.fst" || key == "Prod.snd") && arity(1)) {
        if (head(*args[0]) == "SimpleGraph.Dart.toProd" && term(*args[0]).children.size() == 5)
            return {std::string(key == "Prod.fst" ? "\\operatorname{tail}(" : "\\operatorname{head}(") +
                    render(argument(*args[0],0),names).text + ")"};
        return {std::string(key == "Prod.fst" ? "\\pi_1(" : "\\pi_2(") + arg(0).text + ")"};
    }
    if (key == "List.cons" && arity(2)) {
        if (head(*args[1]) == "List.nil") return {"\\langle " + arg(0).text + "\\rangle"};
        return infix({"\\langle " + arg(0).text + "\\rangle"}, {"\\mathbin{\\Vert}",60}, arg(1));
    }
    if (key == "ite" && count == 5)
        return {"\\begin{cases}" + last(1).text + " &\\text{if } " + last(3).text + "\\\\ " +
                last().text + " &\\text{otherwise}\\end{cases}"};
    if (key == "dite" && count == 5) {
        const auto condition = last(3);
        const auto branch = [&](const Node& expr, bool positive) {
            const auto& value = term(expr);
            Names inner = names;
            const bool lambda = value.is("l");
            const auto variable = checkedBinderName(inner,lambda ? value.at(1).atom : "#condition",
                                                     lambda ? value.at(2).atom : "h");
            const auto body = lambda ? render(value.at(4),inner).text :
                                       render(value,names).within(95) + "(" + variable + ")";
            const auto premise = positive ? condition.text : "\\neg " + condition.within(41);
            if (lambda && !mentions(value.at(4),value.at(1).atom)) return body + " &\\text{if } " + premise;
            return body + " &\\text{given } " + variable + "\\text{ proving } " + premise;
        };
        return {"\\begin{cases}" + branch(argument(raw,1),true) + "\\\\ " +
                branch(argument(raw,0),false) + "\\end{cases}"};
    }
    if (fn.is("v") || fn.is("l")) return call(render(fn, names), args, names);
    if (key == "True.intro" || role(fn, 2) == "proof") throw Unsupported{};
    if (key.empty() || role(fn, 2).empty()) throw Unsupported{};
    return call({named()}, args, names);
}

bool ordinaryArrow(const Node& raw) {
    return raw.is("q") && role(raw,5) == "explicit" && role(raw,7) == "type" &&
           role(raw,6) != "proof" && !mentions(raw.at(4),raw.at(1).atom);
}

bool collectionType(const std::string& key) {
    return key == "Finset" || key == "Set" || key == "SimpleGraph" || key == "List" ||
           key == "Multiset" || key == "Sym2";
}

// Compare the domains themselves. In particular, two identical-looking
// finite sets can live on distinct carriers. Only ordinary, nondependent
// function spaces qualify; their fresh binder identifiers need not coincide.
bool compatibleIntroduction(const Node& first, const Node& second, bool outer = true) {
    const auto& a = term(first);
    const auto& b = term(second);
    if (a.is("s") && b.is("s"))
        return a.at(1).atom == b.at(1).atom ||
               (outer && positiveLevel(a.at(1).atom) && positiveLevel(b.at(1).atom));
    if ((a.is("v") && b.is("v")) || (a.is("c") && b.is("c")))
        return a.at(1).atom == b.at(1).atom;
    if (ordinaryArrow(a) && ordinaryArrow(b))
        return compatibleIntroduction(a.at(3),b.at(3),false) &&
               compatibleIntroduction(a.at(4),b.at(4),false);
    const auto key = head(a);
    return collectionType(key) && applicationOf(a,key.c_str(),1) && applicationOf(b,key.c_str(),1) &&
           compatibleIntroduction(argument(a,0),argument(b,0),false);
}

std::string objectDescription(const Node& type, const Names& names, bool plural) {
    const auto& raw = term(type);
    const auto key = head(raw);
    const auto noun = [&](const char* singular, const char* many) {
        return std::string(plural ? many : singular);
    };
    if (raw.is("s")) return raw.at(1).atom == "0" ? noun("a proposition","propositions") :
                            positiveLevel(raw.at(1).atom) ? noun("a type","types") : noun("a sort","sorts");
    if (key == "Nat") return noun("a natural number","natural numbers");
    if (key == "Int") return noun("an integer","integers");
    if (key == "Rat") return noun("a rational number","rational numbers");
    if (key == "NNRat") return noun("a nonnegative rational number","nonnegative rational numbers");
    if (key == "Real") return noun("a real number","real numbers");
    if (key == "Bool") return noun("a Boolean value","Boolean values");
    if (applicationOf(raw,"Equiv",2))
        return noun("a bijection from ","bijections from ") + "\\(" + bijectionEndpoint(raw.at(2),names).text +
               "\\) to \\(" + bijectionEndpoint(raw.at(3),names).text + "\\)";
    if (applicationOf(raw,"SimpleGraph.Iso",4) || applicationOf(raw,"SimpleGraph.Embedding",4)) {
        const auto kind = key == "SimpleGraph.Iso" ? noun("a graph isomorphism","graph isomorphisms") :
                                                     noun("an induced graph embedding","induced graph embeddings");
        return kind + " from \\(" + render(argument(raw,1),names).text + "\\) to \\(" +
               render(argument(raw,0),names).text + "\\)";
    }
    if (key == "Sym2" && raw.is("a") && raw.children.size() == 3)
        return noun("an unordered pair from ","unordered pairs from ") + "\\(" + render(argument(raw, 0), names).text +
               "\\), with repetition allowed";
    if (collectionType(key) && raw.is("a") && raw.children.size() == 3) {
        const auto element = render(argument(raw,0), names).text;
        const std::string prefix = key == "Finset" ? noun("a finite subset of ","finite subsets of ") :
            key == "Set" ? noun("a subset of ","subsets of ") :
            key == "SimpleGraph" ? noun("a simple graph on ","simple graphs on ") :
            key == "Multiset" ? noun("a multiset of elements of ","multisets of elements of ") :
            noun("a list of elements of ","lists of elements of ");
        return prefix + "\\(" + element + "\\)";
    }
    if (ordinaryArrow(raw) && ordinaryArrow(raw.at(4)) && raw.at(4).at(4).is("s") &&
        raw.at(4).at(4).at(1).atom == "0")
        return noun("a relation from ","relations from ") + "\\(" + render(raw.at(3),names).text +
               "\\) to \\(" + render(raw.at(4).at(3),names).text + "\\)";
    if (ordinaryArrow(raw) && applicationOf(raw.at(4),"Finset",1))
        return noun("a family of finite subsets of ","families of finite subsets of ") +
               "\\(" + render(argument(raw.at(4),0),names).text + "\\) indexed by \\(" +
               render(raw.at(3),names).text + "\\)";
    if (raw.is("q")) return noun("a function of type ","functions of type ") + "\\(" + render(raw, names).text + "\\)";
    return noun("an element of ","elements of ") + "\\(" + render(raw, names).text + "\\)";
}

bool visiblyMentions(const Node& input, const std::string& id) {
    const auto& n = term(input);
    if (n.is("v")) return n.at(1).atom == id;
    if (n.is("a")) {
        if (visiblyMentions(n.at(1), id)) return true;
        const auto& fn = term(n.at(1));
        if ((fn.is("c") || fn.is("v")) && fn.children.size() > 3) {
            for (const auto* arg : explicitArgs(n)) if (visiblyMentions(*arg, id)) return true;
            return false;
        }
    }
    return std::any_of(n.children.begin(), n.children.end(), [&](const Node& child) {
        return child.array && visiblyMentions(child, id);
    });
}

std::string instanceAssumption(const Node& domain, const Names& names) {
    // A binary decidability instance often elaborates as two value binders
    // ending in Decidable (r a b), without the DecidableRel abbreviation.
    if (domain.is("q") && role(domain,6) == "value" && domain.at(4).is("q")) {
        const auto& second = domain.at(4);
        const auto& result = second.at(4);
        if (role(second,6) == "value" && !mentions(second.at(3),domain.at(1).atom) &&
            applicationOf(result,"Decidable",1)) {
            const auto& test = term(argument(result,0));
            if (test.is("a") && test.children.size() == 4 && test.at(1).is("v") &&
                test.at(2).is("v") && test.at(2).at(1).atom == domain.at(1).atom &&
                test.at(3).is("v") && test.at(3).at(1).atom == second.at(1).atom)
                return "Assume the relation \\(" + render(test.at(1),names).text + "\\) is decidable";
        }
    }
    const auto key = head(domain);
    if (!domain.is("a") || term(domain.at(1)).children.size() <= 3) return {};
    const auto args = explicitArgs(domain);
    const auto inMath = [&](const Node& s) { return "\\(" + render(s,names).text + "\\)"; };
    if (key == "IsRefl" && args.size() == 2) return "Assume " + inMath(domain);
    if (args.size() != 1) return {};
    const auto& subject = *args.front();
    if (key == "DecidableRel" && head(subject) == "SimpleGraph.Adj" &&
        term(subject).children.size() == 4)
        return "Assume adjacency in " + inMath(argument(subject,0)) + " is decidable";
    if (key == "DecidableRel" || key == "DecidablePred")
        return std::string("Assume the ") + (key == "DecidableRel" ? "relation " : "predicate ") +
               inMath(subject) + " is decidable";
    if (key == "DecidableEq") return "Assume equality on " + inMath(subject) + " is decidable";
    if (key == "Decidable") return "Assume " + inMath(subject) + " is decidable";
    if (key == "Fintype") return "Fix a finite enumeration of " + inMath(subject);
    if (key == "Finite") return "Assume " + inMath(subject) + " is finite";
    if (key == "Nonempty" || key == "IsEmpty" || key == "Subsingleton" || key == "IsOrderedCancelAddMonoid" || key == "IsOrderedAddMonoid" ||
        key == "IsStrictOrderedRing")
        return "Assume " + inMath(domain);
    static const std::map<std::string, std::string> structures = {
        {"AddCommMonoid","a commutative additive monoid structure"}, {"AddCommGroup","an abelian group structure"},
        {"CommSemiring","a commutative semiring structure"},
        {"Semiring","a semiring structure"}, {"Preorder","a preorder"}, {"LinearOrder","a linear order"},
        {"PartialOrder","a partial order"}, {"HasSubset","a subset relation"}
    };
    if (auto it = structures.find(key); it != structures.end())
        return "Equip " + inMath(subject) + " with " + it->second;
    return {};
}

// A carrier may be equipped with independently quantified additive and order
// structures. Group their introductions only when both use the same free carrier.
bool introduceAlgebraAndOrder(const Node& first, Names& names, const Node*& current, std::string& text) {
    const auto& second = first.at(4);
    if (!second.is("q") || role(second,5) != "instance") return false;
    const auto& algebra = first.at(3);
    const auto& order = second.at(3);
    const auto a = head(algebra), o = head(order);
    if ((a != "AddCommMonoid" && a != "CommSemiring") || (o != "LinearOrder" && o != "PartialOrder") ||
        algebra.children.size() != 3 || order.children.size() != 3) return false;
    const auto& carrier = algebra.at(2);
    if (!carrier.is("v") || !order.at(2).is("v") || carrier.at(1).atom != order.at(2).at(1).atom ||
        visiblyMentions(second, first.at(1).atom) || visiblyMentions(second.at(4), second.at(1).atom)) return false;
    checkedBinderName(names, second.at(1).atom, second.at(2).atom);
    text += "Equip \\(" + render(carrier,names).text + "\\) with " +
            (a == "AddCommMonoid" ? "a commutative additive monoid structure" : "a commutative semiring structure") +
            " and " + (o == "LinearOrder" ? "a linear order" : "a partial order") + ". ";
    current = &second.at(4);
    return true;
}

std::string introductions(const Node*& current, Names& names) {
    std::string text;
    while (current->is("q")) {
        const auto& parameter = *current;
        const auto& domain = parameter.at(3);
        const auto id = parameter.at(1).atom;
        const auto boundRole = role(parameter, 6);
        const auto variable = checkedBinderName(names, id, parameter.at(2).atom);
        bindCarrier(names,parameter,variable);
        if (role(parameter,5) == "instance") {
            if (introduceAlgebraAndOrder(parameter,names,current,text)) continue;
            const auto sentence = visiblyMentions(parameter.at(4),id) ? std::string{} : instanceAssumption(domain,names);
            if (!sentence.empty()) text += sentence + ". ";
            else if (boundRole == "proof")
                text += "Let \\(" + variable + "\\) be a proof of \\(" + render(domain,names).text + "\\). ";
            else text += "Fix a structure \\(" + variable + "\\) of type \\(" + render(domain,names).text + "\\). ";
        } else if (boundRole == "proof") {
            const auto premise = render(domain, names).text;
            const auto& quantified = term(domain);
            if (parameter.at(2).atom == "ih" && quantified.is("q") && role(quantified,7) == "prop" &&
                (role(quantified,6) != "proof" || mentions(quantified.at(4),quantified.at(1).atom))) {
                const auto label = mentions(parameter.at(4),id) ? " \\(" + variable + "\\)" : "";
                text += "Assume as induction hypothesis" + label + " that \\(" + premise + "\\). ";
            } else if (mentions(parameter.at(4), id))
                text += "Let \\(" + variable + "\\) be a proof of \\(" + premise + "\\). ";
            else text += "Assume \\(" + premise + "\\). ";
        } else {
            std::vector<std::string> symbols{"\\(" + variable + "\\)"};
            const Node* next = &parameter.at(4);
            while (next->is("q") && !boundRole.empty() && role(*next,6) == boundRole &&
                   role(*next,5) != "instance" && !names.count(next->at(1).atom) &&
                   compatibleIntroduction(domain,next->at(3))) {
                const auto other = checkedBinderName(names,next->at(1).atom,next->at(2).atom);
                bindCarrier(names,*next,other);
                symbols.push_back("\\(" + other + "\\)");
                next = &next->at(4);
            }
            const bool plural = symbols.size() > 1;
            std::string subjects = symbols.back();
            if (plural) {
                symbols.pop_back();
                subjects = join(symbols,", ") + (symbols.size() == 1 ? " and " : ", and ") + subjects;
            }
            text += "Let " + subjects + " be " + objectDescription(domain, names, plural) + ". ";
            current = next;
            continue;
        }
        current = &parameter.at(4);
    }
    return text;
}
} // namespace

bool isStandardRationalInverse(const Node& instance, const std::string& carrier) {
    return rationalStructure(instance,carrier,"Inv").standard;
}

bool isStandardRationalZero(const Node& expression, const std::string& carrier) {
    const auto& raw = term(expression);
    return isStandardRationalNumeral(raw,carrier) && naturalLiteral(raw.at(3)) == "0";
}

bool isStandardRationalNumeral(const Node& expression, const std::string& carrier) {
    const auto& raw = term(expression);
    return (carrier == "Rat" || carrier == "NNRat") && applicationOf(raw,"OfNat.ofNat",3) &&
        raw.at(2).is("c") && head(raw.at(2)) == carrier && rationalNumeral(raw,carrier).standard;
}

bool isStandardRationalOrder(const Node& expression, const std::string& carrier) {
    const auto& raw = term(expression);
    if (!raw.is("a") || raw.children.size() != 6 || !raw.at(2).is("c") || head(raw.at(2)) != carrier) return false;
    const auto relation = head(raw);
    if (relation == "LT.lt" || relation == "GT.gt") return rationalStructure(raw.at(3),carrier,"LT").standard;
    if (relation == "LE.le" || relation == "GE.ge") return rationalStructure(raw.at(3),carrier,"LE").standard;
    return false;
}

std::string checkedBinderName(Names& names, const std::string& id, const std::string& hint) {
    if (const auto found = names.find(id); found != names.end()) return found->second;
    const auto base = binderBase(hint);
    auto candidate = base;
    for (int suffix = 1; std::any_of(names.begin(), names.end(),
        [&](const auto& item) { return item.second == candidate; }); ++suffix)
        candidate = base + "_{" + std::to_string(suffix) + "}";
    names[id] = candidate;
    return candidate;
}

std::optional<std::string> checkedFormula(const Node& expression, const Names& names) {
    try { return render(expression, names).text; }
    catch (const Unsupported&) { return std::nullopt; }
}

void prepareCheckedNames(Node& document) {
    std::map<std::string, std::set<std::string>> owners;
    const auto shortName = [](const std::string& name) {
        const auto human = publicSpelling(name);
        return human.substr(human.find_last_of('.') + 1);
    };
    visitConstants(document, [&](Node& c) {
        const auto& name = c.at(1).atom;
        const auto readable = publicSpelling(name);
        if (!readable.empty() && readable.front() != '_' && readable.find("._") == std::string::npos)
            owners[shortName(name)].insert(name);
    });
    visitConstants(document, [&](Node& c) {
        const auto& name = c.at(1).atom;
        const auto leaf = shortName(name);
        const auto found = owners.find(leaf);
        if (found == owners.end() || !found->second.count(name)) return;
        if (found->second.size() == 1) c.checkedName = leaf;
        else if (name == publicSpelling(name)) c.checkedName = name;
        else c.checkedName = "local." + name.substr(9);
    });
}

std::optional<std::string> describeCheckedStatement(const Node& type) {
    try {
        Names names;
        const Node* conclusion = &type;
        const std::string preface = introductions(conclusion, names);
        if (applicationOf(*conclusion,"Eq",3)) {
            if (const auto* candidates = duplicateFreeCandidates(argument(*conclusion,0))) {
                return preface + "Start with " + candidateSource(*candidates,names) +
                    ". Each entry has no repeated elements, so it represents a finite set. "
                    "The resulting finite sets occur without repetition and form \\(" +
                    render(argument(*conclusion,1),names).text + "\\).";
            }
        }
        return preface + (preface.empty() ? "" : "Then ") + "\\(" + render(*conclusion, names).text + "\\).";
    } catch (const Unsupported&) { return std::nullopt; }
}

std::optional<std::string> describeCheckedDefinition(const std::string& fullName,
                                                      const Node& type, const Node& value) {
    try {
        Names names;
        const Node* result = &type;
        const std::string preface = introductions(result, names);
        const Node* signature = &type;
        const Node* body = &value;
        std::vector<std::string> args;
        while (signature->is("q") && body->is("l")) {
            const auto name = names.at(signature->at(1).atom);
            names[body->at(1).atom] = name;
            if (role(*signature,5) == "explicit") args.push_back(name);
            signature = &signature->at(4);
            body = &body->at(4);
        }
        if (signature->is("q")) throw Unsupported{};
        const auto lhs = identifier(fullName) + (args.empty() ? "" : "(" + join(args,", ") + ")");
        return preface + "Define \\(" + lhs + " = " + render(*body, names).text + "\\).";
    } catch (const Unsupported&) { return std::nullopt; }
}
} // namespace proof
