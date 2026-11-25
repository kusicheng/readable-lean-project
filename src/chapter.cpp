#include "chapter.hpp"
#include "expressions.hpp"
#include "incidence_titles.hpp"
#include "paper_links.hpp"
#include "statement_titles.hpp"

#include <algorithm>
#include <charconv>
#include <cctype>
#include <fstream>
#include <functional>
#include <set>
#include <sstream>
#include <stdexcept>

namespace proof {
using paper_titles::finiteMembership;
using paper_titles::titleApplication;
using paper_titles::titleVariable;

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
    if (node.isString()) return {prose(node, "theorem"), {}, {}, {}};
    fields(node, {"theorem", "alternate", "role", "title"});
    auto role = field(node, "role", node.lookup("role") != nullptr);
    if (!role.empty() && role != "theorem" && role != "lemma" && role != "corollary")
        throw std::runtime_error("Unknown mathematical result role " + role);
    return {field(node, "theorem", true), field(node, "alternate", node.lookup("alternate") != nullptr),
            role, field(node, "title", node.lookup("title") != nullptr)};
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

bool containsConstant(const Node& expr, const std::string& symbol) {
    if (expr.is("c")) return expr.at(1).atom == symbol;
    return std::any_of(expr.children.begin(),expr.children.end(),[&](const Node& child) {
        return child.array && containsConstant(child,symbol);
    });
}

// A source author can supply a conventional mathematical title in the first
// sentence of a docstring. Keep the proof text and all statements generated.
std::string documentedTitle(const std::string& doc) {
    const auto first = doc.find_first_not_of(" \t\r\n");
    if (first == std::string::npos) return {};
    const auto paragraph = doc.find("\n\n",first);
    std::string line = doc.substr(first,paragraph - first);
    for (const std::string caseTitle : {"First case of the inductive step","Second case of the inductive step"})
        if (line.compare(0,caseTitle.size()+1,caseTitle+":")==0) return caseTitle;
    const std::string version = "This is the version of **";
    if (line.compare(0,version.size(),version)==0)
        line.erase(0,version.size()-2);
    if (line.compare(0,6,"The **")==0) line.erase(0,4);
    const bool bold = line.compare(0,2,"**")==0;
    std::string direction;
    if (bold) {
        const auto close = line.find("**",2);
        if (close == std::string::npos) return {};
        const auto suffix = line.substr(close+2,line.find('.',close+2)-(close+2));
        const bool qualified = suffix.compare(0,5," for ")==0 || suffix.compare(0,4," on ")==0;
        if (suffix == ", forward direction" || suffix == ", reverse direction")
            direction = " (" + suffix.substr(2) + ")";
        line = line.substr(2,close-2);
        if (!line.empty() && line.back()=='.') line.pop_back();
        else if (qualified) line += suffix;
    } else {
        line = line.substr(0,line.find('.'));
        if (line.compare(0,4,"The ")!=0) return {};
        const auto space = line.find_last_of(" \t\r\n");
        const auto last = line.substr(space+1);
        static const std::set<std::string> names{"lemma","theorem","principle","formula","identity","inequality"};
        if (!names.count(last)) return {};
    }
    std::istringstream words(line);
    std::string word, title;
    while (words >> word) {
        // Theorem names may contain accented Latin letters, as in Turán.
        // Keep the same narrow title grammar for punctuation and source markup.
        for (std::size_t i=0; i<word.size(); ++i) {
            const auto c = static_cast<unsigned char>(word[i]);
            if ((c>='a' && c<='z') || (c>='A' && c<='Z') || c=='\'' || c=='-') continue;
            if (i+1 == word.size()) return {};
            const auto next = static_cast<unsigned char>(word[i+1]);
            if (next<0x80 || next>0xbf ||
                !((c==0xc3 && next!=0x97 && next!=0xb7) || c==0xc4 || c==0xc5)) return {};
            ++i;
        }
        if (!title.empty()) title += ' ';
        title += word;
    }
    if (title.size()>100) return {};
    return title + direction;
}

// Different formulations may share the same documented theorem name.
// Identify the indexing in the checked sum rather than its declaration name.
static std::string sumForm(const Node& statement) {
    const Node* conclusion = &statement;
    while (conclusion->is("q")) conclusion = &conclusion->at(4);
    if (!titleApplication(*conclusion,"LE.le",4)) return {};
    const auto& sum = argument(*conclusion,1);
    if (!titleApplication(sum,"Finset.sum",5)) return {};
    if (titleApplication(sum.at(2),"Finset",1)) return " (sum over sets)";
    const auto& summand = argument(sum,0);
    if (head(sum.at(2))!="Nat" || !summand.is("l")) return {};
    const auto bySize = [&](auto&& self,const Node& n) -> bool {
        if (n.is("a") && head(n)=="Finset.slice" &&
            titleVariable(argument(n,0),summand.at(1).atom)) return true;
        return std::any_of(n.children.begin(),n.children.end(),[&](const Node& child) {
            return child.array && self(self,child);
        });
    };
    return bySize(bySize,summand.at(4)) ? " (sum by set size)" : "";
}

// The checked application f(x) identifies both the map and its bound argument.
static std::string functionAt(const Node& n, const std::string& id) {
    if (n.is("a") && n.children.size()==3 && n.at(1).is("v") && titleVariable(n.at(2),id))
        return n.at(1).at(1).atom;
    return {};
}

struct FiberMeasure {
    const Node& source;
    std::string map;
    std::string weight;
};

static std::optional<FiberMeasure> fiberMeasure(const Node& quantity, const std::string& y) {
    const Node& measure = titleApplication(quantity,"Nat.cast",3) ? argument(quantity,0) : quantity;
    const bool weighted = titleApplication(quantity,"Finset.sum",5);
    if (!weighted && !titleApplication(measure,"Finset.card",2)) return {};
    const auto& filter = argument(measure,weighted ? 1 : 0);
    if (!titleApplication(filter,"Finset.filter",4)) return {};
    const auto& predicate = filter.at(3);
    if (!predicate.is("l") || !titleApplication(predicate.at(4),"Eq",3)) return {};
    const auto& eq = predicate.at(4);
    if (!titleVariable(argument(eq,0),y)) return {};
    const auto map = functionAt(argument(eq,1),predicate.at(1).atom);
    if (map.empty()) return {};
    std::string weight;
    if (weighted) {
        const auto& summand = argument(measure,0);
        if (!summand.is("l")) return {};
        weight = functionAt(summand.at(4),summand.at(1).atom);
        if (weight.empty()) return {};
    }
    return FiberMeasure{argument(filter,0),map,weight};
}

static std::string fiberSetting(const Node& statement, const Node& witness, const FiberMeasure& fiber) {
    const auto& claim = witness.at(4);
    const auto& y = witness.at(1).atom;
    const bool bounded = titleApplication(claim,"And",2);
    if (bounded) {
        const auto& mem = argument(claim,1);
        if (!finiteMembership(mem) || !titleVariable(argument(mem,0),y) || !argument(mem,1).is("v") ||
            !fiber.source.is("v")) return {};
    }
    for (const Node* binder=&statement; binder->is("q"); binder=&binder->at(4)) {
        const auto& hypothesis = binder->at(3);
        if (!bounded) {
            if (titleApplication(fiber.source,"Finset.univ",2) && titleApplication(hypothesis,"Fintype",1) &&
                witness.at(3).is("v") && titleVariable(argument(hypothesis,0),witness.at(3).at(1).atom))
                return " for maps between finite types";
            continue;
        }
        if (!hypothesis.is("q") || !hypothesis.at(4).is("q")) continue;
        const auto& target = argument(argument(claim,1),1).at(1).atom;
        const auto& source = fiber.source.at(1).atom;
        const auto& index = hypothesis.at(1).atom;
        const auto& premise = hypothesis.at(4).at(3);
        const auto& result = hypothesis.at(4).at(4);
        if (finiteMembership(premise) && titleVariable(argument(premise,1),source) &&
            titleVariable(argument(premise,0),index) && finiteMembership(result) &&
            titleVariable(argument(result,1),target) && functionAt(argument(result,0),index)==fiber.map)
            return " for maps into the target";
        if (fiber.weight.empty() || !titleApplication(premise,"Not",1) || !titleApplication(result,"LE.le",4))
            continue;
        const auto& outside = argument(premise,0);
        if (!finiteMembership(outside) || !titleVariable(argument(outside,1),target) ||
            !titleVariable(argument(outside,0),index)) continue;
        for (const bool nonpositive : {true,false}) {
            const auto& zero = argument(result,nonpositive ? 0 : 1);
            if (!titleApplication(zero,"OfNat.ofNat",3) || !zero.at(3).is("n") || zero.at(3).at(1).atom!="0" ||
                !titleApplication(zero.at(4),"Zero.toOfNat0",2)) continue;
            const auto outsideFiber = fiberMeasure(argument(result,nonpositive ? 1 : 0),index);
            if (outsideFiber && titleVariable(outsideFiber->source,source) && outsideFiber->map==fiber.map &&
                outsideFiber->weight==fiber.weight)
                return nonpositive ? " when fibers outside the target have nonpositive weight" :
                                     " when fibers outside the target have nonnegative weight";
        }
    }
    return {};
}

// A title may use a Hamiltonian hypothesis only for the walk that it describes.
// The theorem name, the printed variable name and the order of hypotheses can all change.
static std::string hamiltonianSubject(const Node& statement, const Node& subject) {
    if (!subject.is("v")) return {};
    for (const Node* q=&statement; q->is("q"); q=&q->at(4)) {
        const auto& h = q->at(3);
        if (!h.is("a") || !titleVariable(argument(h,0),subject.at(1).atom)) continue;
        if (titleApplication(h,"SimpleGraph.Walk.IsHamiltonian",6)) return "Hamiltonian path";
        if (titleApplication(h,"SimpleGraph.Walk.IsHamiltonianCycle",5)) return "Hamiltonian cycle";
        if (titleApplication(h,"SimpleGraph.IsHamiltonian",4)) return "Hamiltonian graph";
        if (titleApplication(h,"SimpleGraph.Walk.IsPath",5)) return "path";
    }
    return {};
}

static std::string hamiltonianTitle(const Node& statement, const Node& claim) {
    if (!claim.is("a")) return {};
    const auto& last = argument(claim,0);
    const bool path = titleApplication(claim,"SimpleGraph.Walk.IsHamiltonian",6);
    const bool cycle = titleApplication(claim,"SimpleGraph.Walk.IsHamiltonianCycle",5);
    if (path || cycle) {
        if (titleApplication(last,"SimpleGraph.Walk.map",8))
            return path ? "When the image walk is a Hamiltonian path" :
                          "When the image walk is a Hamiltonian cycle";
        if (path && hamiltonianSubject(statement,last) == "path")
            return "A sufficient condition for a path to be Hamiltonian";
    }
    if (titleApplication(claim,"SimpleGraph.Walk.IsPath",5) &&
        hamiltonianSubject(statement,last) == "Hamiltonian path")
        return "Absence of repeated vertices in a Hamiltonian path";
    if (titleApplication(claim,"SimpleGraph.Walk.IsCycle",4) &&
        hamiltonianSubject(statement,last) == "Hamiltonian cycle")
        return "The cycle property of a Hamiltonian cycle";
    if (titleApplication(claim,"SimpleGraph.Connected",2) &&
        hamiltonianSubject(statement,last) == "Hamiltonian graph")
        return "Connectivity of a Hamiltonian graph";
    if (titleApplication(claim,"SimpleGraph.IsHamiltonian",4) && last.is("v")) {
        for (const Node* q=&statement; q->is("q"); q=&q->at(4)) {
            const auto& h = q->at(3);
            if (titleApplication(h,"LE.le",4) && titleApplication(h.at(2),"SimpleGraph",1) &&
                titleApplication(h.at(3),"SimpleGraph.instLE",1) &&
                titleVariable(argument(h,0),last.at(1).atom) &&
                hamiltonianSubject(statement,argument(h,1)) == "Hamiltonian graph")
                return "Hamiltonicity under edge inclusion";
        }
    }
    if (titleApplication(claim,"Iff",2)) {
        const auto& lhs = argument(claim,1);
        if (!lhs.is("a") || !argument(lhs,0).is("v")) return {};
        const auto& walk = argument(lhs,0).at(1).atom;
        if (titleApplication(lhs,"SimpleGraph.Walk.IsHamiltonian",6) && last.is("q")) {
            const auto& mem = last.at(4);
            if (titleApplication(mem,"Membership.mem",5) && titleApplication(mem.at(4),"List.instMembership",1) &&
                titleApplication(mem.at(5),"SimpleGraph.Walk.support",5) &&
                titleVariable(argument(mem.at(5),0),walk) && titleVariable(argument(mem,0),last.at(1).atom))
                return "A vertex-coverage criterion for a Hamiltonian path";
        }
        if (titleApplication(lhs,"SimpleGraph.Walk.IsHamiltonianCycle",5) && titleApplication(last,"And",2) &&
            titleApplication(argument(last,1),"SimpleGraph.Walk.IsCycle",4) &&
            titleVariable(argument(argument(last,1),0),walk)) {
            const auto& property = argument(last,0);
            if (titleApplication(property,"SimpleGraph.Walk.IsHamiltonian",6) &&
                titleApplication(argument(property,0),"SimpleGraph.Walk.tail",5) &&
                titleVariable(argument(argument(property,0),0),walk))
                return "Characterizing Hamiltonian cycles by their tails";
            if (property.is("q") && titleApplication(property.at(4),"Eq",3)) {
                const auto& count = argument(property.at(4),1);
                if (titleApplication(count,"List.count",4) &&
                    titleApplication(count.at(3),"instBEqOfDecidableEq",2) &&
                    titleApplication(argument(count,0),"List.tail",2)) {
                    const auto& vertices = argument(argument(count,0),0);
                    if (titleApplication(vertices,"SimpleGraph.Walk.support",5) && titleVariable(argument(vertices,0),walk))
                        return "Characterizing Hamiltonian cycles by vertex counts";
                }
            }
        }
    }
    if (titleApplication(claim,"Membership.mem",5) && titleApplication(claim.at(4),"List.instMembership",1) &&
        titleApplication(claim.at(5),"SimpleGraph.Walk.support",5)) {
        const auto subject = hamiltonianSubject(statement,argument(claim.at(5),0));
        if (!subject.empty()) return "Vertices visited by a " + subject;
    }
    if (!titleApplication(claim,"Eq",3)) return {};
    const auto& lhs = argument(claim,1);
    if (titleApplication(lhs,"SimpleGraph.Walk.length",5)) {
        const auto subject = hamiltonianSubject(statement,argument(lhs,0));
        if (!subject.empty()) return "Length of a " + subject;
    }
    if (titleApplication(lhs,"List.toFinset",3) && titleApplication(argument(lhs,0),"SimpleGraph.Walk.support",5)) {
        const auto subject = hamiltonianSubject(statement,argument(argument(lhs,0),0));
        if (!subject.empty()) return "The vertex set of a " + subject;
    }
    if (titleApplication(lhs,"List.count",4) && titleApplication(lhs.at(3),"instBEqOfDecidableEq",2) &&
        titleApplication(argument(lhs,0),"SimpleGraph.Walk.support",5)) {
        const auto& vertices = argument(lhs,0);
        const auto subject = hamiltonianSubject(statement,argument(vertices,0));
        if (!subject.empty()) {
            const auto& start = vertices.at(4);
            return (start.is("v") && titleVariable(lhs.at(4),start.at(1).atom) ?
                    "Visits to the starting vertex of a " : "Visits to a specified vertex of a ") + subject;
        }
    }
    return {};
}

static std::string resultTitle(const Node& record, bool sourcePaper) {
    const auto& name = record.at(0).atom;
    const auto leaf = name.substr(name.find_last_of('.')+1);
    // The hypotheses are printed in the statement. Names that encode them as
    // repeated "of ..." clauses do not need to reproduce them in the heading.
    const auto summary = leaf.substr(0,leaf.find("_of_"));
    const auto sourceTitle = [&] {
        // Source identifiers also name anonymous examples, internal aliases
        // and arbitrary student labels. The numbered statement stands alone
        // when its mathematics does not supply a useful optional caption.
        return sourcePaper ? std::string{} : declarationTitle(summary);
    };
    if (summary.size()>5 && summary.compare(summary.size()-5,5,"_cond")==0 && summary.size()<leaf.size()) {
        const auto condition = declarationTitle(summary.substr(0,summary.size()-5)) + " condition";
        const auto operation = leaf.substr(summary.size()+4);
        if (operation=="erase") return condition + " after deletion";
        if (operation=="restrict") return condition + " for a restricted family";
        if (operation=="compl") return condition + " on the complement";
    }
    const Node* conclusion = &record.at(1);
    while (conclusion->is("q")) conclusion = &conclusion->at(4);
    if (const auto title = paper_titles::parityTitle(record.at(1),*conclusion); !title.empty()) return title;
    if (const auto title = paper_titles::matchingCharacterization(*conclusion); !title.empty()) return title;
    if (const auto title = paper_titles::neighborhoodTitle(*conclusion); !title.empty()) return title;
    if (titleApplication(*conclusion,"Function.Surjective",3) &&
        titleApplication(argument(*conclusion,0),"SimpleGraph.Subgraph.IsMatching.toEdge",4))
        return "Every matching edge is the edge assigned to some vertex";
    if (titleApplication(*conclusion,"Eq",3)) {
        if (const auto title = paper_titles::enumerationTitle(argument(*conclusion,1),argument(*conclusion,0)); !title.empty())
            return title;
        if (const auto title = paper_titles::uniquenessTitle(record.at(1),*conclusion); !title.empty()) return title;
        if (const auto title = paper_titles::sequenceTitle(*conclusion); !title.empty()) return title;
        if (paper_titles::sameTitleTerm(argument(*conclusion,1),argument(*conclusion,0)))
            return "Reflexivity of equality";
    }
    if (const auto title = hamiltonianTitle(record.at(1),*conclusion); !title.empty()) return title;
    if (const auto bounds = paper_titles::incidenceBounds(record.at(1),*conclusion); !bounds.empty()) return "Double counting" + bounds;
    if (const auto sparse = paper_titles::sparseFiberTitle(record.at(1),*conclusion); !sparse.empty()) return sparse;
    const auto comparison = head(*conclusion);
    const bool weak = comparison == "LE.le", strict = comparison == "LT.lt", equal = comparison == "Eq";
    if ((weak || strict || equal) && conclusion->is("a") && conclusion->children.size() >= 4) {
        const auto& a = argument(*conclusion,1);
        const auto& b = argument(*conclusion,0);
        const auto left = head(a), right = head(b);
        if (equal && left == right && containsConstant(a,"Finset.bipartiteAbove") &&
            containsConstant(b,"Finset.bipartiteBelow")) {
            if (left == "Finset.prod") return "A product over incidences in two orders";
            if (left == "Finset.sum") return containsConstant(a,"Finset.card") ?
                "Counting incidences by rows and columns" : "A sum over incidences in two orders";
        }
        const bool sizes = left == right && (left == "Fintype.card" || left == "Finset.card");
        if (sizes && weak && leaf.find("leftTotal") != std::string::npos)
            return "A cardinality bound from a left-total relation";
        if (sizes && weak && leaf.find("rightTotal") != std::string::npos)
            return "A cardinality bound from a right-total relation";
        const bool weighted = left == right && (left == "HSMul.hSMul" || left == "HMul.hMul") &&
            containsConstant(a,"Finset.card") && containsConstant(b,"Finset.card");
        if (weighted) return equal ? "An equality of weighted cardinalities" :
            strict ? "A strict bound on weighted cardinalities" : "A bound on weighted cardinalities";
        if (equal && left == "Finset.card" && containsConstant(a,"Finset.powerset") && right == "HPow.hPow")
            return "The number of subsets of a finite set";
        if (equal && left == "Finset.card" && containsConstant(a,"Finset.powersetCard") && right == "Nat.choose")
            return "The number of subsets of a prescribed size";
    }
    if (head(*conclusion) == "Exists") {
        if (const auto title = paper_titles::congruentPairTitle(*conclusion); !title.empty()) return title;
        const auto& predicate = term(argument(*conclusion,0));
        if (predicate.is("l")) {
            const Node* condition = &predicate.at(4);
            if (head(*condition) == "And") condition = &argument(*condition,0);
            const auto relation = head(*condition);
            const auto& id = predicate.at(1).atom;
            const auto contains = [&](auto&& self,const Node& n) -> bool {
                if (n.is("v")) return n.at(1).atom == id;
                for (const auto& c : n.children) if (c.array && self(self,c)) return true;
                return false;
            };
            if ((relation == "LT.lt" || relation == "LE.le") && condition->children.size() >= 4) {
                const bool left = contains(contains,argument(*condition,1));
                const bool right = contains(contains,argument(*condition,0));
                if (left != right) {
                    const auto& quantity = argument(*condition,left ? 1 : 0);
                    const auto fiber = fiberMeasure(quantity,id);
                    if (!fiber && leaf.find("fiber")==std::string::npos) return sourceTitle();
                    const bool sum = fiber ? !fiber->weight.empty() : containsConstant(quantity,"Finset.sum");
                    if (!sum && !containsConstant(quantity,"Finset.card") &&
                        !containsConstant(quantity,"Fintype.card")) return sourceTitle();
                    std::string title = "A fiber ";
                    title += sum ? "with weight " : "with size ";
                    if (relation == "LT.lt") title += left ? "below" : "above";
                    else title += left ? "at most" : "at least";
                    if (!fiber) return title + " the bound";
                    const bool naturalSize = !sum && condition->children.size()==6 &&
                                             head(condition->at(2))=="Nat";
                    title += naturalSize ? " the natural-number bound" : " the bound";
                    return title + fiberSetting(record.at(1),predicate,*fiber);
                }
            }
        }
    }
    return sourceTitle();
}

Chapter readChapter(const std::filesystem::path& path) {
    const auto root = read(path);
    fields(root, {"title", "introduction", "terminology", "glossary", "sections",
                  "symbols", "prerequisites", "format"});
    Chapter chapter;
    chapter.title = field(root, "title", true);
    chapter.introduction = field(root, "introduction");
    if (root.lookup("format")) {
        const auto format = field(root, "format", true);
        if (format != "paper" && format != "chapter") throw std::runtime_error("Unknown document format");
        chapter.paper = format == "paper";
    }
    if (const auto* titles = root.lookup("prerequisites")) {
        if (!titles->isObject) throw std::runtime_error("Expected a dictionary of prerequisite titles");
        for (const auto& entry : titles->object)
            chapter.prerequisiteTitles.emplace(entry.first, field(*titles, entry.first, true));
    }
    if (const auto* symbols = root.lookup("symbols")) {
        if (!symbols->isObject) throw std::runtime_error("Expected a symbol dictionary");
        std::set<std::string> used;
        for (const auto& entry : symbols->object) {
            const auto label = prose(entry.second, "symbol");
            if (label.empty() || !std::all_of(label.begin(), label.end(),
                    [](char c) { return (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z'); }))
                throw std::runtime_error("A mathematical symbol must contain only ASCII letters");
            if (!used.insert(label).second) throw std::runtime_error("Duplicate mathematical symbol " + label);
            chapter.symbols.emplace(entry.first, label);
        }
    }
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

void applyChapterSymbols(Node& checked, const Chapter& chapter) {
    if (chapter.symbols.empty()) return;
    const auto& catalog = checked.at(3);
    if (!catalog.array) throw std::runtime_error("Missing checked symbol catalog");
    std::map<std::string, std::size_t> arities;
    for (const auto& entry : catalog.children) {
        const auto& digits = entry.at(1).atom;
        std::size_t arity;
        const auto end = digits.data() + digits.size();
        const auto parsed = std::from_chars(digits.data(), end, arity);
        if (parsed.ec != std::errc{} || parsed.ptr != end)
            throw std::runtime_error("Invalid checked symbol arity");
        arities.emplace(entry.at(0).atom, arity);
    }
    for (const auto& entry : chapter.symbols) {
        if (!arities.count(entry.first))
            throw std::runtime_error("Expected a referenced natural-number definition: " + entry.first);
    }
    const auto annotate = [&](auto&& self, Node& node) -> void {
        if (!node.array) return;
        if (node.is("a") || node.is("c")) {
            const auto name = head(node);
            const auto symbol = chapter.symbols.find(name);
            if (symbol != chapter.symbols.end() &&
                arities.at(name) == (node.is("a") ? node.children.size() - 2 : 0))
                node.mathSymbol = symbol->second;
        }
        for (auto& child : node.children) self(self, child);
    };
    // Source traces, private helpers and constructor signatures can repeat the
    // same formula as a theorem statement and must use the same notation.
    for (const auto i : {0u,1u,4u,5u,6u,9u})
        if (i<checked.children.size()) annotate(annotate,checked.children[i]);
}

std::string declarationTitle(const std::string& name) {
    if (name == "Finset.powersetCard") return "Subsets of prescribed cardinality";
    if (name == "SimpleGraph.Walk.IsHamiltonian") return "Hamiltonian paths";
    if (name == "SimpleGraph.IsHamiltonian") return "Hamiltonian graphs";
    const auto leaf = name.substr(name.find_last_of('.') + 1);
    std::vector<std::string> words;
    std::string word;
    const auto flush = [&] {
        if (!word.empty()) words.push_back(word);
        word.clear();
    };
    for (std::size_t i = 0; i < leaf.size(); ++i) {
        const unsigned char c = leaf[i];
        // A subscript digit in a declaration name identifies a variant.
        // Use a text-font digit in the heading; formulas keep their subscripts.
        if (c==0xe2 && i+2<leaf.size() && static_cast<unsigned char>(leaf[i+1])==0x82) {
            const auto digit = static_cast<unsigned char>(leaf[i+2]);
            if (digit>=0x80 && digit<=0x89) {
                word += static_cast<char>('0'+digit-0x80);
                i += 2;
                continue;
            }
        }
        if (c == '_') { flush(); continue; }
        if (i > 0 && std::isupper(c) && std::islower(static_cast<unsigned char>(leaf[i-1])))
            flush();
        word += static_cast<char>(std::tolower(c));
    }
    flush();
    static const std::map<std::string, std::string> terms{
        {"le", "at most"}, {"lt", "less than"}, {"ge", "at least"}, {"gt", "greater than"},
        {"eq", "equals"}, {"ne", "differs from"}, {"iff", "if and only if"},
        {"mem", "membership"}, {"dvd", "divisibility"}, {"card", "cardinality"},
        {"nodup", "without repetitions"}, {"mul", "product"}, {"succ", "successor"},
        {"inj", "injectivity"}, {"add", "sum"}, {"sub", "difference"}, {"pow", "power"},
        {"funext","function extensionality"}, {"coe","coercion"}, {"comm","commutation"},
        {"congr","congruence"}, {"nsmul","repeated addition"}, {"prod","product"},
        {"pos","positivity"}, {"nonpos","nonpositive"}, {"nonneg","nonnegative"},
        {"ssubsets","proper subsets"}, {"powerset","power set"}, {"univ","whole space"},
        {"const","constant"}
    };
    std::string result;
    for (const auto& token : words) {
        if (!result.empty()) result += ' ';
        const auto it = terms.find(token);
        result += it == terms.end() ? token : it->second;
    }
    if (!result.empty()) result[0] = static_cast<char>(std::toupper(static_cast<unsigned char>(result[0])));
    return result;
}

std::string prerequisiteLabel(const std::string& name) {
    static constexpr char digits[] = "0123456789abcdef";
    std::string key = "premise:";
    for (unsigned char c : name) {
        key += digits[c / 16];
        key += digits[c % 16];
    }
    return key;
}

std::string prerequisiteReference(const Node& entry) {
    const auto key = prerequisiteLabel(entry.at(0).atom);
    const auto numbered = numberedReference("Prerequisite~P",key);
    if (entry.children.size() < 4) return numbered;
    auto title = documentedTitle(entry.at(3).atom);
    if (title.empty()) return numbered;
    if (title.compare(0,4,"The ")==0) title[0] = 't';
    return paperLink(key,"\\emph{" + escapeLatex(title) + "}") + " (" + numbered + ")";
}

// Automatically sized TeX delimiters form unbreakable boxes. Use ordinary
// delimiters in long inline formulas so TeX can wrap at their operators.
std::string wrapPaperMath(std::string text) {
    // Keep amsthm's end-of-proof mark on the final text line. A blank
    // paragraph before the environment ends otherwise strands it on its own.
    for (std::size_t end=0; (end=text.find("\\end{proof}",end))!=std::string::npos; ) {
        const auto last=text.find_last_not_of(" \t\r\n",end-1);
        if (last!=std::string::npos) {
            text.replace(last+1,end-last-1,"\n");
            end=last+2;
        }
        end+=sizeof("\\end{proof}")-1;
    }
    // The checked formula printer uses this atom only for the standard
    // rational reciprocal. Look in prerequisites as well as proof bodies.
    std::string conventions;
    if (text.find("\\mathord{\\frac{1}{") != std::string::npos)
        conventions += "\nFor rational reciprocals we use the convention \\(1/0 = 0\\).\n\n";
    if (text.find("\\operatorname{prefix}_{") != std::string::npos)
        conventions += "\nThe prefix \\(\\operatorname{prefix}_{p}(v)\\) follows the walk \\(p\\) through "
                       "its first visit to \\(v\\). In \\(q \\mathbin{\\Vert} r\\), we follow \\(q\\) and then \\(r\\).\n\n";
    if (text.find("\\operatorname{tail}(") != std::string::npos &&
        text.find("\\operatorname{Walk}_{") != std::string::npos)
        conventions += "\nFor a walk \\(p\\) with at least one edge, \\(\\operatorname{tail}(p)\\) "
                       "is the walk after its first edge. A walk of length zero is its own tail.\n\n";
    if (text.find("\\operatorname{incl}_{") != std::string::npos)
        conventions += "\nThe inclusion \\(\\operatorname{incl}_{G,H}\\) of graphs on the same vertex set "
                       "fixes each vertex and carries each edge of \\(G\\) to the same edge in \\(H\\).\n\n";
    if (!conventions.empty()) {
        const auto abstractEnd = text.find("\\end{abstract}\n");
        const std::string heading = abstractEnd == std::string::npos ? "\\maketitle\n" : "\\end{abstract}\n";
        const auto end = text.find(heading);
        if (end != std::string::npos)
            text.insert(end + heading.size(),conventions);
    }
    std::size_t start = 0;
    while ((start = text.find("\\(",start)) != std::string::npos) {
        const auto end = text.find("\\)",start+2);
        if (end == std::string::npos) break;
        auto segment = text.substr(start+2,end-start-2);
        if (segment.size() > 110) {
            for (const std::string command : {"\\left","\\right"}) {
                std::size_t pos = 0;
                while ((pos=segment.find(command,pos)) != std::string::npos) {
                    const auto after = pos+command.size();
                    if (after < segment.size() && segment[after] == '.')
                        segment.erase(pos,command.size()+1);
                    else if (after < segment.size() && std::string("()[]|\\").find(segment[after]) != std::string::npos)
                        segment.erase(pos,command.size());
                    else pos = after;
                }
            }
            for (std::size_t i=0; (i=segment.find(", ",i)) != std::string::npos; i+=15)
                if (i==0 || segment[i-1]!='\\') segment.insert(i+1,"\\allowbreak{}");
            text.replace(start+2,end-start-2,segment);
        }
        start += segment.size()+4;
    }
    return text;
}

static bool hamiltonianSingletonConvention(const Node& equation) {
    const Node* eq = &equation;
    while (eq->is("q")) eq = &eq->at(4);
    if (!titleApplication(*eq,"Eq",3)) return false;
    const auto& graph = argument(*eq,1);
    const auto& implication = argument(*eq,0);
    if (!titleApplication(graph,"SimpleGraph.IsHamiltonian",4) || !graph.at(2).is("v") ||
        !implication.is("q") || !titleApplication(implication.at(3),"Ne",3)) return false;
    const auto& size = argument(implication.at(3),1);
    const auto& one = argument(implication.at(3),0);
    return titleApplication(size,"Fintype.card",2) && titleVariable(size.at(2),graph.at(2).at(1).atom) &&
           titleApplication(one,"OfNat.ofNat",3) && one.at(3).is("n") && one.at(3).at(1).atom == "1" &&
           titleApplication(one.at(4),"instOfNatNat",1);
}

// The adapter checks the decision procedure's own branch equation and the
// constructor's injectivity theorem. Tie that evidence to this exact public
// alias before explaining its computation in place of a private helper name.
static std::optional<std::pair<std::string,std::string>> recordEqualityTest(const Node& entry,
                                                                             const Node& checked) {
    if (entry.children.size()<4 || checked.children.size()<=9) return {};
    const auto& certificate = entry.at(3);
    if (!certificate.array || certificate.children.size()!=7 || certificate.at(0).atom!="record-equality-test" ||
        entry.at(1).children.size()!=1 || entry.at(2).children.size()!=1 ||
        entry.at(2).at(0).atom!=certificate.at(1).atom) return {};
    const auto& type = certificate.at(2).atom;
    const auto& ctor = certificate.at(3).atom;
    const auto& field = certificate.at(4).atom;
    if (certificate.at(5).atom!=ctor+".injEq") return {};
    const Node* eq = &entry.at(1).at(0);
    while (eq->is("q")) eq = &eq->at(4);
    if (!titleApplication(*eq,"Eq",3) || !titleApplication(eq->at(2),"DecidableEq",1) ||
        head(argument(eq->at(2),0))!=type || head(eq->at(3))!=entry.at(0).atom) return {};
    const auto& alias = eq->at(4);
    const auto privateName = head(alias);
    if (privateName.compare(0,9,"_private.")!=0 || certificate.at(6).atom!=privateName+".eq_1" ||
        alias.is("a")!=eq->at(3).is("a")) return {};
    if (alias.is("a") && (alias.children.size()!=eq->at(3).children.size() ||
        !std::equal(alias.children.begin()+2,alias.children.end(),eq->at(3).children.begin()+2,
                    paper_titles::sameTitleTerm))) return {};
    for (const auto& constructor : checked.at(9).children) {
        if (constructor.at(0).atom!=ctor || constructor.children.size()<4 || constructor.at(3).atom!="object") continue;
        std::vector<const Node*> binders;
        const Node* result = &constructor.at(1);
        while (result->is("q")) { binders.push_back(result); result=&result->at(4); }
        const auto& fields = constructor.at(2).children;
        if (head(*result)!=type || fields.empty() || fields.size()>binders.size()) return {};
        const Node* data = nullptr;
        for (std::size_t i=0; i<fields.size(); ++i) {
            const auto* binder = binders[binders.size()-fields.size()+i];
            if (binder->children.size()<=6 || fields[i].atom!=binder->at(2).atom) return {};
            if (binder->at(6).atom=="proof") continue;
            if (data || fields[i].atom!=field) return {};
            data = binder;
        }
        if (!data) return {};
        auto subject = declarationTitle(field);
        if (!subject.empty()) subject[0]=static_cast<char>(std::tolower(static_cast<unsigned char>(subject[0])));
        const bool lists = titleApplication(data->at(3),"List",1) && field=="toList";
        const auto comparison = lists ? std::string("Compare the underlying lists.") :
            "Compare the values of the \\emph{" + escapeLatex(subject) + "} field.";
        return std::make_pair("Equality test (" + escapeLatex(declarationTitle(type)) + ")",
            comparison + " Two records are equal exactly when these values agree.");
    }
    return {};
}

std::size_t writePaperDefinitions(std::ostream& output, const Node& checked, const Chapter& chapter,
                                  DefinitionRules& rules) {
    if (checked.children.size() < 5) return 0;
    std::map<std::string, const Node*> definitions;
    for (const auto& entry : checked.at(4).children)
        definitions.emplace(entry.at(0).atom, &entry);
    std::set<std::string> visited;
    std::vector<std::string> order;
    std::set<std::string> omittedSplitters;
    const auto visit = [&](auto&& self, const Node& node) -> void {
        if (node.is("c")) {
            const auto& name = node.at(1).atom;
            if (omittedSplitters.count(name)) return;
            const auto it = definitions.find(name);
            if (it != definitions.end() && visited.insert(name).second) {
                self(self, it->second->at(1));
                order.push_back(name);
            }
            return;
        }
        for (const auto& child : node.children)
            if (child.array) self(self, child);
    };
    for (const auto& record : checked.at(0).children) visit(visit, record.at(1));
    // A local mathematical function may enter only in an intermediate
    // assertion, including an assertion in a private helper's proof.
    // The adapter's definition catalog excludes matchers and projections.
    const auto statementDefinitions=visited;
    std::map<std::string,const Node*> privateDefinitions;
    const auto generatedSplitter=[&](const std::string& name) {
        // Lean puts a generated splitter under its registered matcher's name,
        // adding a module-private prefix when the matcher itself is public.
        for (const auto& row:checked.at(2).children) {
            const auto splitter=row.at(0).atom+".splitter";
            if (name==splitter || (name.size()>splitter.size() &&
                name.compare(name.size()-splitter.size()-1,splitter.size()+1,"."+splitter)==0)) return true;
        }
        return false;
    };
    for (const auto& [name,entry]:definitions) {
        if (name.rfind("_private.",0)!=0 || visited.count(name)) continue;
        if (generatedSplitter(name)) omittedSplitters.insert(name);
        else privateDefinitions.emplace(name,entry);
    }
    if (!privateDefinitions.empty()) {
        std::map<std::string,const Node*> helpers;
        if (checked.children.size()>6) for (const auto& row:checked.at(6).children)
            helpers.emplace(row.at(0).atom,&row);
        std::set<std::string> reached;
        const auto visible=[&](auto&& self,const Node& expr)->void {
            if (expr.is("c")) {
                if (privateDefinitions.count(expr.at(1).atom)) visit(visit,expr);
            } else if (expr.is("a")) {
                const auto& fn=expr.at(1);
                self(self,fn);
                if ((fn.is("v") || fn.is("c")) && fn.children.size()>3) {
                    for (const auto& position:fn.at(3).children) {
                        const auto& digits=position.atom;
                        std::size_t index=0;
                        const auto end=digits.data()+digits.size();
                        const auto result=std::from_chars(digits.data(),end,index);
                        if (result.ec==std::errc{} && result.ptr==end && index<expr.children.size()-2)
                            self(self,expr.at(2+index));
                    }
                } else for (std::size_t i=2;i<expr.children.size();++i) self(self,expr.at(i));
            } else if (expr.is("q") || expr.is("l") || expr.is("t")) {
                self(self,expr.at(3));
                self(self,expr.at(4));
                if (expr.is("t")) self(self,expr.at(5));
            } else if (expr.is("proj")) self(self,expr.at(3));
        };
        const auto walk=[&](auto&& self,const Node& node)->void {
            if (node.is("p")) {
                visible(visible,node.at(1));
                self(self,node.at(2));
            } else if (node.is("c")) {
                const auto it=helpers.find(node.at(1).atom);
                if (it!=helpers.end() && reached.insert(it->first).second) {
                    visible(visible,it->second->at(1));
                    self(self,it->second->at(2));
                }
            } else if (node.is("l") || node.is("t")) {
                visible(visible,node.at(3));
                self(self,node.at(4));
                if (node.is("t")) self(self,node.at(5));
            } else if (node.is("a")) {
                self(self,node.at(1));
                // A constructive witness is printed even for a constant predicate.
                if (head(node)=="Exists.intro" && node.children.size()==6) visible(visible,node.at(4));
                if (head(node)=="Nonempty.intro" && node.children.size()==4) visible(visible,node.at(3));
                std::vector<const Node*> premises;
                if (proofArguments(node,premises))
                    for (const auto* premise:premises) self(self,*premise);
                else for (std::size_t i=2;i<node.children.size();++i) self(self,node.at(i));
            } else if (node.is("proj")) self(self,node.at(3));
        };
        for (const auto& record:checked.at(0).children) walk(walk,record.at(2));
    }
    if (order.empty()) return 0;
    std::size_t incomplete = 0;
    std::size_t ordinal = 0;
    output << "\\section*{Definitions}\n";
    for (const auto& name : order) {
        const auto& entry = *definitions.at(name);
        const auto decision = recordEqualityTest(entry,checked);
        const auto alias = chapter.symbols.find(name);
        const auto title = decision ? decision->first : escapeLatex(declarationTitle(name));
        output << "\\paragraph{" << title;
        if (alias != chapter.symbols.end() && (!chapter.automaticLayout || alias->second != name.substr(name.find_last_of('.')+1)))
            output << " (\\(" << alias->second << "\\))";
        output << ".} ";
        const auto& equations = entry.at(1).children;
        const auto* names = entry.children.size()>2 ? &entry.at(2).children : nullptr;
        if (names && names->size()!=equations.size())
            throw std::runtime_error("Mismatched defining equation names for " + name);
        const bool numbered = names && std::any_of(names->begin(),names->end(),[](const Node& n) {
            return !n.atom.empty();
        });
        std::map<std::string,std::size_t> seen;
        bool missing = false;
        for (std::size_t i=0; i<equations.size(); ++i) {
            const auto& equation = equations[i];
            auto line = decision ? std::optional<std::string>(decision->second) : std::nullopt;
            if (!line && !statementDefinitions.count(name) && privateDefinitions.count(name))
                line=describeCheckedRationalQuotient(equation);
            if (!line) line=describeCheckedStatement(equation,true);
            if (!line) { missing = true; continue; }
            const auto [it,inserted] = seen.emplace(*line,ordinal+1);
            if (inserted) {
                if (numbered) {
                    ++ordinal;
                    const auto key = "defeq:" + std::to_string(ordinal);
                    output << "\\par\\noindent\\refstepcounter{definingequation}\\label{" << key
                           << "}\\paperlineanchor{" << key << "}\\textup{(" << paperLink(key,"D" + std::to_string(ordinal)) << ")} ";
                }
                output << *line << '\n';
                if (name == "SimpleGraph.IsHamiltonian" && hamiltonianSingletonConvention(equation))
                    output << "In particular, every graph on a single vertex is Hamiltonian by this convention.\n";
            }
            if (numbered && !(*names)[i].atom.empty())
                rules.emplace((*names)[i].atom,DefiningEquation{&equation,
                    numberedReference("defining equation~D","defeq:" + std::to_string(it->second))});
        }
        if (missing || seen.empty()) {
            ++incomplete;
            output << "Some defining equations could not be rendered.\n";
        }
        output << '\n';
    }
    return incomplete;
}

static void theoremDependencies(const Node& expression, const std::map<std::string, const Node*>& records,
                         const std::map<std::string,const Node*>& helpers, std::set<std::string>& expanded,
                         std::set<std::string>& dependencies) {
    const auto& raw = term(expression);
    if (raw.is("c")) {
        const auto& name = raw.at(1).atom;
        if (records.count(name)) dependencies.insert(name);
        else if (auto it = helpers.find(name); it != helpers.end() && expanded.insert(name).second)
            theoremDependencies(*it->second,records,helpers,expanded,dependencies);
    } else {
        for (const auto& child : raw.children) {
            if (child.array) theoremDependencies(child,records,helpers,expanded,dependencies);
        }
    }
}

static std::map<std::string,const Node*> proofHelpers(const Node& document) {
    std::map<std::string,const Node*> helpers;
    if (document.children.size() > 6)
        for (const auto& helper : document.at(6).children)
            helpers.emplace(helper.at(0).atom,&helper.at(2));
    return helpers;
}

std::string selectedAlternate(const Node& record) {
    return record.children.size() > 3 ? record.at(3).atom : "";
}

std::vector<const Node*> orderTheorems(const Node& document, const Chapter* chapter) {
    const auto& records = document.at(0);
    const auto helpers = proofHelpers(document);
    std::map<std::string, const Node*> byName;
    for (const auto& record : records.children) {
        if (!byName.emplace(record.at(0).atom, &record).second)
            throw std::runtime_error("Duplicate theorem in document");
    }
    std::vector<const Node*> selected;
    std::map<std::string, std::size_t> sectionIds;
    if (chapter) {
        for (std::size_t index = 0; index < chapter->sections.size(); ++index) {
            for (const auto& theorem : chapter->sections[index].theorems) {
                const auto found = byName.find(theorem.theorem);
                if (found == byName.end() || selectedAlternate(*found->second) != theorem.alternate)
                    throw std::runtime_error("Missing checked proof selection " + theorem.request());
                selected.push_back(found->second);
                sectionIds.emplace(theorem.theorem, index);
            }
        }
        if (selected.size() != byName.size())
            throw std::runtime_error("Unexpected checked theorems outside the chapter selection");
    } else {
        for (const auto& record : records.children) selected.push_back(&record);
    }
    std::set<std::string> visited;
    std::set<std::string> active;
    std::vector<const Node*> ordered;
    std::function<void(const Node&)> visit = [&](const Node& record) {
        const auto& name = record.at(0).atom;
        if (visited.count(name) != 0) return;
        if (!active.insert(name).second) throw std::runtime_error("Cyclic theorem dependency");
        std::set<std::string> dependencies;
        std::set<std::string> expanded;
        theoremDependencies(record.at(2), byName, helpers, expanded, dependencies);
        for (const auto* candidate : selected) {
            const auto& dependency = candidate->at(0).atom;
            if (dependencies.count(dependency) == 0) continue;
            if (chapter && sectionIds.at(dependency) > sectionIds.at(name))
                throw std::runtime_error(name + " depends on a later section via " + dependency);
            visit(*candidate);
        }
        active.erase(name);
        visited.insert(name);
        ordered.push_back(&record);
    };
    for (const auto* record : selected) visit(*record);
    return ordered;
}

Chapter automaticPaper(const Node& checked, const std::string& title) {
    if (title.find_first_not_of(" \t\r\n") == std::string::npos)
        throw std::runtime_error("A paper title must contain text");
    Chapter chapter;
    chapter.paper = true;
    chapter.automaticLayout = true;
    chapter.title = title;
    // Give familiar single-sorted arithmetic the same specialization path as a
    // configured paper. Wider signatures retain their checked generic notation.
    if (checked.children.size() > 4) {
        std::map<std::string,std::vector<std::string>> candidates;
        std::map<std::string,std::string> numeric;
        for (const auto& entry : checked.at(3).children) numeric.emplace(entry.at(0).atom,entry.at(1).atom);
        std::map<std::string,std::vector<std::string>> sequences;
        for (const auto& entry : checked.at(4).children) {
            const auto& name = entry.at(0).atom;
            if (!numeric.count(name)) continue;
            const auto leaf = name.substr(name.find_last_of('.') + 1);
            if (!leaf.empty() && leaf.find_first_not_of(
                    "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ") == std::string::npos) {
                candidates[leaf].push_back(name);
                if (numeric.at(name)=="1" && leaf.size()>3 && leaf.compare(0,3,"num")==0 &&
                    leaf[3]>='A' && leaf[3]<='Z') sequences[leaf.substr(3,1)].push_back(name);
            }
        }
        for (const auto& item : candidates)
            if (item.second.size() == 1) chapter.symbols.emplace(item.second.front(), item.first);
        if (!sequences.empty()) {
            std::set<std::string> bound;
            const auto visit = [&](auto&& self, const Node& node) -> void {
                if (node.is("q") || node.is("l") || node.is("t")) bound.insert(node.at(2).atom);
                for (const auto& child : node.children) if (child.array) self(self,child);
            };
            visit(visit,checked);
            for (const auto& [symbol,names] : sequences)
                if (names.size()==1 && !candidates.count(symbol) && !bound.count(symbol))
                    chapter.symbols[names.front()] = symbol;
        }
    }
    std::map<std::string,std::vector<std::string>> sections;
    std::map<std::string,std::string> titles;
    std::map<std::string,std::size_t> titleCounts;
    if (checked.children.size() > 8) {
        static const std::map<std::string,std::string> headings{
            {"Powerset","Power sets"}, {"SSubsets","Proper subsets"}, {"powersetCard","Subsets of prescribed size"},
            {"Bipartite","Bipartite relations"}, {"OrderedSemiring","Bounds in ordered semirings"},
            {"StrictOrderedSemiring","Strict bounds in ordered semirings"}, {"Finset","Finite sets"},
            {"Set","Sets"}, {"Fintype","Finite types"}, {"Nat","Natural numbers"}, {"SimpleGraph","Simple graphs"},
            {"Walk","Walks"}
        };
        for (const auto& entry : checked.at(8).children) {
            const auto& scope = entry.at(1).children;
            auto& names = sections[entry.at(0).atom];
            if (entry.children.size() > 3 && entry.at(3).isString()) {
                const auto title = documentedTitle(entry.at(3).atom);
                if (!title.empty()) {
                    titles.emplace(entry.at(0).atom,title);
                    ++titleCounts[title];
                }
            }
            const auto add = [&](const std::string& name) {
                if (name.empty() || name == "[anonymous]") return;
                const auto leaf = name.substr(name.find_last_of('.') + 1);
                const auto it = headings.find(leaf);
                names.push_back(it == headings.end() ? declarationTitle(leaf) : it->second);
            };
            if (scope.empty()) add(entry.at(2).atom);
            for (const auto& name : scope) add(name.atom);
        }
    }
    for (const auto* record : orderTheorems(checked,nullptr)) {
        if (record->children.size() != 3)
            throw std::runtime_error("Automatic papers require original checked proofs");
        const auto& name = record->at(0).atom;
        const auto& path = sections[name];
        if (chapter.sections.empty() || chapter.sections.back().sourceHeadings != path)
            chapter.sections.push_back({path.empty() ? "Results" : path.back(),{},{},{},path});
        auto theoremTitle = titles[name];
        if (!theoremTitle.empty()) {
            const Node* conclusion = &record->at(1);
            while (conclusion->is("q")) conclusion = &conclusion->at(4);
            const auto bounds = paper_titles::incidenceBounds(record->at(1),*conclusion);
            if (!bounds.empty()) theoremTitle += bounds;
            else if (titleCounts.at(theoremTitle)>1) theoremTitle += sumForm(record->at(1));
        }
        chapter.sections.back().theorems.push_back({name, {}, {}, theoremTitle});
    }
    if (chapter.sections.size() == 1) {
        chapter.sections.front().title = "Results";
        chapter.sections.front().sourceHeadings.clear();
    }
    return chapter;
}

void writeSectionHeading(std::ostream& out, const Section& section, const Section* previous) {
    const auto& path = section.sourceHeadings;
    if (path.empty()) {
        out << "\\section{" << escapeLatex(section.title) << "}\n";
        return;
    }
    static const char* levels[] = {"section","subsection","subsubsection","paragraph","subparagraph"};
    const auto heading = [&](std::size_t level,const std::string& title) {
        out << "\\" << levels[std::min<std::size_t>(level,4)] << "{" << escapeLatex(title) << "}\n";
    };
    std::size_t common = 0;
    while (previous && common < path.size() && common < previous->sourceHeadings.size() &&
           path[common] == previous->sourceHeadings[common]) ++common;
    if (common == path.size()) {
        const bool sizes = std::all_of(section.theorems.begin(),section.theorems.end(),[](const Selection& s) {
            return s.title.find("cardinalit") != std::string::npos;
        });
        heading(common,sizes ? "Cardinality bounds" : "Further results");
    }
    for (auto i=common; i<path.size(); ++i) heading(i,path[i]);
}

void preparePaper(Chapter& chapter, const Node& checked) {
    if (!chapter.paper) return;
    std::map<std::string, const Node*> proofs;
    std::map<std::string, const Node*> signatures;
    std::map<std::string, std::string> titles;
    std::set<std::string> used;
    for (const auto& record : checked.at(0).children) {
        proofs.emplace(record.at(0).atom, &record.at(2));
        signatures.emplace(record.at(0).atom, &record.at(1));
        titles.emplace(record.at(0).atom,resultTitle(record,chapter.automaticLayout));
    }
    const auto helpers = proofHelpers(checked);
    for (const auto& item : proofs) {
        std::set<std::string> expanded;
        theoremDependencies(*item.second,proofs,helpers,expanded,used);
    }
    std::set<std::string> simplifiedResults;
    if (checked.children.size()>5) {
        for (const auto& trace : checked.at(5).children) {
            if (trace.children.size()<3 || trace.at(2).children.size()!=1) continue;
            for (const auto& event : trace.at(1).children) {
                if (event.at(0).atom=="simp" && event.at(1).children.size()==1 &&
                    event.at(2).children.empty() && event.at(1).at(0).at(0).atom==trace.at(2).at(0).atom)
                    simplifiedResults.insert(trace.at(0).atom);
            }
        }
    }
    // Substitution, symmetry and chaining can turn earlier lemmas into a
    // corollary without introducing any independent mathematical premise.
    const std::set<std::string> composition{"Eq.trans", "Eq.symm", "congrArg", "congrFun",
        "congr", "Eq.mp", "Eq.mpr", "Iff.mp", "Iff.mpr", "Iff.symm", "Iff.trans", "Iff.intro",
        "Eq.refl", "rfl", "id", "And.left", "And.right", "And.intro"};
    const auto follows = [&](auto&& self, const Node& expr, bool& citesEarlier) -> bool {
        const auto& raw = term(expr);
        if (raw.is("l")) return self(self, raw.at(4), citesEarlier);
        if (raw.is("v")) return true;
        const auto name = head(raw);
        if (proofs.count(name)) citesEarlier = true;
        else if (!composition.count(name)) return false;
        if (raw.is("c")) return true;
        if (!raw.is("a") || raw.at(1).children.size() < 5) return false;
        const Node* binder = proofs.count(name) ? signatures.at(name) : nullptr;
        std::size_t position = 0;
        for (const auto& index : raw.at(1).at(4).children) {
            std::size_t i = 0;
            const char* end = index.atom.data() + index.atom.size();
            const auto parsed = std::from_chars(index.atom.data(), end, i);
            if (parsed.ec != std::errc{} || parsed.ptr != end || i >= raw.children.size()-2) return false;
            while (binder && position < i) {
                binder = binder->is("q") ? &binder->at(4) : nullptr;
                ++position;
            }
            // A specialization can supply a concrete carrier's order or algebra
            // through instance synthesis. Its explicit mathematical premises
            // still have to be hypotheses or consequences of earlier results.
            if (binder && binder->is("q") && binder->children.size() > 5 &&
                binder->at(5).atom == "instance") continue;
            if (!self(self, raw.at(i+2), citesEarlier)) return false;
        }
        return true;
    };
    for (auto& section : chapter.sections) {
        for (auto& result : section.theorems) {
            const auto it = proofs.find(result.theorem);
            if (it == proofs.end()) throw std::runtime_error("Missing checked proof for " + result.theorem);
            if (result.title.empty()) result.title = titles.at(result.theorem);
            if (!result.role.empty()) continue;
            const Node* argumentProof = it->second;
            // A single closing simplification can specialize the statement of
            // a prior result. The final argument of equality transport proves
            // the original statement; all rewrite evidence is still narrated.
            if (simplifiedResults.count(result.theorem)) {
                while (term(*argumentProof).is("l")) argumentProof = &term(*argumentProof).at(4);
                while (term(*argumentProof).is("a")) {
                    const auto& app = term(*argumentProof);
                    const auto rule = head(app);
                    if ((rule=="id" && app.children.size()==4) ||
                        ((rule=="Eq.mp" || rule=="Eq.mpr") && app.children.size()==6))
                        argumentProof = &argument(app,0);
                    else break;
                }
            }
            bool citesEarlier = false;
            if (section.main == result.theorem) result.role = "theorem";
            else if (follows(follows, *argumentProof, citesEarlier) && citesEarlier) result.role = "corollary";
            else result.role = used.count(result.theorem) ? "lemma" : "theorem";
        }
    }
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
