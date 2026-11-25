#include "proof_cost.hpp"
#include <charconv>
#include <algorithm>
#include <limits>
#include <set>
#include <sstream>
#include <stdexcept>

namespace proof {
namespace {
enum Operation { hypothesis, application, rewrite, binding, branch, certificate };
constexpr std::array<const char*,6> labels{
    "hypotheses","applications","rewrites","bindings","branches","certificate steps"};

bool proofValue(const Node& value) {
    if (value.is("p")) return true;
    if (value.is("l")) return value.children.size() > 7 && value.at(7).atom == "proof";
    if (value.is("v") || value.is("c")) return value.children.size() > 2 && value.at(2).atom == "proof";
    if (value.is("proj")) return value.children.size() > 4 && value.at(4).atom == "proof";
    if (value.is("t")) return value.children.size() > 6 && value.at(6).atom == "proof";
    return false;
}

void witnessProofs(const Node& witness, const std::map<std::string,std::size_t>& fields,
                   std::vector<const Node*>& pending) {
    const auto& raw = term(witness);
    if (raw.is("l")) { witnessProofs(raw.at(4),fields,pending); return; }
    if (raw.is("u")) { pending.push_back(&raw); return; }
    if (!raw.is("a")) return;
    std::vector<const Node*> proofs;
    if (!proofArguments(raw,proofs)) return;
    pending.insert(pending.end(),proofs.begin(),proofs.end());
    const auto ctor = fields.find(head(raw));
    if (ctor==fields.end() || ctor->second>raw.children.size()-2) return;
    for (std::size_t i=raw.children.size()-ctor->second;i<raw.children.size();++i) {
        const auto* field = &raw.at(i);
        if (std::find(proofs.begin(),proofs.end(),field)==proofs.end())
            witnessProofs(*field,fields,pending);
    }
}
}

ProofWeights parseProofWeights(const std::string& text) {
    constexpr std::array<const char*,6> keys{
        "hypothesis","application","rewrite","binding","branch","certificate"};
    ProofWeights result = defaultProofWeights;
    std::set<std::string> seen;
    std::size_t start = 0;
    for (;;) {
        const auto end = text.find(',', start);
        const auto item = text.substr(start,end == std::string::npos ? end : end-start);
        const auto sep = item.find('=');
        const auto key = item.substr(0,sep);
        const auto it = std::find(keys.begin(),keys.end(),key);
        if (it == keys.end() || sep == std::string::npos || !seen.insert(key).second)
            throw std::runtime_error("Unknown, missing or repeated proof weight in " + item);
        const auto* limit = item.data() + item.size();
        auto& weight = result[static_cast<std::size_t>(it-keys.begin())];
        const auto parsed = std::from_chars(item.data()+sep+1,limit,weight);
        if (parsed.ec != std::errc{} || parsed.ptr != limit)
            throw std::runtime_error("Proof weights must be nonnegative integers");
        if (end == std::string::npos) return result;
        start = end+1;
    }
}

std::size_t ProofCost::total() const {
    std::size_t value = 0;
    for (std::size_t i=0; i<counts.size(); ++i) {
        const auto max = std::numeric_limits<std::size_t>::max();
        if (counts[i] && weights[i] > (max-value) / counts[i]) return max;
        value += weights[i]*counts[i];
    }
    return value;
}

std::string ProofCost::describe() const {
    if (!available) return "proof cost unavailable (the export contains incomplete proof evidence)";
    std::ostringstream out;
    out << "proof cost " << total() << " (";
    bool first = true;
    for (std::size_t i=0; i<counts.size(); ++i) {
        if (!counts[i]) continue;
        if (!first) out << ", ";
        out << counts[i] << ' ' << labels[i] << " x " << weights[i];
        first = false;
    }
    out << ')';
    return out.str();
}

ProofCost measureProof(const Node& proof, const Node* document, const ProofWeights& weights) {
    ProofCost cost;
    cost.weights = weights;
    std::map<std::string,const Node*> helpers;
    if (document && document->children.size() > 6) {
        for (const auto& helper : document->at(6).children)
            helpers.emplace(helper.at(0).atom, &helper.at(2));
    }
    std::set<std::string> expandedHelpers;
    std::map<std::string,std::size_t> objectFields;
    if (document && document->children.size()>9)
        for (const auto& ctor : document->at(9).children)
            if (ctor.children.size()>3 && ctor.at(3).atom=="object")
                objectFields.emplace(ctor.at(0).atom,ctor.at(2).children.size());
    std::vector<const Node*> pending{&proof};
    while (!pending.empty()) {
        const auto& raw = term(*pending.back());
        pending.pop_back();
        if (raw.is("u")) {
            cost.available = false;
        } else if (raw.is("l")) {
            ++cost.counts[binding];
            pending.push_back(&raw.at(4));
        } else if (raw.is("t")) {
            ++cost.counts[binding];
            const auto& value = raw.at(4);
            if (proofValue(value)) pending.push_back(&value);
            else witnessProofs(value,objectFields,pending);
            pending.push_back(&raw.at(5));
        } else if (raw.is("v")) {
            ++cost.counts[hypothesis];
        } else if (raw.is("a") || raw.is("c")) {
            const auto name = head(raw);
            const auto leaf = name.substr(name.find_last_of('.')+1);
            const auto helper = helpers.find(name);
            if (helper != helpers.end() && expandedHelpers.insert(name).second)
                pending.push_back(helper->second);
            Operation op = application;
            if (name.rfind("Lean.Omega.",0) == 0 || name.rfind("Linarith.",0) == 0)
                op = certificate;
            else if (name == "congr" || name == "congrArg" || name == "congrFun" ||
                     name == "propext" || name.compare(0,3,"Eq.") == 0) op = rewrite;
            else if (name == "Iff.intro" || name == "Or.elim" || name == "Exists.elim" ||
                     leaf == "rec" || leaf == "recOn" || leaf == "recAux" || leaf == "casesOn" ||
                     leaf == "byCases" || leaf == "byContradiction")
                op = branch;
            ++cost.counts[op];
            if (!raw.is("a")) continue;
            const auto& fn = raw.at(1);
            if ((fn.is("c") || fn.is("v")) && fn.children.size() >= 5 && fn.at(4).array) {
                std::vector<const Node*> premises;
                if (!proofArguments(raw,premises)) cost.available = false;
                pending.insert(pending.end(),premises.begin(),premises.end());
                const Node* witness = nullptr;
                if (name=="Exists.intro" && raw.children.size()==6) witness = &raw.at(4);
                if (name=="Nonempty.intro" && raw.children.size()==4) witness = &raw.at(3);
                if (witness && std::find(premises.begin(),premises.end(),witness)==premises.end())
                    witnessProofs(*witness,objectFields,pending);
            } else {
                if (fn.is("l")) pending.push_back(&fn);
                for (std::size_t i=2; i<raw.children.size(); ++i)
                    if (proofValue(raw.at(i))) pending.push_back(&raw.at(i));
            }
        }
    }
    return cost;
}
} // namespace proof
