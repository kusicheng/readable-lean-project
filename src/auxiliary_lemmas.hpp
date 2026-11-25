#pragma once

#include "chapter.hpp"
#include "expressions.hpp"
#include "paper_links.hpp"

#include <algorithm>
#include <map>
#include <set>
#include <string>
#include <vector>

namespace proof::auxiliary {

// Distinct logical constructors cannot become equal by unfolding a definition.
// A proof annotated with such a different conclusion cannot license a helper.
inline bool incompatibleConclusion(const Node& helper) {
    const Node* statement = &helper.at(1);
    const Node* body = &helper.at(2);
    while (statement->is("q") && body->is("l")) {
        statement = &statement->at(4);
        body = &body->at(4);
    }
    if (!body->is("p")) return false;
    static const std::set<std::string> logical = {"True","False","Eq","HEq","And","Or","Iff","Exists"};
    const auto required = head(*statement);
    const auto actual = head(body->at(1));
    return required!=actual && logical.count(required) && logical.count(actual);
}

// Count occurrences in the proof itself. A type annotation can contain the same
// helper as its proof, but does not constitute a second proof of anything.
struct Uses {
    std::map<std::string,unsigned> helpers;
    std::size_t applications = 0;
};

inline void count(const Node& node, const std::map<std::string,const Node*>& helpers, Uses& uses) {
    if (node.is("p")) return count(node.at(2),helpers,uses);
    if (node.is("c")) {
        if (helpers.count(node.at(1).atom)) {
            auto& total = uses.helpers[node.at(1).atom];
            total = std::min(2u,total+1);
        }
        return;
    }
    if (node.is("l") || node.is("q")) return count(node.at(4),helpers,uses);
    if (node.is("t")) {
        count(node.at(4),helpers,uses);
        return count(node.at(5),helpers,uses);
    }
    if (node.is("a")) {
        ++uses.applications;
        for (std::size_t i=1;i<node.children.size();++i) count(node.at(i),helpers,uses);
    } else if (node.is("proj")) count(node.at(3),helpers,uses);
}

inline std::vector<const Node*> repeated(const Node& record, const Node& input, const DefinitionRules& definitions) {
    if (input.children.size()<=6) return {};
    std::map<std::string,const Node*> helpers;
    for (const auto& helper : input.at(6).children)
        if (!definitions.count(helper.at(0).atom)) helpers.emplace(helper.at(0).atom,&helper);
    if (helpers.empty()) return {};
    Uses root;
    count(record.at(2),helpers,root);
    std::map<std::string,Uses> uses;
    std::vector<std::string> ordered;
    const auto visit = [&](auto&& self,const std::string& name) -> void {
        if (uses.count(name)) return;
        auto& local = uses[name];
        count(helpers.at(name)->at(2),helpers,local);
        for (const auto& edge : local.helpers) self(self,edge.first);
        ordered.push_back(name);
    };
    for (const auto& edge : root.helpers) visit(visit,edge.first);
    auto demand = root.helpers;
    for (auto it=ordered.rbegin();it!=ordered.rend();++it)
        for (const auto& [child,n] : uses.at(*it).helpers)
            demand[child] = std::min(2u,demand[child]+demand[*it]*n);
    std::vector<const Node*> result;
    for (const auto& name : ordered)
        if (demand[name]>=2 && uses.at(name).applications>=24) result.push_back(helpers.at(name));
    return result;
}

struct Lemma {
    std::string statement;
    std::string proof;
    std::set<std::string> premises;
    std::string reference;
};

inline std::string reference(std::size_t theorem, std::size_t index) {
    return paperLink("aux:"+std::to_string(theorem)+":"+std::to_string(index),
                     "Auxiliary lemma~"+std::to_string(theorem)+"."+std::to_string(index));
}

// A generic helper may render successfully while its particular application
// still needs inlining. Publish only the lemmas the final argument actually uses.
inline std::string assemble(std::string main, std::vector<Lemma>& lemmas, std::size_t theorem,
                            std::set<std::string>& premises) {
    std::vector<bool> needed(lemmas.size());
    for (std::size_t i=lemmas.size();i-- > 0;) {
        needed[i] = main.find(lemmas[i].reference)!=std::string::npos;
        for (std::size_t j=i+1;!needed[i] && j<lemmas.size();++j)
            if (needed[j] && lemmas[j].proof.find(lemmas[i].reference)!=std::string::npos) needed[i]=true;
    }
    std::string prefix;
    std::size_t ordinal = 0;
    for (std::size_t i=0;i<lemmas.size();++i) {
        if (!needed[i]) continue;
        auto& lemma = lemmas[i];
        ++ordinal;
        if (ordinal!=i+1) {
            const auto updated = reference(theorem,ordinal);
            const auto renumber = [&](std::string& text) {
                std::size_t pos=0;
                while ((pos=text.find(lemma.reference,pos))!=std::string::npos) {
                    text.replace(pos,lemma.reference.size(),updated);
                    pos+=updated.size();
                }
            };
            renumber(main);
            for (std::size_t j=i+1;j<lemmas.size();++j) if (needed[j]) renumber(lemmas[j].proof);
        }
        const auto number = std::to_string(theorem)+"."+std::to_string(ordinal);
        const auto key = "aux:"+std::to_string(theorem)+":"+std::to_string(ordinal);
        prefix += "\\par\\smallskip\\noindent\\paperlineanchor{"+key+"}\\textbf{Auxiliary lemma~"+number+
                  ".} "+lemma.statement+"\n\\par\\noindent\\emph{Proof of the auxiliary lemma.} "+
                  lemma.proof+"\n";
        premises.insert(lemma.premises.begin(),lemma.premises.end());
    }
    if (prefix.empty()) return main;
    const auto introduction = ordinal==1 ? "We first prove the following auxiliary lemma.\n" :
                                           "We first prove the following auxiliary lemmas.\n";
    return introduction+prefix+"\\par\\smallskip\\noindent\\emph{Proof of the main assertion.}\\enspace\n"+main;
}

} // namespace proof::auxiliary
