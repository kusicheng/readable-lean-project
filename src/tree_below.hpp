#pragma once

#include "nat_below.hpp"
#include <array>

namespace proof::tree_below {

inline const Node* certificate(const Node& raw, const nat_below::Catalog& catalog) {
    if (!raw.is("a") || raw.children.size()!=6) return nullptr;
    const auto& step=term(raw.at(5));
    if (!nat_below::binder(step,"l") || !nat_below::binder(step.at(4),"l")) return nullptr;
    const auto& match=term(step.at(4).at(4));
    const auto it=catalog.find(head(match));
    if (it==catalog.end() || it->second->children.size()!=6 || !match.is("a") || match.children.size()<7 ||
        it->second->at(1).atom!=std::to_string(match.children.size()-7)) return nullptr;
    const auto& cert=it->second->at(5);
    return cert.is("binaryTreeCases") && cert.children.size()==4 && head(raw)==cert.at(1).atom+".brecOn"
        ? &cert : nullptr;
}

struct Branches {
    const Node* leaf;
    const Node* leafGoal;
    const Node* label;
    std::array<const Node*,2> children;
    std::array<Node,2> hypotheses;
    std::array<std::string,2> ids;
    Node nodeProof;
};

// Replace only the certified entries of the recursion table, at a site
// requiring that child's proposition. Swapping the two entries is detectable
// even if the surrounding equality proof lacks an explicit type annotation.
template<class Required>
bool replace(Node& n, const Node& bundle, const Branches& branches, Required required,
             const Node* parent=nullptr, std::size_t slot=0) {
    if (n.is("proj") && n.children.size()==5 && n.at(1).atom=="PProd" && n.at(2).atom=="0" &&
        n.at(4).atom=="proof") {
        const auto& part=term(n.at(3));
        if (part.is("proj") && part.children.size()==5 && part.at(1).atom=="PProd" &&
            nat_below::local(part.at(3),bundle) && (part.at(2).atom=="0" || part.at(2).atom=="1")) {
            const auto child=part.at(2).atom=="0" ? 0u : 1u;
            if (!parent || !required(*parent,slot,branches.hypotheses[child])) return false;
            auto local=part.at(3);
            local.children[1].atom=branches.ids[child];
            local.children[2].atom="proof";
            n=std::move(local);
            return true;
        }
    }
    if (nat_below::local(n,bundle)) return false;
    for (std::size_t i=0;i<n.children.size();++i)
        if (n.at(i).array && !replace(n.children[i],bundle,branches,required,&n,i)) return false;
    return true;
}

template<class Same, class Apply, class Required>
std::optional<Branches> open(const Node& raw, const Node& cert, const Node& conclusion,
                             Same same, Apply apply, Required required) {
    const auto& motive=raw.at(3);
    const auto& step=term(raw.at(5));
    const auto& bundle=step.at(4);
    const auto& match=term(bundle.at(4));
    const auto& tree=step.at(3);
    if (!nat_below::binder(motive,"l") || !tree.is("a") || head(tree)!=cert.at(1).atom ||
        tree.children.size()!=3 || !same(tree.at(2),raw.at(2)) || !same(motive.at(3),tree) ||
        !nat_below::local(argument(match,3),step) || !nat_below::local(argument(match,0),bundle)) return {};
    const auto goalAt=[&](const Node& value,const Node& goal) {
        auto want=apply(motive,value);
        return want && same(*want,goal);
    };
    const auto below=[&](const Node& t) {
        return t.is("a") && t.children.size()==5 && head(t)==cert.at(1).atom+".below" &&
               same(t.at(2),raw.at(2)) && same(t.at(3),motive);
    };
    const auto& family=argument(match,4);
    if (!goalAt(raw.at(4),conclusion) || !below(bundle.at(3)) || !nat_below::local(bundle.at(3).at(4),step) ||
        !nat_below::binder(family,"l") || !same(family.at(3),tree) || !nat_below::binder(family.at(4),"q"))
        return {};
    const auto& premise=family.at(4);
    if (!below(premise.at(3)) || !nat_below::local(premise.at(3).at(4),family) ||
        !goalAt(premise.at(3).at(4),premise.at(4))) return {};
    const auto& nil=argument(match,2);
    const auto& label=argument(match,1);
    if (!nat_below::binder(nil,"l") || (head(nil.at(3))!="Unit" && head(nil.at(3))!="PUnit") ||
        !nat_below::binder(nil.at(4),"l") ||
        !nat_below::binder(label,"l") || !same(label.at(3),raw.at(2)) || !nat_below::binder(label.at(4),"l") ||
        !nat_below::binder(label.at(4).at(4),"l")) return {};
    const auto& left=label.at(4);
    const auto& right=left.at(4);
    const auto& leaf=nil.at(4);
    const auto& node=right.at(4);
    if (!same(left.at(3),tree) || !same(right.at(3),tree) || !nat_below::binder(node,"l") ||
        !below(leaf.at(3)) || !below(node.at(3)) || leaf.children.size()!=9 || node.children.size()!=9) return {};
    const auto& emptyTree=leaf.at(3).at(4);
    const auto& fullTree=node.at(3).at(4);
    if (!emptyTree.is("a") || emptyTree.children.size()!=3 || head(emptyTree)!=cert.at(2).atom ||
        !same(emptyTree.at(2),raw.at(2)) || !fullTree.is("a") || fullTree.children.size()!=6 ||
        head(fullTree)!=cert.at(3).atom || !same(fullTree.at(2),raw.at(2)) ||
        !nat_below::local(fullTree.at(3),label) || !nat_below::local(fullTree.at(4),left) ||
        !nat_below::local(fullTree.at(5),right)) return {};
    const auto claims=[&](const Node& branch,const Node& value) {
        const auto& evidence=branch.at(8);
        return evidence.is("binaryTreeInductionCase") && evidence.children.size()==4 && branch.at(4).is("p") &&
               same(branch.at(4).at(1),evidence.at(1)) && goalAt(value,evidence.at(2));
    };
    if (!claims(leaf,emptyTree) || !claims(node,fullTree) || !leaf.at(8).at(3).children.empty() ||
        nat_below::containsLocal(leaf.at(4),nil) || nat_below::containsLocal(leaf.at(4),leaf)) return {};
    const auto& paths=node.at(8).at(3);
    Branches branches{&leaf.at(4),&leaf.at(8).at(2),&label,{&left,&right},{},{},node.at(4)};
    if (paths.children.size()!=2) return {};
    for (std::size_t i=0;i<2;++i) {
        const auto& path=paths.at(i);
        if (path.children.size()!=3 || path.at(0).atom!=std::to_string(i) || path.at(1).atom!="0" ||
            !goalAt(fullTree.at(i+4),path.at(2))) return {};
        branches.hypotheses[i]=path.at(2);
        branches.ids[i]=node.at(1).atom+".subtree."+std::to_string(i);
    }
    if (!replace(branches.nodeProof,node,branches,required)) return {};
    return branches;
}

} // namespace proof::tree_below
