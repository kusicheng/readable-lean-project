#pragma once

#include "record_equality.hpp"
#include <algorithm>

namespace proof::record_equality {

// In an indexed structure, a proof field can relate a data field to the
// common index. Extensionality first transports along that equality and can
// then transport equalities between proofs. Follow the actual eliminators.
class IndexedEvidence {
    using Signatures = std::map<std::string,const Node*>;
    using Reduce = std::optional<Node> (*)(const Node&);
    using Specialize = std::optional<Node> (*)(const Node&,const Node&);

    const Node& spec_;
    const Signatures& signatures_;
    Equal equal_;
    Reduce beta_;
    Specialize specialize_;
    std::string family_;
    std::size_t parameters_ = 0;
    std::vector<bool> proofFields_;


    // At this point each constructor proof argument has to pass witnesses().
    // Only proof fields of this exact constructor are irrelevant to conversion.
    Node normalize(const Node& input) const {
        Node result=term(input);
        for (auto& child : result.children)
            if (child.array) child=normalize(child);
        if (auto reduced=beta_(result)) return normalize(*reduced);
        if (!result.is("a")) return result;
        if (result.children.size()==parameters_+3) {
            const auto& object=argument(result,0);
            if (isConstructor(object)) {
                const auto& fields=spec_.at(2).children;
                for (std::size_t i=0;i<fields.size();++i) {
                    if (head(result)!=family_+"."+fields[i].atom) continue;
                    for (std::size_t j=0;j<parameters_;++j)
                        if (!equal_(result.at(j+2),object.at(j+2))) return result;
                    return object.at(parameters_+2+i);
                }
            }
        }
        if (isConstructor(result)) {
            for (std::size_t i=0;i<proofFields_.size();++i) {
                if (!proofFields_[i]) continue;
                Node marker=result.at(1);
                marker.children[1].atom="#irrelevant-proof-field";
                result.children[parameters_+i+2]=std::move(marker);
            }
        }
        return result;
    }

    static bool usesEvidence(const Node& expr,const std::string& id) {
        const auto& raw=term(expr);
        if (raw.is("v")) return raw.at(1).atom==id;
        if (raw.is("l")) return usesEvidence(raw.at(4),id);
        if (!raw.is("a")) return false;
        std::vector<const Node*> premises;
        if (!proofArguments(raw,premises)) return false;
        return std::any_of(premises.begin(),premises.end(),
            [&](const Node* premise) { return usesEvidence(*premise,id); });
    }

    bool isConstructor(const Node& n) const {
        return n.is("a") && head(n)==spec_.at(0).atom &&
               n.children.size()==parameters_+proofFields_.size()+2;
    }

    bool same(const Node& a,const Node& b) const {
        return equal_(a,b) || equal_(normalize(a),normalize(b));
    }

    Node reduceHead(Node type) const {
        while (auto reduced=beta_(type)) type=std::move(*reduced);
        return type;
    }

    std::optional<Node> nextDomain(const Node& binder,const Node& value) const {
        auto result=specialize_(binder,value);
        if (result) *result=reduceHead(std::move(*result));
        return result;
    }

    // Check even the witnesses buried in a constructor inside an equality
    // annotation. Replacing a positivity or index proof must remain visible.
    bool witnesses(const Node& value, Locals scope) {
        if (value.is("u")) return false;
        if (value.is("p")) return proof(value,value.at(1),std::move(scope));
        if (value.is("q") || value.is("l")) {
            if (!witnesses(value.at(3),scope)) return false;
            scope[value.at(1).atom]=&value.at(3);
            return witnesses(value.at(4),std::move(scope));
        }
        if (value.is("a") && head(value)==spec_.at(0).atom)
            return isConstructor(value) && bool(applicationType(value,spec_.at(1),scope));
        for (const auto& child : value.children)
            if (child.array && !witnesses(child,scope)) return false;
        return true;
    }

    std::optional<Node> applicationType(const Node& app, Node signature, const Locals& scope) {
        for (std::size_t i=2;i<app.children.size();++i) {
            if (!signature.is("q")) return {};
            const auto& arg=app.at(i);
            const bool isProof=signature.at(6).atom=="proof" || arg.is("p") ||
                               (arg.is("v") && arg.at(2).atom=="proof");
            if (isProof ? !proof(arg,signature.at(3),scope) : !witnesses(arg,scope)) return {};
            auto next=nextDomain(signature,arg);
            if (!next) return {};
            signature=std::move(*next);
        }
        return signature;
    }

    bool proof(const Node& expr,const Node& inputType,Locals scope) {
        const Node type=reduceHead(inputType);
        if (expr.is("p") && (!same(expr.at(1),type) || !witnesses(expr.at(1),scope))) return false;
        const auto& raw=term(expr);
        if (raw.is("v")) {
            const auto* actual=localType(raw,scope);
            if (!actual || !same(*actual,type)) return false;
            return true;
        }
        if (raw.is("l")) {
            if (!type.is("q") || !same(raw.at(3),type.at(3)) || !witnesses(raw.at(3),scope)) return false;
            Node local;
            local.array=true;
            local.children={raw.at(0),raw.at(1),raw.at(6)};
            local.children[0].atom="v";
            const auto target=nextDomain(type,local);
            scope[local.at(1).atom]=&raw.at(3);
            return target && proof(raw.at(4),*target,std::move(scope));
        }
        if (!raw.is("a")) return false;
        const auto name=head(raw);
        if (name=="Eq.refl" || name=="HEq.refl") {
            if (raw.children.size()!=4) return false;
            const bool matches=name=="Eq.refl"
                ? call(type,"Eq",3) && same(type.at(4),raw.at(3))
                : call(type,"HEq",4) && same(type.at(4),raw.at(2)) && same(type.at(5),raw.at(3));
            return matches && same(type.at(2),raw.at(2)) && same(type.at(3),raw.at(3)) &&
                   witnesses(raw.at(2),scope) && witnesses(raw.at(3),scope);
        }
        if (name!="Eq.casesOn" && name!="Eq.ndrec" && name!="Eq.symm" && name!="eq_of_heq") return false;
        const auto sig=signatures_.find(name);
        if (sig==signatures_.end()) return false;
        const auto actual=applicationType(raw,*sig->second,scope);
        return actual && same(*actual,type);
    }

public:
    IndexedEvidence(const Node& spec,const Signatures& signatures,Equal equal,Reduce beta,Specialize specialize)
        : spec_(spec),signatures_(signatures),equal_(equal),beta_(beta),specialize_(specialize) {
        const Node* result=&spec.at(1);
        std::vector<bool> binders;
        while (result->is("q")) {
            binders.push_back(result->at(6).atom=="proof");
            result=&result->at(4);
        }
        family_=head(*result);
        const auto fields=spec.at(2).children.size();
        if (binders.size()>fields) {
            parameters_=binders.size()-fields;
            proofFields_.assign(binders.begin()+parameters_,binders.end());
        }
    }

    // Return the position of the proof field that equates a function of the
    // first record's data to its index. Plain records use the existing rule.
    std::optional<std::size_t> check(const Node& expr,const Node& record,const Locals& scope,
                                     const std::vector<std::string>& dataEqualities) {
        const auto& first=term(expr);
        if (!parameters_ || !expr.is("p") || !call(first,"Eq.casesOn",8) || !isConstructor(record) ||
            !first.at(5).is("v") || !first.at(6).is("v")) return {};
        const auto begin=record.children.begin()+2;
        if (std::none_of(begin,begin+parameters_,[&](const Node& arg) { return equal_(arg,first.at(5)); })) return {};
        for (std::size_t i=0;i<proofFields_.size();++i) {
            if (!proofFields_[i] || !equal_(record.at(parameters_+i+2),first.at(6))) continue;
            if (!proof(expr,expr.at(1),scope)) return {};
            for (const auto& id : dataEqualities)
                if (!usesEvidence(expr,id)) return {};
            return parameters_+i+2;
        }
        return {};
    }
};

} // namespace proof::record_equality
