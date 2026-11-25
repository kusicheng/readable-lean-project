import Lean

open Lean Lean.Meta

namespace Adapter

private def text := Json.str

private def binderId (var : Expr) : Json :=
  text var.fvarId!.name.toString

private def binderName (name : Name) : Json :=
  text name.eraseMacroScopes.toString

-- Distinguish a proposition, its evidence, a type, and an ordinary value from
-- their kernel types. A parameter declared P : Prop is itself a proposition.
private def roleFromType (type : Expr) : MetaM Json := do
  if let .sort level := (← whnf type) then
    return text (if level.isZero then "prop" else "type")
  return text (if ← isProp type then "proof" else "value")

private def binderKind : BinderInfo → Json
  | .default => text "explicit"
  | .implicit => text "implicit"
  | .strictImplicit => text "strictImplicit"
  | .instImplicit => text "instance"

private def namedHead (fn application : Expr) : MetaM Json := do
  let (tag, name) := if fn.isFVar then ("v", binderId fn) else ("c", text fn.constName!.toString)
  let mut visible := #[]
  let mut premises := #[]
  let mut type ← inferType fn
  let args := application.getAppArgs
  for arg in args, i in [:args.size] do
    let .forallE _ domain body info ← whnf type | throwError "Expected a function in a checked application"
    if ← isProp domain then
      premises := premises.push (text (toString i))
    else if info == .default then
      visible := visible.push (text (toString i))
    type := body.instantiate1 arg
  return Json.arr #[text tag, name, ← roleFromType type, Json.arr visible, Json.arr premises]

/-- A product match with a single branch is its body applied to the two projections.
    Keep the original term if Lean does not validate the replacement definitionally. -/
private def expandPairMatch (e : Expr) : MetaM Expr := do
  let some app ← matchMatcherApp? e (alsoCasesOn := true) | return e
  unless app.discrs.size == 1 && app.altNumParams == #[2] && app.remaining.isEmpty do return e
  let pair := app.discrs[0]!
  unless (← whnf (← inferType pair)).isAppOfArity ``Prod 2 do return e
  let body := (mkApp2 app.alts[0]! (.proj ``Prod 0 pair) (.proj ``Prod 1 pair)).headBeta
  if ← isDefEq e body then return body else return e

private def binaryTreeConstructors? (family : Name) : MetaM (Option (InductiveVal × Name × Name)) := do
  let env ← getEnv
  let some (.inductInfo ind) := env.find? family | return none
  let [leaf, node] := ind.ctors | return none
  unless ind.all == [family] && ind.numIndices == 0 && ind.numNested == 0 &&
      isBRecOnRecursor env (mkBRecOnName family) && (← getConstInfoCtor leaf).numFields == 0 &&
      (← getConstInfoCtor node).numFields == 3 do return none
  return some (ind, leaf, node)

/-- Relate the two recursive entries of a binary constructor's below-table
    to the actual children. An abstract motive distinguishes left from right
    even if the user's particular proposition happens to be constant. -/
private def binaryInductionCase? (domain table proof : Expr) : MetaM (Option (Expr × Array Expr)) := do
  let some below := domain.getAppFn.constName? | return none
  let family := below.getPrefix
  unless below == mkBelowName family do return none
  let some (ind, leaf, node) ← binaryTreeConstructors? family | return none
  let args := domain.getAppArgs
  unless args.size == ind.numParams + 2 do return none
  let params := args.extract 0 ind.numParams
  let motive := args[ind.numParams]!
  let index := args[ind.numParams+1]!
  let target := (mkApp motive index).headBeta
  unless (← isProp target) && (← isDefEq (← inferType proof) target) do return none
  if index.isAppOf leaf && index.getAppArgs == params then return some (target, #[])
  unless index.isAppOfArity node (ind.numParams+3) &&
      index.getAppArgs.extract 0 ind.numParams == params do return none
  let children := index.getAppArgs.extract (ind.numParams+1) (ind.numParams+3)
  unless children.all (·.isFVar) && children.allDiff do return none
  let project := fun (t : Expr) (side : Nat) => Expr.proj ``PProd 0 (.proj ``PProd side t)
  withLocalDeclD `predicate (← inferType motive) fun predicate => do
    let abstractDomain := mkAppN domain.getAppFn (params ++ #[predicate, index])
    withLocalDeclD `table abstractDomain fun abstractTable => do
      let mut targets := #[]
      for child in children, i in [:children.size] do
        let concrete := (mkApp motive child).headBeta
        let checked ← try
          pure ((← isDefEq (← inferType (project abstractTable i)) (mkApp predicate child)) &&
            (← isDefEq (← inferType (project table i)) concrete))
        catch _ => pure false
        unless checked do return none
        targets := targets.push concrete
      return some (target, targets)

/-- Export kernel expressions while opening binders for local type inference.
    Proof annotations are suppressed in type trees and on application heads. -/
private partial def serialize (expression : Expr) (annotateProofs : Bool)
    (compactRing : Bool := false) : MetaM Json := do
  let e ← if annotateProofs then pure expression else expandPairMatch expression.headBeta
  -- A ring certificate proves that both sides have the same normal form. In
  -- the bounded retry, retain its original equality. C++ recomputes both
  -- polynomials from that equality and checks all rational operations.
  if compactRing && annotateProofs && e.isAppOfArity `Mathlib.Tactic.Ring.of_eq 6 then
    let args := e.getAppArgs
    let isNormalization := fun (p : Expr) =>
      p.getAppFn.constName?.any fun n => n == ``Eq.refl || n.getPrefix == `Mathlib.Tactic.Ring
    if args[0]!.isConstOf `Rat && isNormalization args[4]! && isNormalization args[5]! then
      let typeJson ← serialize (← inferType e) false
      return Json.arr #[text "p", typeJson, Json.arr #[text "ringEquality", text "Mathlib.Tactic.Ring.of_eq"]]
  let raw ← match e with
    | .const .. | .fvar _ => namedHead e e
    | .lam name domain body info => do
      let domainJson ← serialize domain false
      withLocalDecl name info domain fun var => do
        let proof := body.instantiate1 var
        let bodyJson ← serialize proof annotateProofs compactRing
        let fields := #[text "l", binderId var, binderName name, domainJson, bodyJson,
          binderKind info, ← roleFromType domain, ← roleFromType (← inferType e)]
        -- A branch may prove P(k) in a definitionally different form, for example
        -- with k+1 written as succ k. Certify the actual and expected propositions.
        if annotateProofs && domain.isAppOfArity ``Nat.below 2 then
          if let .arr annotated := bodyJson then
            if annotated.size == 3 && annotated[0]! == text "p" then
              let args := domain.getAppArgs
              let target := (mkApp args[0]! args[1]!).headBeta
              if (← isProp target) && (← isDefEq (← inferType proof) target) then
                return Json.arr (fields.push (Json.arr #[text "inductionCase", annotated[1]!,
                  ← serialize target false]))
        if annotateProofs && domain.getAppFn.constName?.any (fun n => n == mkBelowName n.getPrefix) then
          if let .arr annotated := bodyJson then
            if annotated.size == 3 && annotated[0]! == text "p" then
              if let some (target, children) ← binaryInductionCase? domain var proof then
                let mut paths := #[]
                for child in children, i in [:children.size] do
                  paths := paths.push (Json.arr #[text (toString i), text "0", ← serialize child false])
                return Json.arr (fields.push (Json.arr #[text "binaryTreeInductionCase", annotated[1]!,
                  ← serialize target false, Json.arr paths]))
        return Json.arr fields
    | .forallE name domain body info => do
      let domainJson ← serialize domain false
      withLocalDecl name info domain fun var => do
        let bodyJson ← serialize (body.instantiate1 var) false
        return Json.arr #[text "q", binderId var, binderName name, domainJson, bodyJson,
          binderKind info, ← roleFromType domain, ← roleFromType (← inferType e)]
    | .letE name domain value body _ => do
      let domainJson ← serialize domain false
      let valueJson ← serialize value annotateProofs compactRing
      withLetDecl name domain value fun var => do
        let bodyJson ← serialize (body.instantiate1 var) annotateProofs compactRing
        return Json.arr #[text "t", binderId var, binderName name, domainJson, valueJson, bodyJson,
          ← roleFromType (← inferType e)]
    | .app .. => do
      let head := e.getAppFn
      let fn ← if head.isConst || head.isFVar then namedHead head e else serialize head false
      let args ← e.getAppArgs.mapM fun arg => serialize arg annotateProofs compactRing
      pure <| Json.arr (#[text "a", fn] ++ args)
    | .lit (.natVal n) => pure <| Json.arr #[text "n", text (toString n)]
    | .sort level => pure <| Json.arr #[text "s", text (toString level)]
    | .mdata _ body => serialize body annotateProofs compactRing
    | .proj structureName i value =>
      return Json.arr #[text "proj", text structureName.toString, text (toString i),
        ← serialize value false, ← roleFromType (← inferType e)]
    | .bvar _ => pure <| Json.arr #[text "u", text "unopened bound variable"]
    | .mvar _ => pure <| Json.arr #[text "u", text "metavariable"]
    | .lit (.strVal _) => pure <| Json.arr #[text "u", text "string literal"]
  if annotateProofs && (e.isApp || e.isConst) then
    let inferredType ← inferType e
    if ← isProp inferredType then
      let typeJson ← serialize inferredType false
      return Json.arr #[text "p", typeJson, raw]
    else
      return raw
  else
    return raw

private def readTheorem (theoremName : String) : MetaM TheoremVal := do
  let name := theoremName.toName
  let some (.thmInfo declaration) := (← getEnv).find? name
    | throwError "Expected an imported theorem named '{theoremName}'"
  return declaration

private structure Selection where
  original : TheoremVal
  proof : TheoremVal

private def selectTheorem (request : String) : MetaM Selection := do
  match request.splitOn "=" with
  | [name] =>
    let declaration ← readTheorem name
    return ⟨declaration, declaration⟩
  | [name, alternate] =>
    let original ← readTheorem name
    let proof ← readTheorem alternate
    unless original.name != proof.name do
      throwError "An alternate must be a separate theorem: '{name}'"
    unless ← isDefEq original.type proof.type do
      throwError "Alternate '{alternate}' has a different statement from '{name}'"
    return ⟨original, proof⟩
  | _ => throwError "Expected a theorem name or original=alternate"

private def unavailableEvidence : Json :=
  Json.arr #[text "u", text "checked proof exceeded the extraction heartbeat limit"]

/-- Recover the introductions and established local facts preceding an oversized
    certificate. Each value is the original checked proof of its binding. The
    whole recovery shares one heartbeat allowance; the first inaccessible suffix
    remains explicitly incomplete, so it cannot be used to conclude the proof. -/
private partial def bindingEvidence (expression : Expr) : MetaM Json := do
  tryCatchRuntimeEx (do
    let e := expression.consumeMData
    let role ← roleFromType (← inferType e)
    if let .lam name domain body info := e then
      let domainJson ← serialize domain false
      let domainRole ← roleFromType domain
      return ← withLocalDecl name info domain fun var => do
        return Json.arr #[text "l", binderId var, binderName name, domainJson,
          ← bindingEvidence (body.instantiate1 var), binderKind info, domainRole, role]
    let binding? := match e with
      | .letE name domain value body _ => some (name, domain, value, body)
      | _ => Id.run do
        unless e.isAppOfArity ``letFun 4 do return none
        let args := e.getAppArgs
        let .lam name domain body _ := args[3]!.consumeMData | return none
        return some (name, domain, args[2]!, body)
    let some (name, domain, value, body) := binding? | return unavailableEvidence
    let domainJson ← serialize domain false
    let valueJson ← serialize value true
    withLetDecl name domain value fun var => do
      return Json.arr #[text "t", binderId var, binderName name, domainJson, valueJson,
        ← bindingEvidence (body.instantiate1 var), role]) fun ex => do
    if !ex.isMaxHeartbeat then throw ex
    return unavailableEvidence

private def proofEvidence (name : Name) (value : Expr) : MetaM Json := withCurrHeartbeats do
  tryCatchRuntimeEx (serialize value true) fun ex => do
    if !ex.isMaxHeartbeat then throw ex
    IO.eprintln s!"Extraction heartbeat limit reached for checked proof '{name}'"
    if value.getUsedConstants.contains `Mathlib.Tactic.Ring.of_eq then
      tryCatchRuntimeEx (withCurrHeartbeats (serialize value true true)) fun retry => do
        if !retry.isMaxHeartbeat then throw retry
        withCurrHeartbeats (bindingEvidence value)
    else withCurrHeartbeats (bindingEvidence value)

private def exportTheorem (selection : Selection) : MetaM Json := withCurrHeartbeats do
  let typeJson ← serialize selection.original.type false
  let valueJson ← proofEvidence selection.proof.name selection.proof.value
  let record := #[text selection.original.name.toString, typeJson, valueJson]
  return Json.arr <| if selection.original.name == selection.proof.name then record
    else record.push (text selection.proof.name.toString)

/-- Only ordinary functions from natural numbers to natural numbers get paper notation. -/
private def natArity : Expr → Option Nat
  | .forallE _ domain body _ =>
    if domain.isConstOf ``Nat then (natArity body).map Nat.succ else none
  | result => if result.isConstOf ``Nat then some 0 else none

/-- Discover declarations from exactly the modules named on the command line.
    Position is the primary key and name breaks ties, independently of environment hashing. -/
private def discoverTheorems (modules : Array Name) : MetaM (List String) := do
  let env ← getEnv
  let mut result := #[]
  for mod in modules do
    let constNames ← if mod == env.mainModule then
      pure (env.constants.foldStage2 (fun acc name _ => acc.push name) #[])
    else if let some idx := env.getModuleIdx? mod then
      pure env.header.moduleData[idx]!.constNames
    else throwError "Module '{mod}' was not imported"
    let mut entries : Array (Nat × Nat × String) := #[]
    for name in constNames do
      unless name.isInternalDetail || name.hasMacroScopes || isPrivateName name do
        if let some (.thmInfo _) := env.find? name then
          unless (← isEqnThm name) || isReservedName env name do
            -- A proof-valued field projection is generated by the structure
            -- declaration. Its field belongs in the construction proof.
            let parent := name.getPrefix
            if isStructure env parent && (getStructureFields env parent).any (fun f => parent ++ f == name) then
              continue
            let pos := (← findDeclarationRangesCore? name).map (·.selectionRange.pos)
            -- Lean generates size and injectivity lemmas for constructors. A
            -- user-authored theorem has its own declaration range.
            let ctor := name.getPrefix
            if pos.isNone && (env.find? ctor).any (fun info => info.isCtor) &&
                [mkSizeOfSpecLemmaName ctor, mkInjectiveTheoremNameFor ctor,
                 mkInjectiveEqTheoremNameFor ctor].contains name then continue
            entries := entries.push (pos.map (·.line) |>.getD 0, pos.map (·.column) |>.getD 0, name.toString)
    result := result ++ (entries.qsort (fun a b => compare a b == .lt)).map (·.2.2)
  if result.isEmpty then throwError "No public theorem declarations in the requested modules"
  return result.toList

/-- The package library directory, independent of how the package names its modules. -/
private def moduleDirectory (mod : Name) : IO System.FilePath := do
  let mut path ← findOLean mod
  for _ in mod.components do path := path.parent.getD path
  return path.normalize

private structure DefiningEquation where
  type : Expr
  rule : Option Name := none

private def equationsFor (decl : DefinitionVal) : MetaM (Array DefiningEquation) := do
  let mut equations := #[]
  if let some names ← (try getEqnsFor? decl.name catch _ => pure none) then
    for name in names do
      let info ← getConstInfo name
      equations := equations.push {type := info.type, rule := some name}
  if equations.isEmpty then
    -- A checked definition is definitionally equal to its body after application.
    let eq ← lambdaTelescope decl.value fun xs body => do
      let lhs := mkAppN (mkConst decl.name (decl.levelParams.map mkLevelParam)) xs
      mkForallFVars xs (← mkEq lhs body)
    -- Some definitions have a single registered unfold theorem instead of
    -- individual equations. Record its name only for this exact statement.
    let mut rule := none
    if let some name ← (try getUnfoldEqnFor? decl.name (nonRec := true) catch _ => pure none) then
      if (← getConstInfo name).type == eq then rule := some name
    equations := #[{type := eq, rule}]
  if natArity decl.type == some 1 then
    let atZero := mkApp (mkConst decl.name (decl.levelParams.map mkLevelParam)) (mkNatLit 0)
    if let some n ← getNatValue? (← whnf atZero) then
      let base ← mkEq atZero (mkNatLit n)
      unless equations.any (fun eq => eq.type == base) do equations := equations.push {type := base}
  return equations

/-- Check that a comparison is equality of the sole data field of two generic
    constructor patterns. Any other fields must actually be proofs. -/
private def comparedRecordField? (ctor : ConstructorVal) (left right test : Expr) :
    MetaM (Option Nat) := do
  let arity := ctor.numParams + ctor.numFields
  unless left.isAppOfArity ctor.name arity && right.isAppOfArity ctor.name arity do return none
  let a := left.getAppArgs
  let b := right.getAppArgs
  unless a.extract 0 ctor.numParams == b.extract 0 ctor.numParams do return none
  let leftFields := a.extract ctor.numParams arity
  let rightFields := b.extract ctor.numParams arity
  let fields := leftFields ++ rightFields
  unless fields.all (·.isFVar) && fields.allDiff do return none
  let mut data := #[]
  for i in [:leftFields.size] do
    unless ← isProp (← inferType leftFields[i]!) do data := data.push i
  let #[i] := data | return none
  let some (_, x, y) := test.eq? | return none
  return if x == leftFields[i]! && y == rightFields[i]! then some i else none

/-- A public equality instance can alias a private decision procedure. For
    one-field records, verify its actual branch test and independently check
    the kernel's constructor-injectivity equation before presenting the test. -/
private def recordEqualityTest? (decl : DefinitionVal) (equations : Array DefiningEquation) :
    MetaM (Option (Name × Json)) := do
  unless decl.type.getForallBody.isAppOfArity ``DecidableEq 1 do return none
  let #[eq] := equations | return none
  let some rule := eq.rule | return none
  forallTelescope eq.type fun params body => do
    let some (type, lhs, rhs) := body.eq? | return none
    unless type.isAppOfArity ``DecidableEq 1 && lhs.isAppOf decl.name &&
        lhs.getAppArgs == params && rhs.getAppArgs == params do return none
    let some helper := rhs.getAppFn.constName? | return none
    let env ← getEnv
    unless (isPrivateName helper || helper.hasMacroScopes) && env.isSafeDefinition helper do return none
    let some family := type.appArg!.getAppFn.constName? | return none
    unless isStructure env family do return none
    let ctor := getStructureCtor env family
    if isPrivateName ctor.name || ctor.name.isInternalDetail then return none
    let fieldNames := getStructureFields env family
    unless fieldNames.size == ctor.numFields do return none
    let inj := mkInjectiveEqTheoremNameFor ctor.name
    let some injInfo := env.find? inj | return none
    let field ← forallTelescope injInfo.type fun binders conclusion => do
      let some (_, recordEq, test) := conclusion.eq? | return none
      let some (_, left, right) := recordEq.eq? | return none
      unless binders == left.getAppArgs ++ right.getAppArgs.extract ctor.numParams right.getAppNumArgs do
        return none
      comparedRecordField? ctor left right test
    let some i := field | return none
    let some #[branch] ← (try getEqnsFor? helper catch _ => pure none) | return none
    let .str parent suffix := branch | return none
    unless parent == helper do return none
    let branchField ← forallTelescope (← getConstInfo branch).type fun binders conclusion => do
      let some (result, call, value) := conclusion.eq? | return none
      unless call.isAppOf helper && call.getAppNumArgs == params.size + 2 &&
          result.isAppOfArity ``Decidable 1 &&
          (value.isAppOfArity ``dite 5 || value.isAppOfArity ``ite 5) do return none
      let left := call.appFn!.appArg!
      let right := call.appArg!
      let patternVars := call.getAppArgs.extract 0 params.size ++
        left.getAppArgs.extract ctor.numParams left.getAppNumArgs ++
        right.getAppArgs.extract ctor.numParams right.getAppNumArgs
      unless binders == patternVars do return none
      let some (_, x, y) := result.appArg!.eq? | return none
      unless x == left && y == right do return none
      comparedRecordField? ctor left right value.getAppArgs[1]!
    unless branchField == some i do return none
    -- A hygienic Name may print its private prefix differently after appending
    -- the equation suffix. Use the same spelling as the original alias above.
    let test := Json.arr #[text "record-equality-test", text rule.toString, text family.toString,
      text ctor.name.toString, text fieldNames[i]!.toString, text inj.toString,
      text (helper.toString ++ "." ++ suffix)]
    return some (ctor.name, test)

/-- Follow the dependencies of defining equations within the selected packages.
    Imported standard-library internals stay outside a user module's definition list. -/
private def localDefinitions (modules : Array Name) (seeds : NameSet) :
    MetaM (Array Json × NameSet × NameSet) := do
  let env ← getEnv
  let standard := (← getLibDir (← getBuildDir)).normalize
  let directories ← liftM (m := IO) (modules.filterMapM fun mod => do
    try return some (← moduleDirectory mod) catch _ => return none)
  let mut localModules : NameMap Bool := {}
  let mut seen : NameSet := {}
  let mut candidates := seeds
  let mut todo := seeds.toList.toArray.qsort (fun a b => a.toString < b.toString)
  let mut definitions := #[]
  let mut decisionConstructors : NameSet := {}
  let mut i := 0
  while i < todo.size do
    let name := todo[i]!
    i := i + 1
    if seen.contains name then continue
    seen := seen.insert name
    let some (.defnInfo decl) := env.find? name | continue
    let owner := (← findModuleOf? name).getD env.mainModule
    let isLocal ← match localModules.find? owner with
      | some answer => pure answer
      | none => do
        if modules.contains owner then pure true else if owner.getRoot == `Mathlib then pure false else
          let dir ← moduleDirectory owner
          pure (dir != standard && (directories.contains dir ||
            (modules.contains env.mainModule && owner.getRoot == env.mainModule.getRoot)))
    localModules := localModules.insert owner isLocal
    if !isLocal || (privateToUserName name).isInternalDetail || name.hasMacroScopes ||
       !env.isSafeDefinition name || isMatcherCore env name || env.isProjectionFn name then continue
    let (equations, types) ← withCurrHeartbeats do
      let equations ← equationsFor decl
      return (equations, ← equations.mapM fun eq => serialize eq.type false)
    for eq in equations do
      for dep in eq.type.getUsedConstants do
        if !candidates.contains dep then
          candidates := candidates.insert dep
          todo := todo.push dep
    let rules := equations.map fun eq => text (eq.rule.map (·.toString) |>.getD "")
    let mut entry := #[text name.toString, Json.arr types, Json.arr rules]
    if let some (ctor, test) ← withCurrHeartbeats (recordEqualityTest? decl equations) then
      decisionConstructors := decisionConstructors.insert ctor
      entry := entry.push test
    definitions := definitions.push (name.toString, Json.arr entry)
  return ((definitions.qsort (fun a b => a.1 < b.1)).map (·.2), candidates, decisionConstructors)

private def internalProofName (name : Name) : Bool :=
  name.isInternalDetail || name.hasMacroScopes || isPrivateName name

private def certifiedEquation (name : Name) : MetaM Bool := do
  let .str owner suffix := name | return false
  let env ← getEnv
  if !env.isSafeDefinition owner || isMatcherCore env owner then return false
  if isEqnReservedNameSuffix suffix then
    -- The inverse registration is local to the original environment. Asking
    -- Lean for the owning definition's equations also works for imports.
    let equations ← getEqnsFor? owner
    return equations.any (fun registered => registered.contains name)
  if suffix == unfoldThmSuffix then
    return (← getUnfoldEqnFor? owner (nonRec := true)) == some name
  return false

/-- Describe only kernel-generated eliminators of a single, non-nested inductive.
    Lean records the major and minor positions in a kernel recursor. Its registered
    wrappers have different telescope orders, inspected with Lean's recursor API. -/
private def recursorRecord? (name : Name) : MetaM (Option Json) := do
  let env ← getEnv
  let (rec, branches, major, recursive) ← match env.find? name with
    | some (.recInfo rec) => do
      let family ← getConstInfoInduct rec.getMajorInduct
      let branches := (List.range rec.numMinors).map (rec.getFirstMinorIdx + ·)
      pure (rec, branches, rec.getMajorIdx, family.isRec)
    | some (.defnInfo _) => do
      let casesOn := isCasesOnRecursor env name
      if !casesOn && !isRecOnRecursor env name then return none
      let some info ← (try some <$> mkRecursorInfo name catch _ => pure none) | return none
      let family := info.typeName
      if name != (if casesOn then mkCasesOnName family else mkRecOnName family) ||
          !(info.produceMotive.all id) then return none
      let rec ← getConstInfoRec (mkRecName family)
      pure (rec, (List.range info.numArgs).filter info.isMinor, info.majorPos, info.recursive)
    | _ => return none
  let family ← getConstInfoInduct rec.getMajorInduct
  if family.all != [family.name] || family.numNested != 0 || rec.numMotives != 1 ||
      branches.length != family.ctors.length || (rec.rules.map (·.ctor)) != family.ctors then return none
  return some <| Json.arr #[text name.toString, text family.name.toString,
    Json.arr (family.ctors.toArray.map fun ctor => text ctor.toString),
    Json.arr (branches.toArray.map fun i => text (toString i)), text (toString major),
    text (if recursive then "recursion" else "cases")]

/-- A structure's constructor telescope supplies the types of its obligations,
    including proofs packaged inside an existential witness such as an isomorphism. -/
private def propertyConstructor? (name : Name) : MetaM (Option Json) := do
  let env ← getEnv
  let some (.ctorInfo ctor) := env.find? name | return none
  unless isStructure env ctor.induct && !isPrivateName name && !name.isInternalDetail do return none
  let fields := getStructureFields env ctor.induct
  if fields.isEmpty || fields.size != ctor.numFields then return none
  forallTelescope ctor.type fun xs result => do
    unless xs.size == ctor.numParams + fields.size do return none
    let property ← isProp result
    if property then
      for x in xs.extract ctor.numParams xs.size do
        unless ← isProp (← inferType x) do return none
    return some <| Json.arr #[text name.toString, ← serialize ctor.type false,
      Json.arr (fields.map fun field => text field.toString), text (if property then "property" else "object")]

/-- Certify a one-branch match on a record in Type or Prop. The motive must be
    applied to the record built from the branch binders in constructor order.
    Proof irrelevance would make definitional equality too permissive here. -/
private def matchedStructureConstructor? (name : Name) (info : Match.MatcherInfo) :
    MetaM (Option Name) := do
  unless info.numDiscrs == 1 && info.altNumParams.size == 1 &&
      Match.getNumEqsFromDiscrInfos info.discrInfos == 0 do return none
  let env ← getEnv
  forallBoundedTelescope (← getConstInfo name).type (some info.arity) fun xs _ => do
    if xs.size != info.numParams + 3 then return none
    let motive := xs[info.numParams]!
    let target ← whnf (← inferType xs[info.numParams + 1]!)
    let some family := target.getAppFn.constName? | return none
    unless isStructure env family do return none
    let ctor := getStructureCtor env family
    if ctor.numFields == 0 || info.altNumParams != #[ctor.numFields] then return none
    forallBoundedTelescope (← inferType xs[info.numParams + 2]!) (some ctor.numFields) fun fields result => do
      unless fields.size == ctor.numFields && result.isApp && result.appFn! == motive do return none
      let pattern := result.appArg!
      unless pattern.isAppOf ctor.name && pattern.getAppArgs == target.getAppArgs ++ fields do return none
      return some ctor.name

/-- Identify a two-alternative natural-number matcher from the types of its
    alternatives. A nullary alternative receives a dummy Unit argument. -/
private def matchesNatZeroSucc (name : Name) (info : Match.MatcherInfo) : MetaM Bool := do
  unless info.numParams == 0 && info.numDiscrs == 1 && info.altNumParams == #[1, 1] &&
      Match.getNumEqsFromDiscrInfos info.discrInfos == 0 do return false
  forallBoundedTelescope (← getConstInfo name).type (some info.arity) fun xs _ => do
    unless xs.size == 4 && (← whnf (← inferType xs[1]!)).isConstOf ``Nat do return false
    let atIndex := fun (alt domain : Expr) (index : Expr → Expr) => do
      forallBoundedTelescope (← inferType alt) (some 1) fun fields target => do
        if fields.size != 1 || !target.isApp || target.appFn! != xs[0]! then return false
        unless ← isDefEq (← inferType fields[0]!) domain do return false
        isDefEq target.appArg! (index fields[0]!)
    let zero ← atIndex xs[2]! (mkConst ``Unit) (fun _ => mkNatLit 0)
    if !zero then return false
    atIndex xs[3]! (mkConst ``Nat) (fun k => mkApp (mkConst ``Nat.succ) k)

/-- Identify leaf and binary-node cases from the kernel constructors and the
    registered matcher's result at each branch, in order. -/
private def binaryTreeCases? (name : Name) (info : Match.MatcherInfo) : MetaM (Option Json) := do
  unless info.numDiscrs == 1 && info.altNumParams == #[1, 3] &&
      Match.getNumEqsFromDiscrInfos info.discrInfos == 0 do return none
  forallBoundedTelescope (← getConstInfo name).type (some info.arity) fun xs _ => do
    unless xs.size == info.numParams + 4 do return none
    let motive := xs[info.numParams]!
    let target ← whnf (← inferType xs[info.numParams+1]!)
    let some family := target.getAppFn.constName? | return none
    let some (ind, leaf, node) ← binaryTreeConstructors? family | return none
    unless target.getAppNumArgs == ind.numParams do return none
    let leafOK ← forallBoundedTelescope (← inferType xs[info.numParams+2]!) (some 1) fun vars result => do
      unless vars.size == 1 && result.isApp && result.appFn! == motive &&
          (← isDefEq (← inferType vars[0]!) (mkConst ``Unit)) do return false
      let index := result.appArg!
      return index.isAppOf leaf && index.getAppArgs == target.getAppArgs
    unless leafOK do return none
    let nodeOK ← forallBoundedTelescope (← inferType xs[info.numParams+3]!) (some 3) fun vars result => do
      unless vars.size == 3 && result.isApp && result.appFn! == motive do return false
      if ← isDefEq (← inferType vars[0]!) target then return false
      unless (← isDefEq (← inferType vars[1]!) target) && (← isDefEq (← inferType vars[2]!) target) do
        return false
      let index := result.appArg!
      return index.isAppOf node && index.getAppArgs == target.getAppArgs ++ vars
    unless nodeOK do return none
    return some <| Json.arr #[text "binaryTreeCases", text family.toString, text leaf.toString, text node.toString]

/-- Internal declarations cannot be cited as public prerequisites. Follow their
    actual theorem bodies, including private user lemmas, lifted proofs and
    numeric bootstrap helpers. Public mathematical theorems retain their citation
    boundary; a registered defining equation carries its own checked evidence. -/
private def proofDependencies (theorems : Array Selection) : MetaM (NameSet × NameSet) := do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut helpers : NameSet := {}
  let mut todo := #[]
  for selection in theorems do
    todo := todo ++ selection.proof.value.getUsedConstants
  let mut i := 0
  while i < todo.size do
    let name := todo[i]!
    i := i + 1
    if seen.contains name then continue
    seen := seen.insert name
    let some (.thmInfo decl) := env.find? name | continue
    if internalProofName name || (← certifiedEquation name) then
      helpers := helpers.insert name
      todo := todo ++ decl.value.getUsedConstants
  return (seen, helpers)

/-- A definition can prove a proposition, or be a general eliminator used here
    at universe zero. Only specialize universe parameters which are zero at every
    occurrence in these checked proofs; a shared citation then applies to all of them. -/
private def definitionUses (theorems : Array Selection) (helpers : NameSet) :
    MetaM (NameMap (List Bool)) := do
  let env ← getEnv
  let uses ← IO.mkRef ({} : NameMap (List Bool))
  let note := fun (expr : Expr) => expr.forEach' (m := IO) fun e => do
    if let .const name levels := e then
      if !levels.isEmpty && (env.find? name).any (·.isDefinition) then
        let zeros := levels.map (·.isZero)
        uses.modify fun m =>
          let common := (m.find? name).map (List.zipWith (· && ·) zeros) |>.getD zeros
          m.insert name common
    return true
  for selection in theorems do note selection.proof.value
  for name in helpers do
    if let some (.thmInfo decl) := env.find? name then note decl.value
  uses.get

private def proofDefinitionType? (decl : DefinitionVal) (uses : NameMap (List Bool)) :
    MetaM (Option Expr) := do
  if decl.safety != .safe || internalProofName decl.name then return none
  if ← isProp decl.type then return some decl.type
  let some zeros := uses.find? decl.name | return none
  if !zeros.any id then return none
  let levels := decl.levelParams.zipWith (fun u z => if z then Level.zero else mkLevelParam u) zeros
  let type := decl.type.instantiateLevelParams decl.levelParams levels
  if ← isProp type then return some type else return none

private def exportDocument (modules : Array Name) (requests : List String) : MetaM Json := do
  let env ← getEnv
  let names ← if requests.isEmpty then discoverTheorems modules else pure requests
  let theorems ← names.toArray.mapM fun name => withCurrHeartbeats (selectTheorem name)
  -- Checked dependency closures overlap substantially for a whole mathematics file.
  -- Reuse Lean's own axiom collector state across declarations and alternate proofs.
  let mut axioms : CollectAxioms.State := {}
  for selection in theorems do
    for name in #[selection.original.name, selection.proof.name] do
      if axioms.visited.contains name then continue
      axioms := ((CollectAxioms.collect name).run env).run axioms |>.2
      if axioms.axioms.contains ``sorryAx then throwError "Theorem '{name}' depends on a sorry"
  let records ← theorems.mapM exportTheorem
  let (dependencies, helpers) ← withCurrHeartbeats (proofDependencies theorems)
  let uses ← definitionUses theorems helpers
  let mut prerequisites := #[]
  let mut matchers := #[]
  let mut recursors := #[]
  let mut propertyConstructors := #[]
  let mut matchedConstructors : NameSet := {}
  let mut helperBodies := #[]
  let mut candidates : NameSet := {}
  for selection in theorems do
    for name in selection.original.type.getUsedConstants do candidates := candidates.insert name
  for name in dependencies.toList.toArray.qsort (fun left right => left.toString < right.toString) do
    candidates := candidates.insert name
    if let some recursor ← withCurrHeartbeats (recursorRecord? name) then recursors := recursors.push recursor
    if let some ctor ← withCurrHeartbeats (propertyConstructor? name) then
      propertyConstructors := propertyConstructors.push ctor
    if let some (.thmInfo declaration) := env.find? name then
      for dep in declaration.type.getUsedConstants do candidates := candidates.insert dep
      let typeJson ← withCurrHeartbeats (serialize declaration.type false)
      let visibility := if helpers.contains name then "internal" else "public"
      let mut entry := #[text name.toString, typeJson, text visibility]
      if visibility == "public" then
        if let some doc ← findSimpleDocString? env name (includeBuiltin := false) then
          entry := entry.push (text (doc.take 512))
      prerequisites := prerequisites.push (Json.arr entry)
      if helpers.contains name then
        helperBodies := helperBodies.push (Json.arr #[text name.toString, typeJson,
          ← proofEvidence name declaration.value])
    else if let some (.defnInfo declaration) := env.find? name then
      if let some type ← withCurrHeartbeats (proofDefinitionType? declaration uses) then
        for dep in type.getUsedConstants do candidates := candidates.insert dep
        prerequisites := prerequisites.push (Json.arr #[text name.toString,
          ← withCurrHeartbeats (serialize type false), text "public"])
    if let some info := getMatcherInfoCore? env name then
      let mut record := #[
        text name.toString, text (toString info.numParams), text (toString info.numDiscrs),
        Json.arr (info.altNumParams.map (fun size => text (toString size))),
        text (toString (Match.getNumEqsFromDiscrInfos info.discrInfos))]
      if let some ctor ← withCurrHeartbeats (matchedStructureConstructor? name info) then
        matchedConstructors := matchedConstructors.insert ctor
        record := record.push (text ctor.toString)
      else if ← withCurrHeartbeats (matchesNatZeroSucc name info) then
        record := record.push (Json.arr #[text "natCases", text "Nat.zero", text "Nat.succ"])
      else if let some cases ← withCurrHeartbeats (binaryTreeCases? name info) then
        record := record.push cases
      matchers := matchers.push (Json.arr record)
  let (definitions, allCandidates, decisionConstructors) ← localDefinitions modules candidates
  for name in decisionConstructors do matchedConstructors := matchedConstructors.insert name
  for name in matchedConstructors.toList.toArray.qsort (fun a b => a.toString < b.toString) do
    if !dependencies.contains name then
      if let some ctor ← withCurrHeartbeats (propertyConstructor? name) then
        propertyConstructors := propertyConstructors.push ctor
  let mut symbols := #[]
  for name in allCandidates.toList.toArray.qsort (fun a b => a.toString < b.toString) do
    if let some (.defnInfo declaration) := env.find? name then
      if let some arity := natArity declaration.type then
        symbols := symbols.push (Json.arr #[text name.toString, text (toString arity)])
  return Json.arr #[Json.arr records, Json.arr prerequisites, Json.arr matchers, Json.arr symbols,
    Json.arr definitions, Json.arr #[], Json.arr helperBodies, Json.arr recursors,
    Json.arr #[], Json.arr propertyConstructors]

private def exportModules (moduleList : String) (names : List String) : IO Json := do
  let modules := (moduleList.splitOn ",").toArray.map String.toName
  let imports := modules.map fun name => {module := name : Import}
  let env ← importModules (loadExts := true) (leakEnv := true) imports {}
  let action := exportDocument modules names
  let (document, _) ← action.run'.toIO {fileName := "Adapter.lean", fileMap := default} {env}
  return document

private def exportGoal (goal : MVarId) : MetaM Json := goal.withContext do
  let mut locals := #[]
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let type ← instantiateMVars decl.type
    locals := locals.push (Json.arr #[text decl.fvarId.name.toString, binderName decl.userName,
      ← serialize type false, ← roleFromType type])
  return Json.arr #[text goal.name.toString, Json.arr locals,
    ← serialize (← instantiateMVars (← goal.getType)) false]

private def reflexivityFact (term expected : Expr) : MetaM (Option Json) := do
  let bare := term.consumeMData
  -- A source-level `show ... from rfl` wraps reflexivity in a typed `letFun`.
  let proof ← if bare.isAppOf ``letFun || bare.isLet then whnf bare else pure bare
  let .const name _ := proof.getAppFn | return none
  unless [``Eq.refl, ``Iff.rfl, `rfl].contains name do return none
  unless expected.isAppOf ``Eq || expected.isAppOf ``Iff do return none
  unless ← isDefEqGuarded (← inferType term) expected do return none
  return some (Json.arr #[text "reflexivity", text name.toString, ← serialize expected false, Json.arr #[]])

/-- Keep every proof premise of an applied rule, including unproved goals of an
    `apply` step. Its conclusion and premise *statements* must already be determined. -/
private def stepEvidence (goal : MVarId) (openApplication : Bool) : MetaM (Array Json) := goal.withContext do
  let some assigned ← getExprMVarAssignment? goal | return #[]
  let proof ← instantiateMVars assigned
  let seen ← IO.mkRef ({} : Std.HashSet Expr)
  let facts ← IO.mkRef (#[] : Array Json)
  let expected ← instantiateMVars (← goal.getType)
  if let some fact ← reflexivityFact proof expected then
    facts.modify (·.push fact)
    seen.modify (·.insert expected)
  proof.forEach' fun e => do
    if !e.hasLooseBVars && (!e.hasMVar || (openApplication && e == proof)) then
      let fn := e.getAppFn
      let name? ← if fn.isFVar then
        pure (some ("local", fn.fvarId!.name))
      else if let .const name _ := fn then
        let env ← getEnv
        if internalProofName name then pure none else
          match env.find? name with
          | some (.thmInfo _) => pure <| some ("theorem", name)
          | some (.defnInfo d) => do
            if d.safety == .safe && (← isProp (← inferType fn)) then pure <| some ("theorem", name)
            else pure none
          | _ => pure none
      else pure none
      if let some (origin, name) := name? then
        let type ← instantiateMVars (← inferType e)
        if !type.hasMVar && !type.hasLooseBVars && !type.isForall && (← isProp type) &&
            !(← seen.get).contains type then
          let mut premises := #[]
          let mut fnType ← inferType fn
          for arg in e.getAppArgs do
            let .forallE _ domain body _ ← whnf fnType | return true
            if ← isProp domain then
              let premise ← instantiateMVars domain
              if premise.hasMVar || premise.hasLooseBVars then return true
              premises := premises.push (← serialize premise false)
              if !(← seen.get).contains premise then
                if let some fact ← reflexivityFact arg premise then
                  facts.modify (·.push fact)
                  seen.modify (·.insert premise)
            fnType := body.instantiate1 arg
          facts.modify (·.push (Json.arr #[text origin, text name.toString,
            ← serialize type false, Json.arr premises]))
          seen.modify (·.insert type)
    return true
  facts.get

private def tacticKind? (stx : Syntax) : Option String := do
  let .atom (.original ..) token := stx[0] | none
  let families := ["simp", "simp_all", "simpa", "rw", "rwa", "exact", "apply", "induction",
    "cases", "split", "by_cases", "omega", "linarith", "rfl", "intro", "intros", "constructor", "assumption",
    "ext", "ext1"]
  if !families.contains token then none else
    some <| if ["simp_all", "simpa"].contains token then "simp"
      else if token == "rwa" then "rw" else if token == "intros" then "intro"
      else if token == "split" || token == "by_cases" then "cases"
      else if token == "ext1" then "ext" else token

private def splitGoals (ctx : Elab.ContextInfo) (stx : Syntax)
    (children : PersistentArray Elab.InfoTree) : IO (Array Json) := do
  let some alts := stx.find? (·.isOfKind ``Parser.Tactic.inductionAlts) | return #[]
  if !alts[1].isNone then return #[]
  -- Lean's induction elaborator runs each explicit alternative in a TacticInfo
  -- scope with the span of that alternative's left-hand side and arrow.
  let spans := alts[2].getArgs.map fun alt => (alt[0].getPos?, alt[1].getTailPos?)
  let starts ← IO.mkRef (#[] : Array ((Option String.Pos × Option String.Pos) × Json))
  for tree in children do
    tree.visitM' (ctx? := some ctx) (preNode := fun branchCtx info _ => do
      if let .ofTacticInfo branch := info then
        let span := (branch.stx.getPos?, branch.stx.getTailPos?)
        if branch.stx.isOfKind nullKind && spans.contains span then
          if let [goal] := branch.goalsBefore then
            let state ← {branchCtx with mctx := branch.mctxBefore}.runMetaM {} (exportGoal goal)
            starts.modify (·.push (span, state))
          return false
      return true)
  let starts ← starts.get
  if starts.map (·.1) != spans then return #[]
  return starts.map (·.2)

private def exportTactic (ctx : Elab.ContextInfo) (info : Elab.TacticInfo) (kind : String)
    (children : PersistentArray Elab.InfoTree) : IO Json := do
  let before ← { ctx with mctx := info.mctxBefore }.runMetaM {} (info.goalsBefore.mapM exportGoal)
  let (after, facts, certificates) ← { ctx with mctx := info.mctxAfter }.runMetaM {} do
    let after ← info.goalsAfter.mapM exportGoal
    let mut facts := #[]
    let mut certificates := #[]
    for goal in info.goalsBefore do
      if info.goalsAfter.contains goal then continue
      if !(["omega", "linarith", "induction", "cases"].contains kind) then
        facts := facts ++ (← stepEvidence goal (kind == "apply" || kind == "ext"))
      if kind == "omega" || kind == "linarith" then
        let some value ← getExprMVarAssignment? goal | continue
        let value ← instantiateMVars value
        if !value.hasMVar then
          certificates := certificates.push (Json.arr #[text goal.name.toString,
            ← goal.withContext (proofEvidence goal.name value)])
    return (after, facts, certificates)
  let after ← if (kind == "induction" || kind == "cases") && before.length == 1 && after.isEmpty then
      splitGoals ctx info.stx children
    else pure after.toArray
  return Json.arr #[text kind, Json.arr before.toArray, Json.arr after, Json.arr facts,
    Json.arr certificates]

private structure Trace where
  steps : Array Json := #[]
  roots : Array String := #[]
  deriving Inhabited

private structure SourceExample where
  start : String.Pos
  stop : String.Pos
  original : Name
  alias : Name
  env : Environment
  renames : NameMap Name := {}

/-- The frontend deliberately records the checked example in a scoped environment
    and discards it from its module. Recover that exact declaration by source span. -/
private def findExamples (st : Elab.Frontend.State) : IO (Array SourceExample) := do
  let mut spans := #[]
  for command in st.commands do
    for node in command.topDown do
      if node.isOfKind ``Parser.Command.example then
        spans := spans.push (node.getPos?.get!, node.getTailPos?.get!)
  if spans.isEmpty then return #[]
  let result ← IO.mkRef (#[] : Array SourceExample)
  for tree in st.commandState.infoState.trees do
    tree.visitM' (preNode := fun ctx info _ => do
      let some name := ctx.parentDecl? | return true
      unless name.getString! == "_example" do return true
      let some pos := info.stx.getPos? | return true
      let some i := spans.findIdx? (fun (a,b) => a ≤ pos && pos < b) | return true
      let (start,stop) := spans[i]!
      if (← result.get).any (fun ex => ex.start == start) then return false
      if !(ctx.env.checked.get.find? name).isSome then return true
      let mut alias := name.getPrefix.str s!"Example_{i + 1}"
      while (st.commandState.env.contains alias) do alias := alias.appendAfter "_"
      result.modify (·.push {start, stop, original := name, alias, env := ctx.env})
      return false)
  let found ← result.get
  if found.size != spans.size then throw <| IO.userError "Could not recover every checked anonymous example"
  return found.qsort (fun a b => a.start < b.start)

/-- Recheck each recovered proof under a distinct paper identifier. Auxiliary
    declarations removed with the example (including separately lifted proofs) get
    their own names too. This prevents two anonymous proofs sharing a helper by accident. -/
private partial def replayExample (ex : SourceExample) (name : Name) (renames : NameMap Name) :
    MetaM (NameMap Name) := do
  if renames.contains name then return renames
  let some src := ex.env.checked.get.find? name | throwError "Missing constant '{name}' in a checked example"
  if name != ex.original then
    if let some shared := (← getEnv).find? name then
      if shared.type == src.type && shared.value? true == src.value? true then return renames
  let some body := src.value? true | throwError "Cannot replay example-local declaration '{name}'"
  let mut renames := renames
  for dep in src.type.getUsedConstants ++ body.getUsedConstants do
    renames ← replayExample ex dep renames
  let rename (e : Expr) := e.replace fun
    | .const n ls => (renames.find? n).map (fun newName => mkConst newName ls)
    | _ => none
  let alias := if name == ex.original then ex.alias else ex.alias ++ name
  let type := rename src.type
  let value := rename body
  let decl ← if name == ex.original || src.isTheorem then
      pure <| Declaration.thmDecl { name := alias, type, value, levelParams := src.levelParams }
    else match src with
    | .defnInfo v => pure <| .defnDecl {v with name := alias, type, value, all := [alias]}
    | .opaqueInfo v => pure <| .opaqueDecl {v with name := alias, type, value, all := [alias]}
    | _ => throwError "Unsupported local declaration '{name}' in anonymous example"
  withOptions (fun opts => Elab.async.set opts false) (addDecl decl)
  return renames.insert name alias

private partial def renameTrace (renames : NameMap Name) : Json → Json
  | .arr xs => Id.run do
    let mut ys := xs.map (renameTrace renames)
    if let some (Json.str tag) := xs[0]? then
      if tag == "c" || tag == "theorem" || tag == "proj" then
        if let some (Json.str name) := xs[1]? then
          if let some alias := renames.find? name.toName then ys := ys.set! 1 (text alias.toString)
    return Json.arr ys
  | other => other

private def collectTraces (st : Elab.Frontend.State) (names : List String)
    (examples : Array SourceExample) : IO Json := do
  -- Only a direct declaration body can certify the root of a complete tactic proof.
  let mut bodies : Array (Option String.Pos × Option String.Pos) := #[]
  for command in st.commands do
    if let some val := command.find? (·.isOfKind ``Parser.Command.declValSimple) then
      let body := val[1]
      if body.isOfKind ``Parser.Term.byTactic then bodies := bodies.push (body.getPos?, body.getTailPos?)
  let traces ← IO.mkRef ({} : NameMap Trace)
  for tree in st.commandState.infoState.trees do
    tree.visitM' (preNode := fun ctx info children => do
      let some name := ctx.parentDecl? | return true
      let ex? := examples.find? fun ex => name == ex.original &&
        (info.stx.getPos?.any fun pos => ex.start ≤ pos && pos < ex.stop)
      let name := ex?.map (·.alias) |>.getD name
      if !names.contains name.toString then return true
      if let .ofTermInfo term := info then
        if term.stx.isOfKind ``Parser.Term.byTactic && bodies.contains (term.stx.getPos?, term.stx.getTailPos?) then
          if let .mvar root := term.expr.consumeMData then
            let old := ((← traces.get).find? name).getD {}
            if !old.roots.contains root.name.toString then
              traces.modify (·.insert name {old with roots := old.roots.push root.name.toString})
      if let .ofTacticInfo tactic := info then
        if tactic.stx.isOfKind ``Parser.Term.byTactic &&
            bodies.contains (tactic.stx.getPos?, tactic.stx.getTailPos?) &&
            tactic.goalsAfter.isEmpty then
          let old := ((← traces.get).find? name).getD {}
          traces.modify (·.insert name {old with roots := (old.roots ++
            (tactic.goalsBefore.toArray.map (·.name.toString))).toList.eraseDups.toArray})
        if let some kind := tacticKind? tactic.stx then
          if !tactic.goalsBefore.isEmpty && tactic.goalsBefore != tactic.goalsAfter then
            let step ← exportTactic ctx tactic kind children
            let step := ex?.map (fun ex => renameTrace ex.renames step) |>.getD step
            let old := ((← traces.get).find? name).getD {}
            traces.modify (·.insert name {old with steps := old.steps.push step})
            return kind == "induction" || kind == "cases"
      return true)
  let entries := (← traces.get).toList.toArray.qsort (fun x y => x.1.toString < y.1.toString)
  return Json.arr <| entries.map fun (name, trace) =>
    Json.arr #[text name.toString, Json.arr trace.steps, Json.arr (trace.roots.map text)]

private structure CommandPlacement where
  start : String.Pos
  stop : String.Pos
  sections : Array String
  namespaceName : Name

/-- The actual scope stack distinguishes a namespace frame (its namespace
    changes) from a section frame (its namespace stays the same). Lean already
    handled anonymous scopes, compound headers and matching end commands. -/
private partial def commandPlacements (snap : Language.Lean.CommandParsedSnapshot)
    (scopes : List Elab.Command.Scope) (acc : Array CommandPlacement := #[]) :
    Array CommandPlacement := Id.run do
  let mut acc := acc
  if let some start := snap.stx.getPos? then
    if let some stop := snap.stx.getTailPos? then
      let mut parent := Name.anonymous
      let mut sections := #[]
      for frame in scopes.reverse do
        if !frame.header.isEmpty && frame.currNamespace == parent then
          sections := sections.push frame.header
        parent := frame.currNamespace
      acc := acc.push {start, stop, sections, namespaceName := parent}
  if let some next := snap.nextCmdSnap? then
    return commandPlacements next.get snap.resultSnap.get.cmdState.scopes acc
  return acc

private def declarationPlacements (names : List String) (commands : Array CommandPlacement)
    (fileMap : FileMap) : MetaM Json := do
  let env ← getEnv
  let mut entries := #[]
  for request in names do
    let name := ((request.splitOn "=").head!).toName
    if (← findModuleOf? name).getD env.mainModule != env.mainModule then continue
    let some ranges ← findDeclarationRangesCore? name | continue
    let pos := fileMap.ofPosition ranges.selectionRange.pos
    let some cmd := commands.find? (fun c => c.start ≤ pos && pos < c.stop) | continue
    let ns := if cmd.namespaceName.isAnonymous then "" else cmd.namespaceName.toString
    let doc := (← findSimpleDocString? env name (includeBuiltin := false)).getD ""
    entries := entries.push <| Json.arr #[text name.toString, Json.arr (cmd.sections.map text), text ns, text doc]
  return Json.arr entries

private def exportSource (fileName : String) (requests : List String) : IO Json := do
  let file : System.FilePath := fileName
  let searchRoots ← initSrcSearchPath
  let moduleName := (← searchModuleNameOfFileName file (searchRoots ++ [← IO.currentDir])).getD
    (Name.mkSimple (file.fileStem.getD "Source"))
  let input := Parser.mkInputContext (← IO.FS.readFile file) fileName
  let (header, parserState, messages) ← Parser.parseHeader input
  let opts := Elab.async.set {} false
  let (env, messages) ← Elab.processHeader header opts messages input (leakEnv := true)
  let commandState := Elab.Command.mkState (env.setMainModule moduleName) messages opts
  let (st, placements) ← do
    let snapshot ← Elab.IO.processCommandsIncrementally input parserState
      {commandState with infoState.enabled := true} none
    pure (snapshot.toState, commandPlacements snapshot.initialSnap commandState.scopes)
  if st.commandState.messages.hasErrors then
    for msg in st.commandState.messages.toList do
      if msg.severity == .error then IO.eprintln (← msg.toString)
    throw <| IO.userError "The source file has Lean errors"
  let sourceExamples ← if requests.isEmpty then findExamples st else pure #[]
  let action : MetaM _ := do
    let mut examples := #[]
    for ex in sourceExamples do
      let decl := (ex.env.checked.get.find? ex.original).get!
      if !(← withEnv ex.env (isProp decl.type)) then
        let pos := input.fileMap.toPosition ex.start
        IO.eprintln s!"{fileName}:{pos.line}:{pos.column}: skipping data-valued {ex.alias} (no proof statement)"
        continue
      let renames ← replayExample ex ex.original {}
      addDocStringCore' ex.alias (← findSimpleDocString? ex.env ex.original (includeBuiltin := false))
      let pos := input.fileMap.toPosition ex.start
      let stop := input.fileMap.toPosition ex.stop
      let range : DeclarationRange := ⟨pos, pos.column, stop, stop.column⟩
      addDeclarationRanges ex.alias ⟨range, range⟩
      examples := examples.push {ex with renames}
    let names ← if requests.isEmpty then discoverTheorems #[moduleName] else pure requests
    let doc ← exportDocument #[moduleName] names
    return (names, doc, examples, ← declarationPlacements names placements input.fileMap)
  let ((names, doc, examples, sections), _) ← action.run'.toIO {fileName, fileMap := input.fileMap} {env := st.commandState.env}
  let .arr entries := doc | throw <| IO.userError "Invalid document"
  return Json.arr <| (entries.set! 5 (← collectTraces st names examples)).set! 8 sections

def run (output input : String) (names : List String) : IO Unit := do
  initSearchPath (← getBuildDir)
  let document ← if input.endsWith ".lean" then exportSource input names else exportModules input names
  if output == "-" then
    IO.println document.compress
  else
    IO.FS.writeFile output (document.compress ++ "\n")

end Adapter

unsafe def main (args : List String) : IO UInt32 := do
  match args with
  | output :: modules :: rest =>
    try
      -- This is a standalone, single-project frontend. The outer `lean --run`
      -- import phase has already reset this flag. Keep imported regions alive
      -- because package initializers may retain references into them.
      enableInitializersExecution
      Adapter.run output modules rest
      return 0
    catch error =>
      IO.eprintln error.toString
      return 1
  | _ =>
    IO.eprintln "Usage: lean --run Adapter.lean <output.json|-> <file.lean | module[,module...]> [theorem[=alternate] ...]"
    return 1
