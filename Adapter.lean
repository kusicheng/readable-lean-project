import Lean

open Lean Lean.Meta

namespace Adapter

private def text := Json.str

private def binderId (var : Expr) : Json :=
  text var.fvarId!.name.toString

private def binderName (name : Name) : Json :=
  text name.eraseMacroScopes.toString

/-- Export kernel expressions while opening binders for local type inference.
    Proof annotations are suppressed in type trees and on application heads. -/
private partial def serialize (expression : Expr) (annotateProofs : Bool) : MetaM Json := do
  let e := if annotateProofs then expression else expression.headBeta
  let raw ← match e with
    | .const name _ => pure <| Json.arr #[text "c", text name.toString]
    | .fvar _ => pure <| Json.arr #[text "v", binderId e]
    | .lam name domain body info => do
      let domainJson ← serialize domain false
      withLocalDecl name info domain fun var => do
        let bodyJson ← serialize (body.instantiate1 var) annotateProofs
        return Json.arr #[text "l", binderId var, binderName name, domainJson, bodyJson]
    | .forallE name domain body info => do
      let domainJson ← serialize domain false
      withLocalDecl name info domain fun var => do
        let bodyJson ← serialize (body.instantiate1 var) false
        return Json.arr #[text "q", binderId var, binderName name, domainJson, bodyJson]
    | .letE name domain value body _ => do
      let domainJson ← serialize domain false
      let valueJson ← serialize value annotateProofs
      withLetDecl name domain value fun var => do
        let bodyJson ← serialize (body.instantiate1 var) annotateProofs
        return Json.arr #[text "t", binderId var, binderName name, domainJson, valueJson, bodyJson]
    | .app .. => do
      let fn ← serialize e.getAppFn false
      let args ← e.getAppArgs.mapM fun arg => serialize arg annotateProofs
      pure <| Json.arr (#[text "a", fn] ++ args)
    | .lit (.natVal n) => pure <| Json.arr #[text "n", text (toString n)]
    | .sort level => pure <| Json.arr #[text "s", text (toString level)]
    | .mdata _ body => serialize body annotateProofs
    | .proj .. => pure <| Json.arr #[text "u", text "projection"]
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
  if (← Lean.collectAxioms name).contains ``sorryAx then
    throwError "Theorem '{theoremName}' depends on a sorry"
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

private def exportTheorem (selection : Selection) : MetaM Json := do
  let typeJson ← serialize selection.original.type false
  let valueJson ← serialize selection.proof.value true
  let record := #[text selection.original.name.toString, typeJson, valueJson]
  return Json.arr <| if selection.original.name == selection.proof.name then record
    else record.push (text selection.proof.name.toString)

private def exportDocument (names : List String) : MetaM Json := do
  let env ← getEnv
  let theorems ← names.toArray.mapM selectTheorem
  let records ← theorems.mapM exportTheorem
  let mut dependencies : Array Name := #[]
  for selection in theorems do
    for dependency in selection.proof.value.getUsedConstants do
      if !dependencies.contains dependency then
        dependencies := dependencies.push dependency
  let mut prerequisites := #[]
  let mut matchers := #[]
  for name in dependencies.qsort (fun left right => left.toString < right.toString) do
    if let some (.thmInfo declaration) := env.find? name then
      let typeJson ← serialize declaration.type false
      let visibility := if name.isInternalDetail || Lean.isPrivateName name then "internal" else "public"
      prerequisites := prerequisites.push (Json.arr #[text name.toString, typeJson, text visibility])
    if let some info := getMatcherInfoCore? env name then
      matchers := matchers.push <| Json.arr #[
        text name.toString, text (toString info.numParams), text (toString info.numDiscrs),
        Json.arr (info.altNumParams.map (fun size => text (toString size))),
        text (toString (Match.getNumEqsFromDiscrInfos info.discrInfos))]
  return Json.arr #[Json.arr records, Json.arr prerequisites, Json.arr matchers]

def run (output moduleList : String) (names : List String) : IO Unit := do
  initSearchPath (← getBuildDir)
  let imports := (moduleList.splitOn ",").toArray.map fun name => {module := name.toName : Import}
  let env ← importModules imports {}
  let action := exportDocument names
  let (document, _) ← action.run'.toIO {fileName := "Adapter.lean", fileMap := default} {env}
  if output == "-" then
    IO.println document.compress
  else
    IO.FS.writeFile output (document.compress ++ "\n")

end Adapter

def main (args : List String) : IO UInt32 := do
  match args with
  | output :: modules :: first :: rest =>
    try
      Adapter.run output modules (first :: rest)
      return 0
    catch error =>
      IO.eprintln error.toString
      return 1
  | _ =>
    IO.eprintln "Usage: lean --run Adapter.lean <output.json|-> <module[,module...]> <theorem[=alternate]>..."
    return 1
