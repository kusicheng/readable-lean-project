import Lean
open Lean Lean.Meta

structure Twin (P : Prop) : Prop where
  left : P
  right : P

private def positional (P : Prop) (motive : Twin P → Prop) (h : Twin P)
    (step : ∀ (a b : P), motive ⟨a, b⟩) : motive h :=
  step h.left h.right

private def reversed (P : Prop) (motive : Twin P → Prop) (h : Twin P)
    (step : ∀ (a b : P), motive ⟨b, a⟩) : motive h :=
  step h.right h.left

-- Supply the same arity metadata for the two distinct kernel-checked signatures.
run_meta do
  for name in [``positional, ``reversed] do
    Match.addMatcherInfo name {
      numParams := 1, numDiscrs := 1, altNumParams := #[2],
      uElimPos? := none, discrInfos := #[{}] }

theorem inOrder (P : Prop) (h : Twin P) : P :=
  positional P (fun _ => P) h (fun a _ => a)

theorem outOfOrder (P : Prop) (h : Twin P) : P :=
  reversed P (fun _ => P) h (fun a _ => a)
