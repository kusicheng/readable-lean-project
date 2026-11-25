import Init

namespace ConditionalEquations

def step (n : Nat) : Nat :=
  if h : n > 0 then
    letFun h fun _ => n + 1
  else 0

def useProof (n : Nat) (f : n > 0 → Nat) : Nat :=
  if h : n > 0 then letFun h fun k => f k else 0

def useValue (n : Nat) : Nat :=
  letFun (n + 1) fun x => x + x

example (n : Nat) : step n = step n := rfl
example (n : Nat) (f : n > 0 → Nat) : useProof n f = useProof n f := rfl
example (n : Nat) : useValue n = useValue n := rfl

end ConditionalEquations
