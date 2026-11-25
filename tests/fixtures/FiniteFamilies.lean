import Mathlib.Combinatorics.SimpleGraph.Subgraph

namespace FiniteFamilies

variable {V : Type} {G : SimpleGraph V} (M : G.Subgraph)

example [∀ v, Fintype (M.neighborSet v)] (v : V) : M.degree v = M.degree v := rfl

-- The enumerated neighbors belong to f v, rather than v.
example (f : V → V) [∀ v, Fintype (M.neighborSet (f v))] (v : V) :
    M.neighborSet (f v) = M.neighborSet (f v) := rfl

example (F : V → Type) [∀ v, Fintype (F v)] (v : V) : F v = F v := rfl

end FiniteFamilies
