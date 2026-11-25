# Generated papers and their Lean sources

## A short proof to read first

The two-page Bell paper derives a recurrence by taking the last factor of a finite product, then obtains a factorial quotient by dividing by a positive integer. It compiles two original Mathlib proofs with their prerequisites stated on page 1. The three-page matching paper shows why the number of vertices covered by a matching is even. Both papers are direct compiler output. [Bell PDF](../papers/uniform-bell.pdf) · [Bell LaTeX](../papers/uniform-bell.tex) · [Matching PDF](../papers/matching-parity.pdf) · [Matching LaTeX](../papers/matching-parity.tex)

Suppose $x$ and $y$ are rational numbers with $2x+y\le 9$ and $1\le y$. To prove $x\le 4$, the generated paper assumes $x>4$ and adds three inequalities. Doubling $4-x<0$ cancels the $2x$ from the first inequality. The sum would give $0<0$. The compact edition gives that argument in three sentences. The expanded edition also shows how the inequalities were rearranged. Both retain the rounding step in the paper's separate integer proof. [Lean source](../tests/fixtures/Arithmetic.lean) · [Compact PDF](../papers/arithmetic-certificates.pdf) · [Compact LaTeX](../papers/arithmetic-certificates.tex) · [Expanded PDF](../papers/arithmetic-certificates-expanded-current.pdf) · [Expanded LaTeX](../papers/arithmetic-certificates-expanded.tex)

## Two answers to the same exercise

The exercise asks for a finite-sum proof of the weighted pigeonhole principle. Submission A cites the weighted pigeonhole theorem with the required hypotheses. Submission B shows how to partition the total weight by fibers and extract a witness from a strict comparison of sums. The exercise, scoring criteria and reader results are in [the evaluation](evaluation.md#grading-a-generated-proof). [Both Lean submissions](../tests/fixtures/FiberSubmissions.lean) · [A as PDF](../papers/gradeability-fiber-a.pdf) · [A as LaTeX](../papers/gradeability-fiber-a.tex) · [B as PDF](../papers/gradeability-fiber-b.pdf) · [B as LaTeX](../papers/gradeability-fiber-b.tex)

## A paper built from a complete library file

In the Hamiltonian graph paper, click either lemma citation in **Corollary 5** to go directly to its statement and proof. Lemma 2 shows that a Hamiltonian path visits every vertex, and Lemma 4 proves the converse for a path. For a counting argument, start with **Lemma 7** on page 7. A Hamiltonian path visits each vertex once, so its vertex sequence has one entry per vertex and the path has one fewer edge. **Theorem 13** applies that lemma to the tail of a cycle to show the cycle has as many edges as vertices. Each equality in those counts comes from the checked proof. [PDF](../papers/mathlib-hamiltonian-linked.pdf) · [LaTeX](../papers/mathlib-hamiltonian.tex) · [Original Lean file](https://github.com/leanprover-community/mathlib4/blob/c44e0c8ee63ca166450922a373c7409c5d26b00b/Mathlib/Combinatorics/SimpleGraph/Hamiltonian.lean)

In the derangements paper, Lemma 2 counts objects using a bijection supplied by Mathlib. The compiler identifies its domain and the two alternatives in its range. The proof of the final alternating-sum formula states the sum at zero, then gives the successor step and its induction hypothesis. The article was typeset directly from the compiler's LaTeX. [PDF](../papers/mathlib-derangements.pdf) · [LaTeX](../papers/mathlib-derangements.tex) · [Original Lean file](https://github.com/leanprover-community/mathlib4/blob/c44e0c8ee63ca166450922a373c7409c5d26b00b/Mathlib/Combinatorics/Derangements/Finite.lean)

The following articles likewise use the entire original source file. Each Lean link identifies the Mathlib 4.19 revision used in the experiment.

| Article | Generated paper | Lean input |
|---|---|---|
| Refined Bell numbers | [PDF](../papers/mathlib-bell.pdf) · [LaTeX](../papers/mathlib-bell.tex) | [Bell](https://github.com/leanprover-community/mathlib4/blob/c44e0c8ee63ca166450922a373c7409c5d26b00b/Mathlib/Combinatorics/Enumerative/Bell.lean) |
| Dyck words and binary trees | [PDF](../papers/mathlib-dyck-words.pdf) · [LaTeX](../papers/mathlib-dyck-words.tex) | [DyckWord](https://github.com/leanprover-community/mathlib4/blob/c44e0c8ee63ca166450922a373c7409c5d26b00b/Mathlib/Combinatorics/Enumerative/DyckWord.lean) |
| Matchings in graphs | [PDF](../papers/mathlib-matching.pdf) · [LaTeX](../papers/mathlib-matching.tex) | [Matching](https://github.com/leanprover-community/mathlib4/blob/c44e0c8ee63ca166450922a373c7409c5d26b00b/Mathlib/Combinatorics/SimpleGraph/Matching.lean) |
| Pigeonhole principles | [PDF](../papers/mathlib-pigeonhole.pdf) · [LaTeX](../papers/mathlib-pigeonhole.tex) | [Pigeonhole](https://github.com/leanprover-community/mathlib4/blob/c44e0c8ee63ca166450922a373c7409c5d26b00b/Mathlib/Combinatorics/Pigeonhole.lean) |
| Double counting | [PDF](../papers/mathlib-double-counting.pdf) · [LaTeX](../papers/mathlib-double-counting.tex) | [DoubleCounting](https://github.com/leanprover-community/mathlib4/blob/c44e0c8ee63ca166450922a373c7409c5d26b00b/Mathlib/Combinatorics/Enumerative/DoubleCounting.lean) |
| Subsets of a finite set | [PDF](../papers/mathlib-powerset.pdf) · [LaTeX](../papers/mathlib-powerset.tex) | [Powerset](https://github.com/leanprover-community/mathlib4/blob/c44e0c8ee63ca166450922a373c7409c5d26b00b/Mathlib/Data/Finset/Powerset.lean) |
| Degree sum | [PDF](../papers/mathlib-degree-sum.pdf) · [LaTeX](../papers/mathlib-degree-sum.tex) | [DegreeSum](https://github.com/leanprover-community/mathlib4/blob/c44e0c8ee63ca166450922a373c7409c5d26b00b/Mathlib/Combinatorics/SimpleGraph/DegreeSum.lean) |
| Hall's marriage theorem | [PDF](../papers/mathlib-hall.pdf) · [LaTeX](../papers/mathlib-hall.tex) | [Hall](https://github.com/leanprover-community/mathlib4/blob/c44e0c8ee63ca166450922a373c7409c5d26b00b/Mathlib/Combinatorics/Hall/Finite.lean) |
| Inclusion-exclusion | [PDF](../papers/mathlib-inclusion-exclusion.pdf) · [LaTeX](../papers/mathlib-inclusion-exclusion.tex) | [InclusionExclusion](https://github.com/leanprover-community/mathlib4/blob/c44e0c8ee63ca166450922a373c7409c5d26b00b/Mathlib/Combinatorics/Enumerative/InclusionExclusion.lean) |
| Intersecting families | [PDF](../papers/mathlib-intersecting.pdf) · [LaTeX](../papers/mathlib-intersecting.tex) | [Intersecting](https://github.com/leanprover-community/mathlib4/blob/c44e0c8ee63ca166450922a373c7409c5d26b00b/Mathlib/Combinatorics/SetFamily/Intersecting.lean) |
| Cardinalities of finite sets | [PDF](../papers/mathlib-finset-card.pdf) · [LaTeX](../papers/mathlib-finset-card.tex) | [Card](https://github.com/leanprover-community/mathlib4/blob/c44e0c8ee63ca166450922a373c7409c5d26b00b/Mathlib/Data/Finset/Card.lean) |
| Turán's theorem | [PDF](../papers/mathlib-turan.pdf) · [LaTeX](../papers/mathlib-turan.tex) | [Turan](https://github.com/leanprover-community/mathlib4/blob/c44e0c8ee63ca166450922a373c7409c5d26b00b/Mathlib/Combinatorics/SimpleGraph/Turan.lean) |
| The LYM inequality and Sperner's theorem | [PDF](../papers/mathlib-lym.pdf) · [LaTeX](../papers/mathlib-lym.tex) | [LYM](https://github.com/leanprover-community/mathlib4/blob/c44e0c8ee63ca166450922a373c7409c5d26b00b/Mathlib/Combinatorics/SetFamily/LYM.lean) |

## Where the prose comes from

The compiler-only counting paper derives six results about binary words that avoid consecutive heads. Its layout supplies the title, a section heading and notation. The compiler generates the mathematical statements, prerequisites and proof paragraphs. [Lean source](../proofs/Counting580.lean) · [Layout](../chapter/counting580-compiler-only.json) · [PDF](../papers/counting580-compiler-only.pdf) · [LaTeX](../papers/counting580-compiler-only.tex)

The expository editions below include abstracts and introductory prose supplied by their layouts. Their theorem statements, proofs and cross-references still come from the checked declarations.

| Topic | Expository edition | Lean input |
|---|---|---|
| Counting admissible binary words | [PDF](../papers/counting580.pdf) · [LaTeX](../papers/counting580.tex) | [Counting580](../proofs/Counting580.lean) |
| Row and column sums of an incidence table | [PDF](../papers/incidence580.pdf) · [LaTeX](../papers/incidence580.tex) | [Incidence580](../proofs/Incidence580.lean) |
| Maximizing edges across a bipartition | [PDF](../papers/optimization580.pdf) · [LaTeX](../papers/optimization580.tex) | [Optimization580](../proofs/Optimization580.lean) |
| Avoiding bad events by a first-moment bound | [PDF](../papers/firstmoment580.pdf) · [LaTeX](../papers/firstmoment580.tex) | [FirstMoment580](../proofs/FirstMoment580.lean) |
| Complementary pairs of subsets | [PDF](../papers/intersecting580.pdf) · [LaTeX](../papers/intersecting580.tex) | [Intersecting580](../proofs/Intersecting580.lean) |

The elementary number-theory pilot contains 23 results culminating in the parity of an arithmetic progression. Its layout shows how multiple sections can share definitions and cite earlier results. [Generated chapter](../examples/pilot.tex) · [Layout](../chapter/pilot.json)
