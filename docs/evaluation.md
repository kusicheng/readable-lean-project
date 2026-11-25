# Coverage, readability and reproducibility

## Grading a generated proof

The project tested two Lean solutions to the same course-style exercise. Let $s,t$ be finite sets, suppose $f$ maps $s$ into $t$, and give each $x\in s$ a natural weight $w(x)$. If $|t|b<\sum_{x\in s}w(x)$, prove **by comparison of finite sums** that some $y\in t$ has $\sum_{x\in s,\ f(x)=y}w(x)>b$. The two submissions have identical hypotheses and conclusions. [Original Lean submissions](../tests/fixtures/FiberSubmissions.lean)

The project fixed four criteria, worth one point each, before grading the papers. An imported identity or general comparison lemma can establish a step when the paper shows how its premises are met.

1. Regroup the total weight as a sum over fibers indexed by $t$, using the maps-into hypothesis.
2. Rewrite $|t|b$ as a constant sum and exhibit a strict comparison of two sums over $t$.
3. Infer that some fiber has weight greater than $b$ from that strict comparison.
4. Obtain a witness in $t$ and the requested bound for that witness.

Independent AI readers graded the generated papers using this rubric. They awarded **A 1/4**. A invokes the weighted pigeonhole theorem with both hypotheses, which establishes the conclusion and witness. They awarded **B 4/4**. B evaluates the constant sum, applies the strict hypothesis, groups the weights by $f$ using the maps-into condition, and applies a general comparison lemma to obtain a larger summand. Lean accepted both answers. A professor has yet to grade these papers or evaluate the project rubric. [Paper A](../papers/gradeability-fiber-a.pdf) · [A's LaTeX](../papers/gradeability-fiber-a.tex) · [Paper B](../papers/gradeability-fiber-b.pdf) · [B's LaTeX](../papers/gradeability-fiber-b.tex)

One notation detail matters when reading A's prerequisite. In an additive monoid, $n\mathbin{\bullet} b$ denotes $n$ copies of $b$ added together. Here $b$ is a natural number, so that repeated sum equals the ordinary product $nb$ used in the submission.

## What the reader tests found

AI readers worked from generated PDFs. Their reports identify particular arguments they could reconstruct and places where the prose or notation obscured the reasoning.

- In the double-counting paper, a reader recovered the incidence sum and the totality and uniqueness assumptions behind a cardinality bound. In the powerset paper, a reader caught an ambiguous grouping of union and difference. [Double counting](../papers/mathlib-double-counting.pdf) · [Powersets](../papers/mathlib-powerset.pdf)
- Readers recovered both inductive cases of Hall's theorem and the five equalities in weighted inclusion-exclusion. Their reports led to introducing a chosen representative together with its membership and printing the bound on an indexed intersection. [Hall](../papers/mathlib-hall.pdf) · [Inclusion-exclusion](../papers/mathlib-inclusion-exclusion.pdf)
- A reader recovered the final inequality in Sperner's theorem, including the LYM bound and multiplication by a positive denominator. In the derangements paper a reader could reconstruct the recurrence and alternating sum but initially could not identify the bijection used to count the two cases. The revised paper states the imported bijection and both alternatives in its target. [Sperner](../papers/mathlib-lym.pdf) · [Derangements](../papers/mathlib-derangements.pdf)
- In the converse direction of Turán's theorem, a reader initially needed justification for two cardinality equalities. The reader found both in the revised edition before the graph isomorphisms were composed. The full paper runs to 169 pages, which also illustrates the reading cost of exporting a complete library file. [Turán](../papers/mathlib-turan.pdf)

## What the compiler finished

A declaration counts as complete when the renderer explains or cites its proof throughout. The eleven complete Mathlib articles contain **304 selected declarations**, including three aliases in the LYM file. The original eight development modules account for 261. An earlier run completed 217 of those 261. Turán progressed from 9/19 to 19/19 during development. The first frozen runs on the derangements and LYM files completed 9/9 and 15/15, respectively. Later changes improved their prose. [Measured coverage and per-file source hashes](../benchmarks/mathlib-paper-coverage.tsv) · [Earlier trial](../benchmarks/mathlib-coverage.tsv) · [Articles and original sources](examples.md#a-paper-built-from-a-complete-library-file)

An additional Catalan-number file remains at **10/14**. Its private telescoping lemma exports six local facts, including nonzero denominators and binomial identities. The final arithmetic calculation exceeds the export budget. The closed-form proof and three results that depend on it consequently remain incomplete. These library cases and the two grading submissions do not determine the success rate on arbitrary UIUC MATH 580 homework. [Original Catalan file](https://github.com/leanprover-community/mathlib4/blob/c44e0c8ee63ca166450922a373c7409c5d26b00b/Mathlib/Combinatorics/Enumerative/Catalan.lean)

## Compilation resources

The eleven-file table separates elaborating and exporting the original Lean source from rendering its checked export with C++. In the recorded Windows runs, the 131-declaration finite-set cardinality file took about **30 seconds** to check and export, followed by **4 seconds** to render, with about **1 GiB** peak memory in C++. The 19-declaration Turán file took about **41 seconds** to check and export and **13 seconds** to render, with about **3.6 GiB** peak memory in C++. The larger proof terms in the latter file make declaration count a poor timing estimate by itself. The timings are individual runs with prebuilt dependencies. [Per-file timings, memory and export sizes](../benchmarks/mathlib-paper-coverage.tsv)

The original four-file benchmark also timed standalone Lean checking and PDF typesetting. Its end-to-end total adds source elaboration and export, C++ rendering and typesetting. It sampled the process-tree working set every 20 ms on Windows with a Core Ultra 9 185H and 31.5 GiB of RAM. Downloading dependencies and building the compiler took place outside the timed stages. [Original four-file measurements](../benchmarks/mathlib-v4.19.tsv)

## Reproducibility and earlier experiments

The clean-build verifier compiles the local paper editions twice and compares their LaTeX bytes. For the archived compact and expanded arithmetic papers, the corresponding compiler builds reproduced their published LaTeX byte for byte from the same checked input. The expanded edition predates an unused counter in today's preamble. Each rebuilt PDF matched its published page dimensions, extracted text and rendered pixels at 144 dpi. PDF file hashes differed. [Compact LaTeX](../papers/arithmetic-certificates.tex) · [Expanded LaTeX](../papers/arithmetic-certificates-expanded.tex) · [Reproduction commands](configuration.md#reproduce-the-examples)

The initial number-theory experiment used three development proofs and two reserved proofs. The frozen C++ templates narrated all five. A reader reconstructed both reserved arguments from the document alone. The curator had shared a high-level description of the methods before the freeze. A separate checked `omega` proof left a placeholder in that early translator. [Structured output](../examples/structured.tex) · [Initial automation output](../examples/automation.tex)

In the chapter pilot, the prototype finished 4/10 previously selected divisibility proofs. The extended compiler finished all ten original proofs. After a second freeze it rendered all five proofs in the progression section on the first run. Readers of the chapter alone reconstructed the decisive steps in Theorems 10, 16 and 23. [Pilot chapter](../examples/pilot.tex) · [Baseline](../chapter/baseline.tsv) · [Extended results](../chapter/after-extension.tsv)
