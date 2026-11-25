# Lean to LaTeX

This compiler turns checked Lean 4 proofs in number theory and finite combinatorics into English LaTeX. The Lean adapter exports theorem statements, proof terms, inferred propositions, and declaration metadata. C++ orders theorems and facts, tracks case scope, chooses reusable sentence templates and citations, and assembles chapters and papers.

## Default for future papers

Compile the original Lean declarations with the existing translator and typeset its emitted LaTeX directly. Keep the layout to presentation metadata such as the title, theorem selection and order, and notation. The standard edition contains the compiler's own prerequisite statements, theorem statements, and proof narration. Reserve authored abstracts, introductions, glossaries, substitute proofs, and edits to the generated text for a separately labeled edition when explicitly requested. If a selected proof produces a placeholder, report it as incomplete.

The **compiler-only counting paper** uses the same six original declarations as the expository edition below. Its layout supplies a title, one section heading, and the existing symbol aliases. [PDF](papers/counting580-compiler-only.pdf) · [Unedited LaTeX](papers/counting580-compiler-only.tex) · [Input layout](chapter/counting580-compiler-only.json) · [Lean source](proofs/Counting580.lean)

## Compile an unchanged Lean proof file

Run the following commands in the proof author's Lake project with its dependencies built. The tested toolchain is Lean 4.19. Point the first command at this project's adapter and the second at the built C++ executable. The source-file path runs Lean's elaborator, including the project's real tactics. It exports checked declarations, local definitions, and the goal states and supporting facts available from the original source.

~~~sh
lake env lean --run /path/to/Adapter.lean checked.json Homework.lean
lean-to-latex checked.json homework.tex --paper "Combinatorics homework" --proof-budget 24
tectonic homework.tex
~~~

With a file, the default selection includes public named proofs and anonymous proposition-valued `example` declarations in source order. Internal dependencies appear before the first proof that uses them. To select particular theorems, append their qualified names to the adapter command. To use a compiled module, replace the filename with its module name. The source file supplies tactic steps and anonymous examples that a compiled module can discard. The adapter rejects proofs with a transitive `sorry`.

In paper mode the compiler infers lemmas from later use, corollaries from specialization or substitution of earlier results, and theorems for independent conclusions. A layout can override a selection with `{"theorem": "My.result", "role": "corollary", "title": "A counting consequence"}`. Results share a counter, and citations use the role of the result they refer to. Definitions and named prerequisites appear before the proofs. An unrendered proof or definition leaves a visible notice in the paper and gives the translator exit status 1.

### How much of the arithmetic appears

The C++ renderer assigns weights to operations in Lean's checked proof. A hypothesis use, an ordinary rule application, and a binding each cost 1. An equality rewrite costs 2, a case split or induction costs 4, and an arithmetic-certificate step costs 3. Generated proof helpers contribute their bodies. The default budget is 24. At or below the budget the renderer uses its expanded templates. Above the budget it combines supported operations into calculations. An applicable earlier result keeps its citation in either mode. `--threshold` controls formula display independently.

~~~sh
lean-to-latex checked.json compact.tex --paper "Combinatorics homework" --proof-budget 0
lean-to-latex checked.json detailed.tex --paper "Combinatorics homework" --proof-budget 1000000
lean-to-latex checked.json custom.tex --paper "Combinatorics homework" --proof-budget 30 --proof-weights rewrite=3,branch=6
~~~

The diagnostic stream reports the weighted operation counts for each theorem and each supported arithmetic tactic call. Lean executes the tactic once. The C++ renderer can reuse the resulting checked proof at any budget. The weights estimate reading effort. In the rational example, ring normalization, numeral normalization and equality reflexivity account for 175 of 218 points. The inspection file lists every charged rule and the six counting-paper scores. [Proof complexity breakdown](benchmarks/proof-complexity.txt)

The budget selects a narration template. The score has no calibration against human reading time. For a substitution, the renderer recognizes named rules for reflexivity, symmetry, transitivity and congruence, follows their proof arguments, and cites the hypotheses and lemmas that justify the substitution. Compact mode can fold a chain starting with a reflexive equality into the resulting identity. An unfamiliar rule needs a supported derivation or a cited result with its premises accounted for. Failure leaves a visible gap. The compact rational arithmetic template keeps the three inequalities, their coefficients and the contradiction. The expanded template also spells out three subtractions and a multiplication. [Substitution evidence](src/general_proof.cpp) · [Arithmetic templates](src/arithmetic_proof.cpp)

To inspect your own file, save the C++ diagnostic stream when generating the paper.

~~~sh
lean-to-latex checked.json homework.tex --paper "Combinatorics homework" 2> proof-cost.txt
~~~

In the rational example the theorem scores 222 and its `linarith` call scores 218. A budget of 220 expands the arithmetic inside a compact theorem. At the default budget of 24, the seven sentences in the expanded proof become three. Both versions give the coefficients and the cancellation to zero. In the integer example both versions retain the rounding step from twice an integer being at most nine to the integer being at most four. These are direct compilations of the same two Lean declarations. [Lean input](tests/fixtures/Arithmetic.lean) · [Compact PDF](papers/arithmetic-certificates.pdf) · [Expanded PDF](papers/arithmetic-certificates-expanded.pdf) · [Compact LaTeX](papers/arithmetic-certificates.tex) · [Expanded LaTeX](papers/arithmetic-certificates-expanded.tex)

Both published arithmetic LaTeX files reproduce byte for byte with their respective compiler builds. The expanded edition uses an earlier build. Its document body matches the current output and its preamble predates one unused counter.

## Grading a generated proof

Readability and gradeability are the current development priorities. The reading tests ask whether a reader can reconstruct the argument, identify what the author proved or imported, and assign credit for the requested method using only the generated paper.

For the weighted pigeonhole exercise, let $s,t$ be finite sets, let $f$ map $s$ into $t$, and assign each $x\in s$ a natural weight $w(x)$. Given $|t|b<\sum_{x\in s}w(x)$, prove that some $y\in t$ has fiber weight greater than $b$. The exercise asks for a proof by comparison of finite sums.

The project uses the following four-point rubric for this reading experiment. Each point requires visible evidence in the proof. Citing an identity or general sum comparison with its premises is sufficient. A citation of the weighted pigeonhole theorem itself can earn the conclusion point.

1. Regroup the total weight as a sum over fibers indexed by $t$, using the maps-into hypothesis.
2. Rewrite $|t|b$ as a constant sum and obtain a strict comparison of two sums over $t$.
3. Use that strict comparison to establish that one summand exceeds $b$.
4. Obtain a witness in $t$ and the claimed bound on its fiber weight.

## Whole Mathlib files

Each paper below uses the complete original Mathlib source file and a document title. Section headings follow the named scopes in the source. The compiler states imported prerequisites before their use, labels direct consequences as corollaries and puts the reasons beside the lines of short calculations. Tectonic typesets the emitted LaTeX directly.

| Paper | Proofs narrated | Files |
|---|---:|---|
| Pigeonhole principles | 29/29 | [PDF](papers/mathlib-pigeonhole.pdf) · [LaTeX](papers/mathlib-pigeonhole.tex) · [Original source](https://github.com/leanprover-community/mathlib4/blob/c44e0c8ee63ca166450922a373c7409c5d26b00b/Mathlib/Combinatorics/Pigeonhole.lean) |
| Double counting in finite relations | 22/22 | [PDF](papers/mathlib-double-counting.pdf) · [LaTeX](papers/mathlib-double-counting.tex) · [Original source](https://github.com/leanprover-community/mathlib4/blob/c44e0c8ee63ca166450922a373c7409c5d26b00b/Mathlib/Combinatorics/Enumerative/DoubleCounting.lean) |
| Subsets of a finite set | 35/35 | [PDF](papers/mathlib-powerset.pdf) · [LaTeX](papers/mathlib-powerset.tex) · [Original source](https://github.com/leanprover-community/mathlib4/blob/c44e0c8ee63ca166450922a373c7409c5d26b00b/Mathlib/Data/Finset/Powerset.lean) |
| The degree sum of a finite graph | 12/12 | [PDF](papers/mathlib-degree-sum.pdf) · [LaTeX](papers/mathlib-degree-sum.tex) · [Original source](https://github.com/leanprover-community/mathlib4/blob/c44e0c8ee63ca166450922a373c7409c5d26b00b/Mathlib/Combinatorics/SimpleGraph/DegreeSum.lean) |
| Hall's marriage theorem | 7/7 | [PDF](papers/mathlib-hall.pdf) · [LaTeX](papers/mathlib-hall.tex) · [Original source](https://github.com/leanprover-community/mathlib4/blob/c44e0c8ee63ca166450922a373c7409c5d26b00b/Mathlib/Combinatorics/Hall/Finite.lean) |
| The inclusion-exclusion principle | 5/5 | [PDF](papers/mathlib-inclusion-exclusion.pdf) · [LaTeX](papers/mathlib-inclusion-exclusion.tex) · [Original source](https://github.com/leanprover-community/mathlib4/blob/c44e0c8ee63ca166450922a373c7409c5d26b00b/Mathlib/Combinatorics/Enumerative/InclusionExclusion.lean) |
| Intersecting families of sets | 20/20 | [PDF](papers/mathlib-intersecting.pdf) · [LaTeX](papers/mathlib-intersecting.tex) · [Original source](https://github.com/leanprover-community/mathlib4/blob/c44e0c8ee63ca166450922a373c7409c5d26b00b/Mathlib/Combinatorics/SetFamily/Intersecting.lean) |
| Cardinalities of finite sets | 131/131 | [PDF](papers/mathlib-finset-card.pdf) · [LaTeX](papers/mathlib-finset-card.tex) · [Original source](https://github.com/leanprover-community/mathlib4/blob/c44e0c8ee63ca166450922a373c7409c5d26b00b/Mathlib/Data/Finset/Card.lean) |
| Turán's theorem on extremal graphs | 19/19 | [PDF](papers/mathlib-turan.pdf) · [LaTeX](papers/mathlib-turan.tex) · [Original source](https://github.com/leanprover-community/mathlib4/blob/c44e0c8ee63ca166450922a373c7409c5d26b00b/Mathlib/Combinatorics/SimpleGraph/Turan.lean) |
| Counting derangements | 9/9 | [PDF](papers/mathlib-derangements.pdf) · [LaTeX](papers/mathlib-derangements.tex) · [Original source](https://github.com/leanprover-community/mathlib4/blob/c44e0c8ee63ca166450922a373c7409c5d26b00b/Mathlib/Combinatorics/Derangements/Finite.lean) |
| The LYM inequality and Sperner's theorem | 15/15, including three aliases | [PDF](papers/mathlib-lym.pdf) · [LaTeX](papers/mathlib-lym.tex) · [Original source](https://github.com/leanprover-community/mathlib4/blob/c44e0c8ee63ca166450922a373c7409c5d26b00b/Mathlib/Combinatorics/SetFamily/LYM.lean) |

An AI reader received only the double-counting PDF and reconstructed results 9, 18 and 21. It recovered the sum over incidences, both inequalities needed for the regular case, and the totality and uniqueness assumptions needed for the cardinality bound. Its feedback led to clearer references to the two substitution identities and explicit specialization to the full finite sets. Course-instructor grading is still open.

A second PDF-only AI reader reconstructed results 11, 13 and 19 in the powerset paper. It identified an ambiguous union with a set difference. The formula printer now renders both possible groupings explicitly. In the two counting proofs the reader had to infer where a universal premise was discharged.

The eleven complete files contain 304 narrated declarations. The first eight supplied 261 development proofs. An earlier run completed 217/261. Turán's theorem improved from 9/19 during development. The first translation of the separate derangements source completed 9/9 before any changes prompted by that paper. The compiler also completed all 12 theorems and three aliases in the LYM file on its first run. [Current measurements](benchmarks/mathlib-paper-coverage.tsv) · [Earlier measurements](benchmarks/mathlib-coverage.tsv)

An earlier edition of Sperner's theorem grouped fourteen prerequisite citations and a positivity condition in a single sentence. The 27-page edition displays the quotient of the family size by the middle binomial coefficient as a bound in the nonnegative rationals. Its next step uses the strict positivity of that coefficient to clear the denominator. A PDF-only AI reader recovered both steps, the preceding application of the LYM inequality and the final return to natural-number cardinalities. In the pigeonhole paper, all 29 results have distinct titles. A separate reader distinguished a map into the target from a hypothesis on the weights of exterior fibers, and located the precise citation that used the maps-into hypothesis. [Sperner paper](papers/mathlib-lym.pdf) · [Pigeonhole paper](papers/mathlib-pigeonhole.pdf)

Two more AI readers worked from the Hall and inclusion–exclusion PDFs alone. They recovered both inductive cases of Hall's theorem and all five equalities proving the weighted union formula. The Hall reader needed to cross-reference five lemmas and flagged a choice whose membership was introduced late. The inclusion–exclusion reader found a missing visible bound inside an indexed intersection. The compiler now binds the chosen representative immediately and prints the intersection with its precise index set. These are direct translations of full library files. Formal narration counts do not measure how readily a professor can grade them.

A PDF-only AI reader recovered the forward direction of Turán's theorem, including the part-preserving bijection, its adjacency test and both cases for the number of vertices. The first reading flagged a missing justification in the converse. The revised proof states the two equalities identifying the cardinalities of the vertex sets before it composes the isomorphisms. The same reader verified those steps in that edition. The current paper is 169 pages. Its 12 lemmas and two corollaries accompany five theorems.

Another PDF-only AI reader recovered the initial values, recurrence and alternating sum for derangements. Lemma 2 on page 9 identifies the imported recursion bijection, its domain and both alternatives in its range. The source uses this bijection as a library result. The compiler introduces the notation \(D\) for the counting function and labels the base case and induction hypothesis in its proof of the alternating sum. The paper is 35 pages.

Proofs packaged inside a constructed witness contribute to its narration and operation count. If a field lacks proof evidence, the paper marks the result incomplete and reports the cost as unavailable. The six operation weights retain their original values.

The renderer completes 10/14 proofs in another file on Catalan numbers. It cites the previously printed Catalan recurrence. For a private telescoping lemma it exports the two nonzero denominators, two cancellation facts and two binomial identities. The remaining arithmetic calculation exceeds the export budget, so that proof and its dependent results remain incomplete. [Catalan source](https://github.com/leanprover-community/mathlib4/blob/c44e0c8ee63ca166450922a373c7409c5d26b00b/Mathlib/Combinatorics/Enumerative/Catalan.lean)

The expanded benchmark timed the original-source check and export once, then timed the final C++ renderer and typesetter against those exports. Other verification work was running on the same machine. Timing and peak memory describe that run.

The original four-file benchmark records a standalone Lean check, the adapter's source elaboration and export, C++ rendering, and PDF typesetting. End-to-end time sums the last three stages. Peak memory is the largest process-tree working set sampled every 20 ms. Each row is one Windows run with a Core Ultra 9 185H, 31.5 GiB RAM, Lean and Mathlib 4.19, and prebuilt dependencies. Times exclude downloading dependencies and building the compiler. A complete proof is one the renderer can explain or cite throughout. [Initial resource and coverage measurements](benchmarks/mathlib-v4.19.tsv)

Run `python -B tests/verify_papers.py --mathlib-project /path/to/mathlib4` with the 4.19 checkout and its prerequisites built to reproduce the direct-output and arithmetic checks.

## Combinatorial mathematics papers

These expository papers develop selected topics from [UIUC MATH 580](https://math.illinois.edu/resources/syllabus-math-580). The paper layouts provide the abstracts, notation, and section introductions. The theorem statements, proof paragraphs, and references come from the checked Lean declarations. The examples use Lean core 4.19.0.

| Paper | Mathematical result | Files |
|---|---|---|
| Avoiding consecutive heads | A Fibonacci recurrence counts admissible binary words. At length $2k$ their count is at most $3^k$. | [PDF](papers/counting580.pdf) · [LaTeX](papers/counting580.tex) · [Lean](proofs/Counting580.lean) |
| Counting incidences by rows and columns | Two inductions identify the row and column sums of a finite incidence table. In a regular uniform structure this gives $vr=bk$ and a divisibility obstruction. | [PDF](papers/incidence580.pdf) · [LaTeX](papers/incidence580.tex) · [Lean](proofs/Incidence580.lean) |
| How many edges fit across a bipartition? | Balancing the two parts maximizes the number of edges in a complete bipartite graph. The proof computes the exact gain for a transfer and treats even and odd orders. | [PDF](papers/optimization580.pdf) · [LaTeX](papers/optimization580.tex) · [Lean](proofs/Optimization580.lean) |
| Avoiding bad events | If the total number of bad-event incidences is smaller than the number of outcomes, at least one outcome avoids every event. The finite uniform expectation is explained in the introduction. | [PDF](papers/firstmoment580.pdf) · [LaTeX](papers/firstmoment580.tex) · [Lean](proofs/FirstMoment580.lean) |
| Intersecting families of subsets | Complementary pairs bound the size of an intersecting family. All subsets containing one fixed point attain the bound. | [PDF](papers/intersecting580.pdf) · [LaTeX](papers/intersecting580.tex) · [Lean](proofs/Intersecting580.lean) |

The graph arguments use finite binary incidence tables or vertex-part sizes. The probability arguments use finite counts. The Lean files also contain supporting results about the underlying models, including membership and uniqueness of the enumerated words. The collection demonstrates these proof patterns on authored examples. Coverage of arbitrary MATH 580 submissions remains unmeasured.

Build and test the five papers with `python -B tests/verify_papers.py` using the tools listed below. The test builds two fresh copies, compiles the papers, checks resolved theorem references, and compares the LaTeX with the shipped files. Use `--lake` and `--tectonic` to select the toolchain. For an offline Tectonic build, use `--only-cached` and supply local fonts with `--font-dir` if needed.

## Pilot chapter

[Divisibility and parity in the natural numbers](examples/pilot.tex) contains 23 checked results in three sections, including two restatements that connect the progression section to earlier results. Its main theorem shows that an even increment preserves whether a natural number is divisible by two along an arithmetic progression.

- The ten existing Lean core divisibility theorems were evaluated one at a time. The prototype rendered 9 statements and completed 4 proofs. The extended compiler rendered and completed all 10 originals. The primary additions explain equality simplification and generated matches that extract witnesses. Equivalence statements and proof directions support the chapter's later results. [Baseline](chapter/baseline.tsv) · [After extension](chapter/after-extension.tsv)
- The translator rules were frozen before the five-result progression section was opened for translation. All five proofs completed on the first run. The chapter uses the selected proofs as written.
- A reader given the generated chapter alone reconstructed the assumptions, decisive inference, and cited support for Theorems 10, 16, and 23. These cover adding a known multiple, multiplying an even number, and the main progression theorem. The clean-build audit records the actual Lean dependency graph and checks both preselected lemmas are in the main theorem's transitive dependencies. The printed proof may cite a more general earlier result when it suffices.
- The build check also exercises a separately checked alternate for the original `omega` proof. It reports the original as incomplete, labels the alternate as separately checked, and rejects an alternate with a different theorem statement.

## Build the pilot

Use Lean 4.19.0, CMake 3.16 or newer, a C++17 compiler, Ninja, Python 3, and Tectonic. The pilot uses Lean core. Run the following command from the project root.

~~~sh
python3 -B tests/verify_chapter.py
~~~

Use `python` on Windows if that is the installed command. The verifier builds the Lean and C++ sources in two fresh directories, typesets both outputs, checks all theorem references, and compares the LaTeX bytes against each other and the shipped chapter. It prints the SHA-256 and leaves the PDF, LaTeX, and dependency audit under `build/`. Use `--lake PATH` and `--tectonic PATH` for local toolchains, `--generator NAME` for another CMake generator, or `--only-cached` for a populated Tectonic cache.

## Author a chapter

Copy [the pilot layout](chapter/pilot.json). Set the chapter and section titles, introductory prose, glossary definitions, preferred witness and induction terminology, and the ordered declaration names. A section can live in a separate JSON file relative to the layout. Set `main` on the last result of the final section to mark it for readers. Prose fields are treated as plain text and escaped for LaTeX.

A layout with `"format": "paper"` uses an article title and abstract. An optional `symbols` dictionary gives distinct alphabetic display names to referenced Lean definitions with natural-number arguments and results. The adapter checks their signatures. An optional `prerequisites` dictionary supplies English titles for imported results. See the [first-moment layout](chapter/firstmoment580.json).

The compiler keeps the author’s section order and places dependencies before use within each section. A reference into a later section is an input error. The whole chapter shares one prerequisite list and one set of theorem references.

Build the chosen Lean modules and the C++ executable. Use `lean-to-latex --list-chapter CHAPTER.json` to obtain the ordered declaration arguments for `lake env lean --run Adapter.lean checked.json IMPORTS ...`. Then run `lean-to-latex checked.json chapter.tex --chapter CHAPTER.json`.

A theorem entry can be an object with `theorem` and `alternate` names. The adapter requires separate checked declarations with definitionally equal statements and rejects proofs with a transitive `sorry`. The generated proof marks the substitution. The original remains a separate evaluation case.

## Prototype feasibility result

The frozen translator narrated all three development proofs and both reserved proofs on its first held-out run. An independent reviewer used the [structured output](examples/structured.tex) alone and recovered both reserved arguments.

- Theorem 4 applies two earlier theorems to prove divisibility of each summand, then uses divisibility of a sum.
- Theorem 5 starts with $2\mid n$, chooses a witness $k$ with $n=2k$, and uses associativity to obtain $nm=2(km)$. The new witness is $km$.

The adapter and translator were hashed before the implementation team opened the reserved Lean source or generated reserved output. The curator shared a high-level description of the reserved methods before that freeze. No translator edits were made after the freeze.

The [standalone automation output](examples/automation.tex) uses the same translator on the same statement as Theorem 1, proved in Lean with `omega`. Lean checked it, and the translator left one explanation pending. The checked term reasons by contradiction and delegates the calculation to a generated auxiliary theorem. Exporting that auxiliary separately exposed 93 proof-valued annotations and references to 24 theorem declarations. Narrating that route would require support for contradiction and a way to interpret or summarize the linear arithmetic certificate, including integer conversions and remainder reasoning. Development effort for that extension is unmeasured.

Two independent clean runs rebuilt the Lean modules and the C++ executable. Both produced byte-identical `.tex` files and matched the shipped examples. Both documents also compiled to PDF with Tectonic 0.17.0.

## Reproduce the prototype experiment

Install Lean 4.19.0, CMake 3.16 or newer, a C++17 compiler, Ninja, and Python 3. The Lean project uses core Lean and needs no mathlib download. Run the clean-build and comparison test from the project root.

~~~sh
python3 tests/verify.py
~~~

On Windows, use `python` if that is the installed command. Pass `--lake PATH` for a standalone Lean toolchain and `--generator NAME` to choose another CMake generator. The script prints the output directory under `build/` and the two LaTeX SHA-256 hashes.

To run the two stages directly, build the Lean modules and C++ executable, then select the modules and theorem declarations to translate.

~~~sh
lake build DevelopmentProofs ReservedProofs AutomatedProofs
cmake -S . -B build -G Ninja
cmake --build build

lake env lean --run Adapter.lean build/structured.json proofs.Development,proofs.Reserved Examples.two_dvd_double Examples.even_of_two_dvd Examples.two_dvd_double_mul Reserved.composed_doubling_sum Reserved.divisor_preserved_by_multiplication
build/lean-to-latex build/structured.json build/structured.tex

lake env lean --run Adapter.lean build/automation.json proofs.Automation Examples.two_dvd_double_automated
build/lean-to-latex build/automation.json build/automation.tex
~~~

The C++ executable has an `.exe` suffix on Windows. Its exit status is 0 for complete narration, 1 if a proof has a pending explanation, and 2 for an input or I/O error. Status 1 still writes the document. Use a LaTeX engine with AMS packages and run it twice to resolve theorem references.

## Narration rules

- Supporting facts appear before the steps that cite them. Induction cases and local witnesses have separate scopes.
- An applicable earlier theorem takes priority. The citation gives the required instantiation and any premise references. Named library prerequisites have statements at the beginning of the document.
- `--threshold N` sets the expression size cutoff, measured in mathematical expression nodes. The default is 5. Uncited steps above the cutoff show the full expression in display math with its reasoning.
- The implemented fragment includes natural-number addition, multiplication, powers, inequalities, divisibility, named counting functions, conjunctions in statements, existential witnesses, equivalence, equality chains and transport, and natural-number induction. Other checked terms can leave an explanation pending.
