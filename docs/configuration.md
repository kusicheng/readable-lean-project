# Compiling and configuring a paper

## Compile a file in another Lake project

Build the C++17 compiler once. From the translator repository, run the following commands with CMake 3.16 or newer and Ninja.

~~~sh
cmake -S . -B build/compiler -G Ninja -DCMAKE_BUILD_TYPE=Release
cmake --build build/compiler
~~~

Run the next commands **from the Lean project that owns the proof**. Use its normal Lean 4.19 environment with its dependencies built. Replace the translator path and `Homework.lean` with your paths. The Windows executable has the suffix `.exe`.

~~~sh
lake env lean --run /path/to/lean-to-latex/Adapter.lean checked.json Homework.lean
/path/to/lean-to-latex/build/compiler/lean-to-latex checked.json homework.tex --paper "Combinatorics homework"
tectonic homework.tex
~~~

The first command runs Lean's elaborator, including the tactics invoked in the file. It exports checked declarations, local definitions and available tactic evidence. The second writes an English mathematical article to `homework.tex` and reports coverage on standard error. Tectonic produces `homework.pdf`. You can typeset the emitted file with another LaTeX engine that includes the AMS packages. Run pdfLaTeX twice to resolve references.

By default the source-file adapter selects public named proofs and anonymous proposition-valued `example` declarations in source order. Append qualified names to select specific declarations. For example, from the translator repository the following exports just one proof from its elementary Lean file.

~~~sh
lake env lean --run Adapter.lean checked.json proofs/Development.lean Examples.two_dvd_double
~~~

To export a built module, replace the filename with its module name, such as `proofs.Development` after `lake build DevelopmentProofs`. Use the source-file form when you need tactics or anonymous examples. The adapter rejects a proof that depends transitively on `sorry`.

## Read the compiler result

| C++ exit status | Meaning |
|---|---|
| 0 | The selected proofs and required defining equations were rendered. |
| 1 | The compiler wrote a document with a visible gap in a proof or definition. Read standard error to locate it. |
| 2 | An input, option or I/O error prevented normal compilation. |

The compiler produces an article by default. Use `--paper TITLE` to give it a title. Results used to prove later statements can become lemmas. A direct consequence of earlier results can become a corollary. All three roles share a counter. Each citation names the earlier result and links to it. Named library prerequisites appear at the front of the paper.

An automatic article uses a mathematical caption when it recognizes the statement or finds a conventional title in the source documentation. Otherwise the result opens with its number and checked statement. An explicit chapter layout can supply titles. Use `--outline` to reproduce the numbered steps in the original feasibility examples.

## Control the amount of detail

The C++ pass can render the same checked export several times. For example, run these commands with the built compiler on your command path.

~~~sh
lean-to-latex checked.json compact.tex --paper "Homework" --proof-budget 0
lean-to-latex checked.json expanded.tex --paper "Homework" --proof-budget 1000000
lean-to-latex checked.json custom.tex --paper "Homework" --proof-budget 30 --proof-weights rewrite=3,branch=6 2> proof-cost.txt
~~~

The default budget is 24. Above the budget the renderer groups supported operations into calculations. At or below it, the renderer uses expanded templates. It scores each theorem and each supported arithmetic tactic call separately. Earlier proved theorems retain their citations. `--threshold N` controls the size at which an uncited expression moves into display math. Its default is five mathematical expression nodes.

When a compact proof uses the same lengthy private argument more than once, the compiler can state and prove it as an auxiliary lemma. A candidate must have at least two uses, at least 24 applications in its proof, and at least six lines in its reconstructed derivation. Each use must satisfy the lemma's hypotheses. For example, “Auxiliary lemma 43.1” in the Dyck-word paper proves that converting a word to a tree and back returns the original word. Each use links to that proof. The expanded setting keeps the individual derivations. [Dyck-word PDF](../papers/mathlib-dyck-words.pdf) · [Selection rules](../src/auxiliary_lemmas.hpp)

| Weight key | Default | Operation |
|---|---:|---|
| `hypothesis` | 1 | Use of a local hypothesis |
| `application` | 1 | Ordinary rule application |
| `binding` | 1 | Introduction of a bound value or premise |
| `rewrite` | 2 | Equality rewriting |
| `branch` | 4 | Case split or induction |
| `certificate` | 3 | Recognized arithmetic-certificate operation |

The diagnostic stream includes the weighted counts. Generated helper proofs and evidence in the fields of constructed witnesses contribute to them. If required evidence is missing, a proof cost may be unavailable. The weights are presentation heuristics without human reading-time calibration. [Worked score breakdown](../benchmarks/proof-complexity.txt)

For example, the rational-bound theorem scores 222 and its `linarith` call scores 218. At budget 220 the theorem uses compact narration while the arithmetic calculation uses its expanded template. Of the 218 tactic points, 175 come from ring normalization, numeral normalization and 27 reflexivity checks. [Lean example](../tests/fixtures/Arithmetic.lean) · [Compact and expanded editions](examples.md#a-short-proof-to-read-first)

## Select results and sections with a layout

For a compiler-only article, start from the counting layout. It supplies a title, a section, ordered selections and notation. The compiler writes the prerequisite statements and proofs. A selection can override a role or name as in `{"theorem":"My.result","role":"corollary","title":"A counting consequence"}`. [Compiler-only layout](../chapter/counting580-compiler-only.json)

For example, build the supplied chapter's Lean modules and export the declarations chosen by its layout. These Bash commands run from the translator repository with the C++ executable on your command path.

~~~sh
lake build CombinatoricsPapers
mapfile -t selections < <(lean-to-latex --list-chapter chapter/counting580-compiler-only.json)
lake env lean --run Adapter.lean checked.json proofs.Counting580 "${selections[@]}"
lean-to-latex checked.json counting.tex --chapter chapter/counting580-compiler-only.json
tectonic counting.tex
~~~

A chapter keeps the author's section order and puts dependencies before use within each section. A citation into a later section is a layout error. Section files can be relative to their parent layout. A `main` entry identifies a section's main result. A paper layout can supply distinct alphabetic symbols for referenced definitions with natural-number arguments and result, and English titles for named prerequisites. [Pilot chapter layout](../chapter/pilot.json) · [Paper layout with notation](../chapter/firstmoment580.json)

An expository layout can also supply an abstract, section introductions and glossary text. The compiler escapes that prose as text. To select a separate alternate proof explicitly, use a theorem entry with `theorem` and `alternate`. The adapter checks that the declarations have definitionally equal statements, and the paper labels the substitution. The default paper uses the original proof throughout.

## Reproduce the examples

Run the verifiers from the translator repository with Python 3. On systems where the Python 3 executable is named `python`, use that command in place of `python3`.

~~~sh
python3 -B tests/verify.py
python3 -B tests/verify_chapter.py
python3 -B tests/verify_papers.py
python3 -B tests/verify_papers.py --mathlib-project /path/to/mathlib4
~~~

The first command checks the frozen number-theory examples. The second checks the pilot chapter and its references. The third builds the local paper editions in two fresh directories. The last also checks original Mathlib files and arithmetic examples with a prebuilt Mathlib 4.19 checkout. Use `--lake PATH` and `--generator NAME` to select local build tools. The chapter and paper tests accept `--tectonic PATH` and `--only-cached`. The paper test also accepts repeatable `--font-dir PATH` arguments for local fonts. [Prototype verifier](../tests/verify.py) · [Chapter verifier](../tests/verify_chapter.py) · [Paper verifier](../tests/verify_papers.py)

To test the published PDFs, run `python3 tests/verify_pdf_navigation.py` with `pypdfium2` installed. It checks the clickable area of each numbered citation and the location of the printed heading it opens. It also measures word spacing inside Theorem 1 and Lemma 4 of the Hamiltonian paper. [PDF checks](../tests/verify_pdf_navigation.py)
