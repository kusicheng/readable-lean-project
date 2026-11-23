# Lean to LaTeX

This compiler turns checked Lean 4 proofs in elementary number theory into English LaTeX. The Lean adapter exports theorem statements, proof terms, inferred propositions, and declaration metadata. C++ orders theorems and facts, tracks case scope, chooses reusable sentence templates and citations, and assembles the chapter.

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
- The implemented fragment covers natural-number addition, multiplication, equality, divisibility, existential witnesses, equivalence, equality transport, and natural-number induction. Other checked terms can leave an explanation pending.
