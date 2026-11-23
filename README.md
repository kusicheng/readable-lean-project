# Lean to LaTeX

This prototype turns checked Lean 4 proofs in elementary number theory into English LaTeX. The Lean adapter exports theorem statements, proof terms, inferred propositions, and declaration metadata. C++ orders theorems and facts, tracks case scope, chooses reusable sentence templates and citations, and writes the document.

## Feasibility result

The frozen translator narrated all three development proofs and both reserved proofs on its first held-out run. An independent reviewer used the [structured output](examples/structured.tex) alone and recovered both reserved arguments.

- Theorem 4 applies two earlier theorems to prove divisibility of each summand, then uses divisibility of a sum.
- Theorem 5 starts with $2\mid n$, chooses a witness $k$ with $n=2k$, and uses associativity to obtain $nm=2(km)$. The new witness is $km$.

The adapter and translator were hashed before the implementation team opened the reserved Lean source or generated reserved output. The curator shared a high-level description of the reserved methods before that freeze. No translator edits were made after the freeze.

The [standalone automation output](examples/automation.tex) uses the same translator on the same statement as Theorem 1, proved in Lean with `omega`. Lean checked it, and the translator left one explanation pending. The checked term reasons by contradiction and delegates the calculation to a generated auxiliary theorem. Exporting that auxiliary separately exposed 93 proof-valued annotations and references to 24 theorem declarations. Narrating that route would require support for contradiction and a way to interpret or summarize the linear arithmetic certificate, including integer conversions and remainder reasoning. Development effort for that extension is unmeasured.

Two independent clean runs rebuilt the Lean modules and the C++ executable. Both produced byte-identical `.tex` files and matched the shipped examples. Both documents also compiled to PDF with Tectonic 0.17.0.

## Run the experiment

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
- The implemented fragment covers natural-number addition, multiplication, equality, divisibility, existential witnesses, equality transport, and natural-number induction. Other checked terms can leave an explanation pending.
