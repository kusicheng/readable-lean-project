# Lean to LaTeX

Lean to LaTeX compiles checked Lean proofs into deterministic English and LaTeX so a reader can follow the argument and see which results it cites.

## Quickstart

Requires Lean 4.19.0 with Lake, a C++17 compiler, CMake 3.16+, and Ninja.

From the repository root, build the compiler and translate the included divisibility proofs.

```sh
cmake -S . -B build/cli -G Ninja
cmake --build build/cli
lake env lean --run Adapter.lean build/cli/checked.json proofs/Development.lean
./build/cli/lean-to-latex build/cli/checked.json build/cli/divisibility.tex --paper "Divisibility"
```

The compiler writes `build/cli/divisibility.tex` and reports `3/3 proofs complete`.

## Core usage

**Translate a proof.** The first quickstart lemma proves `2 ∣ n + n`. Its generated proof identifies the witness in the sentence “With witness $n$, $n + n = 2 \cdot n$ shows that $2 \mid n + n$.” [Lean input](proofs/Development.lean)

**Grade a solution.** Two Lean proofs establish the same weighted pigeonhole bound. One generated paper cites the result directly. The other shows how regrouping the total weight by fiber gives the strict comparison of sums. [Input](tests/fixtures/FiberSubmissions.lean) · [Citation proof](papers/gradeability-fiber-a.pdf) · [Sum-comparison proof](papers/gradeability-fiber-b.pdf)

Run `./build/cli/lean-to-latex --help` for CLI options.

## Documentation & architecture

- `Adapter.lean` checks the input in its Lean project and exports declarations and proof evidence.
- `src/` contains the C++ rules that turn that evidence into English, mathematical notation, and citations.
- `proofs/` holds sample Lean inputs, `papers/` holds generated articles, and `tests/` checks their reproduction.

[Examples](docs/examples.md) · [Optional configuration](docs/configuration.md) · [Coverage and grading](docs/evaluation.md) · [Changelog](CHANGELOG.md) · [Contributors](CONTRIBUTORS.md)
