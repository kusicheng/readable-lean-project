# Changelog

## Unreleased

- Made a mathematical article the default output. Anonymous examples use numbered statements, and matching and recurrence headings identify which argument changes. Source-documented names such as the degree-sum formula now accompany their prerequisite citations.
- Added narration for checked record equalities and recursive hypotheses used in the complete Mathlib files on refined Bell numbers and Dyck words. The Bell recurrence identifies the last binomial factor in the finite product.

- Made entire result and prerequisite citations clickable in the PDF. Separated theorem headings from their statements and prevented long inline formulas from stretching the prose in proof paragraphs.
- Compiled all 46 results in the original Mathlib graph-matching file and distinguished all 22 headings in the double-counting paper.
- Compiled a complete 17-result article on Hamiltonian graphs. The path and cycle length proofs show the intermediate counts. The article also states the singleton convention and gives the walk used in the connectivity proof. [Generated paper](papers/mathlib-hamiltonian-linked.pdf)
- Distinguished set families and scalar types in the LYM inequality, and made repeated addition explicit in the weighted pigeonhole exercise. [Reading and grading results](docs/evaluation.md)
- Added chapter and paper output for Lean proofs, with worked combinatorics examples.
- Improved the notation for rational reciprocals. Proofs that clear a denominator now show where its positivity was established.
- Added two independently checked solutions to the same weighted pigeonhole exercise. One cites the general theorem and the other derives the bound by comparing finite sums. [Grading examples](docs/examples.md)
- Added `lean-to-latex --help` and a documentation guide for running the compiler and reading its output. [Getting started](README.md)

## Git history

The entries below come from the checked-out history. Edit release notes above this section and run `python scripts/update_project_history.py` from the repository root to refresh both history files. Use `--check` to check them without writing.

<!-- BEGIN generated project history -->

### Tags

This history has no Git tags yet.

### Commits

- 2026-11-24 — update readme and add example docs (`4aa7681`)
- 2026-11-24 — update readme and add example docs (`6e7093f`)
- 2026-11-24 — add more readability rules and fix bugs in exmp (`2696aef`)
- 2026-11-23 — add complete pilor chapter support (`e376d33`)
- 2026-11-22 — initial prototyping (`79567c2`)
- 2026-11-22 — initial prototyping (`04d0033`)
- 2026-11-22 — Initial commit (`3d331f6`)

<!-- END generated project history -->
