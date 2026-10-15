# Generic Rigidity and the Grassmannian — Lean formalization

Lean 4 formalization of results in Alexander Heaton's paper
**[Generic Rigidity and the Grassmannian](https://arxiv.org/abs/2604.05442)** (arXiv:2604.05442).

The project was produced using [Aristotle (Harmonic)](https://aristotle.harmonic.fun/).
The accompanying report (`ARISTOTLE_SUMMARY.md`) states that the project builds without
unfinished proofs and uses only standard Lean axioms. See `PAPER-TO-LEAN.md` for a
statement-by-statement index from the paper to Lean declarations. This README does not
constitute an independent verification of the build.

## Contents

- `RequestProject/` — Lean source files covering rigidity, orientations, path systems,
  Cramer's rule, the Lindström–Gessel–Viennot lemma, and tableau straightening.
- `RequestProject/Results.lean` — formal statements of the main theorem, characterization,
  and numbered results in the article.
- `PAPER-TO-LEAN.md` — detailed correspondence between the paper and the Lean code,
  including scope and hypotheses.
- `ARISTOTLE_SUMMARY.md` — Aristotle's report of the completed formalization.
- `main.tex` — source of the paper supplied with the formalization.
- `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` — pinned Lean project configuration.

## Building locally

With [Lean's `elan` toolchain manager](https://lean-lang.org/install/) installed, run
from this directory:

```bash
lake exe cache get
lake build
```

The project specifies Lean `v4.28.0` and mathlib `v4.28.0`.

## Scope

As recorded in `PAPER-TO-LEAN.md`, the equivalence of generic local rigidity
and infinitesimal rigidity (Asimow–Roth) and the existence of generic
placements are carried as explicit hypotheses where used. The paper's
illustrative examples are not individually formalized. A tableau lemma is
formalized with the necessary positive-height hypothesis; see the notes in
`ARISTOTLE_SUMMARY.md`.

## Aristotle credit

The original Aristotle-generated README supplied these attribution instructions:

- Tag `@Aristotle-Harmonic` on GitHub issues or pull requests.
- For commits containing Aristotle-authored changes, you can include:

```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

For the original project report see `ARISTOTLE_SUMMARY.md`.
