# Hilbert–Vector–Resolvent Theory: expanded preprint

**Draft 0.1, 28 October 2026 — exactly 50 pages.**

[Read the preprint](Hilbert_Vector_Resolvent_Theory_Preprint_50pp_v0_1.pdf)

This manuscript expands the project introduction into a sustained mathematical exposition:

| Pages | Contents |
| --- | --- |
| 1–6 | Abstract, notation, principal claims, rigorous introduction and proof architecture |
| 7–14 | Hilbert-vector models, positive contractions, cyclicity and examples |
| 15–22 | Bernstein algebra, cancellation, moment limits and probability measures |
| 23–30 | Scalar resolvents, analytic domains, signs, continuation and pole exclusion |
| 31–38 | Actual ξ-moments, spectral growth and the two conditional RH routes |
| 39–44 | Weighted models, actual Widder identification and the finite-checker frontier |
| 45–50 | Verification evidence, exact endpoint types, finite-prefix obstruction, quantitative resolvent approximation, references and source concordance |

## Scope

The existing formal endpoints prove `H00 → RiemannHypothesis` and `H00 ↔ RiemannHypothesis` by the recorded routes. **H00 remains unproved.** This manuscript does not claim unconditional RH, a finite accepted certificate, or completion of the archived Widder/angular-PDE route.

The complex Hilbert-space realization, model examples and additional approximation lemmas are mathematical exposition. They are distinguished from the existing audited Lean declarations. The original eleven-page preprint and introduction draft remain available in the parent index.

## Build

Requirements: Python 3, `pdflatex`, and Poppler's `pdfinfo`. A standard TeX Live installation with Latin Modern, AMS packages, geometry, microtype, booktabs, enumitem, fancyhdr and hyperref is sufficient.

```sh
python build.py
```

The build runs LaTeX three times, rejects overfull boxes and unresolved references, verifies all 50 thematic page locations, and confirms exactly 50 physical pages. It writes the PDF and a build-validation JSON file. The source is split into seven chapter files, with the preamble and assembly in `preprint.tex`.

No Lean or Lake is invoked by the manuscript builder. Formal compilation remains assigned to the existing GitHub CI workflow.

## Formal baseline

- Source commit: `c6b95fd9e3d792270026da083bddddbc72bacb22`.
- [Successful CI run 40712534224](https://github.com/randogelist/Hilber-Vector-Resolvent-Theory/actions/runs/40712534224): 118 preserved Lean files, four exact endpoint type checks and 641 axiom-audited declarations.
- Project anchor: `ZETA_HYPERBOLIC_ANCHOR_5`.
- Mode and target: `A_TIER_LEAN`, `GITHUB_CI`.
- Native and GitHub evidence remain distinct; no proof sources are changed by this expansion.
