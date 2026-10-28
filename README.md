# Hilber-Vector-Resolvent-Theory

Two Lean constructions of the conditional implication **`H00 → RiemannHypothesis`**, with two equivalence declarations **`H00 ↔ RiemannHypothesis`**. The common hypothesis `H00` remains unproved. This repository does **not** establish unconditional RH or a finite accepted certificate.

The frozen source is `RH_H00_TWO_ROUTES_LEAN_v0_2_3_construction`. Its Windows Lean 4.33.0 build and axiom audit passed according to the supplied native console excerpt. The original native logs and per-declaration axiom output were not independently supplied; the provenance record preserves that distinction.

- [Paper candidates and theory introduction](Paper-Candidates/README.md)
- [Mathematical preprint](docs/RH_H00_Two_Routes_Native_PASS_and_GitHub_CI.pdf)
- [GitHub Actions runs](https://github.com/randogelist/Hilber-Vector-Resolvent-Theory/actions)
- [Native PASS checkpoint](evidence/NATIVE_PASS_CHECKPOINT.json)
- [CI workflow](.github/workflows/lean.yml)

## Formal statements

All four declarations live in `RH_HilbertLimit.TwoRoutes`:

```lean
nativeRH_of_H00_route_one : H00 → _root_.RiemannHypothesis
H00_iff_nativeRH_route_one : H00 ↔ _root_.RiemannHypothesis
nativeRH_of_H00_route_two : H00 → _root_.RiemannHypothesis
H00_iff_nativeRH_route_two : H00 ↔ _root_.RiemannHypothesis
```

`H00 := zeroBudgetCandidate.Admissible`, where the finite data pair is `(0, 0)`, but admissibility quantifies over **every** natural-number row. It is not a Boolean check of finitely many rows.

| Construction | Forward proof |
| --- | --- |
| [Route 1](RH_HilbertLimit/TwoRoutes/RouteOne.lean) | Zero cancellation gives constant row variation, then subexponential variation and the retained actual spectral closure. |
| [Route 2](RH_HilbertLimit/TwoRoutes/RouteTwo.lean) | Positive Bernstein rows give a probability measure with the actual moments; its analytic resolvent identifies the logarithmic-derivative germ, continues the analytic defect, and excludes nonreal zeros. |

Route 2 shares `H00` and direct positivity lemmas with Route 1, but its forward construction does not call Route 1's RH endpoint. Both equivalences use the same retained converse `H00_of_nativeRH`. The original longer Widder/angular-PDE construction is a separate unfinished route.

## GitHub CI

The active verification target is `GITHUB_CI`, explicitly requested after the native checkpoint. Native evidence and CI evidence remain separate. [Run 40712534224](https://github.com/randogelist/Hilber-Vector-Resolvent-Theory/actions/runs/40712534224) passed at commit `c6b95fd9e3d792270026da083bddddbc72bacb22`: source identity, the full build, all four endpoint types, and all 641 axiom checks. The job log was independently read; see [CI PASS checkpoint](evidence/GITHUB_CI_PASS_CHECKPOINT.json) and [per-declaration axiom results](evidence/GITHUB_CI_AXIOM_AUDIT.json).

- Lean: `leanprover/lean4:v4.33.0`.
- Mathlib: commit `db584cd6d46c92f209a44c0f1c829460d327499d` (verified `v4.33.0` release tag). The original native mathlib commit was not supplied, so cross-target equivalence of dependency revisions is not assumed.
- The 118 preserved Lean files comprise 117 source modules and the final audit source. CI verifies their hashes before building.
- The final audit covers all **641** selected declarations, including the four endpoints. It rejects missing/duplicate entries and any axiom outside `propext`, `Classical.choice`, and `Quot.sound`.
- Build logs, audit output, and verification metadata are uploaded as run artifacts, including on failure when produced. No Windows native project cache is reused in CI.

Pushes, pull requests, and manual workflow dispatches run the checks. All Lean execution for this setup takes place on GitHub Actions; no Lean or Lake execution was performed in the assistant's local environment.

## Evidence and remaining work

The reported native run compiled 3 modules and reused 115 frozen modules, ending with `PROJECT_BUILD=PASS` and `RUN=PASS`. This count includes the final audit task. The audit plan and endpoint coverage were independently inspected statically.

Still open: unconditional `H00` admissibility and universal zero-budget propagation; a terminating finite checker's soundness and completeness; and equivalence between accepted-certificate existence and RH. A finite accepted witness is not established.

The frozen chronological project anchor is **`ZETA_HYPERBOLIC_ANCHOR_5`**. This publication adds a CI target and report; it does not create an Init record or rename the project anchor. Historical preparation comments in the unchanged Lean sources predate the later native PASS report.

## Source provenance

The original package SHA-256 is:

```text
578cc8ad072c79dc7838fcf65a27b9eed707fcc98e0fdf6a4b3601aa20e8c51a
```

The native checkpoint and original package metadata are retained under `evidence/`. The new CI configuration, parser tests, and report generator are separate from the frozen proof source. No new license is assigned by this publication.
