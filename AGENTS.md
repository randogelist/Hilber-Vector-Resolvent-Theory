# Project constraints

- Never execute Lean, Lake, or a Lean compiler locally in an assistant environment. GitHub Actions is the explicitly authorized compiler target.
- Mode: A_TIER_LEAN. Active target: GITHUB_CI. Preserve earlier LOCAL_COMPILER evidence as a distinct checkpoint.
- Frozen project anchor: ZETA_HYPERBOLIC_ANCHOR_5. Preserve this exact spelling.
- Preserve the theorem scope: both H00-to-literal-RiemannHypothesis forward constructions and their equivalences. H00 itself remains assumed.
- Do not claim unconditional RH, finite witness acceptance, checker soundness/completeness, or completion of the original longer Widder/angular-PDE construction.
- The native v0.2.3 proof sources are byte-preserved. Any later source repair needs an explicit new source provenance record; do not silently rewrite the frozen manifest to conceal changes.
- Native PASS is user-reported evidence. CI PASS requires a successful GitHub run with the strict full axiom audit.
- No automatic Init record, branch renaming, or scope change.
