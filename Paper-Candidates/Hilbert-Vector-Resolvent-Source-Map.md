# Introduction: source map and formal status

This record accompanies [Draft 0.1 of the introduction](Hilbert-Vector-Resolvent-Introduction.md). It separates mathematical exposition from the declarations covered by the existing compiler evidence.

## Verification baseline

- Project anchor: `ZETA_HYPERBOLIC_ANCHOR_5`.
- Mode and target remain `A_TIER_LEAN` and `GITHUB_CI`.
- Verified source commit: `c6b95fd9e3d792270026da083bddddbc72bacb22`.
- [GitHub CI run 40712534224](https://github.com/randogelist/Hilber-Vector-Resolvent-Theory/actions/runs/40712534224): build, exact endpoint type checks, and full 641-declaration axiom audit passed.
- [CI checkpoint](../evidence/GITHUB_CI_PASS_CHECKPOINT.json) and [per-declaration axiom results](../evidence/GITHUB_CI_AXIOM_AUDIT.json) preserve the independently read result.
- The 118 frozen Lean files are unchanged by this manuscript work. No local Lean or Lake was run.

## Claim correspondence

| Introduction component | Source anchor | Status |
| --- | --- | --- |
| Norm-square and Cauchy–Schwarz geometry | [RealGramGeometry](../Frontier/ContractiveOrbitFrontier.lean) | Audited abstract interface. It does not assume a vector-space structure, bilinearity, or completeness. |
| Representation by a contractive orbit | [BKQRContractiveOrbit](../Frontier/ContractiveOrbitFrontier.lean) | Parameterized interface: its moment representation and contractivity are supplied fields. Its operator is a function `Vec → Vec`, not necessarily linear or self-adjoint. |
| Contraction and Gram defect decomposition | [MOMENT_DEFECT_IS_BKQR_PAIR_SQUARE](../Derivations/BKQR/DefectGramSquare.lean) | Audited theorem for a supplied real Gram orbit. The introduction's complex Hilbert-space formula is its elementary mathematical analogue. |
| Coefficient bounds and disk summability | [contractiveOrbit_abs_le_base; contractiveOrbit_absolute_summability](../RH_HilbertLimit/TwoRoutes/RouteTwoContractive.lean) | Audited consequences of a supplied orbit; not an existence theorem for every intended coefficient family. |
| Actual positivity from H00 | [actual_weights_nonnegative_of_H00](../RH_HilbertLimit/TwoRoutes/RouteOne.lean), [actual_bernsteinPositive_of_H00](../RH_HilbertLimit/TwoRoutes/ActualPositivePrefix.lean) | Audited actual conditional construction. |
| Finite Bernstein monomial limit | [bernsteinAverage_monomial_tendsto](../RH_HilbertLimit/TwoRoutes/BernsteinMomentLimit.lean) | Audited for arbitrary real sequences; positivity is not needed for this limit. |
| Probability measure with the actual moments | [actualHausdorffMeasure; actualHausdorffMeasure_moment](../RH_HilbertLimit/TwoRoutes/HausdorffMeasure.lean) | Audited construction from H00; no additional representing-measure premise. |
| Scalar resolvent analyticity, derivatives, and sign | [ResolventAnalytic.lean](../RH_HilbertLimit/TwoRoutes/ResolventAnalytic.lean), [MeasureResolvent.lean](../RH_HilbertLimit/TwoRoutes/MeasureResolvent.lean) | Audited integral construction with the stated positivity and denominator conditions. |
| Actual logarithmic-derivative germ | [actual_logDerivative_resolvent_germ](../RH_HilbertLimit/TwoRoutes/MeasureResolvent.lean) | Audited analytic identification from the exact actual moments. |
| Continuation across possible zeros | [entire_ode_on_upperHalfPlane_of_origin_germ](../RH_HilbertLimit/TwoRoutes/ActualResolventContinuation.lean) | Audited continuation of the analytic defect. |
| Actual RH endpoint | [RouteTwo.lean](../RH_HilbertLimit/TwoRoutes/RouteTwo.lean), [ActualHerglotzClosure.lean](../RH_HilbertLimit/TwoRoutes/ActualHerglotzClosure.lean) | Audited H00-to-RH implication; the converse is shared with Route 1. |
| Full positive self-adjoint model on L²(σ) and its operator resolvent | Introduction, Sections 3–4 | Paper-level mathematical realization. No corresponding concrete project Lean implementation is claimed. |
| Weighted vectors, operators, and model coefficients | Introduction, Section 6; pointwise bounds in [RouteTwoContractive.lean](../RH_HilbertLimit/TwoRoutes/RouteTwoContractive.lean) | Bounds on the scalar weight and multiplier are audited. The displayed Hilbert-space packaging is paper-level exposition. |
| Equality with archived actual Widder coefficients | [ActualApproximationConvergence](../RH_HilbertLimit/TwoRoutes/ActualLimitBridge.lean) | Open identification condition in the longer chain; it is not discharged by naming the model coefficients. |

Historical module headers describe their original source-preparation state. Current status comes from the preserved CI evidence and the complete endpoint dependencies. In particular, the earlier input-parameterized spectral statements in `Main.lean` must be read together with the later actual constructions in [AnalyticClosure.lean](../RH_HilbertLimit/AnalyticClosure.lean).

## Editing priorities for the next draft

1. Decide how much of the general contraction framework belongs in the opening introduction and how much should move into a preliminary section.
2. If a fully formal operator presentation is pursued, construct the concrete L²(σ) positive contraction and vector-resolvent identities as a separately audited extension.
3. Preserve separate notation for model coefficients until equality with each intended actual coefficient family is proved.
4. Keep the universal admissibility condition and the terminating finite-checker goal distinct.

This candidate introduces no new unconditional RH claim, no finite accepted witness, and no new Init record.
