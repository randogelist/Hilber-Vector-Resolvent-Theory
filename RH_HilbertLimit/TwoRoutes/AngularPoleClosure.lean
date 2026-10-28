import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Route two: a genuine simple pole forbids a continuous extension

This is the local analytic contradiction used at the end of the angular route.
It is generic complex analysis: the actual coefficient/germ identification and
the actual pole construction must be supplied separately when it is applied.

Prepared without running Lean, Lake, a local compiler, or an axiom audit.
-/

set_option autoImplicit false

namespace RH_HilbertLimit.TwoRoutes

open Filter
open scoped Topology

/-- A function continuous at p cannot agree on a punctured neighbourhood with
a nonzero simple principal part plus a continuous remainder. Multiplication
by z-p gives two incompatible limits: zero and the residue. -/
theorem simplePole_residue_eq_zero_of_continuousAt
    {f remainder : ℂ → ℂ} {p residue : ℂ}
    (hf : ContinuousAt f p)
    (hR : ContinuousAt remainder p)
    (hprincipal : ∀ᶠ z : ℂ in 𝓝[≠] p,
      f z = residue / (z - p) + remainder z) :
    residue = 0 := by
  have hcont : ContinuousAt
      (fun z : ℂ => (z - p) * (f z - remainder z)) p :=
    (continuousAt_id.sub continuousAt_const).mul (hf.sub hR)
  have hfull : Tendsto
      (fun z : ℂ => (z - p) * (f z - remainder z))
      (𝓝 p) (𝓝 (0 : ℂ)) := by
    simpa only [ContinuousAt, sub_self, zero_mul] using hcont
  have hzero : Tendsto
      (fun z : ℂ => (z - p) * (f z - remainder z))
      (𝓝[≠] p) (𝓝 (0 : ℂ)) :=
    hfull.mono_left nhdsWithin_le_nhds
  have heq :
      (fun z : ℂ => (z - p) * (f z - remainder z)) =ᶠ[𝓝[≠] p]
        (fun _ : ℂ => residue) := by
    filter_upwards [hprincipal, self_mem_nhdsWithin] with z hz hzp
    have hne : z - p ≠ 0 := sub_ne_zero.mpr (by simpa using hzp)
    rw [hz]
    field_simp [hne] <;> ring
  have hconst : Tendsto (fun _ : ℂ => residue)
      (𝓝[≠] p) (𝓝 residue) := tendsto_const_nhds
  exact (tendsto_nhds_unique_of_eventuallyEq hzero hconst heq).symm

/-- The original pole function need not be defined continuously at p. It is
enough that a proposed extension agrees with it on the punctured germ. -/
theorem simplePole_no_continuous_extension
    {poleFunction remainder : ℂ → ℂ} {p residue : ℂ}
    (hresidue : residue ≠ 0)
    (hR : ContinuousAt remainder p)
    (hprincipal : ∀ᶠ z : ℂ in 𝓝[≠] p,
      poleFunction z = residue / (z - p) + remainder z) :
    ¬ ∃ extension : ℂ → ℂ,
      ContinuousAt extension p ∧
        poleFunction =ᶠ[𝓝[≠] p] extension := by
  rintro ⟨extension, hcontinuous, hagree⟩
  have hprincipalExtension : ∀ᶠ z : ℂ in 𝓝[≠] p,
      extension z = residue / (z - p) + remainder z := by
    filter_upwards [hprincipal, hagree] with z hprincipalz hagreez
    rw [← hagreez]
    exact hprincipalz
  exact hresidue
    (simplePole_residue_eq_zero_of_continuousAt
      hcontinuous hR hprincipalExtension)

/-- Holomorphic extension is in particular impossible at a genuine simple
pole. This is the exact local obstruction needed after angular coefficient
growth has produced an analytic disk function and the germs are identified. -/
theorem simplePole_no_analytic_extension
    {poleFunction remainder : ℂ → ℂ} {p residue : ℂ}
    (hresidue : residue ≠ 0)
    (hR : AnalyticAt ℂ remainder p)
    (hprincipal : ∀ᶠ z : ℂ in 𝓝[≠] p,
      poleFunction z = residue / (z - p) + remainder z) :
    ¬ ∃ extension : ℂ → ℂ,
      AnalyticAt ℂ extension p ∧
        poleFunction =ᶠ[𝓝[≠] p] extension := by
  rintro ⟨extension, hanalytic, hagree⟩
  exact simplePole_no_continuous_extension hresidue hR.continuousAt hprincipal
    ⟨extension, hanalytic.continuousAt, hagree⟩

end RH_HilbertLimit.TwoRoutes
