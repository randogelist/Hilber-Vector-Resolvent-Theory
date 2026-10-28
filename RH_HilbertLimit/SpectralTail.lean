import RH_HilbertLimit.Geometry
import RH_HilbertLimit.ActualXi
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Data.Finset.Max

/-!
# Finite localization of the summable spectral tail

UNCOMPILED CANDIDATE for the user's native Lean 4.33.0 target.
No Lean, Lake, native compiler, or CI process was run to prepare this file.

Absolute summability gives a finite exceptional set for every ellipse-radius
threshold strictly above one.  In the nontrivial-radius case this localizes
the possible dominant spectrum to a finite set and gives a strictly smaller
uniform bound on the remaining affine factors.  It does not assume finite
support, construct ActualSpectralCalibration, or complete DominantExtraction.

The exact summable_iff_vanishing_norm and Finset.exists_max_image APIs were
inspected in their pinned Mathlib source at v4.33.0.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace RH_HilbertLimit.SpectralTail

/-- Absolute summability makes every fixed positive norm threshold exceptional
at only finitely many indices; repeated nodes are counted separately. -/
theorem norm_lt_outside_finite {ι : Type*} (q : ι → ℂ)
    (hq : Summable (fun i => ‖q i‖)) (ε : ℝ) (hε : 0 < ε) :
    ∃ s : Finset ι, ∀ i, i ∉ s → ‖q i‖ < ε := by
  classical
  obtain ⟨s, hs⟩ := (summable_iff_vanishing_norm.mp hq) ε hε
  refine ⟨s, ?_⟩
  intro i hi
  have hdis : Disjoint ({i} : Finset ι) s := by
    apply Finset.disjoint_left.mpr
    intro j hj hjs
    have hji : j = i := Finset.mem_singleton.mp hj
    exact hi (hji ▸ hjs)
  have hsmall := hs ({i} : Finset ι) hdis
  simpa only [Finset.sum_singleton, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg (q i))] using hsmall

/-- Above one, all but finitely many ellipse radii lie strictly below the threshold. -/
theorem ellipse_lt_outside_finite {ι : Type*} (q : ι → ℂ)
    (hq : Summable (fun i => ‖q i‖)) (r : ℝ) (hr : 1 < r) :
    ∃ s : Finset ι, ∀ i, i ∉ s → ellipseRadius (q i) < r := by
  obtain ⟨s, hs⟩ := norm_lt_outside_finite q hq ((r - 1) / 2) (by linarith)
  refine ⟨s, ?_⟩
  intro i hi
  have hsmall := hs i hi
  have hsub : ‖(1 : ℂ) - q i‖ ≤ 1 + ‖q i‖ := by
    simpa using norm_sub_le (1 : ℂ) (q i)
  dsimp [ellipseRadius]
  linarith

theorem finite_ellipse_superlevel {ι : Type*} (q : ι → ℂ)
    (hq : Summable (fun i => ‖q i‖)) (r : ℝ) (hr : 1 < r) :
    Set.Finite {i : ι | r ≤ ellipseRadius (q i)} := by
  classical
  obtain ⟨s, hs⟩ := ellipse_lt_outside_finite q hq r hr
  apply s.finite_toSet.subset
  intro i hi
  by_contra hmem
  exact (not_lt_of_ge hi) (hs i hmem)

/-- The same finite set works for every natural power of every fixed unit-disk phase. -/
theorem affine_power_bound_outside_finite {ι : Type*} (q : ι → ℂ)
    (hq : Summable (fun i => ‖q i‖)) (r : ℝ) (hr : 1 < r)
    (x : ℂ) (hx : ‖x‖ ≤ 1) :
    ∃ s : Finset ι, ∀ N i, i ∉ s →
      ‖q i * (1 + (x - 1) * q i) ^ N‖ ≤ ‖q i‖ * r ^ N := by
  obtain ⟨s, hs⟩ := ellipse_lt_outside_finite q hq r hr
  refine ⟨s, ?_⟩
  intro N i hi
  have hfactor : ‖1 + (x - 1) * q i‖ ≤ r :=
    (norm_affine_le_ellipseRadius (q i) x hx).trans (hs i hi).le
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg (1 + (x - 1) * q i)) hfactor N)
    (norm_nonneg (q i))

/-- When the spectral radius exceeds one, choose an explicit intermediate
radius and localize every possible dominant node to a finite exceptional set. -/
theorem finite_tail_below_radius {ι : Type*} (q : ι → ℂ)
    (hq : Summable (fun i => ‖q i‖)) (hR : 1 < spectralRadius q) :
    ∃ r : ℝ, 1 < r ∧ r < spectralRadius q ∧
      ∃ s : Finset ι, ∀ i, i ∉ s → ellipseRadius (q i) < r := by
  let r : ℝ := (1 + spectralRadius q) / 2
  have hr : 1 < r := by dsimp [r]; linarith
  have hrR : r < spectralRadius q := by dsimp [r]; linarith
  exact ⟨r, hr, hrR, ellipse_lt_outside_finite q hq r hr⟩

/-- A spectral radius strictly above one is attained at a node.  The finite
exceptional set is obtained from summability, not assumed as finite support. -/
theorem spectralRadius_attained {ι : Type*} (q : ι → ℂ)
    (hq : Summable (fun i => ‖q i‖)) (hb : SpectralBounded q)
    (hR : 1 < spectralRadius q) :
    ∃ i : ι, ellipseRadius (q i) = spectralRadius q := by
  classical
  obtain ⟨r, hr, hrR, s, hs⟩ := finite_tail_below_radius q hq hR
  have hexists : ∃ i : ι, r < ellipseRadius (q i) := by
    by_contra hnone
    have hupper : ∀ i : ι, ellipseRadius (q i) ≤ r := by
      intro i
      by_contra hi
      exact hnone ⟨i, lt_of_not_ge hi⟩
    have hRle : spectralRadius q ≤ r := by
      change sSup (insert (1 : ℝ) (Set.range fun i => ellipseRadius (q i))) ≤ r
      apply csSup_le (Set.insert_nonempty _ _)
      intro a ha
      rcases ha with rfl | ⟨i, rfl⟩
      · exact hr.le
      · exact hupper i
    exact (not_le_of_gt hrR) hRle
  obtain ⟨i₀, hi₀⟩ := hexists
  have hi₀s : i₀ ∈ s := by
    by_contra hi
    exact (not_lt_of_ge hi₀.le) (hs i₀ hi)
  obtain ⟨iMax, hiMax, hmax⟩ :=
    s.exists_max_image (fun i => ellipseRadius (q i)) ⟨i₀, hi₀s⟩
  have hrMax : r < ellipseRadius (q iMax) := hi₀.trans_le (hmax i₀ hi₀s)
  have hglobal : ∀ i : ι, ellipseRadius (q i) ≤ ellipseRadius (q iMax) := by
    intro i
    by_cases hi : i ∈ s
    · exact hmax i hi
    · exact (hs i hi).le.trans hrMax.le
  refine ⟨iMax, le_antisymm (ellipseRadius_le_spectralRadius hb iMax) ?_⟩
  change sSup (insert (1 : ℝ) (Set.range fun i => ellipseRadius (q i))) ≤
    ellipseRadius (q iMax)
  apply csSup_le (Set.insert_nonempty _ _)
  intro a ha
  rcases ha with rfl | ⟨i, rfl⟩
  · exact hr.le.trans hrMax.le
  · exact hglobal i

end RH_HilbertLimit.SpectralTail

namespace RH_HilbertLimit.ActualSpectralCalibration

/-- This finite-tail conclusion is derived from the existing calibration
fields.  It adds no new analytic premise beyond the nontrivial-radius case. -/
theorem finite_tail_below_radius {ι : Type*} (D : ActualSpectralCalibration ι)
    (hR : 1 < spectralRadius D.node) :
    ∃ r : ℝ, 1 < r ∧ r < spectralRadius D.node ∧
      ∃ s : Finset ι, ∀ i, i ∉ s → ellipseRadius (D.node i) < r :=
  SpectralTail.finite_tail_below_radius D.node D.norm_summable hR

/-- Actual calibrated specialization: no additional maximum-attainment
assumption is introduced. -/
theorem spectralRadius_attained {ι : Type*} (D : ActualSpectralCalibration ι)
    (hR : 1 < spectralRadius D.node) :
    ∃ i : ι, ellipseRadius (D.node i) = spectralRadius D.node :=
  SpectralTail.spectralRadius_attained D.node D.norm_summable D.bounded hR

end RH_HilbertLimit.ActualSpectralCalibration
