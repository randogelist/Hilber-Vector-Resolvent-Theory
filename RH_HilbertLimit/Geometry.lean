import Mathlib.Analysis.Complex.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.NormCast

/-!
# The geometric growth parameter

This module contains no xi-specific assumption.  The real-segment condition
is proved equivalent to unit ellipse radius.  A supremum is defined with an
explicit `1` included so that it also behaves correctly for an empty index type.
For the actual nonempty spectrum this is exactly the paper's `R_*`.

Candidate source for native Lean 4.33.0; not compiled in this environment.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace RH_HilbertLimit

def ellipseRadius (z : ℂ) : ℝ := ‖z‖ + ‖1 - z‖

def InUnitSegment (z : ℂ) : Prop :=
  z.im = 0 ∧ 0 ≤ z.re ∧ z.re ≤ 1

theorem one_le_ellipseRadius (z : ℂ) : 1 ≤ ellipseRadius z := by
  have h := norm_add_le z (1 - z)
  simpa [ellipseRadius] using h

theorem ellipseRadius_eq_one_iff (z : ℂ) :
    ellipseRadius z = 1 ↔ InUnitSegment z := by
  constructor
  · intro h
    have hq := Complex.re_le_norm z
    have hc := Complex.re_le_norm (1 - z)
    have hc' : 1 - z.re ≤ ‖1 - z‖ := by simpa using hc
    have heq : z.re = ‖z‖ := by dsimp [ellipseRadius] at h; linarith
    have hn : 0 ≤ z.re := by rw [heq]; exact norm_nonneg z
    have him : z.im = 0 :=
      Complex.abs_re_eq_norm.mp (by rw [abs_of_nonneg hn, heq])
    have hu : z.re ≤ 1 := by
      have hz := norm_nonneg (1 - z)
      dsimp [ellipseRadius] at h
      linarith
    exact ⟨him, hn, hu⟩
  · rintro ⟨him, hlo, hhi⟩
    have hz : z = (z.re : ℂ) := by
      apply Complex.ext <;> simp [him]
    rw [ellipseRadius, hz]
    have hsub : (1 : ℂ) - (z.re : ℂ) = ((1 - z.re : ℝ) : ℂ) := by
      push_cast <;> rfl
    rw [hsub, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg hlo, abs_of_nonneg (sub_nonneg.mpr hhi)]
    ring

theorem ellipseRadius_le_one_iff (z : ℂ) :
    ellipseRadius z ≤ 1 ↔ InUnitSegment z := by
  rw [← ellipseRadius_eq_one_iff]
  exact ⟨fun h => le_antisymm h (one_le_ellipseRadius z), fun h => h.le⟩

theorem one_lt_ellipseRadius_iff (z : ℂ) :
    1 < ellipseRadius z ↔ ¬ InUnitSegment z := by
  rw [← ellipseRadius_le_one_iff, not_le]

def spectralRadius {ι : Type*} (q : ι → ℂ) : ℝ :=
  sSup (insert 1 (Set.range fun i => ellipseRadius (q i)))

def SpectralBounded {ι : Type*} (q : ι → ℂ) : Prop :=
  BddAbove (insert 1 (Set.range fun i => ellipseRadius (q i)))

theorem spectralBounded_of_norm_bound {ι : Type*} {q : ι → ℂ}
    {S : ℝ} (hS : 0 ≤ S) (hq : ∀ i, ‖q i‖ ≤ S) : SpectralBounded q := by
  refine ⟨1 + 2 * S, ?_⟩
  intro x hx
  rcases hx with hx | hx
  · subst x
    linarith
  · rcases hx with ⟨i, rfl⟩
    have ht : ‖(1 : ℂ) - q i‖ ≤ 1 + ‖q i‖ := by
      simpa using norm_sub_le (1 : ℂ) (q i)
    dsimp [ellipseRadius]
    linarith [hq i]

theorem one_le_spectralRadius {ι : Type*} {q : ι → ℂ}
    (hq : SpectralBounded q) : 1 ≤ spectralRadius q := by
  exact le_csSup hq (Set.mem_insert _ _)

theorem ellipseRadius_le_spectralRadius {ι : Type*} {q : ι → ℂ}
    (hq : SpectralBounded q) (i : ι) :
    ellipseRadius (q i) ≤ spectralRadius q := by
  exact le_csSup hq (Set.mem_insert_of_mem _ ⟨i, rfl⟩)

/-- On a nonempty spectrum the protective inserted value is redundant:
this is exactly the supremum used in the paper. -/
theorem spectralRadius_eq_sSup_range {ι : Type*} [Nonempty ι] {q : ι → ℂ}
    (hq : SpectralBounded q) :
    spectralRadius q = sSup (Set.range fun i => ellipseRadius (q i)) := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hb : BddAbove (Set.range fun i => ellipseRadius (q i)) := by
    obtain ⟨B, hB⟩ := hq
    exact ⟨B, fun x hx => hB (Set.mem_insert_of_mem 1 hx)⟩
  apply le_antisymm
  · apply csSup_le (Set.insert_nonempty _ _)
    intro x hx
    rcases hx with hx | hx
    · subst x
      exact (one_le_ellipseRadius (q i₀)).trans (le_csSup hb ⟨i₀, rfl⟩)
    · exact le_csSup hb hx
  · have hn : Set.Nonempty (Set.range fun i : ι => ellipseRadius (q i)) :=
      ⟨ellipseRadius (q i₀), ⟨i₀, rfl⟩⟩
    apply csSup_le hn
    intro x hx
    exact le_csSup hq (Set.mem_insert_of_mem 1 hx)

theorem spectralRadius_eq_one_iff {ι : Type*} {q : ι → ℂ}
    (hq : SpectralBounded q) :
    spectralRadius q = 1 ↔ ∀ i, InUnitSegment (q i) := by
  constructor
  · intro h i
    apply (ellipseRadius_le_one_iff _).mp
    simpa [h] using ellipseRadius_le_spectralRadius hq i
  · intro h
    apply le_antisymm _ (one_le_spectralRadius hq)
    apply csSup_le (Set.insert_nonempty _ _)
    intro x hx
    rcases hx with hx | ⟨i, rfl⟩
    · exact hx.le
    · exact (ellipseRadius_le_one_iff _).mpr (h i)

theorem one_lt_spectralRadius_of_node {ι : Type*} {q : ι → ℂ}
    (hq : SpectralBounded q) (i : ι) (hi : ¬ InUnitSegment (q i)) :
    1 < spectralRadius q :=
  ((one_lt_ellipseRadius_iff _).mpr hi).trans_le
    (ellipseRadius_le_spectralRadius hq i)

/-- The affine factors used in the generating polynomial have this upper bound. -/
theorem norm_affine_le_ellipseRadius (q x : ℂ) (hx : ‖x‖ ≤ 1) :
    ‖1 + (x - 1) * q‖ ≤ ellipseRadius q := by
  calc
    ‖1 + (x - 1) * q‖ = ‖(1 - q) + x * q‖ := by congr 1; ring
    _ ≤ ‖1 - q‖ + ‖x * q‖ := norm_add_le _ _
    _ = ‖1 - q‖ + ‖x‖ * ‖q‖ := by rw [norm_mul]
    _ ≤ ‖1 - q‖ + 1 * ‖q‖ :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right hx (norm_nonneg q))
    _ = ellipseRadius q := by dsimp [ellipseRadius]; ring

/-- The theta zero corresponding to a normalized inverse zero node. -/
def rootOfNode (κ : ℝ) (q : ℂ) : ℂ := -((κ : ℂ) * q)⁻¹

theorem rootOfNode_nonpositive_iff {κ : ℝ} (hκ : 0 < κ)
    {q : ℂ} (hq : q ≠ 0) :
    ((rootOfNode κ q).im = 0 ∧ (rootOfNode κ q).re ≤ 0) ↔
      (q.im = 0 ∧ 0 ≤ q.re) := by
  have hκc : (κ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hκ
  have hd : 0 < Complex.normSq ((κ : ℂ) * q) :=
    Complex.normSq_pos.mpr (mul_ne_zero hκc hq)
  have him : (rootOfNode κ q).im =
      κ * q.im / Complex.normSq ((κ : ℂ) * q) := by
    simp only [rootOfNode, Complex.neg_im, Complex.inv_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, neg_div, neg_neg]
  have hre : (rootOfNode κ q).re =
      -(κ * q.re / Complex.normSq ((κ : ℂ) * q)) := by
    simp only [rootOfNode, Complex.neg_re, Complex.inv_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [him, hre]
  constructor
  · rintro ⟨hi, hr⟩
    have hi' : κ * q.im = 0 :=
      (div_eq_zero_iff.mp hi).resolve_right (ne_of_gt hd)
    have hqi : q.im = 0 := (mul_eq_zero.mp hi').resolve_left (ne_of_gt hκ)
    have hquot : 0 ≤ κ * q.re / Complex.normSq ((κ : ℂ) * q) := by linarith
    have hprod : 0 ≤ κ * q.re := by
      simpa using (le_div_iff₀ hd).mp hquot
    have hqr : 0 ≤ q.re := by
      by_contra hneg
      have hpos : 0 < κ * (-q.re) :=
        mul_pos hκ (neg_pos.mpr (lt_of_not_ge hneg))
      nlinarith only [hprod, hpos]
    exact ⟨hqi, hqr⟩
  · rintro ⟨hi, hr⟩
    constructor
    · simp [hi]
    · exact neg_nonpos.mpr (div_nonneg (mul_nonneg hκ.le hr) hd.le)

theorem square_nonpositive_iff_re_zero (w : ℂ) :
    ((w ^ 2).im = 0 ∧ (w ^ 2).re ≤ 0) ↔ w.re = 0 := by
  constructor
  · rintro ⟨hi, hr⟩
    have hi' : w.re * w.im = 0 := by
      simp only [pow_two, Complex.mul_im] at hi
      nlinarith
    by_cases hw : w.im = 0
    · simp only [pow_two, Complex.mul_re, hw, mul_zero, sub_zero] at hr
      nlinarith [sq_nonneg w.re]
    · exact (mul_eq_zero.mp hi').resolve_right hw
  · intro hw
    constructor
    · simp [pow_two, Complex.mul_im, hw]
    · simp only [pow_two, Complex.mul_re, hw, zero_mul, zero_sub]
      exact neg_nonpos.mpr (mul_self_nonneg w.im)

end RH_HilbertLimit
