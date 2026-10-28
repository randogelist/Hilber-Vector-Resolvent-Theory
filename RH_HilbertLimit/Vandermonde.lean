import RH_HilbertLimit.Growth
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Quantitative finite Vandermonde noncancellation

Distinct complex exponential rates admit an exact inverse-row recovery formula.
It gives a lower bound on a fixed block of consecutive terms.  A smaller
geometric tail can then be absorbed.  These are finite-dimensional theorems;
extracting the dominant finite set from an actual infinite zero spectrum is
a separate obligation, not an assumption silently discharged here.

Prepared without executing Lean; native compilation and axiom audit remain due.
-/

noncomputable section

open Filter
open scoped Topology BigOperators

namespace RH_HilbertLimit

def finiteExponentialSum {d : ℕ} (rate c : Fin d → ℂ) (N : ℕ) : ℂ :=
  ∑ i : Fin d, c i * rate i ^ N

def finiteBlockMatrix {d : ℕ} (rate : Fin d → ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  (Matrix.vandermonde rate).transpose

/-- A strictly positive control constant, even before any row nonvanishing is proved. -/
def inverseRowControl {d : ℕ} (rate : Fin d → ℂ) (i₀ : Fin d) : ℝ :=
  1 + ∑ k : Fin d, ‖(finiteBlockMatrix rate)⁻¹ i₀ k‖

def recoveryConstant {d : ℕ} (rate c : Fin d → ℂ) (i₀ : Fin d) : ℝ :=
  ‖c i₀‖ / inverseRowControl rate i₀

theorem inverseRowControl_pos {d : ℕ} (rate : Fin d → ℂ) (i₀ : Fin d) :
    0 < inverseRowControl rate i₀ := by
  have hs : 0 ≤ ∑ k : Fin d, ‖(finiteBlockMatrix rate)⁻¹ i₀ k‖ :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  unfold inverseRowControl
  linarith

theorem recoveryConstant_pos {d : ℕ} (rate c : Fin d → ℂ) (i₀ : Fin d)
    (hc : c i₀ ≠ 0) : 0 < recoveryConstant rate c i₀ := by
  exact div_pos (norm_pos_iff.mpr hc) (inverseRowControl_pos rate i₀)

theorem finiteBlockMatrix_det_ne_zero {d : ℕ} {rate : Fin d → ℂ}
    (hrate : Function.Injective rate) : (finiteBlockMatrix rate).det ≠ 0 := by
  rw [finiteBlockMatrix, Matrix.det_transpose]
  exact Matrix.det_vandermonde_ne_zero_iff.mpr hrate

theorem finiteExponential_block_mulVec {d : ℕ}
    (rate c : Fin d → ℂ) (N : ℕ) :
    (finiteBlockMatrix rate).mulVec (fun i => c i * rate i ^ N) =
      (fun k : Fin d => finiteExponentialSum rate c (N + (k : ℕ))) := by
  funext k
  simp only [Matrix.mulVec, dotProduct, finiteBlockMatrix,
    Matrix.transpose_apply, Matrix.vandermonde_apply, finiteExponentialSum, pow_add]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Exact recovery of one coefficient times its exponential rate from a consecutive block. -/
theorem finite_exponential_recovery {d : ℕ} {rate : Fin d → ℂ}
    (hrate : Function.Injective rate) (c : Fin d → ℂ) (N : ℕ) (i₀ : Fin d) :
    c i₀ * rate i₀ ^ N =
      ∑ k : Fin d, (finiteBlockMatrix rate)⁻¹ i₀ k *
        finiteExponentialSum rate c (N + (k : ℕ)) := by
  have hu : IsUnit (finiteBlockMatrix rate).det :=
    isUnit_iff_ne_zero.mpr (finiteBlockMatrix_det_ne_zero hrate)
  have hr : ((finiteBlockMatrix rate)⁻¹).mulVec
      (fun k : Fin d => finiteExponentialSum rate c (N + (k : ℕ))) =
      (fun i => c i * rate i ^ N) := by
    rw [← finiteExponential_block_mulVec rate c N, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul (finiteBlockMatrix rate) hu, Matrix.one_mulVec]
  simpa only [Matrix.mulVec, dotProduct] using (congrFun hr i₀).symm

/-- A common upper bound on one block controls every recovered coefficient. -/
theorem coefficient_norm_le_block_bound
    {d : ℕ} {rate c : Fin d → ℂ} {N : ℕ} {i₀ : Fin d} {M : ℝ}
    (hrate : Function.Injective rate) (hM : 0 ≤ M)
    (hb : ∀ k : Fin d, ‖finiteExponentialSum rate c (N + (k : ℕ))‖ ≤ M) :
    ‖c i₀‖ * ‖rate i₀‖ ^ N ≤ inverseRowControl rate i₀ * M := by
  calc
    ‖c i₀‖ * ‖rate i₀‖ ^ N = ‖c i₀ * rate i₀ ^ N‖ := by rw [norm_mul, norm_pow]
    _ = ‖∑ k : Fin d, (finiteBlockMatrix rate)⁻¹ i₀ k *
        finiteExponentialSum rate c (N + (k : ℕ))‖ :=
      congrArg norm (finite_exponential_recovery hrate c N i₀)
    _ ≤ ∑ k : Fin d, ‖(finiteBlockMatrix rate)⁻¹ i₀ k *
        finiteExponentialSum rate c (N + (k : ℕ))‖ := norm_sum_le _ _
    _ = ∑ k : Fin d, ‖(finiteBlockMatrix rate)⁻¹ i₀ k‖ *
        ‖finiteExponentialSum rate c (N + (k : ℕ))‖ := by simp only [norm_mul]
    _ ≤ ∑ k : Fin d, ‖(finiteBlockMatrix rate)⁻¹ i₀ k‖ * M := by
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_left (hb k) (norm_nonneg _)
    _ = (∑ k : Fin d, ‖(finiteBlockMatrix rate)⁻¹ i₀ k‖) * M := by
      rw [Finset.sum_mul]
    _ ≤ inverseRowControl rate i₀ * M := by
      apply mul_le_mul_of_nonneg_right _ hM
      unfold inverseRowControl
      linarith

theorem recoveryConstant_mul_pow_le_block_bound
    {d : ℕ} {rate c : Fin d → ℂ} {N : ℕ} {i₀ : Fin d} {M : ℝ}
    (hrate : Function.Injective rate) (hM : 0 ≤ M)
    (hb : ∀ k : Fin d, ‖finiteExponentialSum rate c (N + (k : ℕ))‖ ≤ M) :
    recoveryConstant rate c i₀ * ‖rate i₀‖ ^ N ≤ M := by
  have h := coefficient_norm_le_block_bound (i₀ := i₀) hrate hM hb
  have hdiv : (‖c i₀‖ * ‖rate i₀‖ ^ N) / inverseRowControl rate i₀ ≤ M := by
    apply (div_le_iff₀ (inverseRowControl_pos rate i₀)).mpr
    simpa only [mul_comm] using h
  calc
    recoveryConstant rate c i₀ * ‖rate i₀‖ ^ N =
        (‖c i₀‖ * ‖rate i₀‖ ^ N) / inverseRowControl rate i₀ := by
      unfold recoveryConstant
      ring
    _ ≤ M := hdiv

/-- A monotone envelope cannot lose a nonzero finite exponential coefficient. -/
theorem finite_exponential_shifted_lower
    {d : ℕ} {rate c : Fin d → ℂ} {V : ℕ → ℝ}
    (hrate : Function.Injective rate) (i₀ : Fin d)
    (hmono : Monotone V)
    (hdom : ∀ n : ℕ, ‖finiteExponentialSum rate c n‖ ≤ V n) :
    ∀ N : ℕ, recoveryConstant rate c i₀ * ‖rate i₀‖ ^ N ≤ V (N + d) := by
  intro N
  have hM : 0 ≤ V (N + d) := (norm_nonneg _).trans (hdom (N + d))
  apply recoveryConstant_mul_pow_le_block_bound hrate hM
  intro k
  exact (hdom (N + (k : ℕ))).trans
    (hmono (Nat.add_le_add_left (Nat.le_of_lt k.isLt) N))

/-- A smaller exponential term is eventually at most half the leading term. -/
theorem absorb_subdominant_tail
    {V : ℕ → ℝ} {A C R r : ℝ} {d : ℕ}
    (hA : 0 < A) (hR : 0 < R) (hr : 0 ≤ r) (hrR : r < R)
    (hpre : ∀ᶠ n in atTop, A * R ^ n ≤ V (n + d) + C * r ^ n) :
    ∀ᶠ n in atTop, (A / 2) * R ^ n ≤ V (n + d) := by
  have hratio0 : 0 ≤ r / R := div_nonneg hr hR.le
  have hratio1 : r / R < 1 := (div_lt_iff₀ hR).mpr (by simpa only [one_mul] using hrR)
  have hp : Tendsto (fun n : ℕ => (r / R) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hratio0 hratio1
  have hlim : Tendsto (fun n : ℕ => C * (r / R) ^ n) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => C) atTop (𝓝 C)).mul hp
  have hsmall : ∀ᶠ n in atTop, C * (r / R) ^ n < A / 2 :=
    (tendsto_order.mp hlim).2 (A / 2) (half_pos hA)
  filter_upwards [hpre, hsmall] with n hn hs
  have hscale : (C * (r / R) ^ n) * R ^ n = C * r ^ n := by
    rw [div_pow]
    field_simp [(pow_pos hR n).ne'] <;> ring
  have htail : C * r ^ n ≤ (A / 2) * R ^ n := by
    rw [← hscale]
    exact mul_le_mul_of_nonneg_right hs.le (pow_nonneg hR.le n)
  nlinarith

/-- Inverse-row recovery remains quantitative in the presence of a bounded tail. -/
theorem finite_tail_preliminary_lower
    {d : ℕ} {rate c : Fin d → ℂ} {V : ℕ → ℝ} {E : ℕ → ℂ} {C r : ℝ}
    (hrate : Function.Injective rate) (i₀ : Fin d)
    (hmono : Monotone V) (hC : 0 ≤ C) (hr : 1 ≤ r)
    (hE : ∀ n : ℕ, ‖E n‖ ≤ C * r ^ n)
    (hdom : ∀ n : ℕ, ‖finiteExponentialSum rate c n + E n‖ ≤ V n) :
    ∀ N : ℕ, recoveryConstant rate c i₀ * ‖rate i₀‖ ^ N ≤
      V (N + d) + (C * r ^ d) * r ^ N := by
  intro N
  have hr0 : 0 ≤ r := zero_le_one.trans hr
  have hV0 : 0 ≤ V (N + d) := (norm_nonneg _).trans (hdom (N + d))
  have hM : 0 ≤ V (N + d) + C * r ^ (N + d) :=
    add_nonneg hV0 (mul_nonneg hC (pow_nonneg hr0 _))
  have hb : ∀ k : Fin d, ‖finiteExponentialSum rate c (N + (k : ℕ))‖ ≤
      V (N + d) + C * r ^ (N + d) := by
    intro k
    have hNk : N + (k : ℕ) ≤ N + d :=
      Nat.add_le_add_left (Nat.le_of_lt k.isLt) N
    calc
      ‖finiteExponentialSum rate c (N + (k : ℕ))‖ ≤
          ‖finiteExponentialSum rate c (N + (k : ℕ)) + E (N + (k : ℕ))‖ +
            ‖E (N + (k : ℕ))‖ := by
        simpa only [add_sub_cancel_right] using
          (norm_sub_le
            (finiteExponentialSum rate c (N + (k : ℕ)) + E (N + (k : ℕ)))
            (E (N + (k : ℕ))))
      _ ≤ V (N + (k : ℕ)) + C * r ^ (N + (k : ℕ)) :=
        add_le_add (hdom _) (hE _)
      _ ≤ V (N + d) + C * r ^ (N + d) :=
        add_le_add (hmono hNk)
          (mul_le_mul_of_nonneg_left (pow_right_mono₀ hr hNk) hC)
  calc
    recoveryConstant rate c i₀ * ‖rate i₀‖ ^ N ≤
        V (N + d) + C * r ^ (N + d) :=
      recoveryConstant_mul_pow_le_block_bound hrate hM hb
    _ = V (N + d) + (C * r ^ d) * r ^ N := by rw [pow_add]; ring

/-- Explicit eventual block lower bound, including a geometrically smaller error term. -/
theorem finite_tail_block_lower
    {d : ℕ} {rate c : Fin d → ℂ} {V : ℕ → ℝ} {E : ℕ → ℂ} {C r : ℝ}
    (hrate : Function.Injective rate) (i₀ : Fin d) (hc : c i₀ ≠ 0)
    (hmono : Monotone V) (hC : 0 ≤ C) (hr : 1 ≤ r) (hrR : r < ‖rate i₀‖)
    (hE : ∀ n : ℕ, ‖E n‖ ≤ C * r ^ n)
    (hdom : ∀ n : ℕ, ‖finiteExponentialSum rate c n + E n‖ ≤ V n) :
    ∃ a : ℝ, 0 < a ∧
      ∀ᶠ n in atTop, ∃ k : ℕ, k ≤ d ∧ a * ‖rate i₀‖ ^ n ≤ V (n + k) := by
  have hA : 0 < recoveryConstant rate c i₀ := recoveryConstant_pos rate c i₀ hc
  have hR : 0 < ‖rate i₀‖ := lt_of_le_of_lt (zero_le_one.trans hr) hrR
  have hpre : ∀ᶠ n in atTop, recoveryConstant rate c i₀ * ‖rate i₀‖ ^ n ≤
      V (n + d) + (C * r ^ d) * r ^ n :=
    Eventually.of_forall (finite_tail_preliminary_lower hrate i₀ hmono hC hr hE hdom)
  have hlow := absorb_subdominant_tail hA hR (zero_le_one.trans hr) hrR hpre
  refine ⟨recoveryConstant rate c i₀ / 2, half_pos hA, ?_⟩
  filter_upwards [hlow] with n hn
  exact ⟨d, le_rfl, hn⟩

/--
The complete ordinary root-limit implication from a finite dominant block,
an explicit subdominant tail estimate, and a matching geometric upper bound.
-/
theorem root_tendsto_of_finite_dominant_tail
    {d : ℕ} {rate c : Fin d → ℂ} {V : ℕ → ℝ} {E : ℕ → ℂ} {C D r : ℝ}
    (hrate : Function.Injective rate) (i₀ : Fin d) (hc : c i₀ ≠ 0)
    (hmono : Monotone V) (hC : 0 ≤ C) (hD : 0 < D)
    (hr : 1 ≤ r) (hrR : r < ‖rate i₀‖)
    (hE : ∀ n : ℕ, ‖E n‖ ≤ C * r ^ n)
    (hdom : ∀ n : ℕ, ‖finiteExponentialSum rate c n + E n‖ ≤ V n)
    (hupper : ∀ᶠ n in atTop, V n ≤ D * ‖rate i₀‖ ^ n) :
    Tendsto (rootScale V) atTop (𝓝 ‖rate i₀‖) := by
  obtain ⟨a, ha, hblock⟩ :=
    finite_tail_block_lower hrate i₀ hc hmono hC hr hrR hE hdom
  have hR : 0 < ‖rate i₀‖ := lt_of_le_of_lt (zero_le_one.trans hr) hrR
  exact root_tendsto_of_monotone_block_bounds hR ha hD hmono hblock hupper

end RH_HilbertLimit
