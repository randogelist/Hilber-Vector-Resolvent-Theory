import RH_HilbertLimit.Main

/-!
# Uniform growth steps and the finite-certificate boundary

This module proves a new scalar implication and applies it to the literal
actual-xi variation sequence.  A single natural-number parameter occurs in
the resulting criterion, but its admissibility still quantifies over every
order.  No terminating checker for that universal predicate is supplied.

In particular, these declarations do NOT prove finite-checker existence iff
RH.  The inherited actual spectral calibration and dominant extraction
remain explicit hypotheses.  No new axiom, assumed checker soundness, or
assumed checker completeness is introduced.

Prepared without running Lean, Lake, or CI.  The source must be compiled
and axiom-audited on the user's native Windows Lean 4.33.0 target.
-/

set_option autoImplicit false
noncomputable section
open scoped Topology BigOperators
open Filter

namespace RH_HilbertLimit

/-- A bound on every successive increment.  The number `K` is finite raw
data, but this predicate is an infinite mathematical obligation, not a Bool
checker and not a finite certificate. -/
def NaturalGrowthStep (V : ℕ → ℝ) (K : ℕ) : Prop :=
  ∀ n : ℕ, ((n : ℝ) + 1) * (V (n + 1) - V n) ≤ (K : ℝ) * V n

/-- An eventual exponential step controls the whole sequence after a finite
prefix has been absorbed into one positive constant. -/
theorem exp_bound_of_eventual_mul_step {V : ℕ → ℝ} {ε : ℝ}
    (hε : 0 ≤ ε)
    (hstep : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      V (n + 1) ≤ Real.exp ε * V n) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      V n ≤ C * Real.exp (ε * (n : ℝ)) := by
  obtain ⟨N, hN⟩ := hstep
  let C : ℝ := max 1 (∑ j ∈ Finset.range (N + 1), |V j|)
  have hC1 : 1 ≤ C := le_max_left _ _
  have hCpos : 0 < C := zero_lt_one.trans_le hC1
  have hprefix : ∀ n : ℕ, n ≤ N →
      V n ≤ C * Real.exp (ε * (n : ℝ)) := by
    intro n hn
    have hsum : |V n| ≤ ∑ j ∈ Finset.range (N + 1), |V j| :=
      Finset.single_le_sum (fun j _ => abs_nonneg (V j))
        (Finset.mem_range.mpr (by omega))
    have hvC : V n ≤ C :=
      (le_abs_self (V n)).trans (hsum.trans (le_max_right _ _))
    have he : 1 ≤ Real.exp (ε * (n : ℝ)) :=
      Real.one_le_exp_iff.mpr (mul_nonneg hε (Nat.cast_nonneg n))
    exact hvC.trans (by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left he hCpos.le)
  refine ⟨C, hCpos, ?_⟩
  intro n
  induction n with
  | zero => exact hprefix 0 (Nat.zero_le N)
  | succ n ih =>
      by_cases hn : n < N
      · exact hprefix (n + 1) (by omega)
      · have hn' : N ≤ n := Nat.le_of_not_gt hn
        calc
          V (n + 1) ≤ Real.exp ε * V n := hN n hn'
          _ ≤ Real.exp ε * (C * Real.exp (ε * (n : ℝ))) :=
            mul_le_mul_of_nonneg_left ih (Real.exp_nonneg ε)
          _ = C * Real.exp (ε * ((n + 1 : ℕ) : ℝ)) := by
            rw [Nat.cast_add, Nat.cast_one, mul_add, mul_one, Real.exp_add]
            ring

/-- Eventual multiplicative growth at every positive exponential rate
implies the exact global `Subexponential` predicate of the passed chain. -/
theorem subexponential_of_eventual_mul_steps {V : ℕ → ℝ}
    (hstep : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      V (n + 1) ≤ Real.exp ε * V n) :
    Subexponential V := by
  intro ε hε
  exact exp_bound_of_eventual_mul_step hε.le (hstep ε hε)

/-- A single all-order inverse-linear relative-increment bound supplies
every positive exponential rate.  No desired limit is assumed. -/
theorem subexponential_of_natural_growth_step {V : ℕ → ℝ}
    (hV : ∀ n : ℕ, 0 ≤ V n) {K : ℕ}
    (hstep : NaturalGrowthStep V K) :
    Subexponential V := by
  apply subexponential_of_eventual_mul_steps
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt ((K : ℝ) / ε)
  refine ⟨N, ?_⟩
  intro n hn
  have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hKN : (K : ℝ) < (N : ℝ) * ε := (div_lt_iff₀ hε).mp hN
  have hKn : (K : ℝ) ≤ ε * ((n : ℝ) + 1) := by
    calc
      (K : ℝ) ≤ (N : ℝ) * ε := hKN.le
      _ ≤ (n : ℝ) * ε := mul_le_mul_of_nonneg_right hNn hε.le
      _ ≤ (n : ℝ) * ε + ε := le_add_of_nonneg_right hε.le
      _ = ε * ((n : ℝ) + 1) := by ring
  have ha : 0 < (n : ℝ) + 1 := by positivity
  have hprod : ((n : ℝ) + 1) * (V (n + 1) - V n) ≤
      ((n : ℝ) + 1) * (ε * V n) := by
    calc
      ((n : ℝ) + 1) * (V (n + 1) - V n) ≤ (K : ℝ) * V n := hstep n
      _ ≤ (ε * ((n : ℝ) + 1)) * V n :=
        mul_le_mul_of_nonneg_right hKn (hV n)
      _ = ((n : ℝ) + 1) * (ε * V n) := by ring
  have hdiff : V (n + 1) - V n ≤ ε * V n :=
    le_of_mul_le_mul_left hprod ha
  have hsum : V (n + 1) ≤ (ε + 1) * V n := by nlinarith
  exact hsum.trans
    (mul_le_mul_of_nonneg_right (Real.add_one_le_exp ε) (hV n))

/-- Under RH and the explicit calibration, the actual sequence has zero
increments.  This establishes admissibility of `K = 0` only for the
universal mathematical predicate above. -/
theorem actual_growth_step_zero_of_nativeRH {ι : Type*}
    (D : ActualSpectralCalibration ι) (hRH : _root_.RiemannHypothesis) :
    NaturalGrowthStep actualVariation 0 := by
  intro n
  rw [D.variation_eq_one_of_nativeRH hRH (n + 1),
    D.variation_eq_one_of_nativeRH hRH n]
  simp

/-- The actual-xi growth-step criterion, with all inherited analytic
hypotheses preserved.  Its `∀ n` has not been reduced to a finite check. -/
theorem actual_exists_natural_growth_step_iff_nativeRH_of_analytic_inputs
    {ι : Type*} (D : ActualSpectralCalibration ι)
    (hExtract : DominantExtraction D) :
    (∃ K : ℕ, NaturalGrowthStep actualVariation K) ↔
      _root_.RiemannHypothesis := by
  constructor
  · rintro ⟨K, hK⟩
    apply (actual_subexponential_iff_nativeRH_of_analytic_inputs D hExtract).mp
    exact subexponential_of_natural_growth_step
      (fun n => (zero_le_one : (0 : ℝ) ≤ 1).trans (D.variation_one_le n)) hK
  · intro hRH
    exact ⟨0, actual_growth_step_zero_of_nativeRH D hRH⟩

/-- Even the integer bound `B = 1` is available under RH, but verifying its
uniform bound is still an all-order obligation, not finite computation. -/
theorem actual_exists_natural_bound_iff_nativeRH_of_analytic_inputs
    {ι : Type*} (D : ActualSpectralCalibration ι)
    (hExtract : DominantExtraction D) :
    (∃ B : ℕ, ∀ n : ℕ, actualVariation n ≤ (B : ℝ)) ↔
      _root_.RiemannHypothesis := by
  constructor
  · rintro ⟨B, hB⟩
    exact (actual_bounded_variation_iff_nativeRH_of_analytic_inputs D hExtract).mp
      ⟨(B : ℝ), hB⟩
  · intro hRH
    refine ⟨1, ?_⟩
    intro n
    simpa only [Nat.cast_one] using (D.variation_eq_one_of_nativeRH hRH n).le

end RH_HilbertLimit
