import RH_HilbertLimit.GrowthStep

/-!
# Eventual inverse-linear growth steps

A nonnegative sequence with the indicated growth-step bound after a finite
cutoff is subexponential. The initial finite prefix is absorbed into the
constant supplied by `exp_bound_of_eventual_mul_step`.

`EventualNaturalGrowthStep` remains an infinite mathematical predicate. The
natural parameters alone are not a terminating certificate for that predicate.
No checker soundness, checker completeness, or RH assumption is introduced.

Prepared without running Lean, Lake, a native compiler, or CI. Native
compilation and axiom audit remain required.
-/

set_option autoImplicit false
noncomputable section

namespace RH_HilbertLimit

/-- The inverse-linear relative-increment bound starts at cutoff `N`.
The parameter order is the sequence, then the cutoff, then the natural bound. -/
def EventualNaturalGrowthStep (V : ℕ → ℝ) (N K : ℕ) : Prop :=
  ∀ n : ℕ, N ≤ n →
    ((n : ℝ) + 1) * (V (n + 1) - V n) ≤ (K : ℝ) * V n

/-- A finite exceptional prefix does not affect subexponential upper growth. -/
theorem subexponential_of_eventual_natural_growth_step {V : ℕ → ℝ}
    (hV : ∀ n : ℕ, 0 ≤ V n) {N K : ℕ}
    (hstep : EventualNaturalGrowthStep V N K) :
    Subexponential V := by
  intro ε hε
  apply exp_bound_of_eventual_mul_step hε.le
  obtain ⟨M, hM⟩ := exists_nat_gt ((K : ℝ) / ε)
  refine ⟨max N M, ?_⟩
  intro n hn
  have hNn : N ≤ n := (le_max_left N M).trans hn
  have hMn : M ≤ n := (le_max_right N M).trans hn
  have hMnR : (M : ℝ) ≤ (n : ℝ) := by exact_mod_cast hMn
  have hKM : (K : ℝ) < (M : ℝ) * ε := (div_lt_iff₀ hε).mp hM
  have hKn : (K : ℝ) ≤ ε * ((n : ℝ) + 1) := by
    calc
      (K : ℝ) ≤ (M : ℝ) * ε := hKM.le
      _ ≤ (n : ℝ) * ε := mul_le_mul_of_nonneg_right hMnR hε.le
      _ ≤ (n : ℝ) * ε + ε := le_add_of_nonneg_right hε.le
      _ = ε * ((n : ℝ) + 1) := by ring
  have ha : 0 < (n : ℝ) + 1 := by positivity
  have hprod : ((n : ℝ) + 1) * (V (n + 1) - V n) ≤
      ((n : ℝ) + 1) * (ε * V n) := by
    calc
      ((n : ℝ) + 1) * (V (n + 1) - V n) ≤ (K : ℝ) * V n := hstep n hNn
      _ ≤ (ε * ((n : ℝ) + 1)) * V n :=
        mul_le_mul_of_nonneg_right hKn (hV n)
      _ = ((n : ℝ) + 1) * (ε * V n) := by ring
  have hdiff : V (n + 1) - V n ≤ ε * V n :=
    le_of_mul_le_mul_left hprod ha
  have hsum : V (n + 1) ≤ (ε + 1) * V n := by nlinarith
  exact hsum.trans
    (mul_le_mul_of_nonneg_right (Real.add_one_le_exp ε) (hV n))

/-- Existential cutoff and bound form of the same implication. -/
theorem subexponential_of_exists_eventual_natural_growth_step {V : ℕ → ℝ}
    (hV : ∀ n : ℕ, 0 ≤ V n)
    (hstep : ∃ N K : ℕ, EventualNaturalGrowthStep V N K) :
    Subexponential V := by
  obtain ⟨N, K, hNK⟩ := hstep
  exact subexponential_of_eventual_natural_growth_step hV hNK

end RH_HilbertLimit
