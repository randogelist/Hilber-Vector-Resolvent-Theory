import Mathlib.RingTheory.Polynomial.Bernstein
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Finite Bernstein algebra for an actual real moment sequence

Candidate source for the user's native Lean 4.33.0 compiler.
No Lean process was run while preparing this file.

The exported definitions are the literal finite binomial formulas from
the B-Tier paper.  Polynomial linearity is used only to prove their
finite identities; no positivity or analytic realization is assumed.

API sources inspected at mathlib tag `v4.33.0`:
* `Mathlib/RingTheory/Polynomial/Bernstein.lean`
* `Mathlib/Algebra/Polynomial/Coeff.lean`
* `Mathlib/Data/Nat/Choose/Basic.lean`
The tag's `lean-toolchain` is `leanprover/lean4:v4.33.0`.
-/

noncomputable section

open scoped BigOperators

namespace RH_HilbertLimit

/-- The literal binomial-difference weight.  Its definition needs no sign premise. -/
def bernsteinWeight (u : ℕ → ℝ) (N j : ℕ) : ℝ :=
  (Nat.choose N j : ℝ) *
    ∑ r ∈ Finset.range (N - j + 1),
      (-1 : ℝ) ^ r * (Nat.choose (N - j) r : ℝ) * u (j + r)

/-- The total variation of one finite row. -/
def rowVariation (u : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (N + 1), |bernsteinWeight u N j|

/-- The polynomial functional prescribed by the real moments. -/
def momentFunctional (u : ℕ → ℝ) : Polynomial ℝ →ₗ[ℝ] ℝ :=
  Polynomial.lsum fun n => u n • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)

@[simp] theorem momentFunctional_monomial (u : ℕ → ℝ) (n : ℕ) (c : ℝ) :
    momentFunctional u (Polynomial.monomial n c) = c * u n := by
  change (Polynomial.monomial n c).sum (fun k a => u k * a) = c * u n
  simp [mul_comm]

@[simp] theorem momentFunctional_one (u : ℕ → ℝ) :
    momentFunctional u (1 : Polynomial ℝ) = u 0 := by
  simpa using momentFunctional_monomial u 0 1

theorem momentFunctional_C_mul (u : ℕ → ℝ) (c : ℝ) (p : Polynomial ℝ) :
    momentFunctional u (Polynomial.C c * p) = c * momentFunctional u p := by
  simpa only [Polynomial.smul_eq_C_mul, smul_eq_mul] using
    (momentFunctional u).map_smul c p

/-- Expanding the polynomial Bernstein basis gives the exact finite formula. -/
theorem bernsteinPolynomial_expansion (N j : ℕ) :
    bernsteinPolynomial ℝ N j =
      ∑ r ∈ Finset.range (N - j + 1),
        Polynomial.monomial (j + r)
          ((Nat.choose N j : ℝ) * (-1 : ℝ) ^ r *
            (Nat.choose (N - j) r : ℝ)) := by
  have hbin : (1 - Polynomial.X : Polynomial ℝ) ^ (N - j) =
      ∑ r ∈ Finset.range (N - j + 1),
        Polynomial.monomial r
          ((-1 : ℝ) ^ r * (Nat.choose (N - j) r : ℝ)) := by
    have hb : (1 - Polynomial.X : Polynomial ℝ) =
        Polynomial.C (-1 : ℝ) * Polynomial.X + 1 := by
      simp only [map_neg, map_one]
      ring
    rw [hb, add_pow]
    apply Finset.sum_congr rfl
    intro r hr
    simp only [one_pow, mul_one, mul_pow,
      ← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, map_natCast]
    ring
  unfold bernsteinPolynomial
  rw [hbin, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  simp only [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow,
    map_natCast, pow_add]
  ring

/-- The polynomial model is proved equal to the exported binomial formula. -/
theorem momentFunctional_bernsteinPolynomial (u : ℕ → ℝ) (N j : ℕ) :
    momentFunctional u (bernsteinPolynomial ℝ N j) = bernsteinWeight u N j := by
  rw [bernsteinPolynomial_expansion]
  simp only [map_sum, momentFunctional_monomial, bernsteinWeight, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  ring

/-- Power-sum calibration transfers to each polynomial.
There is no constant-term series: the additional factor `q i` makes every
monomial one of the supplied positive-order power sums. -/
theorem polynomial_moment_hasSum {ι : Type*} (u : ℕ → ℝ) (q : ι → ℂ)
    (hpower : ∀ n : ℕ, HasSum (fun i => q i ^ (n + 1)) (u n : ℂ))
    (p : Polynomial ℝ) :
    HasSum (fun i => q i * Polynomial.eval₂ (algebraMap ℝ ℂ) (q i) p)
      (momentFunctional u p : ℂ) := by
  induction p using Polynomial.induction_on' with
  | add p s hp hs =>
      simpa only [Polynomial.eval₂_add, mul_add, map_add,
        Complex.ofReal_add] using hp.add hs
  | monomial n c =>
      have hm := (hpower n).mul_left (c : ℂ)
      have hfun : (fun i => (c : ℂ) * q i ^ (n + 1)) =
          (fun i => q i * Polynomial.eval₂ (algebraMap ℝ ℂ) (q i)
            (Polynomial.monomial n c)) := by
        funext i
        simp only [Polynomial.eval₂_monomial]
        change (c : ℂ) * q i ^ (n + 1) = q i * ((c : ℂ) * q i ^ n)
        rw [pow_succ]
        ring
      rw [hfun] at hm
      simpa only [momentFunctional_monomial, Complex.ofReal_mul] using hm

/-- Exact spectral calibration for the literal finite Bernstein weights.
This follows from finite polynomial linearity and the supplied power sums;
it does not assert that such spectral data exist for actual xi. -/
theorem bernsteinWeight_hasSum {ι : Type*} (u : ℕ → ℝ) (q : ι → ℂ)
    (hpower : ∀ n : ℕ, HasSum (fun i => q i ^ (n + 1)) (u n : ℂ))
    (N j : ℕ) :
    HasSum (fun i => (Nat.choose N j : ℂ) * q i ^ (j + 1) *
      (1 - q i) ^ (N - j)) (bernsteinWeight u N j : ℂ) := by
  have hp := polynomial_moment_hasSum u q hpower (bernsteinPolynomial ℝ N j)
  have hfun :
      (fun i => q i * Polynomial.eval₂ (algebraMap ℝ ℂ) (q i)
        (bernsteinPolynomial ℝ N j)) =
      (fun i => (Nat.choose N j : ℂ) * q i ^ (j + 1) *
        (1 - q i) ^ (N - j)) := by
    funext i
    simp only [bernsteinPolynomial, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
      Polynomial.eval₂_natCast, Polynomial.eval₂_X, Polynomial.eval₂_sub,
      Polynomial.eval₂_one, pow_succ]
    ring
  rw [hfun, momentFunctional_bernsteinPolynomial] at hp
  exact hp

@[simp] theorem bernsteinWeight_zero_zero (u : ℕ → ℝ) :
    bernsteinWeight u 0 0 = u 0 := by
  simp [bernsteinWeight]

@[simp] theorem rowVariation_zero (u : ℕ → ℝ) :
    rowVariation u 0 = |u 0| := by
  simp [rowVariation]

/-- Partition of unity gives the exact row mass, without a positivity hypothesis. -/
theorem sum_bernsteinWeight_eq (u : ℕ → ℝ) (N : ℕ) :
    (∑ j ∈ Finset.range (N + 1), bernsteinWeight u N j) = u 0 := by
  simpa only [map_sum, momentFunctional_bernsteinPolynomial,
    momentFunctional_one] using
    congrArg (momentFunctional u) (bernsteinPolynomial.sum ℝ N)

theorem sum_bernsteinWeight_eq_one (u : ℕ → ℝ) (hzero : u 0 = 1) (N : ℕ) :
    (∑ j ∈ Finset.range (N + 1), bernsteinWeight u N j) = 1 := by
  rw [sum_bernsteinWeight_eq, hzero]

theorem rowVariation_nonneg (u : ℕ → ℝ) (N : ℕ) :
    0 ≤ rowVariation u N := by
  exact Finset.sum_nonneg fun j hj => abs_nonneg _

theorem one_le_rowVariation (u : ℕ → ℝ) (hzero : u 0 = 1) (N : ℕ) :
    1 ≤ rowVariation u N := by
  calc
    1 = ∑ j ∈ Finset.range (N + 1), bernsteinWeight u N j :=
      (sum_bernsteinWeight_eq_one u hzero N).symm
    _ ≤ ∑ j ∈ Finset.range (N + 1), |bernsteinWeight u N j| :=
      Finset.sum_le_sum fun j hj => le_abs_self _
    _ = rowVariation u N := rfl

/-- For a row of mass one, variation one is exactly termwise nonnegativity. -/
theorem rowVariation_eq_one_iff (u : ℕ → ℝ) (hzero : u 0 = 1) (N : ℕ) :
    rowVariation u N = 1 ↔
      ∀ j ∈ Finset.range (N + 1), 0 ≤ bernsteinWeight u N j := by
  constructor
  · intro hvariation
    have hsum :
        (∑ j ∈ Finset.range (N + 1),
          (|bernsteinWeight u N j| - bernsteinWeight u N j)) = 0 := by
      rw [Finset.sum_sub_distrib, sum_bernsteinWeight_eq_one u hzero N]
      change rowVariation u N - 1 = 0
      rw [hvariation]
      ring
    have hterms :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun j (_hj : j ∈ Finset.range (N + 1)) =>
          sub_nonneg.mpr (le_abs_self (bernsteinWeight u N j)))).mp hsum
    intro j hj
    exact abs_eq_self.mp (sub_eq_zero.mp (hterms j hj))
  · intro hnonneg
    calc
      rowVariation u N =
          ∑ j ∈ Finset.range (N + 1), bernsteinWeight u N j := by
        apply Finset.sum_congr rfl
        intro j hj
        exact abs_of_nonneg (hnonneg j hj)
      _ = 1 := sum_bernsteinWeight_eq_one u hzero N

private theorem bernsteinPolynomial_coarsening_mul (N j : ℕ) (hj : j ≤ N) :
    Polynomial.C ((N + 1 : ℕ) : ℝ) * bernsteinPolynomial ℝ N j =
      Polynomial.C ((N + 1 - j : ℕ) : ℝ) *
          bernsteinPolynomial ℝ (N + 1) j +
        Polynomial.C ((j + 1 : ℕ) : ℝ) *
          bernsteinPolynomial ℝ (N + 1) (j + 1) := by
  have hleftNat :
      (N + 1 - j) * Nat.choose (N + 1) j = (N + 1) * Nat.choose N j := by
    simpa only [Nat.mul_comm] using (Nat.choose_mul_succ_eq N j).symm
  have hrightNat :
      (j + 1) * Nat.choose (N + 1) (j + 1) = (N + 1) * Nat.choose N j := by
    simpa only [Nat.mul_comm] using (Nat.add_one_mul_choose_eq N j).symm
  have hleft :
      (((N + 1 - j : ℕ) : Polynomial ℝ) *
        (Nat.choose (N + 1) j : Polynomial ℝ)) =
      ((N + 1 : ℕ) : Polynomial ℝ) * (Nat.choose N j : Polynomial ℝ) := by
    simpa only [Nat.cast_mul] using
      congrArg (fun n : ℕ => (n : Polynomial ℝ)) hleftNat
  have hright :
      (((j + 1 : ℕ) : Polynomial ℝ) *
        (Nat.choose (N + 1) (j + 1) : Polynomial ℝ)) =
      ((N + 1 : ℕ) : Polynomial ℝ) * (Nat.choose N j : Polynomial ℝ) := by
    simpa only [Nat.cast_mul] using
      congrArg (fun n : ℕ => (n : Polynomial ℝ)) hrightNat
  have hsub : N + 1 - j = N - j + 1 := by omega
  have hsub' : N + 1 - (j + 1) = N - j := by omega
  rw [hsub] at hleft
  simp only [bernsteinPolynomial, map_natCast, hsub, hsub', pow_succ]
  linear_combination
    -(Polynomial.X ^ j * (1 - Polynomial.X) ^ (N - j) *
      (1 - Polynomial.X)) * hleft -
    (Polynomial.X ^ j * Polynomial.X * (1 - Polynomial.X) ^ (N - j)) * hright

/-- Exact degree coarsening. The coefficients are nonnegative for `j ≤ N`. -/
theorem bernsteinWeight_coarsening (u : ℕ → ℝ) (N j : ℕ) (hj : j ≤ N) :
    bernsteinWeight u N j =
      (((N : ℝ) + 1 - j) / ((N : ℝ) + 1)) * bernsteinWeight u (N + 1) j +
      (((j : ℝ) + 1) / ((N : ℝ) + 1)) *
        bernsteinWeight u (N + 1) (j + 1) := by
  have h := congrArg (momentFunctional u)
    (bernsteinPolynomial_coarsening_mul N j hj)
  simp only [map_add, momentFunctional_C_mul,
    momentFunctional_bernsteinPolynomial] at h
  have hj' : j ≤ N + 1 := by omega
  simp only [Nat.cast_sub hj', Nat.cast_add, Nat.cast_one] at h
  have hden : (N : ℝ) + 1 ≠ 0 := by positivity
  calc
    bernsteinWeight u N j =
        ((((N : ℝ) + 1 - j) * bernsteinWeight u (N + 1) j +
          ((j : ℝ) + 1) * bernsteinWeight u (N + 1) (j + 1)) /
          ((N : ℝ) + 1)) := by
      apply (eq_div_iff hden).2
      simpa only [mul_comm] using h
    _ = _ := by ring

private theorem sum_coarsening_coefficients (f : ℕ → ℝ) (N : ℕ) :
    (∑ j ∈ Finset.range (N + 1),
      ((((N : ℝ) + 1 - j) / ((N : ℝ) + 1)) * f j +
        (((j : ℝ) + 1) / ((N : ℝ) + 1)) * f (j + 1))) =
      ∑ j ∈ Finset.range (N + 2), f j := by
  let A : ℕ → ℝ := fun j => (((N : ℝ) + 1 - j) / ((N : ℝ) + 1)) * f j
  let B : ℕ → ℝ := fun j => ((j : ℝ) / ((N : ℝ) + 1)) * f j
  have hA : (∑ j ∈ Finset.range (N + 1), A j) =
      ∑ j ∈ Finset.range (N + 2), A j := by
    rw [show N + 2 = (N + 1) + 1 by omega, Finset.sum_range_succ A (N + 1)]
    simp [A]
  have hB : (∑ j ∈ Finset.range (N + 1), B (j + 1)) =
      ∑ j ∈ Finset.range (N + 2), B j := by
    rw [show N + 2 = (N + 1) + 1 by omega, Finset.sum_range_succ' B (N + 1)]
    simp [B]
  have hden : (N : ℝ) + 1 ≠ 0 := by positivity
  calc
    _ = (∑ j ∈ Finset.range (N + 1), A j) +
        ∑ j ∈ Finset.range (N + 1), B (j + 1) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [A, B, Nat.cast_add, Nat.cast_one]
    _ = (∑ j ∈ Finset.range (N + 2), A j) +
        ∑ j ∈ Finset.range (N + 2), B j := by rw [hA, hB]
    _ = ∑ j ∈ Finset.range (N + 2), (A j + B j) := by
      rw [Finset.sum_add_distrib]
    _ = ∑ j ∈ Finset.range (N + 2), f j := by
      apply Finset.sum_congr rfl
      intro j hj
      dsimp [A, B]
      field_simp [hden] <;> ring

/-- Total variation cannot decrease when the degree increases. -/
theorem rowVariation_le_succ (u : ℕ → ℝ) (N : ℕ) :
    rowVariation u N ≤ rowVariation u (N + 1) := by
  unfold rowVariation
  calc
    _ ≤ ∑ j ∈ Finset.range (N + 1),
        ((((N : ℝ) + 1 - j) / ((N : ℝ) + 1)) *
            |bernsteinWeight u (N + 1) j| +
          (((j : ℝ) + 1) / ((N : ℝ) + 1)) *
            |bernsteinWeight u (N + 1) (j + 1)|) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjN : j ≤ N := by
        have := Finset.mem_range.mp hj
        omega
      have hjR : (j : ℝ) ≤ N := Nat.cast_le.mpr hjN
      have ha : 0 ≤ ((N : ℝ) + 1 - j) / ((N : ℝ) + 1) :=
        div_nonneg (by linarith) (by positivity)
      have hb : 0 ≤ ((j : ℝ) + 1) / ((N : ℝ) + 1) := by positivity
      rw [bernsteinWeight_coarsening u N j hjN]
      calc
        _ ≤ |(((N : ℝ) + 1 - j) / ((N : ℝ) + 1)) *
              bernsteinWeight u (N + 1) j| +
            |(((j : ℝ) + 1) / ((N : ℝ) + 1)) *
              bernsteinWeight u (N + 1) (j + 1)| := abs_add_le _ _
        _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ = _ := by
      simpa only [Nat.add_assoc] using
        sum_coarsening_coefficients (fun j => |bernsteinWeight u (N + 1) j|) N

theorem rowVariation_monotone (u : ℕ → ℝ) : Monotone (rowVariation u) := by
  exact monotone_nat_of_le_succ (rowVariation_le_succ u)

/-- The sequence-wide variation-one statement is the full finite-row sign hierarchy. -/
theorem all_rowVariation_eq_one_iff (u : ℕ → ℝ) (hzero : u 0 = 1) :
    (∀ N, rowVariation u N = 1) ↔
      ∀ N j, j ≤ N → 0 ≤ bernsteinWeight u N j := by
  constructor
  · intro h N j hj
    exact (rowVariation_eq_one_iff u hzero N).mp (h N) j
      (Finset.mem_range.mpr (by omega))
  · intro h N
    apply (rowVariation_eq_one_iff u hzero N).mpr
    intro j hj
    exact h N j (by have := Finset.mem_range.mp hj; omega)

end RH_HilbertLimit
