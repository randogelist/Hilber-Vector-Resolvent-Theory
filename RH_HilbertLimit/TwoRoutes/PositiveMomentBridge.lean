import RH_HilbertLimit.Bernstein

/-!
# Positive finite Bernstein approximants for the direct second route

Prepared without running Lean, Lake, or a compiler.

This file supplies the finite positive-functional layer behind the Hausdorff
construction. It deliberately does not claim that the limiting measure or
the all-order actual-Widder integral identification has already been built.
No Riemann-hypothesis theorem or spectral-closure theorem is used here.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace RH_HilbertLimit.TwoRoutes

/-- The exact all-row sign condition needed by Hausdorff's moment theorem. -/
def BernsteinPositive (u : ℕ → ℝ) : Prop :=
  ∀ N j : ℕ, j ≤ N → 0 ≤ bernsteinWeight u N j

/-- Evaluation at the finite Bernstein grid, with the literal row weights.
At degree zero the sole grid point is zero, using real division's value at zero. -/
def bernsteinAverage (u : ℕ → ℝ) (N : ℕ) (f : ℝ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range (N + 1), bernsteinWeight u N j * f ((j : ℝ) / N)

theorem bernsteinGrid_mem_Icc (N j : ℕ) (hj : j ≤ N) :
    (j : ℝ) / N ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases hN : N = 0
  · subst N
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    subst j
    simp
  · have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
    refine ⟨div_nonneg (Nat.cast_nonneg j) (Nat.cast_nonneg N), ?_⟩
    apply (div_le_iff₀ hNpos).mpr
    simpa only [one_mul] using (Nat.cast_le.mpr hj : (j : ℝ) ≤ N)

theorem bernsteinAverage_const (u : ℕ → ℝ) (hzero : u 0 = 1)
    (N : ℕ) (c : ℝ) :
    bernsteinAverage u N (fun _ => c) = c := by
  unfold bernsteinAverage
  rw [← Finset.sum_mul, sum_bernsteinWeight_eq_one u hzero N, one_mul]

theorem bernsteinAverage_add (u : ℕ → ℝ) (N : ℕ) (f g : ℝ → ℝ) :
    bernsteinAverage u N (fun q => f q + g q) =
      bernsteinAverage u N f + bernsteinAverage u N g := by
  simp only [bernsteinAverage, mul_add, Finset.sum_add_distrib]

theorem bernsteinAverage_smul (u : ℕ → ℝ) (N : ℕ) (c : ℝ) (f : ℝ → ℝ) :
    bernsteinAverage u N (fun q => c * f q) = c * bernsteinAverage u N f := by
  unfold bernsteinAverage
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem bernsteinAverage_nonneg (u : ℕ → ℝ) (hpos : BernsteinPositive u)
    (N : ℕ) (f : ℝ → ℝ)
    (hf : ∀ q ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f q) :
    0 ≤ bernsteinAverage u N f := by
  apply Finset.sum_nonneg
  intro j hj
  have hjN : j ≤ N := by
    have hj' := Finset.mem_range.mp hj
    omega
  exact mul_nonneg (hpos N j hjN)
    (hf _ (bernsteinGrid_mem_Icc N j hjN))

theorem bernsteinAverage_mono (u : ℕ → ℝ) (hpos : BernsteinPositive u)
    (N : ℕ) (f g : ℝ → ℝ)
    (hfg : ∀ q ∈ Set.Icc (0 : ℝ) 1, f q ≤ g q) :
    bernsteinAverage u N f ≤ bernsteinAverage u N g := by
  apply Finset.sum_le_sum
  intro j hj
  have hjN : j ≤ N := by
    have hj' := Finset.mem_range.mp hj
    omega
  exact mul_le_mul_of_nonneg_left
    (hfg _ (bernsteinGrid_mem_Icc N j hjN)) (hpos N j hjN)

theorem bernsteinAverage_bounds (u : ℕ → ℝ) (hzero : u 0 = 1)
    (hpos : BernsteinPositive u) (N : ℕ) (f : ℝ → ℝ) (L U : ℝ)
    (hf : ∀ q ∈ Set.Icc (0 : ℝ) 1, L ≤ f q ∧ f q ≤ U) :
    L ≤ bernsteinAverage u N f ∧ bernsteinAverage u N f ≤ U := by
  constructor
  · calc
      L = bernsteinAverage u N (fun _ => L) :=
        (bernsteinAverage_const u hzero N L).symm
      _ ≤ bernsteinAverage u N f :=
        bernsteinAverage_mono u hpos N _ _ (fun q hq => (hf q hq).1)
  · calc
      bernsteinAverage u N f ≤ bernsteinAverage u N (fun _ => U) :=
        bernsteinAverage_mono u hpos N _ _ (fun q hq => (hf q hq).2)
      _ = U := bernsteinAverage_const u hzero N U

theorem bernsteinAverage_abs_le (u : ℕ → ℝ) (hzero : u 0 = 1)
    (hpos : BernsteinPositive u) (N : ℕ) (f : ℝ → ℝ) (M : ℝ)
    (hf : ∀ q ∈ Set.Icc (0 : ℝ) 1, |f q| ≤ M) :
    |bernsteinAverage u N f| ≤ M := by
  apply abs_le.mpr
  exact bernsteinAverage_bounds u hzero hpos N f (-M) M
    (fun q hq => abs_le.mp (hf q hq))

/-- Positivity on every nonnegative combination of one Bernstein basis.
This is a finite polynomial statement, before any continuous extension. -/
theorem momentFunctional_nonneg_bernstein_combination
    (u : ℕ → ℝ) (hpos : BernsteinPositive u) (N : ℕ) (c : ℕ → ℝ)
    (hc : ∀ j : ℕ, j ≤ N → 0 ≤ c j) :
    0 ≤ momentFunctional u
      (∑ j ∈ Finset.range (N + 1), Polynomial.C (c j) * bernsteinPolynomial ℝ N j) := by
  simp only [map_sum, momentFunctional_C_mul, momentFunctional_bernsteinPolynomial]
  apply Finset.sum_nonneg
  intro j hj
  have hjN : j ≤ N := by
    have hj' := Finset.mem_range.mp hj
    omega
  exact mul_nonneg (hc j hjN) (hpos N j hjN)

/-- The normalized Widder spectral multiplier. -/
def kernelMultiplier (t : ℝ) : ℝ := 4 * t / (1 + t) ^ 2

theorem kernelMultiplier_nonneg {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ kernelMultiplier t := by
  exact div_nonneg (mul_nonneg (by positivity) ht) (sq_nonneg _)

theorem kernelMultiplier_le_one {t : ℝ} (ht : 0 ≤ t) :
    kernelMultiplier t ≤ 1 := by
  have hden : (0 : ℝ) < (1 + t) ^ 2 := by positivity
  apply (div_le_iff₀ hden).mpr
  nlinarith [sq_nonneg (1 - t)]

/-- The factor multiplying the kernel powers in the normalized measure model. -/
def kernelWeight (κ a q : ℝ) : ℝ := 4 * κ * a / (1 + κ * a * q) ^ 2

theorem kernelWeight_nonneg {κ a q : ℝ} (hκ : 0 < κ) (ha : 0 < a) :
    0 ≤ kernelWeight κ a q := by
  exact div_nonneg (by positivity) (sq_nonneg _)

theorem kernelMultiplier_pow_bounds {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    0 ≤ kernelMultiplier t ^ n ∧ kernelMultiplier t ^ n ≤ 1 := by
  refine ⟨pow_nonneg (kernelMultiplier_nonneg ht) n, ?_⟩
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      calc
        kernelMultiplier t ^ n * kernelMultiplier t ≤ 1 * kernelMultiplier t :=
          mul_le_mul_of_nonneg_right ih (kernelMultiplier_nonneg ht)
        _ ≤ 1 := by simpa only [one_mul] using kernelMultiplier_le_one ht

/-- Every finite Bernstein approximant already obeys the same contraction
bound. Passage to an actual representing measure is a separate limit theorem. -/
theorem bernsteinAverage_kernel_bounds
    (u : ℕ → ℝ) (hpos : BernsteinPositive u)
    {κ a : ℝ} (hκ : 0 < κ) (ha : 0 < a) (N n : ℕ) :
    0 ≤ bernsteinAverage u N
      (fun q => kernelWeight κ a q * kernelMultiplier (κ * a * q) ^ n) ∧
    bernsteinAverage u N
      (fun q => kernelWeight κ a q * kernelMultiplier (κ * a * q) ^ n) ≤
        bernsteinAverage u N (kernelWeight κ a) := by
  have hkernel : ∀ q ∈ Set.Icc (0 : ℝ) 1,
      0 ≤ kernelMultiplier (κ * a * q) ^ n ∧
        kernelMultiplier (κ * a * q) ^ n ≤ 1 := by
    intro q hq
    exact kernelMultiplier_pow_bounds
      (mul_nonneg (mul_nonneg hκ.le ha.le) hq.1) n
  constructor
  · apply bernsteinAverage_nonneg u hpos N
    intro q hq
    exact mul_nonneg (kernelWeight_nonneg hκ ha) (hkernel q hq).1
  · apply bernsteinAverage_mono u hpos N
    intro q hq
    calc
      kernelWeight κ a q * kernelMultiplier (κ * a * q) ^ n ≤
          kernelWeight κ a q * 1 :=
        mul_le_mul_of_nonneg_left (hkernel q hq).2 (kernelWeight_nonneg hκ ha)
      _ = kernelWeight κ a q := mul_one _

end RH_HilbertLimit.TwoRoutes
