import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Scalar growth consequences of explicit exponential estimates

This module contains no statement about the Riemann zeros.  The hypotheses are
ordinary upper and lower estimates, including a bounded-block lower estimate.
No desired limit is included in the hypotheses of the geometric-sandwich
theorems.  The separate spectral argument producing these estimates is not
formalized by this module.

Prepared without running Lean.  Compilation and axiom audit are required on
the authorized native Windows target before any verified status is assigned.
-/

noncomputable section

open Filter
open scoped Topology BigOperators

namespace RH_HilbertLimit

/-- The normalized real logarithm.  The value at index zero is immaterial. -/
def logScale (V : ℕ → ℝ) (n : ℕ) : ℝ := Real.log (V n) / (n : ℝ)

/-- The real `n`th-root expression used in the paper. -/
def rootScale (V : ℕ → ℝ) (n : ℕ) : ℝ :=
  Real.rpow (V n) ((n : ℝ)⁻¹)

/-- A global subexponential upper bound, with a constant for each positive rate. -/
def Subexponential (V : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, V n ≤ C * Real.exp (ε * (n : ℝ))

theorem rootScale_eq_exp_logScale {V : ℕ → ℝ} {n : ℕ}
    (hV : 0 < V n) :
    rootScale V n = Real.exp (logScale V n) := by
  simp only [rootScale, Real.rpow_eq_pow, logScale, Real.rpow_def_of_pos hV,
    div_eq_mul_inv]

theorem log_rootScale_eq_logScale {V : ℕ → ℝ} {n : ℕ}
    (hV : 0 < V n) :
    Real.log (rootScale V n) = logScale V n := by
  rw [rootScale, Real.rpow_eq_pow, Real.log_rpow hV]
  simp only [logScale, div_eq_mul_inv, mul_comm]

theorem logScale_tendsto_iff_rootScale_tendsto
    {V : ℕ → ℝ} {R : ℝ} (hR : 0 < R)
    (hV : ∀ᶠ n in atTop, 0 < V n) :
    Tendsto (logScale V) atTop (𝓝 (Real.log R)) ↔
      Tendsto (rootScale V) atTop (𝓝 R) := by
  constructor
  · intro hlog
    have hexp : Tendsto (fun n => Real.exp (logScale V n)) atTop
        (𝓝 (Real.exp (Real.log R))) :=
      Real.continuous_exp.continuousAt.tendsto.comp hlog
    have hexp' : Tendsto (fun n => Real.exp (logScale V n)) atTop (𝓝 R) := by
      simpa only [Real.exp_log hR] using hexp
    apply hexp'.congr'
    filter_upwards [hV] with n hn
    exact (rootScale_eq_exp_logScale hn).symm
  · intro hroot
    have hlog : Tendsto (fun n => Real.log (rootScale V n)) atTop
        (𝓝 (Real.log R)) :=
      (Real.continuousAt_log hR.ne').tendsto.comp hroot
    apply hlog.congr'
    filter_upwards [hV] with n hn
    exact log_rootScale_eq_logScale hn

theorem logScale_zero_iff_rootScale_one {V : ℕ → ℝ}
    (hV : ∀ᶠ n in atTop, 0 < V n) :
    Tendsto (logScale V) atTop (𝓝 0) ↔
      Tendsto (rootScale V) atTop (𝓝 1) := by
  simpa only [Real.log_one] using
    (logScale_tendsto_iff_rootScale_tendsto (V := V) (R := 1) zero_lt_one hV)

private theorem log_mul_pow_div {a R : ℝ} (ha : 0 < a) (hR : 0 < R)
    {n : ℕ} (hn : 0 < n) :
    Real.log (a * R ^ n) / (n : ℝ) =
      Real.log a / (n : ℝ) + Real.log R := by
  rw [Real.log_mul ha.ne' (pow_ne_zero n hR.ne'), Real.log_pow]
  have hn' : (n : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hn)
  field_simp [hn'] <;> ring

theorem eventually_pos_of_geometric_lower
    {V : ℕ → ℝ} {R c : ℝ} (hR : 0 < R) (hc : 0 < c)
    (hlo : ∀ᶠ n in atTop, c * R ^ n ≤ V n) :
    ∀ᶠ n in atTop, 0 < V n := by
  filter_upwards [hlo] with n hn
  exact lt_of_lt_of_le (mul_pos hc (pow_pos hR n)) hn

/-- Positive two-sided geometric estimates imply the logarithmic growth limit. -/
theorem geometric_sandwich_log_tendsto
    {V : ℕ → ℝ} {R c C : ℝ}
    (hR : 0 < R) (hc : 0 < c) (hC : 0 < C)
    (hb : ∀ᶠ n in atTop, c * R ^ n ≤ V n ∧ V n ≤ C * R ^ n) :
    Tendsto (logScale V) atTop (𝓝 (Real.log R)) := by
  have hlo : Tendsto (fun n : ℕ => Real.log c / (n : ℝ) + Real.log R)
      atTop (𝓝 (Real.log R)) := by
    simpa only [zero_add] using
      (tendsto_const_div_atTop_nhds_zero_nat (Real.log c)).add
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => Real.log R)
          atTop (𝓝 (Real.log R)))
  have hhi : Tendsto (fun n : ℕ => Real.log C / (n : ℝ) + Real.log R)
      atTop (𝓝 (Real.log R)) := by
    simpa only [zero_add] using
      (tendsto_const_div_atTop_nhds_zero_nat (Real.log C)).add
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => Real.log R)
          atTop (𝓝 (Real.log R)))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
  · filter_upwards [hb, eventually_gt_atTop (0 : ℕ)] with n hn hn0
    have hlog := Real.log_le_log (mul_pos hc (pow_pos hR n)) hn.1
    have hdiv := div_le_div_of_nonneg_right hlog (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    rw [log_mul_pow_div hc hR hn0] at hdiv
    exact hdiv
  · filter_upwards [hb, eventually_gt_atTop (0 : ℕ)] with n hn hn0
    have hV : 0 < V n := lt_of_lt_of_le (mul_pos hc (pow_pos hR n)) hn.1
    have hlog := Real.log_le_log hV hn.2
    have hdiv := div_le_div_of_nonneg_right hlog (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    rw [log_mul_pow_div hC hR hn0] at hdiv
    exact hdiv

/-- Positive two-sided geometric estimates imply the ordinary root limit. -/
theorem geometric_sandwich_root_tendsto
    {V : ℕ → ℝ} {R c C : ℝ}
    (hR : 0 < R) (hc : 0 < c) (hC : 0 < C)
    (hb : ∀ᶠ n in atTop, c * R ^ n ≤ V n ∧ V n ≤ C * R ^ n) :
    Tendsto (rootScale V) atTop (𝓝 R) := by
  have hV := eventually_pos_of_geometric_lower hR hc (hb.mono fun _ h => h.1)
  exact (logScale_tendsto_iff_rootScale_tendsto hR hV).mp
    (geometric_sandwich_log_tendsto hR hc hC hb)

/--
A fixed-width block estimate and monotonicity give an estimate at each large
index.  The explicit loss is exactly the factor `R ^ d`.
-/
theorem block_lower_to_eventual_lower
    {V : ℕ → ℝ} {R c : ℝ} {d : ℕ}
    (hR : 0 < R) (hmono : Monotone V)
    (hb : ∀ᶠ n in atTop, ∃ k : ℕ, k ≤ d ∧ c * R ^ n ≤ V (n + k)) :
    ∀ᶠ n in atTop, (c / R ^ d) * R ^ n ≤ V n := by
  rcases eventually_atTop.mp hb with ⟨N, hN⟩
  apply eventually_atTop.mpr
  refine ⟨N + d, ?_⟩
  intro n hn
  have hd : d ≤ n := by omega
  have hnd : N ≤ n - d := by omega
  obtain ⟨k, hkd, hk⟩ := hN (n - d) hnd
  have hle : V ((n - d) + k) ≤ V n := hmono (by omega)
  have hpow : R ^ n = R ^ (n - d) * R ^ d := by
    rw [← pow_add, Nat.sub_add_cancel hd]
  calc
    (c / R ^ d) * R ^ n = c * R ^ (n - d) := by
      rw [hpow]
      field_simp [(pow_pos hR d).ne'] <;> ring
    _ ≤ V n := hk.trans hle

/-- The block lower estimate gives the full ordinary root limit, not just a limsup. -/
theorem root_tendsto_of_monotone_block_bounds
    {V : ℕ → ℝ} {R c C : ℝ} {d : ℕ}
    (hR : 0 < R) (hc : 0 < c) (hC : 0 < C) (hmono : Monotone V)
    (hblock : ∀ᶠ n in atTop, ∃ k : ℕ, k ≤ d ∧ c * R ^ n ≤ V (n + k))
    (hupper : ∀ᶠ n in atTop, V n ≤ C * R ^ n) :
    Tendsto (rootScale V) atTop (𝓝 R) := by
  apply geometric_sandwich_root_tendsto hR (div_pos hc (pow_pos hR d)) hC
  exact (block_lower_to_eventual_lower hR hmono hblock).and hupper

/-- Finite exceptional indices are absorbed into a positive multiplicative constant. -/
theorem subexponential_of_eventual_exp_upper {V : ℕ → ℝ}
    (hV : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, V n ≤ Real.exp (ε * (n : ℝ))) :
    Subexponential V := by
  intro ε hε
  rcases eventually_atTop.mp (hV ε hε) with ⟨N, hN⟩
  let C : ℝ := max 1 (∑ j ∈ Finset.range N, |V j|)
  have hC1 : 1 ≤ C := le_max_left _ _
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one hC1
  refine ⟨C, hC, ?_⟩
  intro n
  have he : 1 ≤ Real.exp (ε * (n : ℝ)) :=
    Real.one_le_exp_iff.mpr (mul_nonneg hε.le (Nat.cast_nonneg n))
  by_cases hn : N ≤ n
  · exact (hN n hn).trans (by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hC1 (Real.exp_nonneg (ε * (n : ℝ))))
  · have hn' : n < N := lt_of_not_ge hn
    have hs : |V n| ≤ ∑ j ∈ Finset.range N, |V j| :=
      Finset.single_le_sum (fun j _ => abs_nonneg (V j)) (Finset.mem_range.mpr hn')
    have hvC : V n ≤ C :=
      (le_abs_self (V n)).trans (hs.trans (le_max_right _ _))
    exact hvC.trans (by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left he hC.le)

theorem subexponential_of_logScale_tendsto_zero {V : ℕ → ℝ}
    (hV : ∀ᶠ n in atTop, 0 < V n)
    (hlog : Tendsto (logScale V) atTop (𝓝 0)) :
    Subexponential V := by
  apply subexponential_of_eventual_exp_upper
  intro ε hε
  have hsmall : ∀ᶠ n in atTop, logScale V n < ε :=
    (tendsto_order.mp hlog).2 ε hε
  filter_upwards [hV, hsmall, eventually_gt_atTop (0 : ℕ)] with n hn hs hn0
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn0
  have hlogle : Real.log (V n) ≤ ε * (n : ℝ) :=
    (div_le_iff₀ hnR).mp (show Real.log (V n) / (n : ℝ) ≤ ε from hs.le)
  exact (Real.log_le_iff_le_exp hn).mp hlogle

private theorem logScale_le_of_exp_upper
    {V : ℕ → ℝ} {C ε : ℝ} {n : ℕ}
    (hV : 0 < V n) (hC : 0 < C) (hn : 0 < n)
    (hu : V n ≤ C * Real.exp (ε * (n : ℝ))) :
    logScale V n ≤ Real.log C / (n : ℝ) + ε := by
  have hlog := Real.log_le_log hV hu
  have hdiv := div_le_div_of_nonneg_right hlog (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hnR : (n : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hn)
  have heq : Real.log (C * Real.exp (ε * (n : ℝ))) / (n : ℝ) =
      Real.log C / (n : ℝ) + ε := by
    rw [Real.log_mul hC.ne' (Real.exp_ne_zero _), Real.log_exp]
    field_simp [hnR] <;> ring
  rw [heq] at hdiv
  exact hdiv

/-- Any logarithmic growth limit of a subexponential positive sequence is nonpositive. -/
theorem log_limit_nonpos_of_subexponential
    {V : ℕ → ℝ} {l : ℝ}
    (hV : ∀ᶠ n in atTop, 0 < V n)
    (hlog : Tendsto (logScale V) atTop (𝓝 l))
    (hSG : Subexponential V) : l ≤ 0 := by
  have hε : ∀ ε : ℝ, 0 < ε → l ≤ ε := by
    intro ε hε
    obtain ⟨C, hC, hCV⟩ := hSG ε hε
    have hu : Tendsto (fun n : ℕ => Real.log C / (n : ℝ) + ε)
        atTop (𝓝 ε) := by
      simpa only [zero_add] using
        (tendsto_const_div_atTop_nhds_zero_nat (Real.log C)).add
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => ε) atTop (𝓝 ε))
    apply le_of_tendsto_of_tendsto hlog hu
    filter_upwards [hV, eventually_gt_atTop (0 : ℕ)] with n hn hn0
    exact logScale_le_of_exp_upper hn hC hn0 (hCV n)
  by_contra h
  have hl : 0 < l := lt_of_not_ge h
  have hh := hε (l / 2) (half_pos hl)
  linarith

theorem logScale_tendsto_zero_of_subexponential {V : ℕ → ℝ}
    (hV : ∀ᶠ n in atTop, 1 ≤ V n) (hSG : Subexponential V) :
    Tendsto (logScale V) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [hV] with n hn
    have hnon : 0 ≤ logScale V n :=
      div_nonneg (Real.log_nonneg hn) (Nat.cast_nonneg n)
    exact ha.trans_le hnon
  · intro b hb
    obtain ⟨C, hC, hCV⟩ := hSG (b / 2) (half_pos hb)
    have hu : Tendsto (fun n : ℕ => Real.log C / (n : ℝ) + b / 2)
        atTop (𝓝 (b / 2)) := by
      simpa only [zero_add] using
        (tendsto_const_div_atTop_nhds_zero_nat (Real.log C)).add
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => b / 2) atTop (𝓝 (b / 2)))
    have hsmall : ∀ᶠ n : ℕ in atTop, Real.log C / (n : ℝ) + b / 2 < b :=
      (tendsto_order.mp hu).2 b (by linarith)
    filter_upwards [hV, hsmall, eventually_gt_atTop (0 : ℕ)] with n hn hs hn0
    have hpos : 0 < V n := lt_of_lt_of_le zero_lt_one hn
    exact lt_of_le_of_lt (logScale_le_of_exp_upper hpos hC hn0 (hCV n)) hs

theorem subexponential_iff_logScale_zero {V : ℕ → ℝ}
    (hV : ∀ᶠ n in atTop, 1 ≤ V n) :
    Subexponential V ↔ Tendsto (logScale V) atTop (𝓝 0) := by
  constructor
  · exact logScale_tendsto_zero_of_subexponential hV
  · exact subexponential_of_logScale_tendsto_zero
      (hV.mono fun _ hn => lt_of_lt_of_le zero_lt_one hn)

theorem subexponential_iff_rootScale_one {V : ℕ → ℝ}
    (hV : ∀ᶠ n in atTop, 1 ≤ V n) :
    Subexponential V ↔ Tendsto (rootScale V) atTop (𝓝 1) := by
  exact (subexponential_iff_logScale_zero hV).trans
    (logScale_zero_iff_rootScale_one
      (hV.mono fun _ hn => lt_of_lt_of_le zero_lt_one hn))

theorem rate_le_one_of_subexponential
    {V : ℕ → ℝ} {R : ℝ} (hR : 0 < R)
    (hV : ∀ᶠ n in atTop, 0 < V n)
    (hlog : Tendsto (logScale V) atTop (𝓝 (Real.log R)))
    (hSG : Subexponential V) : R ≤ 1 := by
  have h := log_limit_nonpos_of_subexponential hV hlog hSG
  exact (Real.log_nonpos_iff hR.le).mp h

/-- Under an explicit geometric sandwich with rate at least one, SG is exactly rate one. -/
theorem geometric_rate_eq_one_iff_subexponential
    {V : ℕ → ℝ} {R c C : ℝ}
    (hR1 : 1 ≤ R) (hc : 0 < c) (hC : 0 < C)
    (hb : ∀ᶠ n in atTop, c * R ^ n ≤ V n ∧ V n ≤ C * R ^ n) :
    R = 1 ↔ Subexponential V := by
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one hR1
  have hV := eventually_pos_of_geometric_lower hR hc (hb.mono fun _ h => h.1)
  have hlog := geometric_sandwich_log_tendsto hR hc hC hb
  constructor
  · intro heq
    apply subexponential_of_logScale_tendsto_zero hV
    simpa only [heq, Real.log_one] using hlog
  · intro hSG
    exact le_antisymm (rate_le_one_of_subexponential hR hV hlog hSG) hR1

theorem geometric_root_one_iff_rate_one
    {V : ℕ → ℝ} {R c C : ℝ}
    (hR : 0 < R) (hc : 0 < c) (hC : 0 < C)
    (hb : ∀ᶠ n in atTop, c * R ^ n ≤ V n ∧ V n ≤ C * R ^ n) :
    Tendsto (rootScale V) atTop (𝓝 1) ↔ R = 1 := by
  have hlimit := geometric_sandwich_root_tendsto hR hc hC hb
  constructor
  · intro hunit
    exact tendsto_nhds_unique hlimit hunit
  · intro hunit
    simpa only [hunit] using hlimit

theorem geometric_root_one_iff_subexponential
    {V : ℕ → ℝ} {R c C : ℝ}
    (hR1 : 1 ≤ R) (hc : 0 < c) (hC : 0 < C)
    (hb : ∀ᶠ n in atTop, c * R ^ n ≤ V n ∧ V n ≤ C * R ^ n) :
    Tendsto (rootScale V) atTop (𝓝 1) ↔ Subexponential V := by
  exact (geometric_root_one_iff_rate_one
    (lt_of_lt_of_le zero_lt_one hR1) hc hC hb).trans
      (geometric_rate_eq_one_iff_subexponential hR1 hc hC hb)

end RH_HilbertLimit
