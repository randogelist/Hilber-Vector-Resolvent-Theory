import RH_HilbertLimit.TwoRoutes.BernsteinMomentLimit
import RH_HilbertLimit.TwoRoutes.ActualPositivePrefix
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# A Hausdorff measure constructed directly from positive Bernstein rows

The finite Bernstein averages are positive and uniformly bounded on every
continuous test function. A single free ultrafilter therefore gives a positive
linear functional. Riesz--Markov--Kakutani represents that functional by a
probability measure, and the finite monomial limit identifies its moments.

No RH theorem, spectral extraction, representing-measure hypothesis, or
continuous-functional extension hypothesis enters the construction.

Source preparation only: Lean and Lake have not been executed.
-/

set_option autoImplicit false
noncomputable section

open Filter MeasureTheory
open scoped BigOperators Topology CompactlySupported

namespace RH_HilbertLimit.TwoRoutes

abbrev HausdorffInterval := Set.Icc (0 : ℝ) 1

/-- Extension used only at the finite grid. No continuity outside the interval
is needed or asserted. -/
def intervalExtension (f : C(HausdorffInterval, ℝ)) (q : ℝ) : ℝ :=
  if hq : q ∈ Set.Icc (0 : ℝ) 1 then f ⟨q, hq⟩ else 0

@[simp] theorem intervalExtension_apply (f : C(HausdorffInterval, ℝ))
    (q : HausdorffInterval) : intervalExtension f q = f q := by
  simp [intervalExtension, q.property]

theorem bernsteinAverage_congr_on_interval (u : ℕ → ℝ) (N : ℕ)
    (f g : ℝ → ℝ)
    (hfg : ∀ q ∈ Set.Icc (0 : ℝ) 1, f q = g q) :
    bernsteinAverage u N f = bernsteinAverage u N g := by
  unfold bernsteinAverage
  apply Finset.sum_congr rfl
  intro j hj
  have hjN : j ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [hfg _ (bernsteinGrid_mem_Icc N j hjN)]

def continuousBernsteinAverage (u : ℕ → ℝ) (N : ℕ)
    (f : C(HausdorffInterval, ℝ)) : ℝ :=
  bernsteinAverage u N (intervalExtension f)

theorem continuousBernsteinAverage_add (u : ℕ → ℝ) (N : ℕ)
    (f g : C(HausdorffInterval, ℝ)) :
    continuousBernsteinAverage u N (f + g) =
      continuousBernsteinAverage u N f + continuousBernsteinAverage u N g := by
  unfold continuousBernsteinAverage
  rw [← bernsteinAverage_add]
  apply bernsteinAverage_congr_on_interval
  intro q hq
  simp [intervalExtension, hq]

theorem continuousBernsteinAverage_smul (u : ℕ → ℝ) (N : ℕ)
    (c : ℝ) (f : C(HausdorffInterval, ℝ)) :
    continuousBernsteinAverage u N (c • f) =
      c * continuousBernsteinAverage u N f := by
  unfold continuousBernsteinAverage
  rw [← bernsteinAverage_smul]
  apply bernsteinAverage_congr_on_interval
  intro q hq
  simp [intervalExtension, hq]

theorem continuousBernsteinAverage_const (u : ℕ → ℝ) (hzero : u 0 = 1)
    (N : ℕ) (c : ℝ) :
    continuousBernsteinAverage u N (ContinuousMap.const _ c) = c := by
  rw [continuousBernsteinAverage]
  calc
    bernsteinAverage u N (intervalExtension (ContinuousMap.const _ c)) =
        bernsteinAverage u N (fun _ => c) := by
      apply bernsteinAverage_congr_on_interval
      intro q hq
      simp [intervalExtension, hq]
    _ = c := bernsteinAverage_const u hzero N c

theorem continuousBernsteinAverage_mono (u : ℕ → ℝ)
    (hpos : BernsteinPositive u) (N : ℕ)
    {f g : C(HausdorffInterval, ℝ)} (hfg : f ≤ g) :
    continuousBernsteinAverage u N f ≤ continuousBernsteinAverage u N g := by
  apply bernsteinAverage_mono u hpos N
  intro q hq
  simpa [intervalExtension, hq] using hfg ⟨q, hq⟩

theorem continuousBernsteinAverage_abs_le (u : ℕ → ℝ) (hzero : u 0 = 1)
    (hpos : BernsteinPositive u) (N : ℕ) (f : C(HausdorffInterval, ℝ)) :
    |continuousBernsteinAverage u N f| ≤ ‖f‖ := by
  apply bernsteinAverage_abs_le u hzero hpos N
  intro q hq
  simpa [intervalExtension, hq, Real.norm_eq_abs] using
    ContinuousMap.norm_coe_le_norm f ⟨q, hq⟩

/-- All test functions use the same free ultrafilter; this is what preserves
addition and scalar multiplication in the selected limits. -/
theorem continuousBernsteinAverage_exists_ultralimit
    (u : ℕ → ℝ) (hzero : u 0 = 1) (hpos : BernsteinPositive u)
    (f : C(HausdorffInterval, ℝ)) :
    ∃ v : ℝ, Tendsto (fun N => continuousBernsteinAverage u N f)
      (Filter.hyperfilter ℕ : Filter ℕ) (𝓝 v) := by
  let A : ℕ → ℝ := fun N => continuousBernsteinAverage u N f
  let V : Ultrafilter ℝ := Ultrafilter.map A (Filter.hyperfilter ℕ)
  have hmem : Set.Icc (-‖f‖) ‖f‖ ∈ V := by
    change A ⁻¹' Set.Icc (-‖f‖) ‖f‖ ∈ (Filter.hyperfilter ℕ : Filter ℕ)
    apply Filter.Eventually.of_forall
    intro N
    exact abs_le.mp (continuousBernsteinAverage_abs_le u hzero hpos N f)
  obtain ⟨v, _, hv⟩ := isCompact_Icc.ultrafilter_le_nhds' V hmem
  refine ⟨v, ?_⟩
  change Filter.map A (Filter.hyperfilter ℕ : Filter ℕ) ≤ 𝓝 v
  simpa only [V, Ultrafilter.coe_map] using hv

def hausdorffValue (u : ℕ → ℝ) (hzero : u 0 = 1)
    (hpos : BernsteinPositive u) (f : C(HausdorffInterval, ℝ)) : ℝ :=
  Classical.choose (continuousBernsteinAverage_exists_ultralimit u hzero hpos f)

theorem tendsto_hausdorffValue (u : ℕ → ℝ) (hzero : u 0 = 1)
    (hpos : BernsteinPositive u) (f : C(HausdorffInterval, ℝ)) :
    Tendsto (fun N => continuousBernsteinAverage u N f)
      (Filter.hyperfilter ℕ : Filter ℕ) (𝓝 (hausdorffValue u hzero hpos f)) :=
  Classical.choose_spec (continuousBernsteinAverage_exists_ultralimit u hzero hpos f)

theorem hausdorffValue_add (u : ℕ → ℝ) (hzero : u 0 = 1)
    (hpos : BernsteinPositive u) (f g : C(HausdorffInterval, ℝ)) :
    hausdorffValue u hzero hpos (f + g) =
      hausdorffValue u hzero hpos f + hausdorffValue u hzero hpos g := by
  apply tendsto_nhds_unique (tendsto_hausdorffValue u hzero hpos (f + g))
  simpa only [continuousBernsteinAverage_add] using
    (tendsto_hausdorffValue u hzero hpos f).add
      (tendsto_hausdorffValue u hzero hpos g)

theorem hausdorffValue_smul (u : ℕ → ℝ) (hzero : u 0 = 1)
    (hpos : BernsteinPositive u) (c : ℝ) (f : C(HausdorffInterval, ℝ)) :
    hausdorffValue u hzero hpos (c • f) = c * hausdorffValue u hzero hpos f := by
  apply tendsto_nhds_unique (tendsto_hausdorffValue u hzero hpos (c • f))
  simpa only [continuousBernsteinAverage_smul] using
    (tendsto_hausdorffValue u hzero hpos f).const_mul c

theorem hausdorffValue_const (u : ℕ → ℝ) (hzero : u 0 = 1)
    (hpos : BernsteinPositive u) (c : ℝ) :
    hausdorffValue u hzero hpos (ContinuousMap.const _ c) = c := by
  apply tendsto_nhds_unique (tendsto_hausdorffValue u hzero hpos _)
  simpa only [continuousBernsteinAverage_const u hzero] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => c)
      (Filter.hyperfilter ℕ : Filter ℕ) (𝓝 c))

theorem hausdorffValue_mono (u : ℕ → ℝ) (hzero : u 0 = 1)
    (hpos : BernsteinPositive u) {f g : C(HausdorffInterval, ℝ)}
    (hfg : f ≤ g) : hausdorffValue u hzero hpos f ≤ hausdorffValue u hzero hpos g := by
  exact le_of_tendsto_of_tendsto'
    (tendsto_hausdorffValue u hzero hpos f)
    (tendsto_hausdorffValue u hzero hpos g)
    (fun N => continuousBernsteinAverage_mono u hpos N hfg)

theorem hausdorffValue_abs_le (u : ℕ → ℝ) (hzero : u 0 = 1)
    (hpos : BernsteinPositive u) (f : C(HausdorffInterval, ℝ)) :
    |hausdorffValue u hzero hpos f| ≤ ‖f‖ := by
  exact le_of_tendsto' (tendsto_hausdorffValue u hzero hpos f).abs
    (fun N => continuousBernsteinAverage_abs_le u hzero hpos N f)

def hausdorffPositiveFunctional (u : ℕ → ℝ) (hzero : u 0 = 1)
    (hpos : BernsteinPositive u) : C_c(HausdorffInterval, ℝ) →ₚ[ℝ] ℝ where
  toFun f := hausdorffValue u hzero hpos f.toContinuousMap
  map_add' f g := hausdorffValue_add u hzero hpos f.toContinuousMap g.toContinuousMap
  map_smul' c f := by
    have hsmul : (c • f).toContinuousMap = c • f.toContinuousMap := by
      ext q
      simp
    change hausdorffValue u hzero hpos (c • f).toContinuousMap =
      c * hausdorffValue u hzero hpos f.toContinuousMap
    rw [hsmul]
    exact hausdorffValue_smul u hzero hpos c f.toContinuousMap
  monotone' := by
    intro f g hfg
    exact hausdorffValue_mono u hzero hpos (fun q => hfg q)

/-- The representing measure is constructed, not supplied as an assumption. -/
def hausdorffMeasure (u : ℕ → ℝ) (hzero : u 0 = 1)
    (hpos : BernsteinPositive u) : Measure HausdorffInterval :=
  RealRMK.rieszMeasure (hausdorffPositiveFunctional u hzero hpos)

theorem hausdorffMeasure_integral (u : ℕ → ℝ) (hzero : u 0 = 1)
    (hpos : BernsteinPositive u) (f : C(HausdorffInterval, ℝ)) :
    (∫ q, f q ∂hausdorffMeasure u hzero hpos) = hausdorffValue u hzero hpos f := by
  let fc : C_c(HausdorffInterval, ℝ) :=
    CompactlySupportedContinuousMap.continuousMapEquiv f
  have hfc : fc.toContinuousMap = f := by
    ext q
    exact CompactlySupportedContinuousMap.continuousMapEquiv_apply_toFun f q
  have h := RealRMK.integral_rieszMeasure
    (hausdorffPositiveFunctional u hzero hpos) fc
  change (∫ q, fc q ∂hausdorffMeasure u hzero hpos) =
    hausdorffValue u hzero hpos fc.toContinuousMap at h
  rw [hfc] at h
  simpa only [fc, CompactlySupportedContinuousMap.continuousMapEquiv_apply_toFun] using h

theorem hausdorffMeasure_univ (u : ℕ → ℝ) (hzero : u 0 = 1)
    (hpos : BernsteinPositive u) : hausdorffMeasure u hzero hpos Set.univ = 1 := by
  let oneC : C_c(HausdorffInterval, ℝ) :=
    CompactlySupportedContinuousMap.continuousMapEquiv (ContinuousMap.const _ (1 : ℝ))
  have hone : ∀ q, oneC q = 1 := by intro q; rfl
  have honeC : oneC.toContinuousMap = ContinuousMap.const _ (1 : ℝ) := by
    ext q
    exact hone q
  have hvalue : hausdorffPositiveFunctional u hzero hpos oneC = 1 := by
    change hausdorffValue u hzero hpos oneC.toContinuousMap = 1
    rw [honeC, hausdorffValue_const]
  apply le_antisymm
  · have h := RealRMK.rieszMeasure_le_of_eq_one
      (hausdorffPositiveFunctional u hzero hpos)
      (f := oneC) (fun q => by rw [hone]; positivity)
      (K := Set.univ) isCompact_univ (fun q _ => hone q)
    simpa only [hausdorffMeasure, hvalue, ENNReal.ofReal_one] using h
  · have h := RealRMK.le_rieszMeasure_tsupport_subset
      (hausdorffPositiveFunctional u hzero hpos)
      (f := oneC) (fun q => by rw [hone]; exact ⟨zero_le_one, le_rfl⟩)
      (V := Set.univ) (Set.subset_univ _)
    simpa only [hausdorffMeasure, hvalue, ENNReal.ofReal_one] using h

instance hausdorffMeasure_isProbabilityMeasure (u : ℕ → ℝ) (hzero : u 0 = 1)
    (hpos : BernsteinPositive u) : IsProbabilityMeasure (hausdorffMeasure u hzero hpos) :=
  ⟨hausdorffMeasure_univ u hzero hpos⟩

def intervalMonomial (k : ℕ) : C(HausdorffInterval, ℝ) where
  toFun q := (q : ℝ) ^ k
  continuous_toFun := continuous_subtype_val.pow k

theorem continuousBernsteinAverage_monomial (u : ℕ → ℝ) (N k : ℕ) :
    continuousBernsteinAverage u N (intervalMonomial k) =
      bernsteinAverage u N (fun q => q ^ k) := by
  apply bernsteinAverage_congr_on_interval
  intro q hq
  simp [intervalExtension, intervalMonomial, hq]

theorem hausdorffValue_monomial (u : ℕ → ℝ) (hzero : u 0 = 1)
    (hpos : BernsteinPositive u) (k : ℕ) :
    hausdorffValue u hzero hpos (intervalMonomial k) = u k := by
  apply tendsto_nhds_unique (tendsto_hausdorffValue u hzero hpos (intervalMonomial k))
  simpa only [continuousBernsteinAverage_monomial] using
    (bernsteinAverage_monomial_tendsto u k).mono_left Nat.hyperfilter_le_atTop

/-- The full Hausdorff conclusion, with no measure-existence premise. -/
theorem hausdorffMeasure_moment (u : ℕ → ℝ) (hzero : u 0 = 1)
    (hpos : BernsteinPositive u) (k : ℕ) :
    (∫ q, (q : ℝ) ^ k ∂hausdorffMeasure u hzero hpos) = u k := by
  have h := hausdorffMeasure_integral u hzero hpos (intervalMonomial k)
  rw [hausdorffValue_monomial] at h
  exact h

theorem exists_probabilityMeasure_of_bernsteinPositive
    (u : ℕ → ℝ) (hzero : u 0 = 1) (hpos : BernsteinPositive u) :
    ∃ σ : Measure HausdorffInterval, IsProbabilityMeasure σ ∧
      ∀ k : ℕ, (∫ q, (q : ℝ) ^ k ∂σ) = u k :=
  ⟨hausdorffMeasure u hzero hpos, inferInstance,
    hausdorffMeasure_moment u hzero hpos⟩

/-- Actual positive measure from the same H00 witness used by route one.
The proof uses the Bernstein signs of H00 and no output of route one. -/
def actualHausdorffMeasure (h : H00) : Measure HausdorffInterval :=
  hausdorffMeasure actualNormalizedMoment actualNormalizedMoment_zero_unconditional
    (actual_bernsteinPositive_of_H00 h)

instance actualHausdorffMeasure_isProbabilityMeasure (h : H00) :
    IsProbabilityMeasure (actualHausdorffMeasure h) :=
  hausdorffMeasure_isProbabilityMeasure _ _ _

theorem actualHausdorffMeasure_moment (h : H00) (k : ℕ) :
    (∫ q, (q : ℝ) ^ k ∂actualHausdorffMeasure h) = actualNormalizedMoment k :=
  hausdorffMeasure_moment _ _ _ k

theorem actual_positive_measure_of_H00 (h : H00) :
    ∃ σ : Measure HausdorffInterval, IsProbabilityMeasure σ ∧
      ∀ k : ℕ, (∫ q, (q : ℝ) ^ k ∂σ) = actualNormalizedMoment k :=
  ⟨actualHausdorffMeasure h, inferInstance, actualHausdorffMeasure_moment h⟩

end RH_HilbertLimit.TwoRoutes
