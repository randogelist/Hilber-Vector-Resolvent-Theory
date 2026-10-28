import RH_HilbertLimit.ActualXi
import OriginTrace
import AngularMaster.LowHeightGeometry

/-!
Source-reviewed candidate only: no Lean or Lake execution has been performed.

These lemmas specialize the archived, literal-xi product and first-trace
theorems to the current Hilbert branch. This intermediate constructor takes
moment reality and all-order power sums. CanonicalBridge fills moment reality.
The power-sum input remains open. No finite witness or checker is constructed.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace RH_HilbertLimit

open AngularMaster OverflowResidueRH

/-- The origin moment is the exact absolutely summable complex zero trace. -/
theorem actualComplexMoment_zero_eq_canonical_trace :
    actualComplexMoment 0 =
      ∑' i : ActualPairIndex, (actualComplexScale i)⁻¹ := by
  simpa [actualComplexMoment, actualLogDerivative] using
    actual_theta_origin_logDeriv_eq_tsum

/-- The real normalization scalar is the real part of the same trace. -/
theorem actualKappa_eq_canonical_trace :
    actualKappa =
      ∑' i : ActualPairIndex, ((actualComplexScale i)⁻¹).re := by
  simpa [actualKappa, actualMoment, actualComplexMoment, actualLogDerivative] using
    actual_theta_origin_real_trace

/-- The actual divisor has an opposite pair: its origin multiplicity is zero,
and the unconditional canonical expansion has nonempty support. -/
theorem actualPairIndex_nonempty : Nonempty ActualPairIndex := by
  have hocc : Nonempty EntireXiPullbackZeroOccurrence := by
    rcases
      entireXiPullbackCanonicalHadamardLogDerivativeDataUnconditional.support_nonempty
      with hm | ho
    · exact False.elim (hm actual_originMultiplicity_eq_zero)
    · exact ho
  obtain ⟨i⟩ := hocc
  exact ⟨(entireXiPullbackZeroOccurrenceNegationPairingData.pairEquiv.symm i).1⟩

/-- The low-height zero-free theorem places every reciprocal scale in the
right half-plane; no RH assumption enters this argument. This is the proof of
RHSmallO.spectralWeight_pos specialized without importing NativeClosure. -/
theorem actualInverseScale_re_pos (i : ActualPairIndex) :
    0 < ((actualComplexScale i)⁻¹).re := by
  have hn : 0 < ‖actualComplexScale i‖ :=
    norm_pos_iff.mpr (actualComplexScale_ne_zero i)
  have hs := actualComplexScale_sector_of_zero_height
    (fun _ hz => actual_xi_zero_one_lt_abs_im hz) i
  have hs' := (div_le_iff₀ hn).mp hs
  have hre : 0 < (actualComplexScale i).re := by nlinarith
  rw [Complex.inv_re]
  exact div_pos hre (Complex.normSq_pos.mpr (actualComplexScale_ne_zero i))

/-- Unconditional positivity of the current branch's exact normalization
scalar, derived from the actual product, low-height exclusion, and nonempty
actual divisor. -/
theorem actualKappa_pos : 0 < actualKappa := by
  classical
  rw [actualKappa_eq_canonical_trace]
  obtain ⟨j⟩ := actualPairIndex_nonempty
  have hsingle := actualComplexScale_inv_re_summable.sum_le_tsum
    ({j} : Finset ActualPairIndex)
    (fun i _ => (actualInverseScale_re_pos i).le)
  simp only [Finset.sum_singleton] at hsingle
  exact lt_of_lt_of_le (actualInverseScale_re_pos j) hsingle

/-- Every theta zero occurs in the actual complex-scale divisor. This is an
exact exhaustion statement about the analytic divisor, not a finite encoding. -/
theorem actualTheta_zero_has_canonical_scale {z : ℂ}
    (hz : AWPIRH.theta z = 0) :
    ∃ i : ActualPairIndex, z = -actualComplexScale i := by
  have hz0 : z ≠ 0 := by
    intro he
    subst z
    exact actual_theta_zero_ne_zero hz
  have hsqrt : Complex.sqrt z ≠ 0 := by
    intro he
    apply hz0
    simpa [he] using (AWPIRH.complex_sqrt_sq z).symm
  let w : ℂ := -Complex.I * Complex.sqrt z
  have hw0 : w ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hsqrt
  have hw : EntireXiPullback w = 0 := by
    change EntireXiPullback (-Complex.I * Complex.sqrt z) = 0
    rw [← actual_theta_eq_external_pullback z]
    exact hz
  have hw2 : w ^ 2 = -z := by
    dsimp [w]
    rw [mul_pow, neg_sq, Complex.I_sq, AWPIRH.complex_sqrt_sq]
    ring
  obtain ⟨i, hi⟩ := entireXiPullbackZeroOccurrenceLoc_exhaustive hw hw0
  let P := entireXiPullbackZeroOccurrenceNegationPairingData
  obtain ⟨⟨j, b⟩, hpair⟩ := P.pairEquiv.surjective i
  refine ⟨j, ?_⟩
  cases b with
  | false =>
      have heq : actualPairZero j = w := by
        change entireXiPullbackZeroOccurrenceLoc (P.pairEquiv (j, false)) = w
        rw [hpair, hi]
      rw [actualComplexScale, heq, hw2, neg_neg]
  | true =>
      have heq : -actualPairZero j = w := by
        change -entireXiPullbackZeroOccurrenceLoc (P.pairEquiv (j, false)) = w
        rw [← P.loc_true j, hpair, hi]
      have hsq : (actualPairZero j) ^ 2 = w ^ 2 := by
        rw [← heq, neg_sq]
      rw [actualComplexScale, hsq, hw2, neg_neg]

/-- The actual normalized reciprocal-scale nodes, retaining multiplicities. -/
def canonicalNode (i : ActualPairIndex) : ℂ :=
  ((actualKappa : ℂ) * actualComplexScale i)⁻¹

theorem canonicalNode_ne_zero (i : ActualPairIndex) : canonicalNode i ≠ 0 := by
  have hκ : (actualKappa : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt actualKappa_pos
  unfold canonicalNode
  exact inv_ne_zero (mul_ne_zero hκ (actualComplexScale_ne_zero i))

theorem canonicalNode_eq_inverseScale_mul (i : ActualPairIndex) :
    canonicalNode i = (actualKappa : ℂ)⁻¹ * (actualComplexScale i)⁻¹ := by
  have hκ : (actualKappa : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt actualKappa_pos
  have ha : actualComplexScale i ≠ 0 := actualComplexScale_ne_zero i
  unfold canonicalNode
  field_simp [hκ, ha] <;> ring

theorem canonicalNode_norm_summable :
    Summable (fun i : ActualPairIndex => ‖canonicalNode i‖) := by
  have hs := actualComplexScale_norm_inv_summable.mul_left ‖(actualKappa : ℂ)⁻¹‖
  refine hs.congr ?_
  intro i
  rw [canonicalNode_eq_inverseScale_mul, norm_mul]

theorem canonicalNode_root_eq (i : ActualPairIndex) :
    rootOfNode actualKappa (canonicalNode i) = -actualComplexScale i := by
  have hκ : (actualKappa : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt actualKappa_pos
  have ha : actualComplexScale i ≠ 0 := actualComplexScale_ne_zero i
  have hmul : (actualKappa : ℂ) * canonicalNode i = (actualComplexScale i)⁻¹ := by
    unfold canonicalNode
    field_simp [hκ, ha] <;> ring
  unfold rootOfNode
  rw [hmul, inv_inv]

theorem canonicalNode_root_zero (i : ActualPairIndex) :
    AWPIRH.theta (rootOfNode actualKappa (canonicalNode i)) = 0 := by
  rw [canonicalNode_root_eq]
  exact actual_theta_neg_complexScale_zero i

theorem canonicalNode_covers (z : ℂ) (hz : AWPIRH.theta z = 0) :
    ∃ i : ActualPairIndex, z = rootOfNode actualKappa (canonicalNode i) := by
  obtain ⟨i, hi⟩ := actualTheta_zero_has_canonical_scale hz
  exact ⟨i, hi.trans (canonicalNode_root_eq i).symm⟩

/-- The actual analytic calibration reduces to its two precise all-order
moment obligations. This constructor is conditional on those identities;
neither argument is finite raw data or a checker acceptance proof. -/
def canonicalCalibration_of_moment_identities
    (hmoment_real : ∀ n, (actualComplexMoment n).im = 0)
    (hpower_sums : ∀ n, HasSum
      (fun i : ActualPairIndex => canonicalNode i ^ (n + 1))
      (actualNormalizedMoment n : ℂ)) :
    ActualSpectralCalibration ActualPairIndex where
  node := canonicalNode
  kappa_pos := actualKappa_pos
  moment_real := hmoment_real
  node_ne_zero := canonicalNode_ne_zero
  norm_summable := canonicalNode_norm_summable
  power_sums := hpower_sums
  root_zero := canonicalNode_root_zero
  covers := canonicalNode_covers

end RH_HilbertLimit
