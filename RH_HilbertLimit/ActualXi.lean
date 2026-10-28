import AWPIRH.ThetaEntire
import RH_HilbertLimit.Geometry
import RH_HilbertLimit.Bernstein
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Actual xi moments and the literal Mathlib RH endpoint

The source is the pole-subtracted, entire Mathlib xi used by the supplied
AWPIRH archives.  There is no arbitrary `RH : Prop` parameter.  In particular,
all RH conclusions below concern `_root_.RiemannHypothesis`.

The analytic spectral calibration interface at the end has no inhabitant
constructed in this package.  Its fields are classical analytic obligations,
not axioms, and are visible arguments of all theorems that consume it.
-/

set_option autoImplicit false
noncomputable section
open scoped Topology BigOperators
open Filter

namespace RH_HilbertLimit

theorem xi_zero_iff_nontrivialZero (s : ℂ) :
    AWPIRH.xi s = 0 ↔ AWPIRH.NontrivialZero s := by
  constructor
  · intro hx
    have hs0 : s ≠ 0 := by
      intro h
      subst s
      norm_num [AWPIRH.xi] at hx
    have hs1 : s ≠ 1 := by
      intro h
      subst s
      norm_num [AWPIRH.xi] at hx
    have hc : completedRiemannZeta s = 0 := by
      rw [AWPIRH.xi_eq_completed hs0 hs1] at hx
      exact (mul_eq_zero.mp hx).resolve_left
        (div_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr hs1)) (by norm_num))
    have hz : riemannZeta s = 0 := by
      rw [riemannZeta_def_of_ne_zero hs0, hc]
      simp
    have hnt : ¬ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1) := by
      rintro ⟨n, hn⟩
      have hr : (1 - s).re = 1 + 2 * ((n : ℝ) + 1) := by
        rw [hn]
        simp
        <;> ring
      have hb : 1 ≤ (1 - s).re := by
        rw [hr]
        nlinarith [Nat.cast_nonneg (α := ℝ) n]
      apply AWPIRH.xi_ne_zero_of_one_le_re hb
      rw [AWPIRH.xi_reflection]
      exact hx
    exact ⟨hz, hnt, hs1⟩
  · exact AWPIRH.xi_zero_of_nontrivialZero

theorem nativeRH_iff_xiZerosCritical :
    _root_.RiemannHypothesis ↔
      ∀ s : ℂ, AWPIRH.xi s = 0 → s.re = 1 / 2 := by
  constructor
  · intro h s hs
    rcases (xi_zero_iff_nontrivialZero s).mp hs with ⟨hz, hnt, h1⟩
    exact h s hz hnt h1
  · intro h s hz hnt h1
    exact h s (AWPIRH.xi_zero_of_nontrivialZero ⟨hz, hnt, h1⟩)

def ThetaZerosNonpositive : Prop :=
  ∀ z : ℂ, AWPIRH.theta z = 0 → z.im = 0 ∧ z.re ≤ 0

theorem nativeRH_iff_thetaZerosNonpositive :
    _root_.RiemannHypothesis ↔ ThetaZerosNonpositive := by
  rw [nativeRH_iff_xiZerosCritical]
  constructor
  · intro h z hz
    have hs : AWPIRH.xi ((1 / 2 : ℂ) + Complex.sqrt z) = 0 := hz
    have hc := h _ hs
    have hr : (Complex.sqrt z).re = 0 := by
      simp only [Complex.add_re] at hc
      norm_num at hc
      linarith
    have hsq := (square_nonpositive_iff_re_zero (Complex.sqrt z)).mpr hr
    simpa only [AWPIRH.complex_sqrt_sq] using hsq
  · intro h s hs
    have hz : AWPIRH.theta ((s - 1 / 2) ^ 2) = 0 := by
      rw [AWPIRH.theta_square]
      have he : (1 / 2 : ℂ) + (s - 1 / 2) = s := by ring
      simpa [AWPIRH.centeredXi, he] using hs
    have hr := (square_nonpositive_iff_re_zero (s - 1 / 2)).mp (h _ hz)
    simp only [Complex.sub_re] at hr
    norm_num at hr
    linarith

def actualLogDerivative (z : ℂ) : ℂ :=
  deriv AWPIRH.theta z / AWPIRH.theta z

/-- The literal complex logarithmic moment, before using its reality. -/
def actualComplexMoment (n : ℕ) : ℂ :=
  ((-1 : ℂ) ^ n * iteratedDeriv n actualLogDerivative 0) / (n.factorial : ℂ)

/-- Its real coordinate.  The calibration's explicit `moment_real` field
identifies this coordinate with the full moment in the paper. -/
def actualMoment (n : ℕ) : ℝ := (actualComplexMoment n).re

def actualKappa : ℝ := actualMoment 0

def actualNormalizedMoment (n : ℕ) : ℝ :=
  actualMoment n / actualKappa ^ (n + 1)

def actualWeight (N j : ℕ) : ℝ :=
  bernsteinWeight actualNormalizedMoment N j

def actualVariation (N : ℕ) : ℝ :=
  rowVariation actualNormalizedMoment N

theorem actualNormalizedMoment_zero (hκ : actualKappa ≠ 0) :
    actualNormalizedMoment 0 = 1 := by
  change actualKappa / actualKappa ^ (0 + 1) = 1
  simpa using div_self hκ

/-- Exact actual-data obligations.  This is infinite analytic data, not a
finite raw witness and not an accepted checker packet.  No constructor is
claimed here.  Repeated nodes are allowed and retain zero multiplicities. -/
structure ActualSpectralCalibration (ι : Type*) where
  node : ι → ℂ
  kappa_pos : 0 < actualKappa
  moment_real : ∀ n, (actualComplexMoment n).im = 0
  node_ne_zero : ∀ i, node i ≠ 0
  norm_summable : Summable (fun i => ‖node i‖)
  power_sums : ∀ n, HasSum (fun i => node i ^ (n + 1))
    (actualNormalizedMoment n : ℂ)
  root_zero : ∀ i, AWPIRH.theta (rootOfNode actualKappa (node i)) = 0
  covers : ∀ z : ℂ, AWPIRH.theta z = 0 →
    ∃ i, z = rootOfNode actualKappa (node i)

namespace ActualSpectralCalibration

variable {ι : Type*} (D : ActualSpectralCalibration ι)

include D in
theorem complexMoment_eq_real (n : ℕ) :
    actualComplexMoment n = (actualMoment n : ℂ) := by
  apply Complex.ext
  · rfl
  · simpa using D.moment_real n

theorem mass_one : HasSum D.node (1 : ℂ) := by
  simpa only [Nat.zero_add, pow_one,
    actualNormalizedMoment_zero (ne_of_gt D.kappa_pos), Complex.ofReal_one]
    using D.power_sums 0

theorem re_mass_one : HasSum (fun i => (D.node i).re) 1 := by
  simpa using Complex.hasSum_re D.mass_one

theorem norm_node_le_total (i : ι) :
    ‖D.node i‖ ≤ ∑' j, ‖D.node j‖ := by
  exact D.norm_summable.le_tsum i (fun j _ => norm_nonneg (D.node j))

theorem bounded : SpectralBounded D.node :=
  spectralBounded_of_norm_bound (tsum_nonneg (fun i => norm_nonneg (D.node i)))
    D.norm_node_le_total

theorem nodes_nonnegative_iff_nativeRH :
    (∀ i, (D.node i).im = 0 ∧ 0 ≤ (D.node i).re) ↔
      _root_.RiemannHypothesis := by
  rw [nativeRH_iff_thetaZerosNonpositive]
  constructor
  · intro hn z hz
    obtain ⟨i, rfl⟩ := D.covers z hz
    exact (rootOfNode_nonpositive_iff D.kappa_pos (D.node_ne_zero i)).mpr (hn i)
  · intro h i
    exact (rootOfNode_nonpositive_iff D.kappa_pos (D.node_ne_zero i)).mp
      (h _ (D.root_zero i))

theorem nodes_segment_iff_nativeRH :
    (∀ i, InUnitSegment (D.node i)) ↔ _root_.RiemannHypothesis := by
  constructor
  · intro h
    exact D.nodes_nonnegative_iff_nativeRH.mp (fun i => ⟨(h i).1, (h i).2.1⟩)
  · intro h
    have hn := D.nodes_nonnegative_iff_nativeRH.mpr h
    intro i
    refine ⟨(hn i).1, (hn i).2, ?_⟩
    have hi := D.re_mass_one.summable.le_tsum i (fun j _ => (hn j).2)
    simpa only [D.re_mass_one.tsum_eq] using hi

theorem radius_one_iff_nativeRH :
    spectralRadius D.node = 1 ↔ _root_.RiemannHypothesis :=
  (spectralRadius_eq_one_iff D.bounded).trans D.nodes_segment_iff_nativeRH

end ActualSpectralCalibration

end RH_HilbertLimit
