import RH_HilbertLimit.SpectralTail

/-!
# Unit phases for the affine spectral factors

Source-only candidate; no local Lean compilation has been performed.

The pointwise construction aligns `1 - q` and `x * q` using two unit complex
factors. It covers `q = 0` and `q = 1` as well as the nondegenerate case, so
no division or additional nonvanishing premise is needed. Above ellipse
radius one, any maximizing phase differs from one, making the affine map
injective in its node argument.

The family endpoint combines this geometry with the existing, proved
maximum-attainment theorem in `SpectralTail`. It supplies phase data only;
the finite grouped expansion and its tail estimate are separate obligations.
In particular, it does not assert that every distinct node on the same
ellipse has a strictly smaller affine norm.

APIs checked against Mathlib v4.33.0 source:
* `Complex.exists_norm_mul_eq_self`, `Complex.exists_norm_eq_mul_self` in
  `Mathlib/Analysis/Complex/Basic.lean`;
* `Complex.norm_of_nonneg` in `Mathlib/Analysis/Complex/Norm.lean`;
* `mul_left_cancel₀` in `Mathlib/Algebra/GroupWithZero/Defs.lean`.
-/

noncomputable section

namespace RH_HilbertLimit.SpectralPhase

/-- A unit phase attains the existing affine upper bound at any chosen node. -/
theorem exists_unit_phase (q : ℂ) :
    ∃ x : ℂ, ‖x‖ = 1 ∧ ‖1 + (x - 1) * q‖ = ellipseRadius q := by
  obtain ⟨a, ha, haq⟩ := Complex.exists_norm_mul_eq_self (1 - q)
  obtain ⟨b, hb, hbq⟩ := Complex.exists_norm_eq_mul_self q
  refine ⟨a * b, ?_, ?_⟩
  · rw [norm_mul, ha, hb, one_mul]
  · have hfactor :
        1 + (a * b - 1) * q = a * ((‖1 - q‖ + ‖q‖ : ℝ) : ℂ) := by
      rw [Complex.ofReal_add, mul_add, haq, hbq]
      ring
    rw [hfactor, norm_mul, ha, one_mul,
      Complex.norm_of_nonneg (add_nonneg (norm_nonneg (1 - q)) (norm_nonneg q))]
    exact add_comm _ _

/-- Above radius one, the maximizing phase cannot be the constant phase one. -/
theorem phase_ne_one {q x : ℂ} (hR : 1 < ellipseRadius q)
    (hmax : ‖1 + (x - 1) * q‖ = ellipseRadius q) : x ≠ 1 := by
  intro hx
  have hunit : ellipseRadius q = 1 := by simpa [hx] using hmax.symm
  exact (ne_of_gt hR) hunit

/-- A nontrivial phase preserves distinct node values under the affine map. -/
theorem affine_injective {x : ℂ} (hx : x ≠ 1) :
    Function.Injective (fun q : ℂ => 1 + (x - 1) * q) := by
  intro q r hqr
  apply mul_left_cancel₀ (sub_ne_zero.mpr hx)
  exact add_left_cancel hqr

/-- Rate collisions for a nontrivial phase are exactly node collisions. -/
theorem affine_eq_iff {x q r : ℂ} (hx : x ≠ 1) :
    1 + (x - 1) * q = 1 + (x - 1) * r ↔ q = r := by
  constructor
  · intro hqr
    exact affine_injective hx hqr
  · intro hqr
    rw [hqr]

/-- A strict ellipse-radius bound remains strict after choosing any disk phase. -/
theorem norm_affine_lt_of_radius_lt {q x : ℂ} {R : ℝ}
    (hx : ‖x‖ ≤ 1) (hq : ellipseRadius q < R) :
    ‖1 + (x - 1) * q‖ < R :=
  (norm_affine_le_ellipseRadius q x hx).trans_lt hq

/-- Interior disk phases give a strict pointwise bound at every nonzero node. -/
theorem norm_affine_lt_ellipseRadius_of_norm_lt_one {q x : ℂ}
    (hq : q ≠ 0) (hx : ‖x‖ < 1) :
    ‖1 + (x - 1) * q‖ < ellipseRadius q := by
  calc
    ‖1 + (x - 1) * q‖ = ‖(1 - q) + x * q‖ := by congr 1; ring
    _ ≤ ‖1 - q‖ + ‖x * q‖ := norm_add_le _ _
    _ = ‖1 - q‖ + ‖x‖ * ‖q‖ := by rw [norm_mul]
    _ < ‖1 - q‖ + 1 * ‖q‖ :=
      add_lt_add_right (mul_lt_mul_of_pos_right hx (norm_pos_iff.mpr hq)) _
    _ = ellipseRadius q := by dsimp [ellipseRadius]; ring

/-- Summability and the existing boundedness premise supply a node and a
nontrivial unit phase attaining the full spectral radius. All other affine
factors retain the same radius as an upper bound. -/
theorem exists_dominant_phase {ι : Type*} (q : ι → ℂ)
    (hq : Summable (fun i => ‖q i‖)) (hb : SpectralBounded q)
    (hR : 1 < spectralRadius q) :
    ∃ (i : ι) (x : ℂ),
      ‖x‖ = 1 ∧ x ≠ 1 ∧ ellipseRadius (q i) = spectralRadius q ∧
      ‖1 + (x - 1) * q i‖ = spectralRadius q ∧
      ∀ j : ι, ‖1 + (x - 1) * q j‖ ≤ spectralRadius q := by
  obtain ⟨i, hi⟩ := SpectralTail.spectralRadius_attained q hq hb hR
  obtain ⟨x, hx, hmax⟩ := exists_unit_phase (q i)
  have hRi : 1 < ellipseRadius (q i) := by rw [hi]; exact hR
  refine ⟨i, x, hx, phase_ne_one hRi hmax, hi, hmax.trans hi, ?_⟩
  intro j
  exact (norm_affine_le_ellipseRadius (q j) x hx.le).trans
    (ellipseRadius_le_spectralRadius hb j)

end RH_HilbertLimit.SpectralPhase

namespace RH_HilbertLimit.ActualSpectralCalibration

/-- Calibrated specialization. This adds no phase-attainment assumption to
`ActualSpectralCalibration`; it uses only its existing fields and `R > 1`. -/
theorem exists_dominant_phase {ι : Type*} (D : ActualSpectralCalibration ι)
    (hR : 1 < spectralRadius D.node) :
    ∃ (i : ι) (x : ℂ),
      ‖x‖ = 1 ∧ x ≠ 1 ∧ ellipseRadius (D.node i) = spectralRadius D.node ∧
      ‖1 + (x - 1) * D.node i‖ = spectralRadius D.node ∧
      ∀ j : ι, ‖1 + (x - 1) * D.node j‖ ≤ spectralRadius D.node :=
  SpectralPhase.exists_dominant_phase D.node D.norm_summable D.bounded hR

end RH_HilbertLimit.ActualSpectralCalibration
