import RH_HilbertLimit.SpectralPhase
import RH_HilbertLimit.SpectralGenerating
import RH_HilbertLimit.Main
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.EquivFin

/-!
# Finite dominant extraction from a summable calibrated spectrum

Candidate for the user's native Lean 4.33.0 compiler. No Lean process was
executed during preparation. The finite dominant set, gap and multiplicities
are constructed below; none is supplied as an additional analytic premise.
This is analytic proof data, not a finite terminating-checker certificate.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace RH_HilbertLimit.SpectralExtraction

/-- A finite family of strict bounds has a common strict bound, including
an already chosen lower threshold. -/
theorem exists_common_strict_bound {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    {a R : ℝ} (ha : a < R) (hf : ∀ i ∈ s, f i < R) :
    ∃ r : ℝ, a ≤ r ∧ r < R ∧ ∀ i ∈ s, f i ≤ r := by
  classical
  revert hf
  refine Finset.induction_on s ?_ ?_
  · intro _
    exact ⟨a, le_rfl, ha, by simp⟩
  · intro i s hi ih hf
    obtain ⟨r, har, hrR, hs⟩ := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    refine ⟨max r (f i), har.trans (le_max_left _ _),
      max_lt_iff.mpr ⟨hrR, hf i (Finset.mem_insert_self _ _)⟩, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact le_max_right _ _
    · exact (hs j hj).trans (le_max_left _ _)

/-- Repeated nodes contribute their full multiplicity to the coefficient. -/
def groupedCoefficient {ι : Type*} (q : ι → ℂ) (s : Finset ι) (z : ℂ) : ℂ := by
  classical
  exact ∑ i ∈ s with q i = z, q i

theorem groupedCoefficient_eq_card_mul {ι : Type*}
    (q : ι → ℂ) (s : Finset ι) (z : ℂ) :
    groupedCoefficient q s z = ((s.filter (fun i => q i = z)).card : ℂ) * z := by
  classical
  unfold groupedCoefficient
  calc
    (∑ i ∈ s with q i = z, q i) = ∑ i ∈ s with q i = z, z := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (Finset.mem_filter.mp hi).2
    _ = ((s.filter (fun i => q i = z)).card : ℂ) * z := by
      simp only [Finset.sum_const, nsmul_eq_mul]

/-- A nonzero node in the finite image cannot disappear by grouping. -/
theorem groupedCoefficient_ne_zero {ι : Type*}
    (q : ι → ℂ) (s : Finset ι) {z : ℂ}
    (hz : z ∈ s.image q) (hz0 : z ≠ 0) :
    groupedCoefficient q s z ≠ 0 := by
  classical
  obtain ⟨i, hi, hiz⟩ := Finset.mem_image.mp hz
  have hcard : 0 < (s.filter (fun j => q j = z)).card :=
    Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hiz⟩⟩
  have hcard0 : ((s.filter (fun j => q j = z)).card : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hcard)
  rw [groupedCoefficient_eq_card_mul]
  exact mul_ne_zero hcard0 hz0

/-- Exact finite regrouping, retaining every repeated-node coefficient. -/
theorem grouped_exponential_sum {ι : Type*}
    (q : ι → ℂ) (s : Finset ι) (rate : ℂ → ℂ) (N : ℕ) :
    (∑ z ∈ s.image q, groupedCoefficient q s z * rate z ^ N) =
      ∑ i ∈ s, q i * rate (q i) ^ N := by
  classical
  have hmaps : ∀ i ∈ s, q i ∈ s.image q :=
    fun i hi => Finset.mem_image_of_mem q hi
  calc
    _ = ∑ z ∈ s.image q, ∑ i ∈ s with q i = z, q i * rate (q i) ^ N := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [groupedCoefficient, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ = _ := Finset.sum_fiberwise_of_maps_to hmaps _

/-- All indices attaining the maximal affine radius form a finite nonempty
head. Its entire complement, including the finite nondominant part, has a
strictly smaller common rate. -/
theorem finite_dominant_indices {ι : Type*} (D : ActualSpectralCalibration ι)
    {x : ℂ} (hx : ‖x‖ ≤ 1) (hR : 1 < spectralRadius D.node)
    (hatt : ∃ i : ι, ‖1 + (x - 1) * D.node i‖ = spectralRadius D.node) :
    ∃ s : Finset ι, s.Nonempty ∧
      (∀ i ∈ s, ‖1 + (x - 1) * D.node i‖ = spectralRadius D.node) ∧
      ∃ r : ℝ, 1 ≤ r ∧ r < spectralRadius D.node ∧
        ∀ i, i ∉ s → ‖1 + (x - 1) * D.node i‖ ≤ r := by
  classical
  obtain ⟨a, ha, haR, S, hS⟩ := D.finite_tail_below_radius hR
  obtain ⟨i₀, hi₀⟩ := hatt
  have hupper (i : ι) : ‖1 + (x - 1) * D.node i‖ ≤ spectralRadius D.node :=
    (norm_affine_le_ellipseRadius (D.node i) x hx).trans
      (ellipseRadius_le_spectralRadius D.bounded i)
  have hi₀S : i₀ ∈ S := by
    by_contra hi
    have hsmall := (norm_affine_le_ellipseRadius (D.node i₀) x hx).trans_lt (hS i₀ hi)
    rw [hi₀] at hsmall
    exact (not_lt_of_ge haR.le) hsmall
  let H : Finset ι := S.filter (fun i => ‖1 + (x - 1) * D.node i‖ = spectralRadius D.node)
  let L : Finset ι := S.filter (fun i => ‖1 + (x - 1) * D.node i‖ ≠ spectralRadius D.node)
  have hL : ∀ i ∈ L, ‖1 + (x - 1) * D.node i‖ < spectralRadius D.node := by
    intro i hi
    exact lt_of_le_of_ne (hupper i) (Finset.mem_filter.mp hi).2
  obtain ⟨r, har, hrR, hr⟩ := exists_common_strict_bound L
    (fun i => ‖1 + (x - 1) * D.node i‖) haR hL
  refine ⟨H, ⟨i₀, Finset.mem_filter.mpr ⟨hi₀S, hi₀⟩⟩,
    (fun i hi => (Finset.mem_filter.mp hi).2), r, ha.le.trans har, hrR, ?_⟩
  intro i hi
  by_cases hiS : i ∈ S
  · have hne : ‖1 + (x - 1) * D.node i‖ ≠ spectralRadius D.node := by
      intro he
      exact hi (Finset.mem_filter.mpr ⟨hiS, he⟩)
    exact hr i (Finset.mem_filter.mpr ⟨hiS, hne⟩)
  · exact ((norm_affine_le_ellipseRadius (D.node i) x hx).trans_lt (hS i hiS)).le.trans har

end RH_HilbertLimit.SpectralExtraction

namespace RH_HilbertLimit.ActualSpectralCalibration

open SpectralExtraction

/-- Dominant extraction is derived from the calibration, including finite
localization, phase choice, multiplicity grouping and the strict remainder.
No finite-support or dominant-extraction hypothesis is introduced. -/
theorem dominantExtraction {ι : Type*} (D : ActualSpectralCalibration ι) :
    DominantExtraction D := by
  classical
  intro hR
  obtain ⟨i₀, x, hx, hx1, hi₀radius, hi₀, hupper⟩ := D.exists_dominant_phase hR
  obtain ⟨H, hH, hmax, r, hr1, hrR, hr⟩ :=
    finite_dominant_indices D hx.le hR ⟨i₀, hi₀⟩
  let Z : Finset ℂ := H.image D.node
  let e : Fin Z.card ≃ Z := Z.equivFin.symm
  let rate : Fin Z.card → ℂ := fun j => 1 + (x - 1) * (e j).val
  let coefficient : Fin Z.card → ℂ := fun j => groupedCoefficient D.node H (e j).val
  obtain ⟨i₁, hi₁⟩ := hH
  have hnodeZ : D.node i₁ ∈ Z := Finset.mem_image_of_mem D.node hi₁
  let j₀ : Fin Z.card := e.symm ⟨D.node i₁, hnodeZ⟩
  have hj₀ : (e j₀).val = D.node i₁ := by
    exact congrArg Subtype.val (e.apply_symm_apply ⟨D.node i₁, hnodeZ⟩)
  have hrate : Function.Injective rate := by
    intro j k hjk
    apply e.injective
    apply Subtype.ext
    exact SpectralPhase.affine_injective hx1 hjk
  have hcoefficient : coefficient j₀ ≠ 0 := by
    change groupedCoefficient D.node H (e j₀).val ≠ 0
    rw [hj₀]
    exact groupedCoefficient_ne_zero D.node H hnodeZ (D.node_ne_zero i₁)
  have hradius : ∀ j, ‖rate j‖ = spectralRadius D.node := by
    intro j
    obtain ⟨i, hi, hie⟩ := Finset.mem_image.mp (e j).property
    change ‖1 + (x - 1) * (e j).val‖ = spectralRadius D.node
    rw [← hie]
    exact hmax i hi
  have hgroup (N : ℕ) : finiteExponentialSum rate coefficient N =
      ∑ i ∈ H, D.node i * (1 + (x - 1) * D.node i) ^ N := by
    calc
      _ = ∑ z : Z, groupedCoefficient D.node H z.val *
          (1 + (x - 1) * z.val) ^ N := by
        exact Fintype.sum_equiv e
          (fun j : Fin Z.card => coefficient j * rate j ^ N)
          (fun z : Z => groupedCoefficient D.node H z.val *
            (1 + (x - 1) * z.val) ^ N) (fun j => rfl)
      _ = ∑ z ∈ Z, groupedCoefficient D.node H z *
          (1 + (x - 1) * z) ^ N := by
        exact Finset.sum_finset_coe
          (fun z : ℂ => groupedCoefficient D.node H z * (1 + (x - 1) * z) ^ N) Z
      _ = _ := grouped_exponential_sum D.node H (fun z => 1 + (x - 1) * z) N
  refine ⟨{
    width := Z.card
    rate := rate
    coefficient := coefficient
    distinguished := j₀
    rates_injective := hrate
    coefficient_ne_zero := hcoefficient
    rates_radius := hradius
    phase := x
    phase_norm := hx.le
    tail := spectralRemainder D.node H x
    tailConstant := ∑' i, ‖D.node i‖
    tailRate := r
    tailConstant_nonneg := tsum_nonneg (fun i => norm_nonneg (D.node i))
    tailRate_one_le := hr1
    tailRate_lt := hrR
    expansion := ?_
    tail_bound := ?_
  }⟩
  · intro N
    rw [D.rowGenerating_eq_sum_add_remainder H N x, ← hgroup N]
  · intro N
    exact D.norm_remainder_le H x r (zero_le_one.trans hr1) hr N

end RH_HilbertLimit.ActualSpectralCalibration
