import PaperCV282.AffineBorderCylinders
import PaperCV282.FinitePrimeEnvironment

/-! # Affine information and the exact conditional border rate

All events live on the original infinite prime-sign source. The rank is the
effective rank of the linear map, and the overlap is a dimension of complete
linear consequences supported on the border coordinates.
-/
namespace PaperC.V282.AffineCrossoverCylinder

open Affine MeasureTheory ProbabilityTheory InfiniteRademacher InfiniteCylinderTransfer
open AffineBorderLinear AffineBorderCylinders MicroscopicBorderEvents
open scoped NNReal

noncomputable section

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤
local instance instPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
local instance instProbabilityInfinite : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

variable {Y L : ℕ} {W : Type*} [AddCommGroup W] [Module F₂ W]

def cylinderRank (G : SampleSpace Y →ₗ[F₂] W) : ℕ :=
  Module.finrank F₂ (LinearMap.range G)

def cylinderInformation (G : SampleSpace Y →ₗ[F₂] W) : ℝ :=
  (cylinderRank G : ℝ) * Real.log 2

def borderOverlap (G : SampleSpace Y →ₗ[F₂] W) (hLY : L ≤ Y) : ℕ :=
  rowOverlap G (borderProjection hLY)

def borderDeficit (G : SampleSpace Y →ₗ[F₂] W) (hLY : L ≤ Y) : ℕ :=
  Nat.primeCounting L - borderOverlap G hLY

def borderRate (G : SampleSpace Y →ₗ[F₂] W) (hLY : L ≤ Y) : ℝ≥0 :=
  1 / 2 ^ borderDeficit G hLY

/-- The cylinder is measurable in the entire observed prime algebra itself. -/
theorem measurableSet_affineCylinder_fullFY (G : SampleSpace Y →ₗ[F₂] W) (b : W) :
    MeasurableSet[MeasurableSpace.comap (restrictToFinite Y) inferInstance]
      (affineCylinder G b) :=
  (comap_measurable (restrictToFinite Y)) (Set.toFinite {sigma : SampleSpace Y | G sigma=b} |>.measurableSet)

theorem cylinder_probability (G : SampleSpace Y →ₗ[F₂] W) (b : W)
    (hcompat : Compatible G b) :
    infiniteRademacherMeasure.real (affineCylinder G b) = 1 / (2 : ℝ) ^ cylinderRank G := by
  rw [affineCylinder_probability, compatible_probability_inverse_rank G b hcompat]
  simp only [Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat, cylinderRank]

theorem cylinderInformation_nonneg (G : SampleSpace Y →ₗ[F₂] W) :
    0 ≤ cylinderInformation G := by
  unfold cylinderInformation
  exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))

theorem exp_cylinderInformation (G : SampleSpace Y →ₗ[F₂] W) :
    Real.exp (cylinderInformation G) = (2 : ℝ) ^ cylinderRank G := by
  rw [cylinderInformation, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]

theorem exp_information_eq_inverse_probability (G : SampleSpace Y →ₗ[F₂] W) (b : W)
    (hcompat : Compatible G b) :
    Real.exp (cylinderInformation G) =
      (infiniteRademacherMeasure.real (affineCylinder G b))⁻¹ := by
  rw [cylinder_probability G b hcompat, exp_cylinderInformation]
  simp

theorem cylinder_probability_eq_exp_neg_information (G : SampleSpace Y →ₗ[F₂] W) (b : W)
    (hcompat : Compatible G b) :
    infiniteRademacherMeasure.real (affineCylinder G b) = Real.exp (-cylinderInformation G) := by
  rw [Real.exp_neg, exp_cylinderInformation, cylinder_probability G b hcompat]
  exact one_div _

theorem borderOverlap_le_rank (G : SampleSpace Y →ₗ[F₂] W) (hLY : L ≤ Y) :
    borderOverlap G hLY ≤ cylinderRank G := by
  have h := Submodule.finrank_mono
    (inf_le_left : rowSpace G ⊓ rowSpace (borderProjection hLY) ≤ rowSpace G)
  rw [rowSpace_finrank] at h
  exact h

theorem borderOverlap_le_primeCounting (G : SampleSpace Y →ₗ[F₂] W) (hLY : L ≤ Y) :
    borderOverlap G hLY ≤ Nat.primeCounting L := by
  have h := rowOverlap_le_right_rank G (borderProjection hLY)
  rwa [borderProjection_rank] at h

theorem deficit_add_overlap (G : SampleSpace Y →ₗ[F₂] W) (hLY : L ≤ Y) :
    borderDeficit G hLY + borderOverlap G hLY = Nat.primeCounting L :=
  Nat.sub_add_cancel (borderOverlap_le_primeCounting G hLY)

theorem stacked_compatible_implies_compatible (G : SampleSpace Y →ₗ[F₂] W) (b : W)
    (hLY : L ≤ Y) (hstack : Compatible (G.prod (borderProjection hLY)) (b,0)) :
    Compatible G b := by
  obtain ⟨sigma, hsigma⟩ := hstack
  exact ⟨sigma, congrArg Prod.fst hsigma⟩

theorem borderRate_pos (G : SampleSpace Y →ₗ[F₂] W) (hLY : L ≤ Y) :
    0 < borderRate G hLY := by
  unfold borderRate
  positivity

theorem borderRate_coe (G : SampleSpace Y →ₗ[F₂] W) (hLY : L ≤ Y) :
    (borderRate G hLY : ℝ) = 1 / (2 : ℝ) ^ borderDeficit G hLY := by
  simp [borderRate]

theorem conditional_border_probability (G : SampleSpace Y →ₗ[F₂] W) (b : W)
    (hLY : L ≤ Y) (hstack : Compatible (G.prod (borderProjection hLY)) (b,0)) :
    (cond infiniteRademacherMeasure (affineCylinder G b)).real (borderEvent L) =
      (borderRate G hLY : ℝ) := by
  rw [theorem_seven_ten_exact_border_mass hLY G b hstack, borderRate_coe]
  rfl

theorem borderRate_le_one (G : SampleSpace Y →ₗ[F₂] W) (hLY : L ≤ Y) :
    borderRate G hLY ≤ 1 := by
  unfold borderRate
  apply (div_le_one (by positivity)).mpr
  exact one_le_pow₀ (by norm_num)

/-- Information compatible with the border can only increase its probability. -/
theorem raw_border_probability_le_rate (G : SampleSpace Y →ₗ[F₂] W) (hLY : L ≤ Y) :
    infiniteRademacherMeasure.real (borderEvent L) ≤ (borderRate G hLY : ℝ) := by
  rw [equation_seven_one, borderRate_coe]
  rw [inv_pow, ← one_div]
  change 1 / (2 : ℝ) ^ Nat.primeCounting L ≤ 1 / (2 : ℝ) ^ borderDeficit G hLY
  apply one_div_le_one_div_of_le (by positivity)
  exact pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)

theorem affine_border_intersection_probability_pos (G : SampleSpace Y →ₗ[F₂] W) (b : W)
    (hLY : L ≤ Y) (hstack : Compatible (G.prod (borderProjection hLY)) (b,0)) :
    0 < infiniteRademacherMeasure.real (affineCylinder G b ∩ borderEvent L) := by
  rw [affineCylinder_inter_border hLY]
  exact affineCylinder_probability_pos _ _ hstack

end
end PaperC.V282.AffineCrossoverCylinder
