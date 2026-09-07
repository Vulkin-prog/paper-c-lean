import PaperCV282.AffineCrossoverCylinder
import PaperCV282.RareConditioningRates

/-! # Exact scalar identities connecting affine ranks to conditioning budgets

The logarithmic information is the information of the actual infinite
event. The border gain is exactly two to the overlap dimension.
-/
namespace PaperC.V282.AffineCrossoverCylinderInformation

open Affine MeasureTheory InfiniteRademacher AffineBorderCylinders AffineCrossoverCylinder
open RareConditioningRates MicroscopicBorderEvents
open scoped NNReal

noncomputable section

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤
local instance instPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

variable {Y L : ℕ} {W : Type*} [AddCommGroup W] [Module F₂ W]

/-- The actual negative log-probability equals rank times log two. -/
theorem eventInformation_eq_cylinderInformation (G : SampleSpace Y →ₗ[F₂] W) (b : W)
    (hcompat : Compatible G b) :
    eventInformation (affineCylinder G b) = cylinderInformation G := by
  rw [eventInformation, cylinder_probability_eq_exp_neg_information G b hcompat, Real.log_exp,
    neg_neg]

theorem borderDeficit_cast (G : SampleSpace Y →ₗ[F₂] W) (hLY : L ≤ Y) :
    (borderDeficit G hLY : ℝ) = (Nat.primeCounting L : ℝ) - (borderOverlap G hLY : ℝ) := by
  exact Nat.cast_sub (borderOverlap_le_primeCounting G hLY)

theorem borderRate_eq_exp_deficit (G : SampleSpace Y →ₗ[F₂] W) (hLY : L ≤ Y) :
    (borderRate G hLY : ℝ) = Real.exp (-(borderDeficit G hLY : ℝ)*Real.log 2) := by
  rw [borderRate_coe, neg_mul, Real.exp_neg, Real.exp_nat_mul,
    Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  exact one_div _

theorem log_borderRate (G : SampleSpace Y →ₗ[F₂] W) (hLY : L ≤ Y) :
    Real.log (borderRate G hLY : ℝ) = -(borderDeficit G hLY : ℝ)*Real.log 2 := by
  rw [borderRate_eq_exp_deficit, Real.log_exp]

/-- Overlap is exactly the factor by which the compatible affine condition increases the border mass. -/
theorem borderRate_eq_raw_mul_overlap (G : SampleSpace Y →ₗ[F₂] W) (hLY : L ≤ Y) :
    (borderRate G hLY : ℝ) = infiniteRademacherMeasure.real (borderEvent L) *
      (2 : ℝ)^borderOverlap G hLY := by
  rw [equation_seven_one, inv_pow, borderRate_coe,
    ← deficit_add_overlap G hLY, pow_add]
  field_simp

end
end PaperC.V282.AffineCrossoverCylinderInformation
