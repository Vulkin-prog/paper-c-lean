import PaperCV282.AffineBorderCylinders
import PaperC.Probability.SectionTwelveMoments

/-! # Arbitrary affine Fourier identities on the actual infinite source

There is no compatibility assumption. The character sum, its zero-or-power
normalization and its absolute discrepancy are all transported from finite
Fourier inversion to the same infinite prime-sign product measure.
-/
namespace PaperC.V282.ClosureAlgebraFourier

open Affine AffineBorderCylinders InfiniteRademacher SectionTwelveMoments
open scoped BigOperators

noncomputable section

local instance instPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

variable {M : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The exact normalized affine mass, including incompatible systems. -/
theorem affine_probability_eq_eta (A : SampleSpace M →ₗ[F₂] (ι → F₂)) (b : ι → F₂) :
    infiniteRademacherMeasure.real (affineCylinder A b) =
      (relationEta A b : ℝ) * 2 ^ relationRho A / 2 ^ Fintype.card ι := by
  rw [affineCylinder_probability, uniformSolutionProbability_eq_eta_mul_two_pow_rho_div]
  push_cast
  rfl

/-- Fourier inversion as a literal sum over the relation space. -/
theorem affine_fourier_identity (A : SampleSpace M →ₗ[F₂] (ι → F₂)) (b : ι → F₂) :
    (2 : ℝ) ^ Fintype.card ι * infiniteRademacherMeasure.real (affineCylinder A b) =
      (relationSignedSum A b : ℝ) := by
  rw [affine_probability_eq_eta, relationSignedSum_eq_eta_mul_two_pow_rho]
  push_cast
  field_simp

local instance instRelationFintype (A : SampleSpace M →ₗ[F₂] (ι → F₂)) :
    Fintype (RelationSpace A) := Fintype.ofFinite _

/-- The relation character is evaluated only on the actual relation subtype. -/
theorem affine_fourier_relation_sum (A : SampleSpace M →ₗ[F₂] (ι → F₂)) (b : ι → F₂) :
    (2 : ℝ) ^ Fintype.card ι * infiniteRademacherMeasure.real (affineCylinder A b) =
      ∑ u : RelationSpace A, (binarySign (relationCharacter A b u) : ℝ) := by
  classical
  rw [affine_fourier_identity, relationSignedSum_eq_sum_relationCharacter]
  push_cast
  rfl

/-- The displayed character consequence, with the stronger absolute value. -/
theorem affine_normalized_discrepancy_le (A : SampleSpace M →ₗ[F₂] (ι → F₂))
    (b : ι → F₂) :
    |(2 : ℝ) ^ Fintype.card ι * infiniteRademacherMeasure.real (affineCylinder A b) - 1| ≤
      (2 : ℝ) ^ relationRho A - 1 := by
  rw [affine_fourier_identity, relationSignedSum_eq_eta_mul_two_pow_rho]
  exact_mod_cast abs_eta_mul_two_pow_rho_sub_one_le A b

end
end PaperC.V282.ClosureAlgebraFourier
