import PaperCV282.ExactMarkedFieldTransfer
import PaperCV282.AllStartSoftPoisson
import PaperCV282.ExactMarkedTailTarget

/-!
# Aggregation of the actual signed exact-mark target

All site, excess and sign coordinates are retained until the weighted map.
The factor two from the signs and the number of dyadic sites give the base
run intensity N/2^L, independently of the excess cutoff.
-/

namespace PaperC.V282.ExactMarkedClusterTarget

open MeasureTheory ProbabilityTheory ExactMarkedModel ExactMarkedFieldTransfer
open AllStartSoftPoisson PoissonFieldMeasure CompoundPoissonTransform GeometricClusterTruncation
open GeometricClusterTarget ExactMarkedTailTarget FiniteFieldPoissonCoupling
open MassPushforward FiniteFieldTotalVariation
open scoped BigOperators NNReal ENNReal

noncomputable section

def weightedSignedCount (N E : ℕ) (k : SignedMarkIndex N E → ℕ) : ℕ :=
  ∑ i, (i.2.1.val + 1) * k i

theorem full_rate_signed_rate_identity (N L E : ℕ) (e : Fin (E + 1)) :
    (N : ℝ) * 2 * (signedMarkRate L e.val : ℝ) =
      (geometricCoordinateRates (fullRate N L) E e : ℝ) := by
  change (N : ℝ) * 2 * (1 / (2 : ℝ) ^ (L + e.val + 2)) =
    ((N : ℝ) / (2 : ℝ) ^ L) / (2 : ℝ) ^ (e.val + 1)
  rw [show L + e.val + 2 = L + (e.val + 1) + 1 by omega, pow_add, pow_add]
  norm_num
  field_simp

theorem signed_target_exponent_eq (N L E : ℕ) (z : ℂ) :
    (∑ i : SignedMarkIndex N E,
      (allSignedRates N L E (dyadicBlock N) i : ℂ) * (z ^ (i.2.1.val + 1) - 1)) =
      ∑ e : Fin (E + 1), (geometricCoordinateRates (fullRate N L) E e : ℂ) *
        (z ^ (e.val + 1) - 1) := by
  classical
  have hall (i : SignedMarkIndex N E) :
      allSignedRates N L E (dyadicBlock N) i = signedMarkRate L i.2.1.val := by
    unfold allSignedRates
    exact if_pos i.1.property
  simp_rw [hall]
  change (∑ i : {x : ℕ // x ∈ dyadicBlock N} × (Fin (E + 1) × F₂), _) = _
  simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
    ZMod.card, nsmul_eq_mul, Fintype.card_coe, TouchingPairs.card_dyadicBlock]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  have hid := congrArg (fun x : ℝ => (x : ℂ)) (full_rate_signed_rate_identity N L E e)
  push_cast at hid
  rw [← hid]
  ring

/-- Exact law of the weighted image of the whole signed Poisson field. -/
theorem hasLaw_weighted_signed_target (N L E : ℕ) :
    HasLaw (weightedSignedCount N E) (weightedGeometricPoissonMeasure (fullRate N L) E)
      (fieldMeasure (allSignedRates N L E (dyadicBlock N))) := by
  refine ⟨(measurable_of_countable _).aemeasurable, ?_⟩
  letI : IsProbabilityMeasure ((fieldMeasure (allSignedRates N L E (dyadicBlock N))).map
      (weightedSignedCount N E)) :=
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
  apply natural_law_eq_of_unit_transforms
  intro z hz
  rw [integral_map (measurable_of_countable _).aemeasurable
    (measurable_of_countable (fun n : ℕ => z ^ n)).aestronglyMeasurable]
  change (∫ k, z ^ (∑ i, (i.2.1.val + 1) * k i)
    ∂fieldMeasure (allSignedRates N L E (dyadicBlock N))) = _
  rw [weighted_poisson_complex_transform, signed_target_exponent_eq,
    weightedGeometricPoissonMeasure,
    integral_map (measurable_of_countable _).aemeasurable
      (measurable_of_countable (fun n : ℕ => z ^ n)).aestronglyMeasurable,
    weighted_poisson_complex_transform]

theorem pushforward_signed_target_eq (N L E : ℕ) :
    pushforwardMass (weightedSignedCount N E)
      (poissonFieldMass (allSignedRates N L E (dyadicBlock N))) =
        fun n => (weightedGeometricPoissonMeasure (fullRate N L) E).real {n} :=
  pushforward_poissonFieldMass_of_hasLaw _ _ _ (hasLaw_weighted_signed_target N L E)

/-- The weighted signed target has the full compound target within the exact geometric tail budget. -/
theorem signed_target_to_compound_tv_le (N L E : ℕ) :
    massTotalVariation
      (fun n => (geometricCompoundMeasure (fullRate N L)).real {n})
      (pushforwardMass (weightedSignedCount N E)
        (poissonFieldMass (allSignedRates N L E (dyadicBlock N)))) ≤
      (fullRate N L : ℝ) / (2 : ℝ) ^ (E + 1) := by
  rw [pushforward_signed_target_eq]
  exact compound_target_truncation_tv_le _ _

/-- Every genuine field law contracts to the compound target with only the geometric tail cost. -/
theorem weighted_field_to_compound_tv_le (N L E : ℕ)
    (p : (SignedMarkIndex N E → ℕ) → ℝ) (hp : HasSum p 1) (hp0 : ∀ k, 0 ≤ p k) :
    massTotalVariation (pushforwardMass (weightedSignedCount N E) p)
      (fun n => (geometricCompoundMeasure (fullRate N L)).real {n}) ≤
        massTotalVariation p (poissonFieldMass (allSignedRates N L E (dyadicBlock N))) +
          (fullRate N L : ℝ) / (2 : ℝ) ^ (E + 1) := by
  have hq := hasSum_poissonFieldMass (allSignedRates N L E (dyadicBlock N))
  have hq0 := poissonFieldMass_nonneg (allSignedRates N L E (dyadicBlock N))
  have hr : HasSum (fun n => (geometricCompoundMeasure (fullRate N L)).real {n}) 1 := by
    exact InfiniteMassCoupling.hasSum_observableLaw
      (geometricCompoundMeasure (fullRate N L)) measurable_id
  have htri := massTotalVariation_triangle
    (hasSum_pushforwardMass (weightedSignedCount N E) hp).summable
    (hasSum_pushforwardMass (weightedSignedCount N E) hq).summable hr.summable
    (pushforwardMass_nonneg (weightedSignedCount N E) hp0)
    (pushforwardMass_nonneg (weightedSignedCount N E) hq0)
    (fun _ => measureReal_nonneg)
  have hcontr := massTotalVariation_pushforward_le (weightedSignedCount N E) hp hq hp0 hq0
  have htail := signed_target_to_compound_tv_le N L E
  rw [massTotalVariation_comm] at htail
  exact htri.trans (add_le_add hcontr htail)

end
end PaperC.V282.ExactMarkedClusterTarget
