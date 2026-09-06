import PaperCV282.ExactMarkedClusterTarget
import PaperCV282.ExactMarkedInfinite
import PaperCV282.ExactMarkedSourceTail

/-!
# The true truncated source cluster count and the geometric compound target

The signed marked field is aggregated only after its complete law has been
formed. This proves the equality with the literal unsigned exact-run count.
-/

namespace PaperC.V282.ExactMarkedClusterTransfer

open MeasureTheory ProbabilityTheory InfiniteRademacher InfiniteCylinderTransfer
open InfiniteExactLengthProbabilityTransfer
open ExactMarkedModel ExactMarkedInfinite ExactMarkedSourceTail ExactMarkedClusterTarget
open ExactMarkedFieldTransfer GeometricClusterTarget AllStartSoftPoisson
open InfiniteMassCoupling FiniteFieldTotalVariation FiniteFieldPoissonCoupling MassPushforward
open scoped BigOperators NNReal ENNReal

noncomputable section

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

local instance instProbabilityInfiniteRademacher : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

theorem weightedSignedCount_infiniteField_eq (N L E : ℕ) (omega : InfiniteSample) :
    weightedSignedCount N E (infiniteSignedField N L E (dyadicBlock N) omega) =
      truncatedExactClusterCount N L E omega := by
  classical
  have hfield (i : SignedMarkIndex N E) :
      infiniteSignedField N L E (dyadicBlock N) omega i =
        signedMarkValue (infiniteValueBit omega) i.1.val L i.2.1.val i.2.2 := by
    simp only [infiniteSignedField, signedMarkValue, i.1.property, true_and]
  unfold weightedSignedCount
  simp_rw [hfield]
  change (∑ i : {x : ℕ // x ∈ dyadicBlock N} × (Fin (E + 1) × F₂), _) = _
  simp only [Fintype.sum_prod_type, ← Finset.mul_sum, sum_signedMarkValue]
  rw [Finset.sum_coe_sort (dyadicBlock N)
    (fun x => ∑ e : Fin (E + 1), (e.val + 1) * exactMarkValue (infiniteValueBit omega) x L e.val)]
  unfold truncatedExactClusterCount
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro e he
  simp [exactMarkValue, mul_ite]

theorem measurable_infiniteSignedField (N L E : ℕ) (mask : Finset ℕ) :
    Measurable (infiniteSignedField N L E mask) := by
  have heq : infiniteSignedField N L E mask =
      cylinderSignedField (dyadicCutoff N (L + E + 1)) N L E mask ∘
        restrictToFinite (dyadicCutoff N (L + E + 1)) := by
    funext omega
    exact (cylinderSignedField_restrict_eq (le_refl _) mask omega).symm
  rw [heq]
  exact (measurable_of_countable _).comp (measurable_restrictToFinite _)

/-- The aggregated mass is the actual source probability of the truncated count. -/
theorem pushforward_infinite_signed_cluster_eq (N L E : ℕ) :
    pushforwardMass (weightedSignedCount N E) (infiniteSignedLaw N L E (dyadicBlock N)) =
      observableLaw infiniteRademacherMeasure (truncatedExactClusterCount N L E) := by
  funext n
  rw [pushforwardMass_eq_restricted]
  have h : (∑' k, if weightedSignedCount N E k = n then
      infiniteSignedLaw N L E (dyadicBlock N) k else 0) =
        infiniteRademacherMeasure.real
          (infiniteSignedField N L E (dyadicBlock N) ⁻¹' {k | weightedSignedCount N E k = n}) := by
    simpa only [Set.mem_setOf_eq, observableLaw, infiniteSignedLaw, Measure.real] using
      restricted_observableLaw_eq_event infiniteRademacherMeasure
        (measurable_infiniteSignedField N L E (dyadicBlock N))
        {k | weightedSignedCount N E k = n}
  calc
    _ = infiniteRademacherMeasure.real
        (infiniteSignedField N L E (dyadicBlock N) ⁻¹' {k | weightedSignedCount N E k = n}) := by
      convert h using 1
      congr 1
      funext k
      split_ifs <;> rfl
    _ = _ := ?_
  unfold observableLaw
  congr 1
  ext omega
  simp only [Set.mem_preimage, Set.mem_setOf_eq, weightedSignedCount_infiniteField_eq]

/-- No assumed arithmetic cost: the actual signed field distance plus the target tail suffices. -/
theorem truncated_source_to_compound_tv_le (N L E : ℕ) :
    massTotalVariation (observableLaw infiniteRademacherMeasure (truncatedExactClusterCount N L E))
      (fun n => (geometricCompoundMeasure (fullRate N L)).real {n}) ≤
        massTotalVariation (infiniteSignedLaw N L E (dyadicBlock N))
          (poissonFieldMass (allSignedRates N L E (dyadicBlock N))) +
            (fullRate N L : ℝ) / (2 : ℝ) ^ (E + 1) := by
  rw [← pushforward_infinite_signed_cluster_eq]
  exact weighted_field_to_compound_tv_le N L E _ (hasSum_infiniteSignedLaw N L E _)
    (infiniteSignedLaw_nonneg N L E _)

end
end PaperC.V282.ExactMarkedClusterTransfer
