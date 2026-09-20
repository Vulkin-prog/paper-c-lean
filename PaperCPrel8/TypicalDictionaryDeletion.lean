import PaperCPrel8.DictionaryAverage
import PaperCV282.DictionaryFieldSecondCost

/-! # Exact dictionary-averaged deletion on each prime fibre

Even a bad arithmetic window has exactly one word. Independent uniform
dictionary selection includes it with probability m/2^B on every fibre.
-/
namespace PaperC.Prel8.TypicalDictionaryDeletion
open PaperC.Affine PaperC.ConditionalStartProbability PaperC.ConditionalAGGInstantiation
open PaperC.ArratiaGoldsteinGordonInput PaperC.SectionTwelveMoments PaperC.SectionThirteenFiniteBound
open PaperC.V282.DictionaryFieldModel PaperC.V282.DictionaryFieldTransfer
open PaperC.V282.DictionaryFieldSecondCost PaperC.V282.DictionaryMarginalCap
open PaperC.V282.MaskedArithmeticGeometry PaperC.V282.PrescribedValues
open PaperC.V282.WindowValues PaperC.V282.InfiniteWordTransfer
open PaperC.V282.RandomDictionary PaperC.Prel8.DictionarySamplingBounds
open scoped BigOperators
noncomputable section
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- Literal real source mass removed by the fixed site mask. -/
def deletedMass (N L Y : ℕ) (mask : Finset ℕ) (W : Finset (Fin (L+1) → PaperC.F₂))
    (sigma : SmallSample (dyadicCutoff N L) Y) : ℝ :=
  ∑ i : DictionaryIndex N L W, if i.1.val ∈ fullBadMask N L Y mask then
    marginal (largeUniformPMF (dyadicCutoff N L) Y) (conditionedWordIndicator N L Y W sigma) i else 0

/-- Summing word labels is the probability of membership in the selected dictionary. -/
theorem deletedMass_eq (N L Y : ℕ) (mask : Finset ℕ) (hmask : mask ⊆ dyadicBlock N)
    (W : Finset (Fin (L+1) → PaperC.F₂)) (sigma : SmallSample (dyadicCutoff N L) Y) :
    deletedMass N L Y mask W sigma =
      ∑ x ∈ fullBadMask N L Y mask, eventProbability (largeUniformPMF (dyadicCutoff N L) Y)
        (fun eta => valueSystem (dyadicCutoff N L) (vertex x (L+1)) (assemble _ _ sigma eta) ∈ W) := by
  unfold deletedMass marginal
  simp only [conditionedWordIndicator_eq_true_iff,finiteWordEvent,Set.mem_setOf_eq,← valueSystem_eq_iff]
  rw [sum_dictionaryIndex N L W (fun x b => if x ∈ fullBadMask N L Y mask then
    eventProbability (largeUniformPMF (dyadicCutoff N L) Y) (fun eta =>
      valueSystem (dyadicCutoff N L) (vertex x (L+1)) (assemble _ _ sigma eta)=b) else 0)]
  simp_rw [Finset.sum_ite_irrel,Finset.sum_const_zero,← eventProbability_mem_eq_sum]
  rw [← Finset.sum_filter]
  have he : (dyadicBlock N).filter (fun x => x ∈ fullBadMask N L Y mask) = fullBadMask N L Y mask := by
    ext x
    simp only [Finset.mem_filter]
    exact ⟨And.right,fun hx => ⟨hmask (fullBadMask_subset_mask N L Y mask hx),hx⟩⟩
  rw [he]

/-- Mean real deletion equals a times the bad-site count on every environment. -/
theorem averaged_deletedMass (N L Y m : ℕ) (mask : Finset ℕ) (hmask : mask ⊆ dyadicBlock N)
    (hm : 1 ≤ m) (hmb : m ≤ 2^(L+1)) (sigma : SmallSample (dyadicCutoff N L) Y) :
    dictionaryAverage (L+1) m (fun W => deletedMass N L Y mask W sigma) =
      ((m:ℝ)/(2:ℝ)^(L+1))*(fullBadMask N L Y mask).card := by
  simp_rw [deletedMass_eq N L Y mask hmask]
  exact averaged_deletion_sum hm hmb _ _ _

end
end PaperC.Prel8.TypicalDictionaryDeletion
