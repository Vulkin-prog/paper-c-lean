import PaperCPrel8.ArithmeticLowCategory
import PaperCPrel8.MicroscopicFiniteLedger

/-! # Exact unconditioned low-type marginals from the actual private-prime geometry -/
namespace PaperC.Prel8.ArithmeticLowMarginals
open Finset ArithmeticLowCategory ActualSignedPalm MicroscopicFiniteLedger SignedPalmForcing
open ConditionalStartProbability CategoricalMomentExpansion CategoricalOccupancyEnvelope
open ArratiaGoldsteinGordonInput IndependentThinning V282.SteinFiniteExpectation V282.ExactMarkedModel
noncomputable section
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P
variable {C Y L E : ℕ} {G : Finset ℕ}

theorem geometry_subset (h : GoodGeometry C Y L E G) {S : Finset ℕ} (hs : S⊆G) :
    GoodGeometry C Y L E S where
  length_pos := h.length_pos
  cutoff_pos := h.cutoff_pos
  support_le := h.support_le
  start_pos j hj := h.start_pos j (hs hj)
  cylinder_le j hj := h.cylinder_le j (hs hj)
  good j hj := h.good j (hs hj)

/-- Individual categorical indicators retain the signed exact-word probabilities. -/
theorem indicator_expectation (h : GoodGeometry C Y L E G) (i : G×(Fin (E+1)×F₂)) :
    finitePMFExpectation (FinitePMF.uniform (SampleSpace C))
      (indicator (retainedCategory C L E G) i)=(signedMarkRate L i.2.1.val:ℝ) := by
  have hh := actual_signed_small_probability (h.start_pos i.1.val i.1.property) h.length_pos
    (mark_cylinder h i) h.cutoff_pos
    (show L+i.2.1.val+2≤Y by have := h.support_le; have := i.2.1.isLt; omega)
    (mark_good h i) i.2.2 (fun _ ↦ True)
  have hp : eventProbability (FinitePMF.uniform (SampleSpace C)) (fun _ ↦ True)=1 := by
    simp [eventProbability,FinitePMF.sum_prob]
  simp only [true_and] at hh
  rw [hp,one_mul] at hh
  rw [indicator_mean]
  change eventProbability _ (fun w ↦ lowCategory C L E i.1.val w=some i.2)=_
  convert hh using 1
  congr 1
  funext w
  exact propext (lowCategory_some h.length_pos w i.2)

/-- The common occupancy mean is obtained by summing actual categories, without a new marginal premise. -/
theorem occupancy_expectation (h : GoodGeometry C Y L E G) (i : G) :
    finitePMFExpectation (FinitePMF.uniform (SampleSpace C))
      (occupancy (retainedCategory C L E G) i)=retainedRate L E := by
  have he := funext (occupancy_sum (retainedCategory C L E G) i)
  rw [he,expectation_finset_sum]
  exact sum_congr rfl (fun a _ ↦ indicator_expectation h (i,a))

end
end PaperC.Prel8.ArithmeticLowMarginals
