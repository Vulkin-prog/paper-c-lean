import PaperCV282.RandomDictionary
import PaperC.Probability.IndependentThinning
import PaperC.Probability.SectionThirteenCouplings

/-!
# An auxiliary dictionary choice independent of the multiplicative source

The joint law is a constructed product, not a hypothesis about two random
variables on an unspecified space. Every finite prime-cylinder observation
of the multiplicative source factors from the dictionary event.
-/
namespace PaperC.V282.RandomDictionaryIndependence

open RandomDictionary IndependentThinning ArratiaGoldsteinGordonInput
open ConditionalStartProbability SectionThirteenCouplings

noncomputable section

/-- The auxiliary subset and the actual finite multiplicative sample have product law. -/
def dictionarySourcePMF (B m C : ℕ) (hm : m ≤ 2^B) :
    FinitePMF (DictionarySample B m × SampleSpace C) :=
  productPMF (uniformDictionaryPMF B m hm) (fullUniformPMF C)

/-- Independence is an identity for every dictionary event and every source-cylinder event. -/
theorem dictionary_event_independent_source (B m C : ℕ) (hm : m ≤ 2^B)
    (P : Finset (Fin B → F₂) → Prop) (Q : SampleSpace C → Prop) :
    eventProbability (dictionarySourcePMF B m C hm) (fun z => P z.1.val ∧ Q z.2) =
      dictionaryFraction B m P * eventProbability (fullUniformPMF C) Q := by
  unfold dictionarySourcePMF
  have h := eventProbability_product_and (uniformDictionaryPMF B m hm) (fullUniformPMF C)
    (fun W : DictionarySample B m => P W.val) Q
  rw [dictionaryFraction_eq_probability B m hm P]
  exact h

/-- In particular the auxiliary exceptional fraction is unchanged in the joint model. -/
theorem dictionary_event_probability_in_source_product (B m C : ℕ) (hm : m ≤ 2^B)
    (P : Finset (Fin B → F₂) → Prop) :
    eventProbability (dictionarySourcePMF B m C hm) (fun z => P z.1.val) = dictionaryFraction B m P := by
  have h := dictionary_event_independent_source B m C hm P (fun _ => True)
  classical
  simpa only [and_true,eventProbability,if_true,(fullUniformPMF C).sum_prob,mul_one] using h

end
end PaperC.V282.RandomDictionaryIndependence
