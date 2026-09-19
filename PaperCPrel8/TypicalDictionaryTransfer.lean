import PaperCPrel8.TypicalDictionaryDeletion
import PaperCPrel8.TypicalDictionaryPairs
import PaperCPrel8.DictionaryMaskedCosts

/-! # Fixed-dictionary process comparison followed by the selection average -/
namespace PaperC.Prel8.TypicalDictionaryTransfer
open PaperC.Affine PaperC.ConditionalStartProbability PaperC.ConditionalAGGInstantiation
open PaperC.ConditionalAGGAverage PaperC.ArratiaGoldsteinGordonInput
open PaperC.SectionTwelveMoments PaperC.SectionThirteenFiniteBound
open PaperC.V282.DictionaryFieldModel PaperC.V282.DictionaryFieldTransfer
open PaperC.V282.DictionaryFieldSecondCost PaperC.V282.DictionaryPairCosts
open PaperC.V282.DictionaryFieldFirstCost PaperC.V282.DictionaryFieldDependency
open PaperC.V282.MaskedArithmeticGeometry PaperC.V282.MaskedPairGeometry
open PaperC.V282.FiniteFieldTotalVariation PaperC.V282.FiniteFieldPoissonCoupling
open PaperC.V282.ProcessAGGInput PaperC.V282.WordOverlapSum
open PaperC.V282.RandomDictionary PaperC.V282.RandomDictionaryOverlap
open PaperC.V282.TwoWindowParity PaperC.V282.RelationProfileRestriction
open PaperC.Prel8.DictionaryAverage PaperC.Prel8.TypicalDictionaryDeletion
open PaperC.Prel8.TypicalDictionaryPairs PaperC.Prel8.DictionaryMaskedCosts
open scoped BigOperators NNReal
noncomputable section
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- Mean conditional distance for a fixed dictionary and deterministic site mask. -/
def maskedDistance (N L Y : ℕ) (mask : Finset ℕ) (W : Finset (Fin (L+1) → PaperC.F₂)) : ℝ :=
  finiteUniformAverage (fun sigma : SmallSample (dyadicCutoff N L) Y =>
    massTotalVariation
      (finiteFieldLaw (largeUniformPMF (dyadicCutoff N L) Y)
        (indicatorField (maskedWordIndicator N L Y W mask sigma)))
      (poissonFieldMass (allWordRates N L W mask)))

/-- The actual separated graph-pair mask, independent of dictionary selection. -/
def farPairs (N L Y : ℕ) (mask : Finset ℕ) : Finset (ℕ × ℕ) :=
  (fullMaskedEdges N L Y mask).filter (fun xy => L < Nat.dist xy.1 xy.2)

/-- Preserve real deletion until after dictionary averaging. -/
theorem fixed_dictionary_le (hAGG : ProcessAGGStatement) {N L Y : ℕ}
    (W : Finset (Fin (L+1) → PaperC.F₂)) (hW : W.Nonempty)
    (mask : Finset ℕ) (hmask : mask ⊆ dyadicBlock N) (hN : 2 ≤ N) (hY : 2*(L+1) ≤ Y) :
    maskedDistance N L Y mask W ≤
      finiteUniformAverage (deletedMass N L Y mask W)+
      2*(dictionaryRate L W:ℝ)^2*(closedDictionarySitePairs L Y (fullGoodMask N L Y mask)).card+
      4*(mask.card:ℝ)*(dictionaryRate L W:ℝ)*overlapWeight W+
      2*dictionaryPairMass (dyadicCutoff N L) L W (farPairs N L Y mask)+
      (dictionaryRate L W:ℝ)*(fullBadMask N L Y mask).card := by
  have hLY : L+1 ≤ Y := by omega
  have hp (sigma : SmallSample (dyadicCutoff N L) Y) :=
    dictionary_field_process_with_deletion hAGG W mask hmask hN hLY sigma
  simp_rw [bOne_dictionary_eq (Y := Y) W mask hmask hN hLY,
    bTwo_dictionary_eq_pairMass W mask hmask,dictionary_pairMass_eq_local_add_separated] at hp
  have hb (sigma : SmallSample (dyadicCutoff N L) Y) :=
    local_mass_le W hW mask hmask hN hY sigma
  have hpoint (sigma : SmallSample (dyadicCutoff N L) Y) :
      massTotalVariation
        (finiteFieldLaw (largeUniformPMF (dyadicCutoff N L) Y)
          (indicatorField (maskedWordIndicator N L Y W mask sigma)))
        (poissonFieldMass (allWordRates N L W mask)) ≤
      deletedMass N L Y mask W sigma+
      2*(dictionaryRate L W:ℝ)^2*(closedDictionarySitePairs L Y (fullGoodMask N L Y mask)).card+
      4*(mask.card:ℝ)*(dictionaryRate L W:ℝ)*overlapWeight W+
      2*conditionalDictionaryPairMass N L Y W (farPairs N L Y mask) sigma+
      (dictionaryRate L W:ℝ)*(fullBadMask N L Y mask).card := by
    have h := hp sigma
    dsimp only [deletedMass,farPairs]
    linarith [hb sigma]
  have h := finiteUniformAverage_mono hpoint
  simp only [environment_add,environment_mul,environment_const,average_dictionaryPairMass_eq] at h
  exact h

/-- Selection averaging eliminates the weighted one-window defect entirely. -/
theorem averaged_field_le (hAGG : ProcessAGGStatement) {N L Y m : ℕ}
    (mask : Finset ℕ) (hmask : mask ⊆ dyadicBlock N) (hN : 2 ≤ N)
    (hY : 2*(L+1) ≤ Y) (hm : 1 ≤ m) (hmb : m ≤ 2^(L+1)) :
    dictionaryAverage (L+1) m (maskedDistance N L Y mask) ≤
      2*((m:ℝ)/(2:ℝ)^(L+1))*(fullBadMask N L Y mask).card+
      2*((m:ℝ)/(2:ℝ)^(L+1))^2*(closedDictionarySitePairs L Y (fullGoodMask N L Y mask)).card+
      4*(mask.card:ℝ)*((m:ℝ)/(2:ℝ)^(L+1))*((m:ℝ)*L/(2:ℝ)^(L+1))+
      2*dictionaryAverage (L+1) m (fun W => dictionaryPairMass (dyadicCutoff N L) L W (farPairs N L Y mask)) := by
  have hw (W) (hW : W ∈ dictionaries (L+1) m) : W.Nonempty :=
    Finset.card_pos.mp (by rw [(mem_dictionaries W).mp hW]; omega)
  have he (W) (hW : W ∈ dictionaries (L+1) m) : (dictionaryRate L W:ℝ)=(m:ℝ)/(2:ℝ)^(L+1) := by
    rw [dictionaryRate_coe,(mem_dictionaries W).mp hW]
  have h := average_mono (f := maskedDistance N L Y mask)
    (g := fun W => finiteUniformAverage (deletedMass N L Y mask W)+
      2*((m:ℝ)/(2:ℝ)^(L+1))^2*(closedDictionarySitePairs L Y (fullGoodMask N L Y mask)).card+
      4*(mask.card:ℝ)*((m:ℝ)/(2:ℝ)^(L+1))*overlapWeight W+
      2*dictionaryPairMass (dyadicCutoff N L) L W (farPairs N L Y mask)+
      ((m:ℝ)/(2:ℝ)^(L+1))*(fullBadMask N L Y mask).card)
    (fun W hW => by simpa only [he W hW] using fixed_dictionary_le hAGG W (hw W hW) mask hmask hN hY)
  simp only [average_add,average_mul,average_const _ _ hmb,
    average_environment_commute,averaged_deletedMass N L Y m mask hmask hm hmb,
    environment_const,average_overlapWeight_eq hm hmb,Nat.add_sub_cancel] at h
  nlinarith

end
end PaperC.Prel8.TypicalDictionaryTransfer
