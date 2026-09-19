import PaperCPrel8.AffineDictionaryCosts
import PaperCPrel8.TypicalDictionaryFinite
import PaperCPrel8.TypicalDictionaryPairs
import PaperCPrel8.DictionaryMaskedCosts

/-! # Fixed-dictionary process comparison followed by the selection average -/
namespace PaperC.Prel8.AffineDictionaryFinite
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
open PaperC.Prel8.AffineDictionarySample PaperC.Prel8.AffineDictionaryInclusion
open PaperC.Prel8.AffineDictionaryMoments PaperC.Prel8.AffineDictionaryCosts
open PaperC.Prel8.TypicalDictionaryTransfer PaperC.Prel8.TypicalDictionaryFinite
open scoped BigOperators NNReal
noncomputable section
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem averaged_field_le (hAGG : ProcessAGGStatement) {N L Y r : ℕ}
    (mask : Finset ℕ) (hmask : mask ⊆ dyadicBlock N) (hN : 2 ≤ N)
    (hY : 2*(L+1) ≤ Y) (hrank : r ≤ L+1) :
    affineAverage (L+1) r (maskedDistance N L Y mask) ≤
      2*(((2^(L+1-r)):ℝ)/(2:ℝ)^(L+1))*(fullBadMask N L Y mask).card+
      2*(((2^(L+1-r)):ℝ)/(2:ℝ)^(L+1))^2*(closedDictionarySitePairs L Y (fullGoodMask N L Y mask)).card+
      4*(mask.card:ℝ)*(((2^(L+1-r)):ℝ)/(2:ℝ)^(L+1))*(((2^(L+1-r)):ℝ)*L/(2:ℝ)^(L+1))+
      2*dictionaryAverage (L+1) (2^(L+1-r)) (fun W => dictionaryPairMass (dyadicCutoff N L) L W (farPairs N L Y mask)) := by
  have hm := (sample_size_bounds hrank).1
  have hmb := (sample_size_bounds hrank).2
  have hw (s : Sample (L+1) r) : (dictionary s).Nonempty :=
    Finset.card_pos.mp (by rw [card_dictionary]; positivity)
  have h := affine_mono hrank (f := maskedDistance N L Y mask)
    (g := fun W => finiteUniformAverage (deletedMass N L Y mask W)+
      2*(((2^(L+1-r)):ℝ)/(2:ℝ)^(L+1))^2*(closedDictionarySitePairs L Y (fullGoodMask N L Y mask)).card+
      4*(mask.card:ℝ)*(((2^(L+1-r)):ℝ)/(2:ℝ)^(L+1))*overlapWeight W+
      2*dictionaryPairMass (dyadicCutoff N L) L W (farPairs N L Y mask)+
      (((2^(L+1-r)):ℝ)/(2:ℝ)^(L+1))*(fullBadMask N L Y mask).card)
    (fun s => by simpa only [dictionaryRate_coe,card_dictionary,Nat.cast_pow,Nat.cast_ofNat] using
      fixed_dictionary_le hAGG (dictionary s) (hw s) mask hmask hN hY)
  simp only [affine_add,affine_mul,affine_const hrank,
    affine_environment_commute,deletion_matches hrank mask hmask,
    averaged_deletedMass N L Y (2^(L+1-r)) mask hmask hm hmb,environment_const,
    overlap_matches (by omega : 1 ≤ L+1) hrank,average_overlapWeight_eq hm hmb,
    Nat.add_sub_cancel,pairMass_matches _ _ _ hrank,Nat.cast_pow,Nat.cast_ofNat] at h
  nlinarith

/-- A finite bound with numerical constants, valid for all permitted dictionary sizes. -/
theorem finite_masked_typical_bound (hAGG : ProcessAGGStatement) {N L Y r : ℕ}
    (mask : Finset ℕ) (hmask : mask ⊆ dyadicBlock N) (hN : 2 ≤ N)
    (hY : 2*(L+1) ≤ Y) (hrank : r ≤ L+1) :
    affineAverage (L+1) r (maskedDistance N L Y mask) ≤
      2*(((2^(L+1-r)):ℝ)/(2:ℝ)^(L+1))*(fullBadMask N L Y mask).card+
      8*(((2^(L+1-r)):ℝ)/(2:ℝ)^(L+1))^2*(mask.card:ℝ)*(L+1:ℝ)+
      6*(((2^(L+1-r)):ℝ)/(2:ℝ)^(L+1))^2*(maskedSupportEdges L Y mask).card+
      2*(((2^(L+1-r)):ℝ)/(2:ℝ)^(L+1))*((1:ℝ)/(2:ℝ)^(L+1))*
        (valueWeightMass (dyadicCutoff N L) L (separatedPairs mask L):ℝ) := by
  have hm := (sample_size_bounds hrank).1
  have hmb := (sample_size_bounds hrank).2
  have h := PaperC.Prel8.AffineDictionaryFinite.averaged_field_le hAGG mask hmask hN hY hrank
  have hf := farPairs_subsets N L Y mask
  have hpos : ∀ xy ∈ farPairs N L Y mask, 1 ≤ xy.1 ∧ 1 ≤ xy.2 := by
    intro xy hxy
    obtain ⟨hx,hy,_⟩ := mem_maskedSupportEdges.mp (hf.1 hxy)
    have hx' := Finset.mem_Ico.mp (hmask hx)
    have hy' := Finset.mem_Ico.mp (hmask hy)
    omega
  have hp := averaged_pairMass_le (dyadicCutoff N L) L (2^(L+1-r)) (farPairs N L Y mask) hpos hm hmb
  simp only [Nat.cast_pow,Nat.cast_ofNat] at hp
  have hc : ((farPairs N L Y mask).card:ℝ) ≤ (maskedSupportEdges L Y mask).card := by
    exact_mod_cast Finset.card_le_card hf.1
  have hr : (valueWeightMass (dyadicCutoff N L) L (farPairs N L Y mask):ℝ) ≤
      (valueWeightMass (dyadicCutoff N L) L (separatedPairs mask L):ℝ) := by
    exact_mod_cast (Finset.sum_le_sum_of_subset hf.2 : valueWeightMass _ _ _ ≤ valueWeightMass _ _ _)
  have hclosed : closedDictionarySitePairs L Y (fullGoodMask N L Y mask) ⊆
      closedDictionarySitePairs L Y mask := by
    intro xy hxy
    obtain ⟨hx,hy,hxy⟩ := (mem_closedDictionarySitePairs _ _ _ _ _).mp hxy
    exact (mem_closedDictionarySitePairs _ _ _ _ _).mpr
      ⟨fullGoodMask_subset_mask N L Y mask hx,fullGoodMask_subset_mask N L Y mask hy,hxy⟩
  have hg : ((closedDictionarySitePairs L Y (fullGoodMask N L Y mask)).card:ℝ) ≤
      2*(mask.card:ℝ)*(L+1:ℝ)+(maskedSupportEdges L Y mask).card := by
    exact_mod_cast (Finset.card_le_card hclosed).trans (PaperC.Prel8.DictionaryMaskedCosts.card_closed_pairs_le mask)
  have hmc := mul_le_mul_of_nonneg_left hc (sq_nonneg (((2^(L+1-r)):ℝ)/(2:ℝ)^(L+1)))
  have hmr := mul_le_mul_of_nonneg_left hr
    (show 0 ≤ (((2^(L+1-r)):ℝ)/(2:ℝ)^(L+1))*((1:ℝ)/(2:ℝ)^(L+1)) by positivity)
  have hmg := mul_le_mul_of_nonneg_left hg (sq_nonneg (((2^(L+1-r)):ℝ)/(2:ℝ)^(L+1)))
  have he : (mask.card:ℝ)*(((2^(L+1-r)):ℝ)/(2:ℝ)^(L+1))*(((2^(L+1-r)):ℝ)*L/(2:ℝ)^(L+1)) =
      (((2^(L+1-r)):ℝ)/(2:ℝ)^(L+1))^2*(mask.card:ℝ)*L := by ring
  nlinarith [he,mul_nonneg (sq_nonneg (((2^(L+1-r)):ℝ)/(2:ℝ)^(L+1))) (Nat.cast_nonneg mask.card)]

/-- Ambient-size specialization used in the uniform asymptotic bounds. -/
theorem finite_typical_bound (hAGG : ProcessAGGStatement) {N L Y r : ℕ}
    (mask : Finset ℕ) (hmask : mask ⊆ dyadicBlock N) (hN : 2 ≤ N)
    (hY : 2*(L+1) ≤ Y) (hrank : r ≤ L+1) :
    affineAverage (L+1) r (maskedDistance N L Y mask) ≤
      2*(((2^(L+1-r)):ℝ)/(2:ℝ)^(L+1))*(fullBadMask N L Y mask).card+
      8*(((2^(L+1-r)):ℝ)/(2:ℝ)^(L+1))^2*(N:ℝ)*(L+1:ℝ)+
      6*(((2^(L+1-r)):ℝ)/(2:ℝ)^(L+1))^2*(maskedSupportEdges L Y mask).card+
      2*(((2^(L+1-r)):ℝ)/(2:ℝ)^(L+1))*((1:ℝ)/(2:ℝ)^(L+1))*
        (valueWeightMass (dyadicCutoff N L) L (separatedPairs mask L):ℝ) := by
  apply (PaperC.Prel8.AffineDictionaryFinite.finite_masked_typical_bound hAGG mask hmask hN hY hrank).trans
  have hc : (mask.card:ℝ) ≤ N := by
    exact_mod_cast (Finset.card_le_card hmask).trans_eq (PaperC.TouchingPairs.card_dyadicBlock N)
  gcongr

end
end PaperC.Prel8.AffineDictionaryFinite
