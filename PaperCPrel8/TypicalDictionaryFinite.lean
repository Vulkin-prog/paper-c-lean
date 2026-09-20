import PaperCPrel8.TypicalDictionaryTransfer

/-! # Explicit finite typical-dictionary comparison on the actual site-word field -/
namespace PaperC.Prel8.TypicalDictionaryFinite
open PaperC.Affine PaperC.SectionTwelveMoments PaperC.SectionThirteenFiniteBound
open PaperC.V282.RandomDictionary PaperC.V282.ProcessAGGInput
open PaperC.V282.MaskedArithmeticGeometry PaperC.V282.MaskedPairGeometry
open PaperC.V282.DictionaryFieldFirstCost PaperC.V282.RelationProfileRestriction
open PaperC.V282.TwoWindowParity PaperC.V282.DictionaryPairCosts
open PaperC.Prel8.TypicalDictionaryPairs PaperC.Prel8.TypicalDictionaryTransfer
noncomputable section

/-- The retained far-pair mask is inside both the support graph and the separated mask. -/
theorem farPairs_subsets (N L Y : ℕ) (mask : Finset ℕ) :
    farPairs N L Y mask ⊆ maskedSupportEdges L Y mask ∧
    farPairs N L Y mask ⊆ separatedPairs mask L := by
  constructor
  · exact (Finset.filter_subset _ _).trans (fullMaskedEdges_subset_support N L Y mask)
  · intro xy hxy
    have hf := Finset.mem_filter.mp hxy
    obtain ⟨hx,hy,_⟩ := mem_maskedSupportEdges.mp (fullMaskedEdges_subset_support N L Y mask hf.1)
    exact (mem_separatedPairs _ _ _ _).mpr ⟨hx,hy,by omega⟩

/-- A finite bound with numerical constants, valid for all permitted dictionary sizes. -/
theorem finite_masked_typical_bound (hAGG : ProcessAGGStatement) {N L Y m : ℕ}
    (mask : Finset ℕ) (hmask : mask ⊆ dyadicBlock N) (hN : 2 ≤ N)
    (hY : 2*(L+1) ≤ Y) (hm : 1 ≤ m) (hmb : m ≤ 2^(L+1)) :
    dictionaryAverage (L+1) m (maskedDistance N L Y mask) ≤
      2*((m:ℝ)/(2:ℝ)^(L+1))*(fullBadMask N L Y mask).card+
      8*((m:ℝ)/(2:ℝ)^(L+1))^2*(mask.card:ℝ)*(L+1:ℝ)+
      6*((m:ℝ)/(2:ℝ)^(L+1))^2*(maskedSupportEdges L Y mask).card+
      2*((m:ℝ)/(2:ℝ)^(L+1))*((1:ℝ)/(2:ℝ)^(L+1))*
        (valueWeightMass (dyadicCutoff N L) L (separatedPairs mask L):ℝ) := by
  have h := averaged_field_le hAGG mask hmask hN hY hm hmb
  have hf := farPairs_subsets N L Y mask
  have hpos : ∀ xy ∈ farPairs N L Y mask, 1 ≤ xy.1 ∧ 1 ≤ xy.2 := by
    intro xy hxy
    obtain ⟨hx,hy,_⟩ := mem_maskedSupportEdges.mp (hf.1 hxy)
    have hx' := Finset.mem_Ico.mp (hmask hx)
    have hy' := Finset.mem_Ico.mp (hmask hy)
    omega
  have hp := averaged_pairMass_le (dyadicCutoff N L) L m (farPairs N L Y mask) hpos hm hmb
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
  have hmc := mul_le_mul_of_nonneg_left hc (sq_nonneg ((m:ℝ)/(2:ℝ)^(L+1)))
  have hmr := mul_le_mul_of_nonneg_left hr
    (show 0 ≤ ((m:ℝ)/(2:ℝ)^(L+1))*((1:ℝ)/(2:ℝ)^(L+1)) by positivity)
  have hmg := mul_le_mul_of_nonneg_left hg (sq_nonneg ((m:ℝ)/(2:ℝ)^(L+1)))
  have he : (mask.card:ℝ)*((m:ℝ)/(2:ℝ)^(L+1))*((m:ℝ)*L/(2:ℝ)^(L+1)) =
      ((m:ℝ)/(2:ℝ)^(L+1))^2*(mask.card:ℝ)*L := by ring
  nlinarith [he,mul_nonneg (sq_nonneg ((m:ℝ)/(2:ℝ)^(L+1))) (Nat.cast_nonneg mask.card)]

/-- Ambient-size specialization used in the uniform asymptotic bounds. -/
theorem finite_typical_bound (hAGG : ProcessAGGStatement) {N L Y m : ℕ}
    (mask : Finset ℕ) (hmask : mask ⊆ dyadicBlock N) (hN : 2 ≤ N)
    (hY : 2*(L+1) ≤ Y) (hm : 1 ≤ m) (hmb : m ≤ 2^(L+1)) :
    dictionaryAverage (L+1) m (maskedDistance N L Y mask) ≤
      2*((m:ℝ)/(2:ℝ)^(L+1))*(fullBadMask N L Y mask).card+
      8*((m:ℝ)/(2:ℝ)^(L+1))^2*(N:ℝ)*(L+1:ℝ)+
      6*((m:ℝ)/(2:ℝ)^(L+1))^2*(maskedSupportEdges L Y mask).card+
      2*((m:ℝ)/(2:ℝ)^(L+1))*((1:ℝ)/(2:ℝ)^(L+1))*
        (valueWeightMass (dyadicCutoff N L) L (separatedPairs mask L):ℝ) := by
  apply (finite_masked_typical_bound hAGG mask hmask hN hY hm hmb).trans
  have hc : (mask.card:ℝ) ≤ N := by
    exact_mod_cast (Finset.card_le_card hmask).trans_eq (PaperC.TouchingPairs.card_dyadicBlock N)
  gcongr

end
end PaperC.Prel8.TypicalDictionaryFinite
