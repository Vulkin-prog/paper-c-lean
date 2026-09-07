import PaperCV282.BulkMarkedLocalCosts
import PaperCV282.FiniteStartMaskPairBounds

/-! # The base-length relation mass for separated signed bulk pairs -/
namespace PaperC.V282.BulkMarkedSeparatedCosts

open ExactMarkedModel ExactMarkedDependency ExactMarkedAggregation ExactMarkedPairCosts
open BulkMarkedLocalCosts BulkSupportGraph BulkProcessCosts
open MacroscopicMaskGeometry MaskedPairGeometry SectionTwelveMoments TwoWindowParity HostRankMass
open ConditionalStartProbability ConditionalAGGInstantiation ConditionalAGGAverage
open ArratiaGoldsteinGordonInput SectionThirteenFiniteBound Affine
open scoped BigOperators

noncomputable section
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

/-- Summing all signed excesses first leaves the actual base event, at the same cylinder. -/
theorem average_signedPairProbability_le_weight {C L E Y x y : ℕ} (hL : 1 ≤ L) :
    finiteUniformAverage (fun sigma : SmallSample C Y => signedPairProbability C L E Y sigma x y) ≤
      (1+((2^relationRho (twoStartSystem C x y L)-1 : ℕ) : ℝ))/(2 : ℝ)^(2*L) := by
  have h := finiteUniformAverage_mono (fun sigma : SmallSample C Y =>
    sum_conditioned_signed_joint_probability_le_base C L E Y x y sigma hL)
  change finiteUniformAverage (fun sigma : SmallSample C Y => signedPairProbability C L E Y sigma x y) ≤
    finiteUniformAverage (fun sigma : SmallSample C Y => ArratiaGoldsteinGordonInput.eventProbability (largeUniformPMF C Y)
      (fun eta => startAt (assemble C Y sigma eta) x L ∧ startAt (assemble C Y sigma eta) y L)) at h
  rw [finiteUniformAverage_largeEventProbability_eq_full C Y
    (fun omega => startAt omega x L ∧ startAt omega y L)] at h
  have hr := (Rat.cast_le (K := ℝ)).mpr
    (FiniteStartMaskPairBounds.uniform_joint_le_relation C L x y (by omega))
  push_cast at hr
  apply h.trans
  apply hr.trans_eq
  rw [Nat.cast_sub Nat.one_le_two_pow]
  push_cast
  ring

/-- The far-pair set is contained in the original support edges and the base separated mask. -/
theorem farMarkedPairs_subsets (L E Y : ℕ) (mask : Finset ℕ) :
    farMarkedPairs (L+E+1) Y (goodMask (L+E+1) Y mask) ⊆ maskedSupportEdges (L+E+1) Y mask ∧
    farMarkedPairs (L+E+1) Y (goodMask (L+E+1) Y mask) ⊆ separatedPairs mask L := by
  constructor
  · exact (Finset.filter_subset _ _).trans
      (maskedSupportEdges_mono (goodMask_subset _ _ _))
  · intro xy hxy
    obtain ⟨he,hd⟩ := Finset.mem_filter.mp hxy
    obtain ⟨hx,hy,ha⟩ := mem_maskedSupportEdges.mp he
    exact mem_separatedPairs _ _ _ _ |>.mpr
      ⟨(mem_goodMask.mp hx).1,(mem_goodMask.mp hy).1,by omega⟩

/-- The far-pair mean pays the actual maximal-support edge count plus the base relation mass. -/
theorem average_far_signedPairMass_le {C L E Y : ℕ}
    (hL : 1 ≤ L) (mask : Finset ℕ) :
    finiteUniformAverage (fun sigma : SmallSample C Y =>
      ∑ xy ∈ farMarkedPairs (L+E+1) Y (goodMask (L+E+1) Y mask),
        signedPairProbability C L E Y sigma xy.1 xy.2) ≤
      ((maskedSupportEdges (L+E+1) Y mask).card +
        (relationWeightMass C L (separatedPairs mask L) : ℝ))/(2 : ℝ)^(2*L) := by
  rw [average_finset_sum]
  have hs := farMarkedPairs_subsets L E Y mask
  calc
    _ ≤ ∑ xy ∈ farMarkedPairs (L+E+1) Y (goodMask (L+E+1) Y mask),
        (1+((2^Affine.relationRho (Affine.twoStartSystem C xy.1 xy.2 L)-1 : ℕ) : ℝ))/(2 : ℝ)^(2*L) := by
      apply Finset.sum_le_sum
      intro xy hxy
      exact average_signedPairProbability_le_weight hL
    _ = (((farMarkedPairs (L+E+1) Y (goodMask (L+E+1) Y mask)).card : ℝ)+
        (relationWeightMass C L (farMarkedPairs (L+E+1) Y (goodMask (L+E+1) Y mask)) : ℝ)) /
        (2 : ℝ)^(2*L) := by
      rw [← Finset.sum_div,Finset.sum_add_distrib]
      simp [relationWeightMass]
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      have hc := Finset.card_le_card hs.1
      have hm : relationWeightMass C L (farMarkedPairs (L+E+1) Y (goodMask (L+E+1) Y mask)) ≤
          relationWeightMass C L (separatedPairs mask L) := by
        exact Finset.sum_le_sum_of_subset hs.2
      exact add_le_add (by exact_mod_cast hc) (by exact_mod_cast hm)

/-- The actual signed b2, with all labels aggregated and R2 at the base length L. -/
theorem average_bTwo_signed_le {C L E Y : ℕ} {sites : Finset ℕ}
    (hsite : ∀ x ∈ sites, 2 ≤ x) (hL : 1 ≤ L) (hC : ∀ x ∈ sites, x+L+E+1 ≤ C)
    (hY : 2*(L+E+2) ≤ Y) (mask : Finset ℕ) (hmask : mask ⊆ sites) :
    finiteUniformAverage (fun sigma : SmallSample C Y =>
      bTwo (largeUniformPMF C Y) (maskedLabelledFamily sites (conditionedSignedAt C L E Y sigma)
        (goodMask (L+E+1) Y mask)) (labelledGraph sites (L+E+1) Y (Fin (E+1) × F₂))) ≤
      (8*(sites.card : ℝ)*(L+E+2)+(maskedSupportEdges (L+E+1) Y mask).card+
        (relationWeightMass C L (separatedPairs mask L) : ℝ))/(2 : ℝ)^(2*L) := by
  simp_rw [bTwo_signed_eq_near_add_far hL mask hmask]
  have hadd (f g : SmallSample C Y → ℝ) :
      finiteUniformAverage (fun i => f i+g i)=finiteUniformAverage f+finiteUniformAverage g := by
    unfold finiteUniformAverage
    rw [Finset.sum_add_distrib,add_div]
  rw [hadd]
  have hn := finiteUniformAverage_mono
    (fun sigma => near_signedPairMass_le hsite hL hC hY mask hmask sigma)
  have hnear : finiteUniformAverage (fun sigma : SmallSample C Y =>
      ∑ xy ∈ nearMarkedPairs (L+E+1) (goodMask (L+E+1) Y mask),
        signedPairProbability C L E Y sigma xy.1 xy.2) ≤
        (8*(sites.card : ℝ)*(L+E+2))/(2 : ℝ)^(2*L) := by
    simpa [finiteUniformAverage,Fintype.card_ne_zero] using hn
  have hfar := average_far_signedPairMass_le (C := C) (E := E) (Y := Y) hL mask
  exact (add_le_add hnear hfar).trans_eq (by ring)

end
end PaperC.V282.BulkMarkedSeparatedCosts
