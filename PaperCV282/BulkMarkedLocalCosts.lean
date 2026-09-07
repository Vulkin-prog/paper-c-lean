import PaperCV282.BulkMarkedTransfer
import PaperCV282.ExactMarkedPairCosts

/-! # Local signed bulk costs, uniformly in the number of exact marks -/
namespace PaperC.V282.BulkMarkedLocalCosts

open ExactMarkedModel ExactMarkedDependency ExactMarkedAggregation ExactMarkedLocalProbability
open ExactMarkedPairCosts BulkSupportGraph BulkProcessCosts
open MacroscopicMaskGeometry MaskedPairGeometry SectionTwelveMoments TwoWindowParity
open ConditionalStartProbability ConditionalAGGInstantiation ConditionalAGGAverage
open ArratiaGoldsteinGordonInput LargePrimeDependencyGraph SectionThirteenFiniteBound
open MixedLengthAffine WindowValues DefectivePredicate
open scoped BigOperators

noncomputable section
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

theorem bulk_neighborPairs_eq_near_union_far (Q Y : ℕ) (mask : Finset ℕ) :
    BulkProcessCosts.labelledNeighborPairs Q Y mask = nearMarkedPairs Q mask ∪ farMarkedPairs Q Y mask := by
  exact ExactMarkedPairCosts.labelledNeighborPairs_eq_near_union_far Q Y mask

theorem good_maximal_vertex {L E Y x : ℕ} {sites mask : Finset ℕ}
    (hsite : ∀ x ∈ sites, 2 ≤ x) (hmask : mask ⊆ sites)
    (hx : x ∈ goodMask (L+E+1) Y mask) (i : Fin (L+E+2)) :
    ¬HDefective Y (vertex x (L+E+2) i) := by
  have hb := hmask (mem_goodMask.mp hx).1
  have hx2 := hsite x hb
  exact not_defective_of_good hx
    (marked_vertex_mem_max (by omega) (le_refl E) i)

/-- The geometric rate sum, not the number of labels, controls each local ordered pair. -/
theorem signedPairProbability_le_four_of_lt {C L E Y x y : ℕ} {sites mask : Finset ℕ}
    (hsite : ∀ x ∈ sites, 2 ≤ x) (hL : 1 ≤ L) (hC : ∀ x ∈ sites, x+L+E+1 ≤ C)
    (hY : 2*(L+E+2) ≤ Y) (hmask : mask ⊆ sites)
    (hx : x ∈ goodMask (L+E+1) Y mask)
    (hy : y ∈ goodMask (L+E+1) Y mask)
    (hxy : x < y) (hd : Nat.dist x y ≤ L+E+1) (sigma : SmallSample C Y) :
    signedPairProbability C L E Y sigma x y ≤ 4/(2 : ℝ)^(2*L) := by
  have hxblock := hmask (mem_goodMask.mp hx).1
  have hyblock := hmask (mem_goodMask.mp hy).1
  have hx2 := hsite x hxblock
  have hxyadd : x+(y-x)=y := by omega
  have hdist : Nat.dist x y=y-x := Nat.dist_eq_sub_of_le hxy.le
  have hcut : y-1+(L+E+2) ≤ C+1 := by
    have hb := hC y hyblock
    have hy2 := hsite y hyblock
    omega
  have hpoint (a b : Fin (E+1) × F₂) :
      eventProbability (largeUniformPMF C Y) (fun eta =>
        conditionedSignedAt C L E Y sigma x a eta=true ∧
        conditionedSignedAt C L E Y sigma y b eta=true) ≤
          4*(signedMarkRate L a.1.val : ℝ)*(signedMarkRate L b.1.val : ℝ) := by
    simp only [conditionedSignedAt,signedAt,decide_eq_true_eq]
    have hp := conditioned_signed_pair_le_four (C := C) (Y := Y) (L := L) (E := E)
      (e := a.1.val) (f := b.1.val) (d := y-x) hx2 hL
      (by have ha := a.1.isLt;omega) (by have hb := b.1.isLt;omega)
      (by omega) (by simpa only [hdist] using hd)
      (by simpa only [hxyadd] using hcut) hY
      (good_maximal_vertex hsite hmask hx)
      (by simpa only [hxyadd] using good_maximal_vertex hsite hmask hy) a.2 b.2 sigma
    simpa only [hxyadd] using hp
  let R : ℝ := ∑ a : Fin (E+1) × F₂, (signedMarkRate L a.1.val : ℝ)
  have hr0 : 0 ≤ R := Finset.sum_nonneg (fun a ha => by positivity)
  have hr : R ≤ 1/(2 : ℝ)^L := by
    simpa only [R,Fintype.sum_prod_type] using sum_all_signedMarkRate_le_base L E
  calc
    _ ≤ ∑ a : Fin (E+1) × F₂, ∑ b : Fin (E+1) × F₂,
        4*(signedMarkRate L a.1.val : ℝ)*(signedMarkRate L b.1.val : ℝ) :=
      Finset.sum_le_sum (fun a ha => Finset.sum_le_sum (fun b hb => hpoint a b))
    _ = 4*R^2 := by simp only [← Finset.mul_sum,← Finset.sum_mul,R];ring
    _ ≤ 4*(1/(2 : ℝ)^L)^2 := by nlinarith
    _ = _ := by rw [Nat.mul_comm 2 L,pow_mul];ring

theorem signedPairProbability_le_four {C L E Y x y : ℕ} {sites mask : Finset ℕ}
    (hsite : ∀ x ∈ sites, 2 ≤ x) (hL : 1 ≤ L) (hC : ∀ x ∈ sites, x+L+E+1 ≤ C)
    (hY : 2*(L+E+2) ≤ Y) (hmask : mask ⊆ sites)
    (hx : x ∈ goodMask (L+E+1) Y mask)
    (hy : y ∈ goodMask (L+E+1) Y mask)
    (hxy : x ≠ y) (hd : Nat.dist x y ≤ L+E+1) (sigma : SmallSample C Y) :
    signedPairProbability C L E Y sigma x y ≤ 4/(2 : ℝ)^(2*L) := by
  rcases lt_or_gt_of_ne hxy with hlt | hgt
  · exact signedPairProbability_le_four_of_lt hsite hL hC hY hmask hx hy hlt hd sigma
  · rw [signedPairProbability_symm]
    exact signedPairProbability_le_four_of_lt hsite hL hC hY hmask hy hx hgt
      (by simpa only [Nat.dist_comm] using hd) sigma

/-- The local site count is linear in Q, uniformly before the excess cutoff. -/
theorem card_nearMarkedPairs_le {Q : ℕ} {sites : Finset ℕ} (mask : Finset ℕ)
    (hmask : mask ⊆ sites) : (nearMarkedPairs Q mask).card ≤ 2*sites.card*(Q+1) := by
  let candidates := sites ×ˢ Finset.range (Q+1)
  let forward := candidates.image (fun z : ℕ × ℕ => (z.1,z.1+z.2))
  let backward := candidates.image (fun z : ℕ × ℕ => (z.1+z.2,z.1))
  have hs : nearMarkedPairs Q mask ⊆ forward ∪ backward := by
    intro xy hxy
    obtain ⟨hp,hd⟩ := Finset.mem_filter.mp hxy
    obtain ⟨hx,hy,hne⟩ := Finset.mem_offDiag.mp hp
    have hm : Nat.dist xy.1 xy.2 ∈ Finset.range (Q+1) := Finset.mem_range.mpr (by omega)
    rcases TouchingPairs.eq_add_or_eq_add_of_dist_eq (L := Nat.dist xy.1 xy.2) rfl with hf | hb
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(xy.1,Nat.dist xy.1 xy.2),
        Finset.mem_product.mpr ⟨hmask hx,hm⟩,Prod.ext rfl hf.symm⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(xy.2,Nat.dist xy.1 xy.2),
        Finset.mem_product.mpr ⟨hmask hy,hm⟩,Prod.ext hb.symm rfl⟩)
  have hf : forward.card ≤ sites.card*(Q+1) := by
    apply (Finset.card_image_le).trans
    simp [candidates]
  have hb : backward.card ≤ sites.card*(Q+1) := by
    apply (Finset.card_image_le).trans
    simp [candidates]
  have hh := (Finset.card_le_card hs).trans (Finset.card_union_le _ _)
  nlinarith


theorem bTwo_signed_eq_near_add_far {C L E Y : ℕ} {sites : Finset ℕ}
    (hL : 1 ≤ L) (mask : Finset ℕ) (hmask : mask ⊆ sites)
    (sigma : SmallSample C Y) :
    bTwo (largeUniformPMF C Y) (maskedLabelledFamily sites (conditionedSignedAt C L E Y sigma)
      (goodMask (L+E+1) Y mask)) (labelledGraph sites (L+E+1) Y (Fin (E+1) × F₂)) =
      (∑ xy ∈ nearMarkedPairs (L+E+1) (goodMask (L+E+1) Y mask),
        signedPairProbability C L E Y sigma xy.1 xy.2) +
      ∑ xy ∈ farMarkedPairs (L+E+1) Y (goodMask (L+E+1) Y mask),
        signedPairProbability C L E Y sigma xy.1 xy.2 := by
  rw [bTwo_labelled_eq]
  · rw [labelPairMass,bulk_neighborPairs_eq_near_union_far,
      Finset.sum_union (disjoint_near_farMarkedPairs _ _ _)]
    rfl
  · exact (goodMask_subset _ _ _).trans hmask
  · intro x hx a b hab eta
    exact signedAt_disjoint hL x a b hab (assemble C Y sigma eta)

/-- All near pairs together cost at most 8*sites*(Q+1)*p^2, independently of the number of marks. -/
theorem near_signedPairMass_le {C L E Y : ℕ} {sites : Finset ℕ}
    (hsite : ∀ x ∈ sites, 2 ≤ x) (hL : 1 ≤ L) (hC : ∀ x ∈ sites, x+L+E+1 ≤ C)
    (hY : 2*(L+E+2) ≤ Y) (mask : Finset ℕ) (hmask : mask ⊆ sites)
    (sigma : SmallSample C Y) :
    (∑ xy ∈ nearMarkedPairs (L+E+1) (goodMask (L+E+1) Y mask),
      signedPairProbability C L E Y sigma xy.1 xy.2) ≤
      (8*(sites.card : ℝ)*(L+E+2))/(2 : ℝ)^(2*L) := by
  have hc := card_nearMarkedPairs_le (Q := L+E+1) (goodMask (L+E+1) Y mask)
    ((goodMask_subset _ _ _).trans hmask)
  calc
    _ ≤ ∑ xy ∈ nearMarkedPairs (L+E+1) (goodMask (L+E+1) Y mask),
        4/(2 : ℝ)^(2*L) := by
      apply Finset.sum_le_sum
      intro xy hxy
      obtain ⟨hpair,hd⟩ := Finset.mem_filter.mp hxy
      obtain ⟨hx,hy,hne⟩ := Finset.mem_offDiag.mp hpair
      exact signedPairProbability_le_four hsite hL hC hY hmask hx hy hne hd sigma
    _ = (4*((nearMarkedPairs (L+E+1) (goodMask (L+E+1) Y mask)).card : ℝ)) /
        (2 : ℝ)^(2*L) := by simp [mul_div_assoc,mul_comm];ring
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      have hcR : ((nearMarkedPairs (L+E+1) (goodMask (L+E+1) Y mask)).card : ℝ) ≤
          2*(sites.card : ℝ)*(L+E+2) := by exact_mod_cast hc
      linarith


end
end PaperC.V282.BulkMarkedLocalCosts
