import PaperCV282.ExactMarkedLocalProbability
import PaperCV282.ExactMarkedAggregation
import PaperCV282.ExactMarkedDependency
import PaperCV282.LabelledProcessCosts
import PaperCV282.FullCylinderStartLaw
import PaperCV282.MaskedPairBounds

/-!
# Averaged second cost for the actual signed marked field

Labels are summed before applying the base two-start estimate. The local
radius uses Q=L+E+1, whereas the separated relation mass keeps length L.
-/
namespace PaperC.V282.ExactMarkedPairCosts

open ExactMarkedModel ExactMarkedDependency ExactMarkedAggregation ExactMarkedLocalProbability
open LabelledSupportGraph LabelledProcessCosts FullCylinderStartLaw
open MaskedArithmeticGeometry MaskedPairGeometry SectionTwelveMoments TwoWindowParity
open ConditionalStartProbability ConditionalAGGInstantiation ConditionalAGGAverage
open ArratiaGoldsteinGordonInput LargePrimeDependencyGraph SectionThirteenFiniteBound
open MixedLengthAffine WindowValues DefectivePredicate
open scoped BigOperators

noncomputable section

@[reducible]
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

/-- All actual excess-sign alternatives are aggregated at this ordered site pair. -/
def signedPairProbability (C L E Y : ℕ) (sigma : SmallSample C Y) (x y : ℕ) : ℝ :=
  ∑ a : Fin (E+1) × F₂, ∑ b : Fin (E+1) × F₂,
    eventProbability (largeUniformPMF C Y) (fun eta =>
      conditionedSignedAt C L E Y sigma x a eta=true ∧
      conditionedSignedAt C L E Y sigma y b eta=true)

def nearMarkedPairs (Q : ℕ) (mask : Finset ℕ) : Finset (ℕ × ℕ) :=
  mask.offDiag.filter (fun xy => Nat.dist xy.1 xy.2 ≤ Q)

def farMarkedPairs (Q Y : ℕ) (mask : Finset ℕ) : Finset (ℕ × ℕ) :=
  (maskedSupportEdges Q Y mask).filter (fun xy => Q < Nat.dist xy.1 xy.2)

theorem signedPairProbability_nonneg (C L E Y : ℕ) (sigma : SmallSample C Y) (x y : ℕ) :
    0 ≤ signedPairProbability C L E Y sigma x y := by
  unfold signedPairProbability
  apply Finset.sum_nonneg
  intro a ha
  exact Finset.sum_nonneg (fun b hb => eventProbability_nonneg _ _)

theorem signedPairProbability_symm (C L E Y : ℕ) (sigma : SmallSample C Y) (x y : ℕ) :
    signedPairProbability C L E Y sigma x y = signedPairProbability C L E Y sigma y x := by
  unfold signedPairProbability
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  congr 1
  funext eta
  exact propext and_comm

theorem good_maximal_vertex {N L E Y x : ℕ} {mask : Finset ℕ}
    (hN : 2 ≤ N) (hmask : mask ⊆ dyadicBlock N)
    (hx : x ∈ fullGoodMask N (L+E+1) Y mask) (i : Fin (L+E+2)) :
    ¬HDefective Y (vertex x (L+E+2) i) := by
  have hb := hmask (mem_fullGoodMask.mp hx).1
  have hx2 := two_le_of_mem_dyadicBlock hN hb
  exact not_defective_of_mem_fullGoodMask hmask hx
    (marked_vertex_mem_max (by omega) (le_refl E) i)

/-- The geometric rate sum, not the number of labels, controls each local ordered pair. -/
theorem signedPairProbability_le_four_of_lt {C N L E Y x y : ℕ} {mask : Finset ℕ}
    (hN : 2 ≤ N) (hL : 1 ≤ L) (hC : dyadicCutoff N (L+E+1) ≤ C)
    (hY : 2*(L+E+2) ≤ Y) (hmask : mask ⊆ dyadicBlock N)
    (hx : x ∈ fullGoodMask N (L+E+1) Y mask)
    (hy : y ∈ fullGoodMask N (L+E+1) Y mask)
    (hxy : x < y) (hd : Nat.dist x y ≤ L+E+1) (sigma : SmallSample C Y) :
    signedPairProbability C L E Y sigma x y ≤ 4/(2 : ℝ)^(2*L) := by
  have hxblock := hmask (mem_fullGoodMask.mp hx).1
  have hyblock := hmask (mem_fullGoodMask.mp hy).1
  have hx2 := two_le_of_mem_dyadicBlock hN hxblock
  have hxyadd : x+(y-x)=y := by omega
  have hdist : Nat.dist x y=y-x := Nat.dist_eq_sub_of_le hxy.le
  have hcut : y-1+(L+E+2) ≤ C+1 := by
    have hb := Finset.mem_Ico.mp hyblock
    unfold dyadicCutoff at hC
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
      (good_maximal_vertex hN hmask hx)
      (by simpa only [hxyadd] using good_maximal_vertex hN hmask hy) a.2 b.2 sigma
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

theorem signedPairProbability_le_four {C N L E Y x y : ℕ} {mask : Finset ℕ}
    (hN : 2 ≤ N) (hL : 1 ≤ L) (hC : dyadicCutoff N (L+E+1) ≤ C)
    (hY : 2*(L+E+2) ≤ Y) (hmask : mask ⊆ dyadicBlock N)
    (hx : x ∈ fullGoodMask N (L+E+1) Y mask)
    (hy : y ∈ fullGoodMask N (L+E+1) Y mask)
    (hxy : x ≠ y) (hd : Nat.dist x y ≤ L+E+1) (sigma : SmallSample C Y) :
    signedPairProbability C L E Y sigma x y ≤ 4/(2 : ℝ)^(2*L) := by
  rcases lt_or_gt_of_ne hxy with hlt | hgt
  · exact signedPairProbability_le_four_of_lt hN hL hC hY hmask hx hy hlt hd sigma
  · rw [signedPairProbability_symm]
    exact signedPairProbability_le_four_of_lt hN hL hC hY hmask hy hx hgt
      (by simpa only [Nat.dist_comm] using hd) sigma

/-- The distant-pair average returns the actual base-length law in any adequate cylinder. -/
theorem average_signedPairProbability_le_base {C N L E Y x y : ℕ}
    (hL : 1 ≤ L) (hx : x ∈ dyadicBlock N) (hy : y ∈ dyadicBlock N)
    (hC : dyadicCutoff N (L+E+1) ≤ C) :
    finiteUniformAverage (fun sigma : SmallSample C Y => signedPairProbability C L E Y sigma x y) ≤
      (jointStartProbability N L x y : ℝ) := by
  have hxcut : x+L ≤ C := by
    have hb := Finset.mem_Ico.mp hx
    unfold dyadicCutoff at hC
    omega
  have hycut : y+L ≤ C := by
    have hb := Finset.mem_Ico.mp hy
    unfold dyadicCutoff at hC
    omega
  calc
    _ ≤ finiteUniformAverage (fun sigma : SmallSample C Y => eventProbability (largeUniformPMF C Y)
        (fun eta => startAt (assemble C Y sigma eta) x L ∧ startAt (assemble C Y sigma eta) y L)) := by
      exact finiteUniformAverage_mono (fun sigma =>
        sum_conditioned_signed_joint_probability_le_base C L E Y x y sigma hL)
    _ = _ := average_conditioned_base_joint_probability Y hx hy hxcut hycut

/-- The local site count is linear in Q, uniformly before the excess cutoff. -/
theorem card_nearMarkedPairs_le {N Q : ℕ} (mask : Finset ℕ)
    (hmask : mask ⊆ dyadicBlock N) : (nearMarkedPairs Q mask).card ≤ 2*N*(Q+1) := by
  let candidates := dyadicBlock N ×ˢ Finset.range (Q+1)
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
  have hf : forward.card ≤ N*(Q+1) := by
    apply (Finset.card_image_le).trans
    simp [candidates,TouchingPairs.card_dyadicBlock]
  have hb : backward.card ≤ N*(Q+1) := by
    apply (Finset.card_image_le).trans
    simp [candidates,TouchingPairs.card_dyadicBlock]
  have hh := (Finset.card_le_card hs).trans (Finset.card_union_le _ _)
  nlinarith


theorem labelledNeighborPairs_eq_near_union_far (Q Y : ℕ) (mask : Finset ℕ) :
    labelledNeighborPairs Q Y mask=nearMarkedPairs Q mask ∪ farMarkedPairs Q Y mask := by
  ext xy
  rcases xy with ⟨x,y⟩
  simp only [mem_labelledNeighborPairs,Finset.mem_union,nearMarkedPairs,farMarkedPairs,
    Finset.mem_filter,Finset.mem_offDiag,mem_maskedSupportEdges]
  have hdist : Q < Nat.dist x y → x ≠ y := by
    intro h heq
    simp only [heq,Nat.dist_self] at h
    omega
  have hcases : Nat.dist x y ≤ Q ∨ Q < Nat.dist x y := le_or_gt _ _
  aesop

theorem disjoint_near_farMarkedPairs (Q Y : ℕ) (mask : Finset ℕ) :
    Disjoint (nearMarkedPairs Q mask) (farMarkedPairs Q Y mask) := by
  apply Finset.disjoint_left.mpr
  intro xy hn hf
  have hnear := (Finset.mem_filter.mp hn).2
  have hfar := (Finset.mem_filter.mp hf).2
  omega

theorem average_finset_sum {ι α : Type*} [Fintype ι] [Nonempty ι]
    (s : Finset α) (f : ι → α → ℝ) :
    finiteUniformAverage (fun i => ∑ a ∈ s, f i a)=
      ∑ a ∈ s, finiteUniformAverage (fun i => f i a) := by
  unfold finiteUniformAverage
  rw [Finset.sum_comm,Finset.sum_div]

theorem bTwo_signed_eq_near_add_far {C N L E Y : ℕ}
    (hL : 1 ≤ L) (mask : Finset ℕ) (hmask : mask ⊆ dyadicBlock N)
    (sigma : SmallSample C Y) :
    bTwo (largeUniformPMF C Y) (maskedLabelledFamily N (conditionedSignedAt C L E Y sigma)
      (fullGoodMask N (L+E+1) Y mask)) (labelledGraph N (L+E+1) Y (Fin (E+1) × F₂)) =
      (∑ xy ∈ nearMarkedPairs (L+E+1) (fullGoodMask N (L+E+1) Y mask),
        signedPairProbability C L E Y sigma xy.1 xy.2) +
      ∑ xy ∈ farMarkedPairs (L+E+1) Y (fullGoodMask N (L+E+1) Y mask),
        signedPairProbability C L E Y sigma xy.1 xy.2 := by
  rw [bTwo_labelled_eq]
  · rw [labelPairMass,labelledNeighborPairs_eq_near_union_far,
      Finset.sum_union (disjoint_near_farMarkedPairs _ _ _)]
    rfl
  · exact (fullGoodMask_subset_mask _ _ _ _).trans hmask
  · intro x hx a b hab eta
    exact signedAt_disjoint hL x a b hab (assemble C Y sigma eta)

/-- All near pairs together cost at most 8*N*(Q+1)*p^2, independently of the number of marks. -/
theorem near_signedPairMass_le {C N L E Y : ℕ}
    (hN : 2 ≤ N) (hL : 1 ≤ L) (hC : dyadicCutoff N (L+E+1) ≤ C)
    (hY : 2*(L+E+2) ≤ Y) (mask : Finset ℕ) (hmask : mask ⊆ dyadicBlock N)
    (sigma : SmallSample C Y) :
    (∑ xy ∈ nearMarkedPairs (L+E+1) (fullGoodMask N (L+E+1) Y mask),
      signedPairProbability C L E Y sigma xy.1 xy.2) ≤
      (8*(N : ℝ)*(L+E+2))/(2 : ℝ)^(2*L) := by
  have hc := card_nearMarkedPairs_le (Q := L+E+1) (fullGoodMask N (L+E+1) Y mask)
    ((fullGoodMask_subset_mask _ _ _ _).trans hmask)
  calc
    _ ≤ ∑ xy ∈ nearMarkedPairs (L+E+1) (fullGoodMask N (L+E+1) Y mask),
        4/(2 : ℝ)^(2*L) := by
      apply Finset.sum_le_sum
      intro xy hxy
      obtain ⟨hpair,hd⟩ := Finset.mem_filter.mp hxy
      obtain ⟨hx,hy,hne⟩ := Finset.mem_offDiag.mp hpair
      exact signedPairProbability_le_four hN hL hC hY hmask hx hy hne hd sigma
    _ = (4*((nearMarkedPairs (L+E+1) (fullGoodMask N (L+E+1) Y mask)).card : ℝ)) /
        (2 : ℝ)^(2*L) := by simp [mul_div_assoc,mul_comm];ring
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      have hcR : ((nearMarkedPairs (L+E+1) (fullGoodMask N (L+E+1) Y mask)).card : ℝ) ≤
          2*(N : ℝ)*(L+E+2) := by exact_mod_cast hc
      linarith

/-- Only the relation defect at the base length is charged to a separated pair. -/
theorem average_signedPairProbability_le_weight {C N L E Y x y : ℕ}
    (hL : 1 ≤ L) (hx : x ∈ dyadicBlock N) (hy : y ∈ dyadicBlock N)
    (hC : dyadicCutoff N (L+E+1) ≤ C) :
    finiteUniformAverage (fun sigma : SmallSample C Y => signedPairProbability C L E Y sigma x y) ≤
      (1+(jointDefectWeight N L (x,y) : ℝ))/(2 : ℝ)^(2*L) := by
  apply (average_signedPairProbability_le_base hL hx hy hC).trans
  have h := (le_abs_self _).trans (abs_jointStartProbability_sub_baseline_le N L x y (by omega))
  have hh := (Rat.cast_le (K := ℝ)).mpr h
  simp only [Rat.cast_sub,Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_ofNat,Rat.cast_natCast] at hh
  have ha : (1+(jointDefectWeight N L (x,y) : ℝ))/(2 : ℝ)^(2*L)=
      1/(2 : ℝ)^(2*L)+(jointDefectWeight N L (x,y) : ℝ)/(2 : ℝ)^(2*L) := by ring
  rw [ha]
  linarith

/-- The far-pair set is contained in the original support edges and the base separated mask. -/
theorem farMarkedPairs_subsets (N L E Y : ℕ) (mask : Finset ℕ) :
    farMarkedPairs (L+E+1) Y (fullGoodMask N (L+E+1) Y mask) ⊆ maskedSupportEdges (L+E+1) Y mask ∧
    farMarkedPairs (L+E+1) Y (fullGoodMask N (L+E+1) Y mask) ⊆ separatedPairs mask L := by
  constructor
  · exact (Finset.filter_subset _ _).trans
      (maskedSupportEdges_mono (fullGoodMask_subset_mask _ _ _ _))
  · intro xy hxy
    obtain ⟨he,hd⟩ := Finset.mem_filter.mp hxy
    obtain ⟨hx,hy,ha⟩ := mem_maskedSupportEdges.mp he
    exact mem_separatedPairs _ _ _ _ |>.mpr
      ⟨(mem_fullGoodMask.mp hx).1,(mem_fullGoodMask.mp hy).1,by omega⟩

/-- The far-pair mean pays the actual maximal-support edge count plus the base relation mass. -/
theorem average_far_signedPairMass_le {C N L E Y : ℕ}
    (hL : 1 ≤ L) (hC : dyadicCutoff N (L+E+1) ≤ C)
    (mask : Finset ℕ) (hmask : mask ⊆ dyadicBlock N) :
    finiteUniformAverage (fun sigma : SmallSample C Y =>
      ∑ xy ∈ farMarkedPairs (L+E+1) Y (fullGoodMask N (L+E+1) Y mask),
        signedPairProbability C L E Y sigma xy.1 xy.2) ≤
      ((maskedSupportEdges (L+E+1) Y mask).card +
        (jointDefectMass N L (separatedPairs mask L) : ℝ))/(2 : ℝ)^(2*L) := by
  rw [average_finset_sum]
  have hs := farMarkedPairs_subsets N L E Y mask
  calc
    _ ≤ ∑ xy ∈ farMarkedPairs (L+E+1) Y (fullGoodMask N (L+E+1) Y mask),
        (1+(jointDefectWeight N L xy : ℝ))/(2 : ℝ)^(2*L) := by
      apply Finset.sum_le_sum
      intro xy hxy
      have hp := mem_separatedPairs _ _ _ _ |>.mp (hs.2 hxy)
      exact average_signedPairProbability_le_weight hL (hmask hp.1) (hmask hp.2.1) hC
    _ = (((farMarkedPairs (L+E+1) Y (fullGoodMask N (L+E+1) Y mask)).card : ℝ)+
        (jointDefectMass N L (farMarkedPairs (L+E+1) Y (fullGoodMask N (L+E+1) Y mask)) : ℝ)) /
        (2 : ℝ)^(2*L) := by
      rw [← Finset.sum_div,Finset.sum_add_distrib]
      simp [jointDefectMass]
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      have hc := Finset.card_le_card hs.1
      have hm : jointDefectMass N L (farMarkedPairs (L+E+1) Y (fullGoodMask N (L+E+1) Y mask)) ≤
          jointDefectMass N L (separatedPairs mask L) := by
        exact Finset.sum_le_sum_of_subset hs.2
      exact add_le_add (by exact_mod_cast hc) (by exact_mod_cast hm)

/-- The actual signed b2, with all labels aggregated and R2 at the base length L. -/
theorem average_bTwo_signed_le {C N L E Y : ℕ}
    (hN : 2 ≤ N) (hL : 1 ≤ L) (hC : dyadicCutoff N (L+E+1) ≤ C)
    (hY : 2*(L+E+2) ≤ Y) (mask : Finset ℕ) (hmask : mask ⊆ dyadicBlock N) :
    finiteUniformAverage (fun sigma : SmallSample C Y =>
      bTwo (largeUniformPMF C Y) (maskedLabelledFamily N (conditionedSignedAt C L E Y sigma)
        (fullGoodMask N (L+E+1) Y mask)) (labelledGraph N (L+E+1) Y (Fin (E+1) × F₂))) ≤
      (8*(N : ℝ)*(L+E+2)+(maskedSupportEdges (L+E+1) Y mask).card+
        (jointDefectMass N L (separatedPairs mask L) : ℝ))/(2 : ℝ)^(2*L) := by
  simp_rw [bTwo_signed_eq_near_add_far hL mask hmask]
  have hadd (f g : SmallSample C Y → ℝ) :
      finiteUniformAverage (fun i => f i+g i)=finiteUniformAverage f+finiteUniformAverage g := by
    unfold finiteUniformAverage
    rw [Finset.sum_add_distrib,add_div]
  rw [hadd]
  have hn := finiteUniformAverage_mono
    (fun sigma => near_signedPairMass_le hN hL hC hY mask hmask sigma)
  have hnear : finiteUniformAverage (fun sigma : SmallSample C Y =>
      ∑ xy ∈ nearMarkedPairs (L+E+1) (fullGoodMask N (L+E+1) Y mask),
        signedPairProbability C L E Y sigma xy.1 xy.2) ≤
        (8*(N : ℝ)*(L+E+2))/(2 : ℝ)^(2*L) := by
    simpa [finiteUniformAverage,Fintype.card_ne_zero] using hn
  have hfar := average_far_signedPairMass_le (Y := Y) hL hC mask hmask
  exact (add_le_add hnear hfar).trans_eq (by ring)

end
end PaperC.V282.ExactMarkedPairCosts
