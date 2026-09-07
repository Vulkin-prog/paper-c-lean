import PaperCV282.SignedMarkedSeparatedRelations
import PaperCV282.SignedGeometricWeights
import PaperCV282.BulkMarkedFirstCost
import PaperCV282.BulkMarkedLocalCosts
import PaperCV282.MacroAggregateWeightedCosts

/-! # Actual signed pair costs with directional weights kept inside the label sums -/
namespace PaperC.V282.MacroAggregateCosts

open Affine ExactMarkedModel ExactMarkedDependency SignedMarkedSeparatedRelations SignedGeometricWeights
open ExactMarkedPairCosts ExactMarkedLocalProbability LabelledProcessCosts
open ConditionalStartProbability ArratiaGoldsteinGordonInput SectionThirteenFiniteBound
open SectionThirteenCouplings ConditionalAGGAverage ConditionalAGGInstantiation
open WindowValues MaskedArithmeticGeometry MaskedPairGeometry SectionTwelveMoments
open DictionaryMarginalCap TwoWindowParity RelationProfileRestriction MacroAggregateWeightedCosts
open DirectionalSteinComparison BulkSupportGraph BulkProcessCosts DictionaryFieldFirstCost
open MacroscopicMaskGeometry BulkMarkedDependency
open scoped BigOperators

noncomputable section

local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

def signedRatePairSum (L E : ℕ) (w : (Fin (E+1) × F₂) → (Fin (E+1) × F₂) → ℝ) : ℝ :=
  ∑ a, ∑ b, w a b*(signedMarkRate L a.1.val : ℝ)*(signedMarkRate L b.1.val : ℝ)

def weightedSignedPair (C L E Y : ℕ) (sigma : SmallSample C Y) (x y : ℕ)
    (w : (Fin (E+1) × F₂) → (Fin (E+1) × F₂) → ℝ) : ℝ :=
  ∑ a, ∑ b, w a b * eventProbability (largeUniformPMF C Y) (fun eta =>
    conditionedSignedAt C L E Y sigma x a eta = true ∧
    conditionedSignedAt C L E Y sigma y b eta = true)

theorem signedRatePairSum_nonneg (L E : ℕ) (w : (Fin (E+1) × F₂) → (Fin (E+1) × F₂) → ℝ)
    (hw : ∀ a b, 0 ≤ w a b) : 0 ≤ signedRatePairSum L E w := by
  unfold signedRatePairSum
  exact Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ =>
    mul_nonneg (mul_nonneg (hw a b) (by positivity)) (by positivity)))

/-- The two bounds on the Hessian give a uniform minimum after the geometric sum. -/
theorem signedRatePairSum_le {L E : ℕ}
    (w : (Fin (E+1) × F₂) → (Fin (E+1) × F₂) → ℝ) {K : ℝ}
    (hK : 0 ≤ K) (hw1 : ∀ a b, w a b ≤ 1)
    (hwd : ∀ a b, w a b ≤ K /
      (Real.sqrt (signedGeometricWeight a.1.val)*Real.sqrt (signedGeometricWeight b.1.val))) :
    signedRatePairSum L E w ≤ (1/(2 : ℝ)^L)^2 * min 1 (12*K) := by
  have h := weighted_geometric_pair_sum_le w hK hw1 hwd
  have heq : signedRatePairSum L E w = (1/(2 : ℝ)^L)^2 *
      (∑ a, ∑ b, w a b*signedGeometricWeight a.1.val*signedGeometricWeight b.1.val) := by
    unfold signedRatePairSum
    simp_rw [signedMarkRate_eq_base_mul_weight]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [heq]
  exact mul_le_mul_of_nonneg_left h (sq_nonneg _)

/-- The four-case local calculation applies to each actual signed label separately. -/
theorem local_signed_joint_le_four {C L E Y x y : ℕ} {sites mask : Finset ℕ}
    (hsite : ∀ x ∈ sites, 2 ≤ x) (hL : 1 ≤ L) (hC : ∀ x ∈ sites, x+L+E+1 ≤ C)
    (hY : 2*(L+E+2) ≤ Y) (hmask : mask ⊆ sites)
    (hx : x ∈ goodMask (L+E+1) Y mask)
    (hy : y ∈ goodMask (L+E+1) Y mask)
    (hxy : x ≠ y) (hd : Nat.dist x y ≤ L+E+1) (sigma : SmallSample C Y)
    (a b : Fin (E+1) × F₂) :
    eventProbability (largeUniformPMF C Y) (fun eta =>
      conditionedSignedAt C L E Y sigma x a eta = true ∧
      conditionedSignedAt C L E Y sigma y b eta = true) ≤
        4*(signedMarkRate L a.1.val : ℝ)*(signedMarkRate L b.1.val : ℝ) := by
  have hordered (x y : ℕ) (hx : x ∈ goodMask (L+E+1) Y mask)
      (hy : y ∈ goodMask (L+E+1) Y mask) (hxy : x<y)
      (hd : Nat.dist x y ≤ L+E+1) (a b : Fin (E+1) × F₂) :
      eventProbability (largeUniformPMF C Y) (fun eta =>
        conditionedSignedAt C L E Y sigma x a eta = true ∧
        conditionedSignedAt C L E Y sigma y b eta = true) ≤
        4*(signedMarkRate L a.1.val : ℝ)*(signedMarkRate L b.1.val : ℝ) := by
    have hxblock := hmask (mem_goodMask.mp hx).1
    have hyblock := hmask (mem_goodMask.mp hy).1
    have hx2 := hsite x hxblock
    have hxyadd : x+(y-x)=y := by omega
    have hdist : Nat.dist x y=y-x := Nat.dist_eq_sub_of_le hxy.le
    have hcut : y-1+(L+E+2) ≤ C+1 := by
      have hb := hC y hyblock
      have hy2 := hsite y hyblock
      omega
    simp only [conditionedSignedAt,signedAt,decide_eq_true_eq]
    have hp := conditioned_signed_pair_le_four (C := C) (Y := Y) (L := L) (E := E)
      (e := a.1.val) (f := b.1.val) (d := y-x) hx2 hL
      (by omega) (by omega) (by omega) (by simpa only [hdist] using hd)
      (by simpa only [hxyadd] using hcut) hY
      (BulkMarkedLocalCosts.good_maximal_vertex hsite hmask hx)
      (by simpa only [hxyadd] using BulkMarkedLocalCosts.good_maximal_vertex hsite hmask hy) a.2 b.2 sigma
    simpa only [hxyadd] using hp
  rcases lt_or_gt_of_ne hxy with hlt | hgt
  · exact hordered x y hx hy hlt hd a b
  · have h := hordered y x hy hx hgt (by simpa only [Nat.dist_comm] using hd) b a
    have heq : (fun eta => conditionedSignedAt C L E Y sigma x a eta = true ∧
        conditionedSignedAt C L E Y sigma y b eta = true) =
        (fun eta => conditionedSignedAt C L E Y sigma y b eta = true ∧
        conditionedSignedAt C L E Y sigma x a eta = true) := by
      funext eta; exact propext and_comm
    rw [heq]
    nlinarith

theorem weightedSignedPair_local_le {C L E Y x y : ℕ} {sites mask : Finset ℕ}
    (hsite : ∀ x ∈ sites, 2 ≤ x) (hL : 1 ≤ L) (hC : ∀ x ∈ sites, x+L+E+1 ≤ C)
    (hY : 2*(L+E+2) ≤ Y) (hmask : mask ⊆ sites)
    (hx : x ∈ goodMask (L+E+1) Y mask)
    (hy : y ∈ goodMask (L+E+1) Y mask)
    (hxy : x ≠ y) (hd : Nat.dist x y ≤ L+E+1) (sigma : SmallSample C Y)
    (w : (Fin (E+1) × F₂) → (Fin (E+1) × F₂) → ℝ) (hw : ∀ a b, 0 ≤ w a b) :
    weightedSignedPair C L E Y sigma x y w ≤ 4*signedRatePairSum L E w := by
  unfold weightedSignedPair signedRatePairSum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b _
  have h := mul_le_mul_of_nonneg_left
    (local_signed_joint_le_four hsite hL hC hY hmask hx hy hxy hd sigma a b) (hw a b)
  convert h using 1; ring

/-- Averaging a fixed weight commutes with the finite conditioning average. -/
theorem finiteUniformAverage_const_mul {ι : Type*} [Fintype ι] (c : ℝ) (f : ι → ℝ) :
    finiteUniformAverage (fun i => c*f i) = c*finiteUniformAverage f := by
  unfold finiteUniformAverage
  rw [← Finset.mul_sum]
  ring

/-- The signed separated bound uses the full value mass at Q+1 vertices. -/
theorem average_weightedSignedPair_le {C x y L E Y : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y) (hL : 1 ≤ L)
    (w : (Fin (E+1) × F₂) → (Fin (E+1) × F₂) → ℝ) (hw : ∀ a b, 0 ≤ w a b) :
    finiteUniformAverage (fun sigma : SmallSample C Y => weightedSignedPair C L E Y sigma x y w) ≤
      signedRatePairSum L E w * (2 : ℝ)^relationRho (twoValueSystem C x y (L+E+1)) := by
  unfold weightedSignedPair
  rw [average_finset_sum]
  simp_rw [average_finset_sum, finiteUniformAverage_const_mul]
  unfold signedRatePairSum
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro a _
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro b _
  have h := mul_le_mul_of_nonneg_left
    (average_signed_joint_probability_le_full_value_weight hx hy hL a b (C := C) (Y := Y)) (hw a b)
  rw [maximal_jointValueSystem_eq_twoValueSystem hx hy] at h
  convert h using 1; ring


/-- Splitting off the independent baseline is exact for the full-value mass. -/
theorem sum_value_relation_weight_eq (C Q : ℕ) (s : Finset (ℕ × ℕ)) :
    (∑ xy ∈ s, (2 : ℝ)^relationRho (twoValueSystem C xy.1 xy.2 Q)) =
      (s.card : ℝ)+(valueWeightMass C Q s : ℝ) := by
  have hp (xy : ℕ × ℕ) : 1 ≤ (2 : ℕ)^relationRho (twoValueSystem C xy.1 xy.2 Q) := by
    exact Nat.one_le_pow _ _ (by norm_num)
  unfold valueWeightMass
  rw [Nat.cast_sum]
  simp_rw [Nat.cast_sub (hp _), Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
  rw [Finset.sum_sub_distrib]
  simp

/-- Every far support edge lies in the actual maximal separated-pair mask. -/
theorem farMarkedPairs_subset_separated (Q Y : ℕ) (mask : Finset ℕ) :
    farMarkedPairs Q Y mask ⊆ separatedPairs mask Q := by
  intro xy hxy
  obtain ⟨he,hd⟩ := Finset.mem_filter.mp hxy
  obtain ⟨hx,hy,ha⟩ := mem_maskedSupportEdges.mp he
  exact (mem_separatedPairs mask Q xy.1 xy.2).mpr ⟨hx,hy,hd⟩

/-- The enlarged full-value defect mass is monotone under restriction of pairs. -/
theorem valueWeightMass_mono {s t : Finset (ℕ × ℕ)} (C Q : ℕ) (h : s ⊆ t) :
    valueWeightMass C Q s ≤ valueWeightMass C Q t :=
  Finset.sum_le_sum_of_subset h

theorem sum_near_weightedSignedPair_le {C L E Y : ℕ} {sites mask : Finset ℕ}
    (hsite : ∀ x ∈ sites, 2 ≤ x) (hL : 1 ≤ L) (hC : ∀ x ∈ sites, x+L+E+1 ≤ C)
    (hY : 2*(L+E+2) ≤ Y) (hmask : mask ⊆ sites) (sigma : SmallSample C Y)
    (w : (Fin (E+1) × F₂) → (Fin (E+1) × F₂) → ℝ) (hw : ∀ a b, 0 ≤ w a b) :
    (∑ xy ∈ nearMarkedPairs (L+E+1) (goodMask (L+E+1) Y mask),
      weightedSignedPair C L E Y sigma xy.1 xy.2 w) ≤
      signedRatePairSum L E w * (8*(sites.card : ℝ)*(L+E+2)) := by
  have hg : goodMask (L+E+1) Y mask ⊆ sites :=
    fun x hx => hmask (goodMask_subset (L+E+1) Y mask hx)
  have hsum : (∑ xy ∈ nearMarkedPairs (L+E+1) (goodMask (L+E+1) Y mask),
      weightedSignedPair C L E Y sigma xy.1 xy.2 w) ≤
      ∑ _xy ∈ nearMarkedPairs (L+E+1) (goodMask (L+E+1) Y mask),
        4*signedRatePairSum L E w := by
    apply Finset.sum_le_sum
    intro xy hxy
    obtain ⟨hp,hd⟩ := Finset.mem_filter.mp hxy
    obtain ⟨hx,hy,hne⟩ := Finset.mem_offDiag.mp hp
    exact weightedSignedPair_local_le hsite hL hC hY hmask hx hy hne hd sigma w hw
  have hc : ((nearMarkedPairs (L+E+1) (goodMask (L+E+1) Y mask)).card : ℝ) ≤
      2*(sites.card : ℝ)*(L+E+2) := by
    exact_mod_cast BulkMarkedLocalCosts.card_nearMarkedPairs_le (goodMask (L+E+1) Y mask) hg
  simp only [Finset.sum_const,nsmul_eq_mul] at hsum
  have hr := signedRatePairSum_nonneg L E w hw
  nlinarith

/-- Weighted distant edges retain their own full-value relations when averaged. -/
theorem average_sum_far_weightedSignedPair_le {C L E Y : ℕ} {sites mask : Finset ℕ}
    (hsite : ∀ x ∈ sites, 2 ≤ x) (hL : 1 ≤ L) (hmask : mask ⊆ sites)
    (w : (Fin (E+1) × F₂) → (Fin (E+1) × F₂) → ℝ) (hw : ∀ a b, 0 ≤ w a b) :
    finiteUniformAverage (fun sigma : SmallSample C Y =>
      ∑ xy ∈ farMarkedPairs (L+E+1) Y (goodMask (L+E+1) Y mask),
        weightedSignedPair C L E Y sigma xy.1 xy.2 w) ≤
      signedRatePairSum L E w *
        ((maskedSupportEdges (L+E+1) Y mask).card +
          (valueWeightMass C (L+E+1) (separatedPairs mask (L+E+1)) : ℝ)) := by
  let far := farMarkedPairs (L+E+1) Y (goodMask (L+E+1) Y mask)
  have hgood := goodMask_subset (L+E+1) Y mask
  have hsupp : far ⊆ maskedSupportEdges (L+E+1) Y mask :=
    fun xy hxy => maskedSupportEdges_mono hgood (Finset.mem_filter.mp hxy).1
  have hsep : far ⊆ separatedPairs mask (L+E+1) := by
    intro xy hxy
    have hp := (mem_separatedPairs _ _ _ _).mp (farMarkedPairs_subset_separated _ _ _ hxy)
    exact (mem_separatedPairs _ _ _ _).mpr ⟨hgood hp.1,hgood hp.2.1,hp.2.2⟩
  rw [average_finset_sum]
  have hpoint (xy : ℕ × ℕ) (hxy : xy ∈ far) :
      finiteUniformAverage (fun sigma : SmallSample C Y => weightedSignedPair C L E Y sigma xy.1 xy.2 w) ≤
        signedRatePairSum L E w * (2 : ℝ)^relationRho (twoValueSystem C xy.1 xy.2 (L+E+1)) := by
    have hp := (mem_separatedPairs _ _ _ _).mp (hsep hxy)
    exact average_weightedSignedPair_le
      (by have h := hsite xy.1 (hmask hp.1); omega)
      (by have h := hsite xy.2 (hmask hp.2.1); omega) hL w hw
  have hsum := Finset.sum_le_sum hpoint
  rw [← Finset.mul_sum, sum_value_relation_weight_eq] at hsum
  have hc : (far.card : ℝ) ≤ (maskedSupportEdges (L+E+1) Y mask).card := by
    exact_mod_cast Finset.card_le_card hsupp
  have hm : (valueWeightMass C (L+E+1) far : ℝ) ≤
      (valueWeightMass C (L+E+1) (separatedPairs mask (L+E+1)) : ℝ) := by
    exact_mod_cast valueWeightMass_mono C (L+E+1) hsep
  exact hsum.trans (mul_le_mul_of_nonneg_left (add_le_add hc hm) (signedRatePairSum_nonneg L E w hw))


/-- Actual conditional first cost, before choosing a Hessian factor. -/
theorem typedBOne_signed_le {C L E Y : ℕ} {sites : Finset ℕ}
    (hsite : ∀ x ∈ sites, 2 ≤ x) (hL : 1 ≤ L) (hC : ∀ x ∈ sites, x+L+E+1 ≤ C)
    (hY : L+E+2 ≤ Y) (mask : Finset ℕ) (hmask : mask ⊆ sites)
    (sigma : SmallSample C Y)
    (w : (Fin (E+1) × F₂) → (Fin (E+1) × F₂) → ℝ) (hw : ∀ a b, 0 ≤ w a b) :
    typedBOne (largeUniformPMF C Y)
      (maskedLabelledFamily sites (conditionedSignedAt C L E Y sigma) (goodMask (L+E+1) Y mask))
      Prod.snd (labelledGraph sites (L+E+1) Y (Fin (E+1) × F₂)) w ≤
      signedRatePairSum L E w * (2*(sites.card : ℝ)*(L+E+2)+(maskedSupportEdges (L+E+1) Y mask).card) := by
  rw [typedBOne_labelled_eq _ _ _ _ _ _
    ((goodMask_subset _ _ _).trans hmask)
    (fun a : Fin (E+1) × F₂ => (signedMarkRate L a.1.val : ℝ)) w
    (signedAt_marginal_masked_good hsite hL hC hY mask sigma)]
  change signedRatePairSum L E w * _ ≤ _
  apply mul_le_mul_of_nonneg_left _ (signedRatePairSum_nonneg L E w hw)
  have hclosed : ((closedDictionarySitePairs (L+E+1) Y (goodMask (L+E+1) Y mask)).card : ℝ) ≤
      2*(sites.card : ℝ)*(L+E+2)+(maskedSupportEdges (L+E+1) Y (goodMask (L+E+1) Y mask)).card := by
    exact_mod_cast BulkMarkedFirstCost.card_closedDictionarySitePairs_le (goodMask (L+E+1) Y mask)
      ((goodMask_subset _ _ _).trans hmask)
  have hedge : ((maskedSupportEdges (L+E+1) Y (goodMask (L+E+1) Y mask)).card : ℝ) ≤
      (maskedSupportEdges (L+E+1) Y mask).card := by
    exact_mod_cast Finset.card_le_card (maskedSupportEdges_mono (goodMask_subset _ _ _))
  linarith

/-- Exact regrouping of the weighted second cost on the two genuine site-pair sets. -/
theorem typedBTwo_signed_eq_near_add_far {C L E Y : ℕ} {sites : Finset ℕ}
    (hL : 1 ≤ L) (mask : Finset ℕ) (hmask : mask ⊆ sites)
    (sigma : SmallSample C Y) (w : (Fin (E+1) × F₂) → (Fin (E+1) × F₂) → ℝ) :
    typedBTwo (largeUniformPMF C Y)
      (maskedLabelledFamily sites (conditionedSignedAt C L E Y sigma) (goodMask (L+E+1) Y mask))
      Prod.snd (labelledGraph sites (L+E+1) Y (Fin (E+1) × F₂)) w =
      (∑ xy ∈ nearMarkedPairs (L+E+1) (goodMask (L+E+1) Y mask),
        weightedSignedPair C L E Y sigma xy.1 xy.2 w) +
      ∑ xy ∈ farMarkedPairs (L+E+1) Y (goodMask (L+E+1) Y mask),
        weightedSignedPair C L E Y sigma xy.1 xy.2 w := by
  rw [typedBTwo_labelled_eq]
  · rw [weightedLabelPairMass,BulkMarkedLocalCosts.bulk_neighborPairs_eq_near_union_far,
      Finset.sum_union (disjoint_near_farMarkedPairs _ _ _)]
    rfl
  · exact (goodMask_subset _ _ _).trans hmask
  · intro x hx a b hab eta
    exact signedAt_disjoint hL x a b hab (assemble C Y sigma eta)

theorem finiteUniformAverage_add {ι : Type*} [Fintype ι] (f g : ι → ℝ) :
    finiteUniformAverage (fun i => f i+g i)=finiteUniformAverage f+finiteUniformAverage g := by
  unfold finiteUniformAverage
  rw [Finset.sum_add_distrib,add_div]

/-- True averaged second cost with maximal full-value relations, not base start relations. -/
theorem average_typedBTwo_signed_le {C L E Y : ℕ} {sites : Finset ℕ}
    (hsite : ∀ x ∈ sites, 2 ≤ x) (hL : 1 ≤ L) (hC : ∀ x ∈ sites, x+L+E+1 ≤ C)
    (hY : 2*(L+E+2) ≤ Y) (mask : Finset ℕ) (hmask : mask ⊆ sites)
    (w : (Fin (E+1) × F₂) → (Fin (E+1) × F₂) → ℝ) (hw : ∀ a b, 0 ≤ w a b) :
    finiteUniformAverage (fun sigma : SmallSample C Y => typedBTwo (largeUniformPMF C Y)
      (maskedLabelledFamily sites (conditionedSignedAt C L E Y sigma) (goodMask (L+E+1) Y mask))
      Prod.snd (labelledGraph sites (L+E+1) Y (Fin (E+1) × F₂)) w) ≤
      signedRatePairSum L E w * (8*(sites.card : ℝ)*(L+E+2)+(maskedSupportEdges (L+E+1) Y mask).card+
        (valueWeightMass C (L+E+1) (separatedPairs mask (L+E+1)) : ℝ)) := by
  simp_rw [typedBTwo_signed_eq_near_add_far hL mask hmask,finiteUniformAverage_add]
  have hn := finiteUniformAverage_mono (fun sigma =>
    sum_near_weightedSignedPair_le hsite hL hC hY hmask sigma w hw)
  have hnear : finiteUniformAverage (fun sigma : SmallSample C Y =>
      ∑ xy ∈ nearMarkedPairs (L+E+1) (goodMask (L+E+1) Y mask),
        weightedSignedPair C L E Y sigma xy.1 xy.2 w) ≤
      signedRatePairSum L E w*(8*(sites.card : ℝ)*(L+E+2)) := by
    simpa [finiteUniformAverage,Fintype.card_ne_zero] using hn
  have hfar := average_sum_far_weightedSignedPair_le (C := C) (Y := Y) hsite hL hmask w hw
  exact (add_le_add hnear hfar).trans_eq (by ring)

/-- Both weighted graph costs share the same dimension-free geometric coefficient. -/
theorem average_typedCost_signed_le {C L E Y : ℕ} {sites : Finset ℕ}
    (hsite : ∀ x ∈ sites, 2 ≤ x) (hL : 1 ≤ L) (hC : ∀ x ∈ sites, x+L+E+1 ≤ C)
    (hY : 2*(L+E+2) ≤ Y) (mask : Finset ℕ) (hmask : mask ⊆ sites)
    (w : (Fin (E+1) × F₂) → (Fin (E+1) × F₂) → ℝ) (hw : ∀ a b, 0 ≤ w a b) :
    finiteUniformAverage (fun sigma : SmallSample C Y => typedCost (largeUniformPMF C Y)
      (maskedLabelledFamily sites (conditionedSignedAt C L E Y sigma) (goodMask (L+E+1) Y mask))
      Prod.snd (labelledGraph sites (L+E+1) Y (Fin (E+1) × F₂)) w) ≤
      signedRatePairSum L E w * (10*(sites.card : ℝ)*(L+E+2)+2*(maskedSupportEdges (L+E+1) Y mask).card+
        (valueWeightMass C (L+E+1) (separatedPairs mask (L+E+1)) : ℝ)) := by
  unfold typedCost
  rw [finiteUniformAverage_add]
  have hn := finiteUniformAverage_mono (fun sigma =>
    typedBOne_signed_le (E := E) (Y := Y) hsite hL hC (by omega) mask hmask sigma w hw)
  have hone : finiteUniformAverage (fun sigma : SmallSample C Y => typedBOne (largeUniformPMF C Y)
      (maskedLabelledFamily sites (conditionedSignedAt C L E Y sigma) (goodMask (L+E+1) Y mask))
      Prod.snd (labelledGraph sites (L+E+1) Y (Fin (E+1) × F₂)) w) ≤
      signedRatePairSum L E w*(2*(sites.card : ℝ)*(L+E+2)+(maskedSupportEdges (L+E+1) Y mask).card) := by
    simpa [finiteUniformAverage,Fintype.card_ne_zero] using hn
  have htwo := average_typedBTwo_signed_le hsite hL hC hY mask hmask w hw
  exact (add_le_add hone htwo).trans_eq (by ring)

end
end PaperC.V282.MacroAggregateCosts
