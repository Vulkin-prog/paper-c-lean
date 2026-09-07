import PaperCV282.FiniteStartMaskPairBounds

/-! # Scalar Stein costs on genuine finite start populations

The first cost is the count of diagonal and graph pairs. The averaged second
cost is the actual unconditional joint mass, with no lower-endpoint change.
-/
namespace PaperC.V282.FiniteStartMaskSteinCosts

open Affine ArratiaGoldsteinGordonInput ConditionalAGGInstantiation ConditionalAGGAverage
open ConditionalDependencyGraph ConditionalStartProbability FiniteStartMaskModel FiniteStartMaskAverages
open FiniteStartMaskPairBounds MacroscopicMaskGeometry MaskedPairGeometry
open LargePrimeDependencyGraph HostRankMass TwoWindowParity
open SectionThirteenFiniteBound ScalarSteinInput ScalarPoissonBounds
open scoped BigOperators NNReal

noncomputable section
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

theorem sum_mask_pair (mask : Finset ℕ) (f : ℕ × ℕ → ℝ) :
    (∑ x : mask, ∑ y : mask, f (x.val,y.val)) = ∑ xy ∈ mask ×ˢ mask, f xy := by
  have hi (x : mask) : (∑ y : mask, f (x.val,y.val)) = ∑ y ∈ mask, f (x.val,y) :=
    (Finset.sum_subtype mask (fun _ => Iff.rfl) (fun y => f (x.val,y))).symm
  simp_rw [hi]
  rw [← Finset.sum_subtype mask (fun _ => Iff.rfl) (fun x => ∑ y ∈ mask, f (x,y))]
  rw [Finset.sum_product]

theorem sum_closedNeighborhood (L Y : ℕ) (mask : Finset ℕ) (f : ℕ × ℕ → ℝ) :
    (∑ x : mask, ∑ y ∈ closedNeighborhood (startMaskGraph L Y mask) x, f (x.val,y.val)) =
      ∑ xy ∈ mask.diag ∪ maskedSupportEdges L Y mask, f xy := by
  have hf : (mask ×ˢ mask).filter
      (fun xy => xy.2 = xy.1 ∨ LargePrimeAdjacent L Y xy.1 xy.2) =
      mask.diag ∪ maskedSupportEdges L Y mask := by
    ext xy
    simp only [Finset.mem_filter,Finset.mem_product,Finset.mem_union,Finset.mem_diag,
      mem_maskedSupportEdges]
    constructor
    · rintro ⟨⟨hx,hy⟩,he|ha⟩
      · exact Or.inl ⟨hx,he.symm⟩
      · exact Or.inr ⟨hx,hy,ha⟩
    · rintro (⟨hx,he⟩|⟨hx,hy,ha⟩)
      · exact ⟨⟨hx,he ▸ hx⟩,Or.inl he.symm⟩
      · exact ⟨⟨hx,hy⟩,Or.inr ha⟩
  unfold closedNeighborhood
  simp_rw [Finset.sum_filter,startMaskGraph_adj,Subtype.ext_iff]
  rw [sum_mask_pair mask (fun xy => if xy.2=xy.1 ∨ LargePrimeAdjacent L Y xy.1 xy.2 then f xy else 0),← Finset.sum_filter,hf]

theorem sum_openNeighborhood (L Y : ℕ) (mask : Finset ℕ) (f : ℕ × ℕ → ℝ) :
    (∑ x : mask, ∑ y ∈ (closedNeighborhood (startMaskGraph L Y mask) x).erase x,
      f (x.val,y.val)) = ∑ xy ∈ maskedSupportEdges L Y mask, f xy := by
  have hn (x : mask) : (closedNeighborhood (startMaskGraph L Y mask) x).erase x =
      Finset.univ.filter (fun y => LargePrimeAdjacent L Y x.val y.val) := by
    ext y
    simp only [Finset.mem_erase,mem_closedNeighborhood,startMaskGraph_adj,
      Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨hne,he|ha⟩
      · exact False.elim (hne he)
      · exact ha
    · intro ha
      exact ⟨fun he => ha.1 (congrArg Subtype.val he).symm,Or.inr ha⟩
  simp_rw [hn,Finset.sum_filter]
  rw [sum_mask_pair mask (fun xy => if LargePrimeAdjacent L Y xy.1 xy.2 then f xy else 0),← Finset.sum_filter]
  congr 1
  ext xy
  simp [mem_maskedSupportEdges,and_assoc]

theorem bOne_eq {C L Y : ℕ} (mask : Finset ℕ)
    (hL : 0<L) (hLY : L+1≤Y) (hpos : ∀ x∈mask,2≤x)
    (hcut : ∀ x∈mask,x+L≤C)
    (hgood : ∀ x∈mask,∀ i : Fin L, ¬DefectivePredicate.HDefective Y (x+i.val))
    (sigma : SmallSample C Y) :
    bOne (largeUniformPMF C Y) (conditionedIndicator C L Y mask sigma) (startMaskGraph L Y mask) =
      ((mask.card : ℝ)+(maskedSupportEdges L Y mask).card)/(2 : ℝ)^(2*L) := by
  unfold bOne
  simp_rw [marginal_eq_baseline mask hL hLY sigma _ (hpos _ (Subtype.mem _))
    (hcut _ (Subtype.mem _)) (hgood _ (Subtype.mem _))]
  rw [sum_closedNeighborhood L Y mask (fun _ => (1 : ℝ)/2^L*((1 : ℝ)/2^L))]
  have hd : Disjoint mask.diag (maskedSupportEdges L Y mask) := by
    apply Finset.disjoint_left.mpr
    intro xy hdiag hedge
    exact (mem_maskedSupportEdges.mp hedge).2.2.1 (Finset.mem_diag.mp hdiag).2
  rw [Finset.sum_const,Finset.card_union_of_disjoint hd,Finset.diag_card]
  simp only [nsmul_eq_mul,Nat.cast_add]
  rw [show 2*L=L+L by omega,pow_add]
  ring

theorem average_bTwo_eq (C L Y : ℕ) (mask : Finset ℕ) :
    finiteUniformAverage (fun sigma : SmallSample C Y =>
      bTwo (largeUniformPMF C Y) (conditionedIndicator C L Y mask sigma) (startMaskGraph L Y mask)) =
      ∑ xy ∈ maskedSupportEdges L Y mask,
        ((uniformEventProbability (fun omega : SampleSpace C =>
          startAt omega xy.1 L ∧ startAt omega xy.2 L) : ℚ) : ℝ) := by
  unfold bTwo
  rw [finiteUniformAverage_fintypeSum]
  simp_rw [finiteUniformAverage_finsetSum,average_joint]
  exact sum_openNeighborhood L Y mask (fun xy => ((uniformEventProbability
    (fun omega : SampleSpace C => startAt omega xy.1 L ∧ startAt omega xy.2 L) : ℚ) : ℝ))

theorem average_bTwo_good_le {C L Y : ℕ} (mask : Finset ℕ)
    (hL : 0<L) (hY : 2*L≤Y) (hpos : ∀ x∈mask,2≤x) (hcut : ∀ x∈mask,x+L≤C) :
    finiteUniformAverage (fun sigma : SmallSample C Y =>
      bTwo (largeUniformPMF C Y) (conditionedIndicator C L Y (goodMask L Y mask) sigma)
        (startMaskGraph L Y (goodMask L Y mask))) ≤
      (((maskedSupportEdges L Y mask).card : ℝ)+
        (relationWeightMass C L (separatedPairs mask L) : ℝ))/(2 : ℝ)^(2*L) := by
  rw [average_bTwo_eq]
  have h := (Rat.cast_le (K := ℝ)).mpr (sum_joint_goodEdges_le mask hL hY hpos hcut)
  push_cast at h
  exact h

end
end PaperC.V282.FiniteStartMaskSteinCosts
