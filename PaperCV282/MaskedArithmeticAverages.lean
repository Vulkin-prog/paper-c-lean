import PaperCV282.MaskedArithmeticGeometry
import PaperC.Asymptotics.MaskedPoissonCritical

/-!
# Exact masked conditional Stein terms

The retained whole-support mask is passed to the historical masked
indicator family. Removed coordinates are identically false. Finite
neighborhood reindexing and the proved coordinate-split averaging theorem
identify the actual conditional b1 and averaged b2 with the exact induced
pair populations. No probability-approximation premise is used.
-/

namespace PaperC.V282.MaskedArithmeticAverages

open LargePrimeDependencyGraph MaskedSteinChen MaskedPoissonCritical SteinChenTerms
open ConditionalAGGAverage ConditionalAGGInstantiation ConditionalDependencyGraph
open ConditionalStartProbability ArratiaGoldsteinGordonInput SectionTwelveMoments
open MaskedArithmeticGeometry SectionThirteenFiniteBound
open scoped BigOperators

noncomputable section

/-- Reindexing the actual closed graph neighborhoods by natural ordered pairs. -/
theorem sum_closedNeighborhood_eq (N L Y : ℕ) (f : ℕ × ℕ → ℝ) :
    (∑ x : {x : ℕ // x ∈ goodStarts N L Y},
      ∑ y ∈ closedNeighborhood (largePrimeDependencyGraph N L Y) x, f (x.val,y.val)) =
        ∑ p ∈ closedDependencyPairs N L Y, f p := by
  classical
  have hs : (∑ x : {x : ℕ // x ∈ goodStarts N L Y},
      ∑ y ∈ closedNeighborhood (largePrimeDependencyGraph N L Y) x, f (x.val,y.val)) =
      ∑ p : ClosedNeighborhoodPair N L Y, f (p.1.val,p.2.val.val) := by
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro x hx
    exact Finset.sum_subtype _ (fun _ => Iff.rfl) _
  rw [hs]
  have he := Fintype.sum_equiv (closedNeighborhoodPairEquiv N L Y)
    (fun p : ClosedNeighborhoodPair N L Y => f (p.1.val,p.2.val.val))
    (fun p : {p : ℕ × ℕ // p ∈ closedDependencyPairs N L Y} => f p.val) (fun _ => rfl)
  rw [he]
  exact (Finset.sum_subtype _ (fun _ => Iff.rfl) _).symm

/-- Reindexing the actual open graph neighborhoods by natural ordered edges. -/
theorem sum_openNeighborhood_eq (N L Y : ℕ) (f : ℕ × ℕ → ℝ) :
    (∑ x : {x : ℕ // x ∈ goodStarts N L Y},
      ∑ y ∈ (closedNeighborhood (largePrimeDependencyGraph N L Y) x).erase x, f (x.val,y.val)) =
        ∑ p ∈ orderedDependencyEdges N L Y, f p := by
  classical
  have hs : (∑ x : {x : ℕ // x ∈ goodStarts N L Y},
      ∑ y ∈ (closedNeighborhood (largePrimeDependencyGraph N L Y) x).erase x, f (x.val,y.val)) =
      ∑ p : OpenNeighborhoodPair N L Y, f (p.1.val,p.2.val.val) := by
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro x hx
    exact Finset.sum_subtype _ (fun _ => Iff.rfl) _
  rw [hs]
  have he := Fintype.sum_equiv (openNeighborhoodPairEquiv N L Y)
    (fun p : OpenNeighborhoodPair N L Y => f (p.1.val,p.2.val.val))
    (fun p : {p : ℕ × ℕ // p ∈ orderedDependencyEdges N L Y} => f p.val) (fun _ => rfl)
  rw [he]
  exact (Finset.sum_subtype _ (fun _ => Iff.rfl) _).symm

/-- Natural pair-mask restriction commutes exactly with a finite sum. -/
theorem sum_pair_mask_eq (s : Finset (ℕ × ℕ)) (mask : Finset ℕ) (f : ℕ × ℕ → ℝ) :
    (∑ p ∈ s, if p.1 ∈ mask ∧ p.2 ∈ mask then f p else 0) =
      ∑ p ∈ s ∩ mask.product mask, f p := by
  classical
  rw [← Finset.sum_filter]
  congr 1
  ext p
  simp

/-- Exact first Stein term for the historical family restricted to any deterministic mask. -/
theorem bOne_masked_eq {N L Y : ℕ} (mask : Finset ℕ)
    (hN : 2 ≤ N) (hL : 0 < L) (hLY : L + 1 ≤ Y)
    (sigma : SmallSample (dyadicCutoff N L) Y) :
    bOne (largeUniformPMF (dyadicCutoff N L) Y)
      (maskedConditionedGoodIndicator N L Y mask sigma) (largePrimeDependencyGraph N L Y) =
        (maskedSteinBOne N L Y mask : ℝ) := by
  classical
  unfold bOne
  simp_rw [marginal_maskedConditionedGoodIndicator mask hN hL hLY sigma]
  have hsum : (∑ x : {x : ℕ // x ∈ goodStarts N L Y},
      ∑ y ∈ closedNeighborhood (largePrimeDependencyGraph N L Y) x,
        (if x.val ∈ mask then (1 : ℝ) / 2 ^ L else 0) *
          (if y.val ∈ mask then (1 : ℝ) / 2 ^ L else 0)) =
      ∑ x : {x : ℕ // x ∈ goodStarts N L Y},
        ∑ y ∈ closedNeighborhood (largePrimeDependencyGraph N L Y) x,
          (if x.val ∈ mask ∧ y.val ∈ mask then (1 : ℝ) / 2 ^ (2 * L) else 0) := by
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro y hy
    by_cases hx : x.val ∈ mask <;> by_cases hy : y.val ∈ mask <;>
      simp [hx,hy,show 2 * L = L + L by omega,pow_add]
  rw [hsum, sum_closedNeighborhood_eq N L Y
    (fun p => if p.1 ∈ mask ∧ p.2 ∈ mask then (1 : ℝ) / 2 ^ (2 * L) else 0), sum_pair_mask_eq]
  rw [maskedSteinBOne_eq_card_div]
  simp [maskedClosedDependencyPairs,div_eq_mul_inv]

/-- Masking a conditional joint marginal is exactly multiplication by the two site indicators. -/
theorem jointMarginal_masked_eq {N L Y : ℕ} (mask : Finset ℕ)
    (sigma : SmallSample (dyadicCutoff N L) Y)
    (x y : {x : ℕ // x ∈ goodStarts N L Y}) :
    jointMarginal (largeUniformPMF (dyadicCutoff N L) Y)
      (maskedConditionedGoodIndicator N L Y mask sigma) x y =
        if x.val ∈ mask ∧ y.val ∈ mask then
          jointMarginal (largeUniformPMF (dyadicCutoff N L) Y)
            (conditionedGoodIndicator N L Y sigma) x y else 0 := by
  classical
  by_cases hx : x.val ∈ mask <;> by_cases hy : y.val ∈ mask <;>
    simp [jointMarginal,eventProbability,maskedConditionedGoodIndicator,hx,hy]

/-- The coordinate split proves the masked conditional joint averaging identity. -/
theorem average_jointMarginal_masked_eq (N L Y : ℕ) (mask : Finset ℕ)
    (x y : {x : ℕ // x ∈ goodStarts N L Y}) :
    finiteUniformAverage (fun sigma : SmallSample (dyadicCutoff N L) Y =>
      jointMarginal (largeUniformPMF (dyadicCutoff N L) Y)
        (maskedConditionedGoodIndicator N L Y mask sigma) x y) =
      if x.val ∈ mask ∧ y.val ∈ mask then (jointStartProbability N L x.val y.val : ℝ) else 0 := by
  classical
  simp_rw [jointMarginal_masked_eq]
  by_cases h : x.val ∈ mask ∧ y.val ∈ mask
  · simp only [if_pos h]
    exact conditionalJointAverageStatement N L Y x y
  · simp [h,finiteUniformAverage]

/-- Exact averaged second Stein term, retaining only edges of the actual mask. -/
theorem average_bTwo_masked_eq (N L Y : ℕ) (mask : Finset ℕ) :
    finiteUniformAverage (fun sigma : SmallSample (dyadicCutoff N L) Y =>
      bTwo (largeUniformPMF (dyadicCutoff N L) Y)
        (maskedConditionedGoodIndicator N L Y mask sigma) (largePrimeDependencyGraph N L Y)) =
      (maskedSteinBTwoAverage N L Y mask : ℝ) := by
  classical
  unfold bTwo
  rw [finiteUniformAverage_fintypeSum]
  simp_rw [finiteUniformAverage_finsetSum,average_jointMarginal_masked_eq]
  rw [sum_openNeighborhood_eq N L Y
    (fun p => if p.1 ∈ mask ∧ p.2 ∈ mask then (jointStartProbability N L p.1 p.2 : ℝ) else 0), sum_pair_mask_eq]
  simp [maskedSteinBTwoAverage,jointPairMass,maskedDependencyEdges]

/-- Passing the exact whole-support good mask does not remove any further site historically. -/
theorem historical_maskedGood_eq_full {N L Y : ℕ} {mask : Finset ℕ}
    (hmask : mask ⊆ dyadicBlock N) :
    maskedGoodStarts N L Y (fullGoodMask N L Y mask) = fullGoodMask N L Y mask :=
  Finset.inter_eq_right.mpr (fullGoodMask_subset_historical_good hmask)

/-- The induced open-edge population is the literal whole-support retained graph. -/
theorem historical_maskedEdges_eq_full {N L Y : ℕ} {mask : Finset ℕ}
    (hmask : mask ⊆ dyadicBlock N) :
    maskedDependencyEdges N L Y (fullGoodMask N L Y mask) = fullMaskedEdges N L Y mask := by
  classical
  ext p
  simp only [mem_maskedDependencyEdges,mem_orderedDependencyEdges,mem_fullMaskedEdges]
  constructor
  · rintro ⟨⟨_,_,ha⟩,hx,hy⟩
    exact ⟨hx,hy,ha⟩
  · rintro ⟨hx,hy,ha⟩
    exact ⟨⟨fullGoodMask_subset_historical_good hmask hx,
      fullGoodMask_subset_historical_good hmask hy,ha⟩,hx,hy⟩

/-- The induced closed population is the exact diagonal plus the actual retained edges. -/
theorem historical_maskedClosed_eq_full {N L Y : ℕ} {mask : Finset ℕ}
    (hmask : mask ⊆ dyadicBlock N) :
    maskedClosedDependencyPairs N L Y (fullGoodMask N L Y mask) = fullMaskedClosedPairs N L Y mask := by
  rw [maskedClosedDependencyPairs_eq_diag_union_edges,historical_maskedGood_eq_full hmask,
    historical_maskedEdges_eq_full hmask]
  rfl

/-- Actual good-site marginals are exactly p; all other historical coordinates are false. -/
theorem marginal_fullGoodMask {N L Y : ℕ} (mask : Finset ℕ)
    (hN : 2 ≤ N) (hL : 0 < L) (hLY : L + 1 ≤ Y)
    (sigma : SmallSample (dyadicCutoff N L) Y)
    (x : {x : ℕ // x ∈ goodStarts N L Y}) :
    marginal (largeUniformPMF (dyadicCutoff N L) Y)
      (maskedConditionedGoodIndicator N L Y (fullGoodMask N L Y mask) sigma) x =
        if x.val ∈ fullGoodMask N L Y mask then (1 : ℝ) / 2 ^ L else 0 :=
  marginal_maskedConditionedGoodIndicator _ hN hL hLY sigma x

/-- The actual first term is precisely the induced diagonal/edge count times p squared. -/
theorem bOne_fullGoodMask_eq {N L Y : ℕ} (mask : Finset ℕ)
    (hmask : mask ⊆ dyadicBlock N) (hN : 2 ≤ N) (hL : 0 < L) (hLY : L + 1 ≤ Y)
    (sigma : SmallSample (dyadicCutoff N L) Y) :
    bOne (largeUniformPMF (dyadicCutoff N L) Y)
      (maskedConditionedGoodIndicator N L Y (fullGoodMask N L Y mask) sigma)
      (largePrimeDependencyGraph N L Y) =
        ((fullGoodMask N L Y mask).card + (fullMaskedEdges N L Y mask).card : ℝ) / 2 ^ (2 * L) := by
  rw [bOne_masked_eq _ hN hL hLY sigma,maskedSteinBOne_eq_card_div,
    historical_maskedClosed_eq_full hmask,card_fullMaskedClosedPairs]
  push_cast
  rfl

/-- The actual averaged second term is the exact joint mass of retained ordered edges. -/
theorem average_bTwo_fullGoodMask_eq {N L Y : ℕ} (mask : Finset ℕ)
    (hmask : mask ⊆ dyadicBlock N) :
    finiteUniformAverage (fun sigma : SmallSample (dyadicCutoff N L) Y =>
      bTwo (largeUniformPMF (dyadicCutoff N L) Y)
        (maskedConditionedGoodIndicator N L Y (fullGoodMask N L Y mask) sigma)
        (largePrimeDependencyGraph N L Y)) =
      (jointPairMass N L (fullMaskedEdges N L Y mask) : ℝ) := by
  rw [average_bTwo_masked_eq]
  unfold maskedSteinBTwoAverage
  rw [historical_maskedEdges_eq_full hmask]

/-- The historical supergraph is an exact dependency graph for the retained indicator family. -/
theorem hasExactDependencyGraph_fullGoodMask {N L Y : ℕ} (mask : Finset ℕ)
    (hL : 0 < L) (sigma : SmallSample (dyadicCutoff N L) Y) :
    HasExactDependencyGraph (largeUniformPMF (dyadicCutoff N L) Y)
      (maskedConditionedGoodIndicator N L Y (fullGoodMask N L Y mask) sigma)
      (largePrimeDependencyGraph N L Y) :=
  hasExactDependencyGraph_maskedConditionedGoodIndicator _ hL sigma

/-- The scalar Stein parameter is the retained mask's own mean in every environment. -/
theorem poissonParameter_fullGoodMask_eq {N L Y : ℕ} (mask : Finset ℕ)
    (hmask : mask ⊆ dyadicBlock N) (hN : 2 ≤ N) (hL : 0 < L) (hLY : L + 1 ≤ Y)
    (sigma : SmallSample (dyadicCutoff N L) Y) :
    poissonParameter (largeUniformPMF (dyadicCutoff N L) Y)
      (maskedConditionedGoodIndicator N L Y (fullGoodMask N L Y mask) sigma) =
        (fullGoodMask N L Y mask).card / (2 : ℝ) ^ L := by
  rw [poissonParameter_maskedConditioned_eq _ hN hL hLY sigma 0]
  have h := maskedCommonGoodPoissonRate_eq (fullGoodMask N L Y mask) hN hL hLY
  rw [historical_maskedGood_eq_full hmask] at h
  exact h

end
end PaperC.V282.MaskedArithmeticAverages
