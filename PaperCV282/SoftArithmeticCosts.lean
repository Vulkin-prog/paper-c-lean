import PaperCV282.SoftGraphDegree
import PaperCV282.TouchingPairMass
import PaperCV282.MaskedBadMass

/-!
# Arithmetic costs for good sites with arbitrary neighbours

The second site may be exceptional. All probabilities below are actual
unconditional probabilities obtained by averaging the conditional field.
Touching pairs pay their full homogeneous mass; only separated pairs pay R2.
-/

namespace PaperC.V282.SoftArithmeticCosts

open Affine ArratiaGoldsteinGordonInput SectionTwelveMoments
open AllStartSoftPoisson AllStartConditionalDependency MaskedArithmeticGeometry
open MaskedBadMass CutoffGraphDegree CutoffGraphCompatibility MaskedPairGeometry
open TouchingPairGeometry TouchingPairMass TwoWindowParity LargePrimeDependencyGraph
open scoped BigOperators

noncomputable section

local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

/-- The affine Fourier estimate needs no good-site assumption on either coordinate. -/
theorem joint_probability_le_baseline_defect {N L x y : ℕ} (hL : 0 < L) :
    (jointStartProbability N L x y : ℝ) ≤
      (1 + (jointDefectWeight N L (x,y) : ℝ)) / (2 : ℝ) ^ (2 * L) := by
  have hq := (le_abs_self _).trans (abs_jointStartProbability_sub_baseline_le N L x y hL)
  have h : jointStartProbability N L x y ≤
      (1 + (jointDefectWeight N L (x,y) : ℚ)) / (2 : ℚ) ^ (2 * L) := by
    rw [add_div]
    linarith
  have hr := (Rat.cast_le (K := ℝ)).mpr h
  push_cast at hr
  exact hr

/-- The homogeneous relation weight bounds even inconsistent affine right-hand sides. -/
theorem joint_probability_le_homogeneous {N L x y : ℕ} (hL : 0 < L) :
    (jointStartProbability N L x y : ℝ) ≤
      (2 : ℝ) ^ relationRho (twoStartSystem (dyadicCutoff N L) x y L) /
        (2 : ℝ) ^ (2 * L) := by
  have h := joint_probability_le_baseline_defect (N := N) (x := x) (y := y) hL
  unfold jointDefectWeight jointRho at h
  rw [Nat.cast_sub Nat.one_le_two_pow] at h
  push_cast at h
  simpa only [add_sub_cancel] using h

/-- Overlap, touching and separated cases, without a good-good restriction. -/
theorem joint_probability_le_three_cases {N L x y : ℕ} (hL : 0 < L) (hxy : x ≠ y) :
    (jointStartProbability N L x y : ℝ) ≤
      (1 + (if L < Nat.dist x y then (jointDefectWeight N L (x,y) : ℝ) else 0) +
        (if Nat.dist x y = L then
          (2 : ℝ) ^ relationRho (twoStartSystem (dyadicCutoff N L) x y L) else 0)) /
        (2 : ℝ) ^ (2 * L) := by
  by_cases hs : L < Nat.dist x y
  · have ht : Nat.dist x y ≠ L := by omega
    simpa only [if_pos hs, if_neg ht, add_zero] using joint_probability_le_baseline_defect hL
  · by_cases ht : Nat.dist x y = L
    · simp only [if_neg hs, if_pos ht, add_zero]
      exact (joint_probability_le_homogeneous hL).trans
        (div_le_div_of_nonneg_right (by linarith) (by positivity))
    · have ho : Nat.dist x y < L := by omega
      rw [jointStartProbability_eq_zero_of_overlap hxy ho]
      simp only [Rat.cast_zero, if_neg hs, if_neg ht, add_zero]
      positivity

/-- Ordered edges can equivalently be selected from the full Cartesian square. -/
theorem support_edges_eq_product_filter (L Y : ℕ) (s : Finset ℕ) :
    maskedSupportEdges L Y s = (s ×ˢ s).filter (fun p => LargePrimeAdjacent L Y p.1 p.2) := by
  classical
  ext p
  simp only [mem_maskedSupportEdges, Finset.mem_filter, Finset.mem_product]
  tauto

/-- Exact conversion between the arithmetic edge population and neighbour sums. -/
theorem support_edge_sum_eq (L Y : ℕ) (s : Finset ℕ) (f : ℕ × ℕ → ℝ) :
    (∑ p ∈ maskedSupportEdges L Y s, f p) =
      ∑ x ∈ s, ∑ y ∈ cutoffNeighbors L Y s x, f (x,y) := by
  classical
  rw [support_edges_eq_product_filter, Finset.sum_filter, Finset.sum_product]
  simp only [cutoffNeighbors, Finset.sum_filter]

/-- Every graph neighbour appears exactly once in the natural-number neighbour set. -/
theorem open_neighbour_sum_eq {N L Y : ℕ}
    (x : {x : ℕ // x ∈ dyadicBlock N}) (f : ℕ → ℝ) :
    (∑ y ∈ (closedNeighborhood (allStartDependencyGraph N L Y) x).erase x, f y.val) =
      ∑ y ∈ cutoffNeighbors L Y (dyadicBlock N) x.val, f y := by
  classical
  rw [← openNeighborhood_image_eq_cutoffNeighbors x, Finset.sum_image]
  intro a _ b _ h
  exact Subtype.val_injective h

/-- The good-by-all pair cost embeds in all actual support edges by positivity. -/
theorem good_all_joint_sum_le_support (N L Y : ℕ) :
    (∑ i ∈ goodSiteIndices N L Y,
      ∑ j ∈ (closedNeighborhood (allStartDependencyGraph N L Y) i).erase i,
        (jointStartProbability N L i.val j.val : ℝ)) ≤
      ∑ p ∈ maskedSupportEdges L Y (dyadicBlock N),
        (jointStartProbability N L p.1 p.2 : ℝ) := by
  classical
  calc
    _ ≤ ∑ i : {x : ℕ // x ∈ dyadicBlock N},
      ∑ j ∈ (closedNeighborhood (allStartDependencyGraph N L Y) i).erase i,
        (jointStartProbability N L i.val j.val : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro i _ _
      apply Finset.sum_nonneg
      intro j _
      exact_mod_cast SteinChenTerms.jointStartProbability_nonneg N L i.val j.val
    _ = ∑ i : {x : ℕ // x ∈ dyadicBlock N},
      ∑ j ∈ cutoffNeighbors L Y (dyadicBlock N) i.val,
        (jointStartProbability N L i.val j : ℝ) := by
      apply Finset.sum_congr rfl
      intro i _
      exact open_neighbour_sum_eq i (fun j => (jointStartProbability N L i.val j : ℝ))
    _ = _ := by
      rw [← Finset.sum_subtype (dyadicBlock N) (fun _ => Iff.rfl)
        (fun x => ∑ y ∈ cutoffNeighbors L Y (dyadicBlock N) x,
          (jointStartProbability N L x y : ℝ)), support_edge_sum_eq]

/-- All support edges pay a baseline, separated relation mass and full touching mass. -/
theorem support_joint_sum_le {N L Y : ℕ} (hL : 0 < L) :
    (∑ p ∈ maskedSupportEdges L Y (dyadicBlock N),
      (jointStartProbability N L p.1 p.2 : ℝ)) ≤
      (((maskedSupportEdges L Y (dyadicBlock N)).card : ℝ) +
        (jointDefectMass N L (separatedPairs (dyadicBlock N) L) : ℝ) +
        homogeneousTouchingMass (dyadicCutoff N L) L (dyadicBlock N)) /
        (2 : ℝ) ^ (2 * L) := by
  classical
  have hpoint := Finset.sum_le_sum (s := maskedSupportEdges L Y (dyadicBlock N))
    (fun p hp => joint_probability_le_three_cases (N := N) hL (mem_maskedSupportEdges.mp hp).2.2.1)
  rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_add_distrib] at hpoint
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hpoint
  apply hpoint.trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hsep : (maskedSupportEdges L Y (dyadicBlock N)).filter
      (fun p => L < Nat.dist p.1 p.2) ⊆ separatedPairs (dyadicBlock N) L := by
    intro p hp
    obtain ⟨he, hd⟩ := Finset.mem_filter.mp hp
    obtain ⟨hx, hy, _⟩ := mem_maskedSupportEdges.mp he
    exact mem_separatedPairs _ _ _ _ |>.mpr ⟨hx,hy,hd⟩
  have htouch : (maskedSupportEdges L Y (dyadicBlock N)).filter
      (fun p => Nat.dist p.1 p.2 = L) ⊆ touchingPairsOn (dyadicBlock N) L := by
    intro p hp
    obtain ⟨he, hd⟩ := Finset.mem_filter.mp hp
    obtain ⟨hx, hy, _⟩ := mem_maskedSupportEdges.mp he
    exact mem_touchingPairsOn.mpr ⟨hx,hy,hd⟩
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  apply add_le_add
  · apply add_le_add (le_refl _)
    change _ ≤ ((∑ p ∈ separatedPairs (dyadicBlock N) L, jointDefectWeight N L p : ℕ) : ℝ)
    rw [Nat.cast_sum]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsep (by intros; positivity)
  · exact Finset.sum_le_sum_of_subset_of_nonneg htouch (by intros; positivity)

/-- A direct degree bound for the number of ordered edges. -/
theorem card_support_edges_le_degree (N L Y : ℕ) :
    ((maskedSupportEdges L Y (dyadicBlock N)).card : ℝ) ≤
      N * (cutoffMaxDegree L Y (dyadicBlock N) : ℝ) := by
  have h := support_edge_sum_eq L Y (dyadicBlock N) (fun _ => (1 : ℝ))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h
  rw [h]
  calc
    _ ≤ ∑ _x ∈ dyadicBlock N, (cutoffMaxDegree L Y (dyadicBlock N) : ℝ) := by
      apply Finset.sum_le_sum
      intro x hx
      exact_mod_cast Finset.le_sup (f := fun z => (cutoffNeighbors L Y (dyadicBlock N) z).card) hx
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, TouchingPairs.card_dyadicBlock]

/-- The actual good-by-all pair ledger used in the soft Stein inequality. -/
theorem good_all_joint_sum_le {N L Y : ℕ} (hL : 0 < L) :
    (∑ i ∈ goodSiteIndices N L Y,
      ∑ j ∈ (closedNeighborhood (allStartDependencyGraph N L Y) i).erase i,
        (jointStartProbability N L i.val j.val : ℝ)) ≤
      ((N : ℝ) * cutoffMaxDegree L Y (dyadicBlock N) +
        (jointDefectMass N L (separatedPairs (dyadicBlock N) L) : ℝ) +
        homogeneousTouchingMass (dyadicCutoff N L) L (dyadicBlock N)) /
        (2 : ℝ) ^ (2 * L) := by
  apply (good_all_joint_sum_le_support N L Y).trans ((support_joint_sum_le hL).trans ?_)
  apply div_le_div_of_nonneg_right _ (by positivity)
  linarith [card_support_edges_le_degree N L Y]

/-- The good diagonal never has more than the N actual dyadic sites. -/
theorem good_indices_card_le (N L Y : ℕ) :
    ((goodSiteIndices N L Y).card : ℝ) ≤ N := by
  have h := Finset.card_le_card (Finset.subset_univ (goodSiteIndices N L Y))
  simpa only [Finset.card_univ, Fintype.card_coe, TouchingPairs.card_dyadicBlock] using
    (show ((goodSiteIndices N L Y).card : ℝ) ≤ Fintype.card {x : ℕ // x ∈ dyadicBlock N}
      by exact_mod_cast h)

/-- The exceptional subtype indices are exactly the whole-support bad starts. -/
theorem bad_indices_sum_eq (N L Y : ℕ) (f : ℕ → ℝ) :
    (∑ i ∈ Finset.univ \ goodSiteIndices N L Y, f i.val) =
      ∑ x ∈ fullBadStarts N L Y, f x := by
  classical
  have hs : Finset.univ \ goodSiteIndices N L Y =
      Finset.univ.filter (fun i : {x : ℕ // x ∈ dyadicBlock N} => i.val ∈ fullBadStarts N L Y) := by
    ext i
    simp only [Finset.mem_sdiff, Finset.mem_univ, mem_goodSiteIndices,
      Finset.mem_filter, true_and, not_not]
  rw [hs, Finset.sum_filter, ← Finset.sum_subtype (dyadicBlock N) (fun _ => Iff.rfl)
    (fun x => if x ∈ fullBadStarts N L Y then f x else 0), ← Finset.sum_filter]
  have hf : (dyadicBlock N).filter (fun x => x ∈ fullBadStarts N L Y) = fullBadStarts N L Y := by
    ext x
    simp only [Finset.mem_filter]
    exact ⟨And.right, fun hx => ⟨fullBadStarts_subset_block N L Y hx,hx⟩⟩
  rw [hf]

/-- Exact cardinality of the exceptional subtype population. -/
theorem bad_indices_card_eq (N L Y : ℕ) :
    ((Finset.univ \ goodSiteIndices N L Y).card : ℝ) = (fullBadStarts N L Y).card := by
  simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using bad_indices_sum_eq N L Y (fun _ => 1)

/-- The exceptional ledger keeps the true first moment and the full root defect. -/
theorem actual_bad_cost_le {N L Y : ℕ} (hN : 2 ≤ N) (hL : 0 < L) :
    (Finset.univ \ goodSiteIndices N L Y).card / (2 : ℝ) ^ L +
      (∑ i ∈ Finset.univ \ goodSiteIndices N L Y, (startProbability N L i.val : ℝ)) ≤
      ((fullDefectMass L (dyadicBlock N) : ℝ) + 2 * (fullBadStarts N L Y).card) /
        (2 : ℝ) ^ L := by
  rw [bad_indices_card_eq, bad_indices_sum_eq N L Y (fun x => (startProbability N L x : ℝ))]
  have hb : fullBadMask N L Y (dyadicBlock N) = fullBadStarts N L Y :=
    Finset.inter_eq_right.mpr (fullBadStarts_subset_block N L Y)
  have hq := masked_total_deletion_cost_le (Y := Y) hN hL (dyadicBlock N) (Finset.Subset.refl _)
  unfold maskedBadStartMass at hq
  rw [hb] at hq
  have hr := (Rat.cast_le (K := ℝ)).mpr hq
  push_cast at hr
  simpa only [add_comm] using hr

end
end PaperC.V282.SoftArithmeticCosts
