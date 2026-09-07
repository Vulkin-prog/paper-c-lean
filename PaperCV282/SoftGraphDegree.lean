import PaperCV282.AllStartSoftPoisson
import PaperCV282.CutoffGraphCompatibility

/-!
# Exceptional-neighbour marginals and maximum degree

The companion's soft argument bounds neighbour marginals by summing their
true unconditional weights. Symmetry of the graph gives the maximum-degree
bound without asserting baseline marginals at exceptional sites.
-/

namespace PaperC.V282.SoftGraphDegree

open ArratiaGoldsteinGordonInput
open scoped BigOperators

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Membership in the open neighbourhood is symmetric. -/
theorem mem_openNeighborhood_symm (G : SimpleGraph ι) (i j : ι) :
    j ∈ (closedNeighborhood G i).erase i ↔
      i ∈ (closedNeighborhood G j).erase j := by
  classical
  simp only [Finset.mem_erase, mem_closedNeighborhood]
  constructor
  · rintro ⟨hne, heq | hadj⟩
    · exact (hne heq).elim
    · exact ⟨Ne.symm hne, Or.inr ((G.adj_comm _ _).mp hadj)⟩
  · rintro ⟨hne, heq | hadj⟩
    · exact (hne heq).elim
    · exact ⟨Ne.symm hne, Or.inr ((G.adj_comm _ _).mp hadj)⟩

/-- Every weight keeps its actual value; no common-marginal assumption is used. -/
theorem weighted_neighbour_sum_le (G : SimpleGraph ι) (good : Finset ι)
    (weight : ι → ℝ) (hweight : ∀ i, 0 ≤ weight i) (degree : ℝ)
    (hdegree : ∀ i, ((closedNeighborhood G i).erase i).card ≤ degree) :
    (∑ i ∈ good, ∑ j ∈ (closedNeighborhood G i).erase i, weight j) ≤
      degree * ∑ j, weight j := by
  classical
  calc
    _ ≤ ∑ i, ∑ j ∈ (closedNeighborhood G i).erase i, weight j := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro i _ _
      exact Finset.sum_nonneg (fun j _ => hweight j)
    _ = ∑ i, ∑ j, if j ∈ (closedNeighborhood G i).erase i then weight j else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      exact (Finset.sum_ite_mem_eq _ _).symm
    _ = ∑ j, ∑ i, if j ∈ (closedNeighborhood G i).erase i then weight j else 0 :=
      Finset.sum_comm
    _ = ∑ j, (((closedNeighborhood G j).erase j).card : ℝ) * weight j := by
      apply Finset.sum_congr rfl
      intro j _
      simp_rw [mem_openNeighborhood_symm G _ j]
      rw [Finset.sum_ite_mem_eq]
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ j, degree * weight j := by
      exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hdegree j) (hweight j))
    _ = _ := (Finset.mul_sum ..).symm

omit [Fintype ι] [DecidableEq ι] in
/-- The actual all-site graph pays its open maximum degree against the actual first moment. -/
theorem actual_neighbour_marginal_sum_le (N L Y : ℕ) :
    (∑ i ∈ AllStartSoftPoisson.goodSiteIndices N L Y,
      ∑ j ∈ (closedNeighborhood
        (AllStartConditionalDependency.allStartDependencyGraph N L Y) i).erase i,
        (startProbability N L j.val : ℝ)) ≤
      (CutoffGraphDegree.cutoffMaxDegree L Y (dyadicBlock N) : ℝ) *
        ∑ j ∈ dyadicBlock N, (startProbability N L j : ℝ) := by
  classical
  have h := weighted_neighbour_sum_le
    (AllStartConditionalDependency.allStartDependencyGraph N L Y)
    (AllStartSoftPoisson.goodSiteIndices N L Y)
    (fun j => (startProbability N L j.val : ℝ))
    (fun j => by exact_mod_cast BadStartMass.startProbability_nonneg N L j.val)
    (CutoffGraphDegree.cutoffMaxDegree L Y (dyadicBlock N) : ℝ)
    (fun i => by
      rw [CutoffGraphCompatibility.card_openNeighborhood_eq_cutoffNeighbors]
      exact_mod_cast Finset.le_sup (f := fun z =>
        (CutoffGraphDegree.cutoffNeighbors L Y (dyadicBlock N) z).card) i.property)
  simpa only [← Finset.sum_subtype (dyadicBlock N) (fun _ => Iff.rfl)
    (fun j => (startProbability N L j : ℝ))] using h

omit [Fintype ι] [DecidableEq ι] in
/-- The full defect mass bounds the neighbour term without replacing bad marginals. -/
theorem actual_neighbour_marginal_sum_le_defects {N L Y : ℕ}
    (hN : 2 ≤ N) (hL : 0 < L) :
    (∑ i ∈ AllStartSoftPoisson.goodSiteIndices N L Y,
      ∑ j ∈ (closedNeighborhood
        (AllStartConditionalDependency.allStartDependencyGraph N L Y) i).erase i,
        (startProbability N L j.val : ℝ)) ≤
      (CutoffGraphDegree.cutoffMaxDegree L Y (dyadicBlock N) : ℝ) *
        ((MaskedArithmeticGeometry.fullDefectMass L (dyadicBlock N) : ℝ) + N) /
          (2 : ℝ) ^ L := by
  have hmass : (∑ j ∈ dyadicBlock N, (startProbability N L j : ℝ)) ≤
      ((MaskedArithmeticGeometry.fullDefectMass L (dyadicBlock N) : ℝ) + N) /
        (2 : ℝ) ^ L := by
    have hq := MaskedBadMass.startProbabilityMass_le_mask_defects hN hL
      (dyadicBlock N) (Finset.Subset.refl _)
    rw [TouchingPairs.card_dyadicBlock] at hq
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  have hmul := mul_le_mul_of_nonneg_left hmass
    (show (0 : ℝ) ≤ CutoffGraphDegree.cutoffMaxDegree L Y (dyadicBlock N) by positivity)
  exact (actual_neighbour_marginal_sum_le N L Y).trans
    (by simpa only [mul_div_assoc] using hmul)

end
end PaperC.V282.SoftGraphDegree
