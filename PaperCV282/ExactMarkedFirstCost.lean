import PaperCV282.ExactMarkedDependency

/-!
# First process cost without growth in the number of exact marks

Only the maximal geometric support enters the pair population. All rates
are summed first and their sum is bounded by the base start probability.
-/
namespace PaperC.V282.ExactMarkedFirstCost

open ExactMarkedModel ExactMarkedDependency LabelledSupportGraph LabelledProcessCosts
open MaskedArithmeticGeometry MaskedPairGeometry ArratiaGoldsteinGordonInput
open ConditionalStartProbability ConditionalAGGInstantiation ConditionalAGGAverage SectionThirteenFiniteBound
open scoped BigOperators

noncomputable section

/-- Uniform conditional b1 bound for all retained excess/sign labels. -/
theorem bOne_signed_le {C N L E Y : ℕ}
    (hN : 2 ≤ N) (hL : 1 ≤ L) (hC : dyadicCutoff N (L+E+1) ≤ C)
    (hY : L+E+2 ≤ Y) (mask : Finset ℕ) (hmask : mask ⊆ dyadicBlock N) (sigma : SmallSample C Y) :
    bOne (largeUniformPMF C Y)
      (maskedLabelledFamily N (conditionedSignedAt C L E Y sigma) (fullGoodMask N (L+E+1) Y mask))
      (labelledGraph N (L+E+1) Y (Fin (E+1) × F₂)) ≤
      (1/(2 : ℝ)^L)^2 * (2*(N : ℝ)*(L+E+2) + (maskedSupportEdges (L+E+1) Y mask).card) := by
  have hg : fullGoodMask N (L+E+1) Y mask ⊆ dyadicBlock N :=
    fun x hx => hmask (fullGoodMask_subset_mask N (L+E+1) Y mask hx)
  have h := bOne_labelled_le (largeUniformPMF C Y) (conditionedSignedAt C L E Y sigma)
    N (L+E+1) Y (fullGoodMask N (L+E+1) Y mask) hg
    (fun a : Fin (E+1) × F₂ => (signedMarkRate L a.1.val : ℝ))
    (fun a => (signedMarkRate L a.1.val).coe_nonneg)
    (by simpa only [Fintype.sum_prod_type] using sum_all_signedMarkRate_le_base L E)
    (signedAt_marginal_masked_good hN hL hC hY mask sigma)
  have hc : ((maskedSupportEdges (L+E+1) Y (fullGoodMask N (L+E+1) Y mask)).card : ℝ) ≤
      (maskedSupportEdges (L+E+1) Y mask).card := by
    exact_mod_cast Finset.card_le_card (maskedSupportEdges_mono (fullGoodMask_subset_mask N (L+E+1) Y mask))
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  push_cast
  linarith

/-- Averaging the first cost has the same bound, uniform in the full small-prime assignment. -/
theorem average_bOne_signed_le {C N L E Y : ℕ}
    (hN : 2 ≤ N) (hL : 1 ≤ L) (hC : dyadicCutoff N (L+E+1) ≤ C)
    (hY : L+E+2 ≤ Y) (mask : Finset ℕ) (hmask : mask ⊆ dyadicBlock N) :
    finiteUniformAverage (fun sigma : SmallSample C Y => bOne (largeUniformPMF C Y)
      (maskedLabelledFamily N (conditionedSignedAt C L E Y sigma) (fullGoodMask N (L+E+1) Y mask))
      (labelledGraph N (L+E+1) Y (Fin (E+1) × F₂))) ≤
      (1/(2 : ℝ)^L)^2 * (2*(N : ℝ)*(L+E+2) + (maskedSupportEdges (L+E+1) Y mask).card) := by
  have h := finiteUniformAverage_mono (fun sigma => bOne_signed_le hN hL hC hY mask hmask sigma)
  have hc : (Fintype.card (SmallSample C Y) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simpa only [finiteUniformAverage,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_div_cancel_left₀ _ hc] using h

end
end PaperC.V282.ExactMarkedFirstCost
