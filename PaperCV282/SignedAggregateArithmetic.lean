import PaperCV282.DirectionalMarkedCosts
import PaperCV282.SignedDirectionalFactors

/-! # The actual averaged signed arithmetic budget in its canonical cylinder -/
namespace PaperC.V282.SignedAggregateArithmetic

open Affine DirectionalMarkedCosts SignedDirectionalFactors SignedGeometricWeights
open ExactMarkedModel ExactMarkedDependency LabelledSupportGraph LabelledProcessCosts
open DirectionalHessian DirectionalSteinComparison ConditionalStartProbability
open ArratiaGoldsteinGordonInput SectionThirteenFiniteBound SectionTwelveMoments ConditionalAGGInstantiation
open MaskedArithmeticGeometry MaskedPairGeometry TwoWindowParity RelationProfileRestriction
open scoped BigOperators NNReal

noncomputable section

/-- The profile cylinder is independent of the larger cylinder used for full conditioning. -/
theorem valueWeightMass_dyadic_cutoff_eq {C N Q : ℕ} (hN : 2 ≤ N)
    (hC : dyadicCutoff N Q ≤ C) (mask : Finset ℕ) (hmask : mask ⊆ dyadicBlock N) :
    valueWeightMass C Q (separatedPairs mask Q) =
      valueWeightMass (dyadicCutoff N Q) Q (separatedPairs mask Q) := by
  unfold valueWeightMass
  apply Finset.sum_congr rfl
  intro xy hxy
  obtain ⟨hx,hy,hd⟩ := (mem_separatedPairs _ _ _ _).mp hxy
  have hxblock := hmask hx
  have hyblock := hmask hy
  have hx2 := two_le_of_mem_dyadicBlock hN hxblock
  have hy2 := two_le_of_mem_dyadicBlock hN hyblock
  obtain ⟨hxl,hxu⟩ := Finset.mem_Ico.mp hxblock
  obtain ⟨hyl,hyu⟩ := Finset.mem_Ico.mp hyblock
  have hK : xy.1+Q ≤ dyadicCutoff N Q+1 ∧ xy.2+Q ≤ dyadicCutoff N Q+1 := by
    unfold dyadicCutoff; constructor <;> omega
  have hC' : xy.1+Q ≤ C+1 ∧ xy.2+Q ≤ C+1 := by constructor <;> omega
  rw [value_relationRho_cutoff_eq hx2 hy2 hC' hK]

/-- Genuine graph costs with the dimension-free coarse/directional minimum. -/
theorem average_typedCost_signed_directional_le {C N L E Y : ℕ}
    (hN : 2 ≤ N) (hL : 1 ≤ L) (hC : dyadicCutoff N (L+E+1) ≤ C)
    (hY : 2*(L+E+2) ≤ Y) (mask : Finset ℕ) (hmask : mask ⊆ dyadicBlock N)
    (lambda : ℝ≥0) (hlambda : 0 < lambda) :
    finiteUniformAverage (fun sigma : SmallSample C Y => typedCost (largeUniformPMF C Y)
      (maskedLabelledFamily N (conditionedSignedAt C L E Y sigma) (fullGoodMask N (L+E+1) Y mask))
      Prod.snd (labelledGraph N (L+E+1) Y (Fin (E+1) × F₂))
      (entryFactor (signedAggregateRates lambda E))) ≤
      (1/(2 : ℝ)^L)^2 * signedDirectionalFactor lambda *
        (10*(N : ℝ)*(L+E+2)+2*(maskedSupportEdges (L+E+1) Y mask).card+
          (valueWeightMass (dyadicCutoff N (L+E+1)) (L+E+1)
            (separatedPairs mask (L+E+1)) : ℝ)) := by
  have h := average_typedCost_signed_le hN hL hC hY mask hmask
    (entryFactor (signedAggregateRates lambda E)) (entryFactor_nonneg _)
  rw [valueWeightMass_dyadic_cutoff_eq hN hC mask hmask] at h
  have hweight := signedRatePairSum_le (L := L) (entryFactor (signedAggregateRates lambda E))
    (by positivity) (entryFactor_le_one _) (entryFactor_signed_le hlambda E)
  exact h.trans (mul_le_mul_of_nonneg_right hweight (by positivity))

end
end PaperC.V282.SignedAggregateArithmetic
