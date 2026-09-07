import PaperCV282.UnsignedWeightedPairs
import PaperCV282.SignedAggregateArithmetic

/-! # Exact directional graph costs with the printed relative profile at Q rows -/
namespace PaperC.V282.UnsignedDirectionalCosts

open Affine UnsignedWeightedPairs UnsignedMarkedRelations DirectionalMarkedCosts
open ExactMarkedModel ExactMarkedDependency ExactMarkedPairCosts
open SignedDirectionalFactors SignedGeometricWeights DirectionalHessian DirectionalSteinComparison
open ConditionalStartProbability ConditionalAGGAverage ConditionalAGGInstantiation
open ArratiaGoldsteinGordonInput SectionThirteenFiniteBound SectionTwelveMoments
open MaskedArithmeticGeometry MaskedPairGeometry LabelledSupportGraph
open LabelledProcessCosts TwoWindowParity
open scoped BigOperators NNReal

noncomputable section

theorem relative_rho_eq_canonical {C N Q x y : ℕ} (hN : 2≤N)
    (hC : dyadicCutoff N Q≤C) (hx : x∈dyadicBlock N) (hy : y∈dyadicBlock N) :
    relationRho (twoStartSystem C x y Q)=jointRho N Q (x,y) := by
  have hx2 := two_le_of_mem_dyadicBlock hN hx
  have hy2 := two_le_of_mem_dyadicBlock hN hy
  have hxb := Finset.mem_Ico.mp hx
  have hyb := Finset.mem_Ico.mp hy
  unfold jointRho
  apply TouchingPairGeometry.relationRho_cutoff_eq hx2 hy2
  · unfold dyadicCutoff at hC
    constructor <;> omega
  · unfold dyadicCutoff
    constructor <;> omega

theorem sum_relative_relation_weight_eq (N Q : ℕ) (s : Finset (ℕ×ℕ)) :
    (∑ xy∈s,(2 : ℝ)^jointRho N Q xy)=(s.card : ℝ)+(jointDefectMass N Q s : ℝ) := by
  have hp (xy : ℕ×ℕ) : 1≤(2 : ℕ)^jointRho N Q xy := Nat.one_le_pow _ _ (by norm_num)
  unfold jointDefectMass jointDefectWeight
  rw [Nat.cast_sum]
  simp_rw [Nat.cast_sub (hp _),Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one]
  rw [Finset.sum_sub_distrib]
  simp

theorem sum_near_weighted_lift_le {C N L E Y : ℕ} {mask : Finset ℕ}
    (hN : 2≤N) (hL : 1≤L) (hC : dyadicCutoff N (L+E+1)≤C)
    (hY : 2*(L+E+1)<Y) (hmask : mask⊆dyadicBlock N) (sigma : SmallSample C Y)
    (w : Fin (E+1)→Fin (E+1)→ℝ) (hw : ∀ e f,0≤w e f) :
    (∑ xy∈nearMarkedPairs (L+E+1) (fullGoodMask N (L+E+1) Y mask),
      weightedSignedPair C L E Y sigma xy.1 xy.2 (liftExcessWeight w)) ≤
      signedRatePairSum L E (liftExcessWeight w)*(4*(N : ℝ)*(L+E+2)) := by
  have hg : fullGoodMask N (L+E+1) Y mask⊆dyadicBlock N :=
    (fullGoodMask_subset_mask _ _ _ _).trans hmask
  have hs := Finset.sum_le_sum (s := nearMarkedPairs (L+E+1) (fullGoodMask N (L+E+1) Y mask))
    (fun xy hxy => by
      obtain ⟨hp,hd⟩ := Finset.mem_filter.mp hxy
      obtain ⟨hx,hy,hne⟩ := Finset.mem_offDiag.mp hp
      exact weightedSignedPair_lift_local_le hN hL hC hY hmask hx hy hne hd sigma w hw)
  have hc : ((nearMarkedPairs (L+E+1) (fullGoodMask N (L+E+1) Y mask)).card : ℝ)≤
      2*(N : ℝ)*(L+E+2) := by
    exact_mod_cast card_nearMarkedPairs_le (fullGoodMask N (L+E+1) Y mask) hg
  simp only [Finset.sum_const,nsmul_eq_mul] at hs
  have hr := signedRatePairSum_nonneg L E (liftExcessWeight w) (fun a b => hw a.1 b.1)
  nlinarith

theorem average_sum_far_weighted_lift_le {C N L E Y : ℕ} {mask : Finset ℕ}
    (hN : 2≤N) (hL : 1≤L) (hC : dyadicCutoff N (L+E+1)≤C) (hmask : mask⊆dyadicBlock N)
    (w : Fin (E+1)→Fin (E+1)→ℝ) (hw : ∀ e f,0≤w e f) :
    finiteUniformAverage (fun sigma : SmallSample C Y =>
      ∑ xy∈farMarkedPairs (L+E+1) Y (fullGoodMask N (L+E+1) Y mask),
        weightedSignedPair C L E Y sigma xy.1 xy.2 (liftExcessWeight w)) ≤
      signedRatePairSum L E (liftExcessWeight w)*
        ((maskedSupportEdges (L+E+1) Y mask).card+
          (jointDefectMass N (L+E+1) (separatedPairs mask (L+E+1)) : ℝ)) := by
  let far := farMarkedPairs (L+E+1) Y (fullGoodMask N (L+E+1) Y mask)
  have hgood := fullGoodMask_subset_mask N (L+E+1) Y mask
  have hsupp : far⊆maskedSupportEdges (L+E+1) Y mask :=
    fun xy hxy => maskedSupportEdges_mono hgood (Finset.mem_filter.mp hxy).1
  have hsep : far⊆separatedPairs mask (L+E+1) := by
    intro xy hxy
    have hp := (mem_separatedPairs _ _ _ _).mp (farMarkedPairs_subset_separated _ _ _ hxy)
    exact (mem_separatedPairs _ _ _ _).mpr ⟨hgood hp.1,hgood hp.2.1,hp.2.2⟩
  rw [average_finset_sum]
  have hpoint (xy : ℕ×ℕ) (hxy : xy∈far) :
      finiteUniformAverage (fun sigma : SmallSample C Y =>
        weightedSignedPair C L E Y sigma xy.1 xy.2 (liftExcessWeight w)) ≤
      signedRatePairSum L E (liftExcessWeight w)*(2 : ℝ)^jointRho N (L+E+1) xy := by
    have hp := (mem_separatedPairs _ _ _ _).mp (hsep hxy)
    have hh := average_weightedSignedPair_lift_le (C := C) (Y := Y) (x := xy.1) (y := xy.2) hL w hw
    rw [relative_rho_eq_canonical hN hC (hmask hp.1) (hmask hp.2.1)] at hh
    exact hh
  have hsum := Finset.sum_le_sum hpoint
  rw [← Finset.mul_sum,sum_relative_relation_weight_eq] at hsum
  have hc : (far.card : ℝ)≤(maskedSupportEdges (L+E+1) Y mask).card := by
    exact_mod_cast Finset.card_le_card hsupp
  have hm : (jointDefectMass N (L+E+1) far : ℝ)≤
      (jointDefectMass N (L+E+1) (separatedPairs mask (L+E+1)) : ℝ) := by
    exact_mod_cast (Finset.sum_le_sum_of_subset hsep :
      jointDefectMass N (L+E+1) far≤jointDefectMass N (L+E+1) (separatedPairs mask (L+E+1)))
  exact hsum.trans (mul_le_mul_of_nonneg_left (add_le_add hc hm)
    (signedRatePairSum_nonneg L E (liftExcessWeight w) (fun a b => hw a.1 b.1)))

/-- The relative profile survives the actual two graph costs; no excess is dropped. -/
theorem average_typedCost_lift_le {C N L E Y : ℕ}
    (hN : 2≤N) (hL : 1≤L) (hC : dyadicCutoff N (L+E+1)≤C)
    (hY : 2*(L+E+1)<Y) (mask : Finset ℕ) (hmask : mask⊆dyadicBlock N)
    (w : Fin (E+1)→Fin (E+1)→ℝ) (hw : ∀ e f,0≤w e f) :
    finiteUniformAverage (fun sigma : SmallSample C Y => typedCost (largeUniformPMF C Y)
      (maskedLabelledFamily N (conditionedSignedAt C L E Y sigma) (fullGoodMask N (L+E+1) Y mask))
      Prod.snd (labelledGraph N (L+E+1) Y (Fin (E+1)×F₂)) (liftExcessWeight w)) ≤
      signedRatePairSum L E (liftExcessWeight w)*
        (6*(N : ℝ)*(L+E+2)+2*(maskedSupportEdges (L+E+1) Y mask).card+
          (jointDefectMass N (L+E+1) (separatedPairs mask (L+E+1)) : ℝ)) := by
  unfold typedCost
  simp_rw [typedBTwo_signed_eq_near_add_far hL mask hmask,finiteUniformAverage_add]
  have hn := finiteUniformAverage_mono (fun sigma =>
    sum_near_weighted_lift_le (E := E) (Y := Y) hN hL hC hY hmask sigma w hw)
  have ho := finiteUniformAverage_mono (fun sigma =>
    typedBOne_signed_le (E := E) (Y := Y) hN hL hC (by omega) mask hmask sigma
      (liftExcessWeight w) (fun a b => hw a.1 b.1))
  have hf := average_sum_far_weighted_lift_le (C := C) (Y := Y) hN hL hC hmask w hw
  simp only [finiteUniformAverage] at hn ho
  simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_univ] at hn ho
  rw [mul_div_cancel_left₀ _ (by exact_mod_cast Fintype.card_ne_zero)] at hn ho
  unfold finiteUniformAverage at hf ⊢
  linarith

theorem average_typedCost_relative_le {C N L E Y : ℕ}
    (hN : 2≤N) (hL : 1≤L) (hC : dyadicCutoff N (L+E+1)≤C)
    (hY : 2*(L+E+1)<Y) (mask : Finset ℕ) (hmask : mask⊆dyadicBlock N)
    (lambda : ℝ≥0) (hlambda : 0<lambda) :
    finiteUniformAverage (fun sigma : SmallSample C Y => typedCost (largeUniformPMF C Y)
      (maskedLabelledFamily N (conditionedSignedAt C L E Y sigma) (fullGoodMask N (L+E+1) Y mask))
      Prod.snd (labelledGraph N (L+E+1) Y (Fin (E+1)×F₂))
      (entryFactor (signedAggregateRates lambda E))) ≤
      (1/(2 : ℝ)^L)^2*signedDirectionalFactor lambda*
        (6*(N : ℝ)*(L+E+2)+2*(maskedSupportEdges (L+E+1) Y mask).card+
          (jointDefectMass N (L+E+1) (separatedPairs mask (L+E+1)) : ℝ)) := by
  let w : Fin (E+1)→Fin (E+1)→ℝ := fun e f =>
    entryFactor (signedAggregateRates lambda E) (e,0) (f,0)
  have heq : liftExcessWeight w=entryFactor (signedAggregateRates lambda E) := rfl
  have h := average_typedCost_lift_le hN hL hC hY mask hmask w
    (fun e f => entryFactor_nonneg _ _ _)
  rw [heq] at h
  have hw := signedRatePairSum_le (L := L) (entryFactor (signedAggregateRates lambda E))
    (by positivity) (entryFactor_le_one _) (entryFactor_signed_le hlambda E)
  exact h.trans (mul_le_mul_of_nonneg_right hw (by positivity))

end
end PaperC.V282.UnsignedDirectionalCosts
