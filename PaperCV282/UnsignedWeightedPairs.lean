import PaperCV282.UnsignedLocalProbability
import PaperCV282.DirectionalMarkedCosts

/-! # Sign-invariant directional weights retain the relative Q-row profile -/
namespace PaperC.V282.UnsignedWeightedPairs

open Affine UnsignedMarkedRelations UnsignedLocalProbability DirectionalMarkedCosts
open ExactMarkedModel ExactMarkedDependency MixedLengthAffine ExactLengthDecomposition
open ExactMarkedPairCosts ConditionalStartProbability ArratiaGoldsteinGordonInput
open ConditionalAGGAverage ConditionalAGGInstantiation SectionThirteenFiniteBound
open WindowValues MaskedArithmeticGeometry SectionTwelveMoments
open scoped BigOperators NNReal

noncomputable section

local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

def liftExcessWeight {E : ℕ} (w : Fin (E+1) → Fin (E+1) → ℝ) :
    (Fin (E+1) × F₂) → (Fin (E+1) × F₂) → ℝ := fun a b => w a.1 b.1

def exactRatePairSum (L E : ℕ) (w : Fin (E+1) → Fin (E+1) → ℝ) : ℝ :=
  ∑ e, ∑ f, w e f*(exactMarkRate L e.val : ℝ)*(exactMarkRate L f.val : ℝ)

theorem signedRatePairSum_lift (L E : ℕ) (w : Fin (E+1) → Fin (E+1) → ℝ) :
    signedRatePairSum L E (liftExcessWeight w)=exactRatePairSum L E w := by
  unfold signedRatePairSum exactRatePairSum
  simp only [Fintype.sum_prod_type,liftExcessWeight]
  apply Finset.sum_congr rfl
  intro e _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro f _
  have he := sum_signedMarkRate L e.val
  have hf := sum_signedMarkRate L f.val
  simp only [Finset.sum_const,Finset.card_univ,ZMod.card,nsmul_eq_mul] at he hf ⊢
  rw [← he,← hf]
  ring

/-- The two sign sums are exact at each fixed pair of excesses and each environment. -/
theorem weightedSignedPair_lift_eq (C L E Y x y : ℕ) (sigma : SmallSample C Y)
    (w : Fin (E+1) → Fin (E+1) → ℝ) :
    weightedSignedPair C L E Y sigma x y (liftExcessWeight w)=
      ∑ e, ∑ f, w e f*eventProbability (largeUniformPMF C Y) (fun eta =>
        ExactLengthEvent (valueBit (assemble C Y sigma eta)) x (excessRowCount L e.val) ∧
        ExactLengthEvent (valueBit (assemble C Y sigma eta)) y (excessRowCount L f.val)) := by
  unfold weightedSignedPair
  simp only [Fintype.sum_prod_type,liftExcessWeight,conditionedSignedAt,signedAt,decide_eq_true_eq]
  apply Finset.sum_congr rfl
  intro e _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro f _
  simp_rw [← Finset.mul_sum]
  rw [sum_signed_joint_eq_exact]

theorem average_weightedSignedPair_lift_le {C x y L E Y : ℕ}
    (hL : 1≤L) (w : Fin (E+1) → Fin (E+1) → ℝ) (hw : ∀ e f,0≤w e f) :
    finiteUniformAverage (fun sigma : SmallSample C Y =>
      weightedSignedPair C L E Y sigma x y (liftExcessWeight w)) ≤
      signedRatePairSum L E (liftExcessWeight w)*
        (2 : ℝ)^relationRho (twoStartSystem C x y (L+E+1)) := by
  simp_rw [weightedSignedPair_lift_eq,average_finset_sum,finiteUniformAverage_const_mul]
  rw [signedRatePairSum_lift]
  unfold exactRatePairSum
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro e _
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro f _
  have h := mul_le_mul_of_nonneg_left
    (average_exact_joint_probability_le_relative_weight (C := C) (Y := Y) (x := x) (y := y)
      (E := E) hL (by omega : e.val≤E) (by omega : f.val≤E)) (hw e f)
  convert h using 1
  ring

theorem local_exact_joint_le_two {C N L E Y x y : ℕ} {mask : Finset ℕ}
    (hN : 2≤N) (hL : 1≤L) (hC : dyadicCutoff N (L+E+1)≤C)
    (hY : 2*(L+E+1)<Y) (hmask : mask⊆dyadicBlock N)
    (hx : x∈fullGoodMask N (L+E+1) Y mask)
    (hy : y∈fullGoodMask N (L+E+1) Y mask)
    (hxy : x≠y) (hd : Nat.dist x y≤L+E+1) (sigma : SmallSample C Y)
    (e f : Fin (E+1)) :
    eventProbability (largeUniformPMF C Y) (fun eta =>
      ExactLengthEvent (valueBit (assemble C Y sigma eta)) x (excessRowCount L e.val) ∧
      ExactLengthEvent (valueBit (assemble C Y sigma eta)) y (excessRowCount L f.val)) ≤
      2*(exactMarkRate L e.val : ℝ)*(exactMarkRate L f.val : ℝ) := by
  have hordered (x y : ℕ) (hx : x∈fullGoodMask N (L+E+1) Y mask)
      (hy : y∈fullGoodMask N (L+E+1) Y mask) (hxy : x<y)
      (hd : Nat.dist x y≤L+E+1) (e f : Fin (E+1)) :
      eventProbability (largeUniformPMF C Y) (fun eta =>
        ExactLengthEvent (valueBit (assemble C Y sigma eta)) x (excessRowCount L e.val) ∧
        ExactLengthEvent (valueBit (assemble C Y sigma eta)) y (excessRowCount L f.val)) ≤
        2*(exactMarkRate L e.val : ℝ)*(exactMarkRate L f.val : ℝ) := by
    have hxblock := hmask (mem_fullGoodMask.mp hx).1
    have hyblock := hmask (mem_fullGoodMask.mp hy).1
    have hx2 := two_le_of_mem_dyadicBlock hN hxblock
    have hxyadd : x+(y-x)=y := by omega
    have hdist : Nat.dist x y=y-x := Nat.dist_eq_sub_of_le hxy.le
    have hcut : y-1+(L+E+2)≤C+1 := by
      have hb := Finset.mem_Ico.mp hyblock
      unfold dyadicCutoff at hC
      omega
    have hp := conditioned_exact_pair_le_two (C := C) (Y := Y) (L := L) (E := E)
      (e := e.val) (f := f.val) (d := y-x) hx2 hL (by omega) (by omega) (by omega)
      (by simpa only [hdist] using hd) (by simpa only [hxyadd] using hcut) hY
      (good_maximal_vertex hN hmask hx) (by simpa only [hxyadd] using good_maximal_vertex hN hmask hy) sigma
    simpa only [hxyadd] using hp
  rcases lt_or_gt_of_ne hxy with hlt | hgt
  · exact hordered x y hx hy hlt hd e f
  · have h := hordered y x hy hx hgt (by simpa only [Nat.dist_comm] using hd) f e
    have heq : (fun eta =>
        ExactLengthEvent (valueBit (assemble C Y sigma eta)) x (excessRowCount L e.val) ∧
        ExactLengthEvent (valueBit (assemble C Y sigma eta)) y (excessRowCount L f.val)) =
      (fun eta =>
        ExactLengthEvent (valueBit (assemble C Y sigma eta)) y (excessRowCount L f.val) ∧
        ExactLengthEvent (valueBit (assemble C Y sigma eta)) x (excessRowCount L e.val)) := by
      funext eta
      exact propext and_comm
    rw [heq]
    nlinarith

theorem weightedSignedPair_lift_local_le {C N L E Y x y : ℕ} {mask : Finset ℕ}
    (hN : 2≤N) (hL : 1≤L) (hC : dyadicCutoff N (L+E+1)≤C)
    (hY : 2*(L+E+1)<Y) (hmask : mask⊆dyadicBlock N)
    (hx : x∈fullGoodMask N (L+E+1) Y mask)
    (hy : y∈fullGoodMask N (L+E+1) Y mask)
    (hxy : x≠y) (hd : Nat.dist x y≤L+E+1) (sigma : SmallSample C Y)
    (w : Fin (E+1) → Fin (E+1) → ℝ) (hw : ∀ e f,0≤w e f) :
    weightedSignedPair C L E Y sigma x y (liftExcessWeight w)≤
      2*signedRatePairSum L E (liftExcessWeight w) := by
  rw [weightedSignedPair_lift_eq,signedRatePairSum_lift]
  unfold exactRatePairSum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro f _
  have h := mul_le_mul_of_nonneg_left
    (local_exact_joint_le_two hN hL hC hY hmask hx hy hxy hd sigma e f) (hw e f)
  convert h using 1
  ring

end
end PaperC.V282.UnsignedWeightedPairs
