import PaperCV282.FiniteStartMaskPairBounds
import PaperCV282.MaskedBadMass
import PaperCV282.MaskedScalarCoupling

/-! # Actual deletion and mean shift for arbitrary finite populations -/
namespace PaperC.V282.FiniteStartMaskDeletion

open Affine WindowValues PointwiseStartBounds MaskedArithmeticGeometry MaskedBadMass
open FiniteStartMaskModel FiniteStartMaskAverages FiniteStartMaskPairBounds MacroscopicMaskGeometry
open ArratiaGoldsteinGordonInput SectionThirteenFiniteBound SectionThirteenCouplings
open ConditionalAGGAverage ScalarSteinInput MaskedScalarCoupling
open scoped BigOperators NNReal

noncomputable section
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

theorem uniform_start_le_fullDefect {C L x : ℕ} (hx : 2≤x) (hL : 0<L) (hcut : x+L≤C) :
    uniformEventProbability (fun omega : SampleSpace C => startAt omega x L) ≤
      (2 : ℚ)^(defectIndices (L+1) x (L+1)).card/(2 : ℚ)^L := by
  rw [uniform_start_eq_affine C L x hL]
  exact (corollary_two_five_upper_finite hx hcut (startRhs L)).trans
    (div_le_div_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1 : ℚ)≤2) (Nat.sub_le _ _)) (by positivity))

theorem sum_uniform_start_le {C L : ℕ} (mask : Finset ℕ) (hL : 0<L)
    (hpos : ∀ x∈mask,2≤x) (hcut : ∀ x∈mask,x+L≤C) :
    (∑ x∈mask,uniformEventProbability (fun omega : SampleSpace C => startAt omega x L)) ≤
      ((fullDefectMass L mask : ℚ)+mask.card)/(2 : ℚ)^L := by
  calc
    _ ≤ ∑ x∈mask,(2 : ℚ)^(defectIndices (L+1) x (L+1)).card/(2 : ℚ)^L :=
      Finset.sum_le_sum fun x hx => uniform_start_le_fullDefect (hpos x hx) hL (hcut x hx)
    _ = _ := by
      rw [← Finset.sum_div,fullDefectMass_cast,Finset.sum_sub_distrib]
      simp

theorem exists_removed_start_of_counts_ne {C L : ℕ} {small mask : Finset ℕ}
    (hsub : small⊆mask) (omega : SampleSpace C)
    (hne : finiteStartCount C L mask omega≠finiteStartCount C L small omega) :
    ∃ x∈mask\small,startAt omega x L := by
  by_contra h
  push Not at h
  apply hne
  unfold finiteStartCount
  symm
  apply Finset.sum_subset hsub
  intro x hx hn
  exact if_neg (h x (Finset.mem_sdiff.mpr ⟨hx,hn⟩))

/-- The true scalar coupling cost of removing any subset of actual sites. -/
theorem finiteLaw_subset_tv_le {C L : ℕ} {small mask : Finset ℕ} (hsub : small⊆mask) :
    natTotalVariation (finiteLaw C L mask) (finiteLaw C L small) ≤
      ∑ x∈mask\small,((uniformEventProbability (fun omega : SampleSpace C => startAt omega x L) : ℚ) : ℝ) := by
  apply (natTotalVariation_finiteNatLaw_le_disagreement (fullUniformPMF C)
    (finiteStartCount C L mask) (finiteStartCount C L small)).trans
  have he (x : ℕ) : ((uniformEventProbability (fun omega : SampleSpace C => startAt omega x L) : ℚ) : ℝ) =
      eventProbability (fullUniformPMF C) (fun omega => startAt omega x L) := by
    rw [eventProbability_fullUniformPMF_eq,finiteUniformProbability_eq_uniformEventProbability]
  simp_rw [he]
  unfold disagreementProbability eventProbability
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro omega _
  by_cases hne : finiteStartCount C L mask omega≠finiteStartCount C L small omega
  · rw [if_pos hne]
    obtain ⟨x,hx,hs⟩ := exists_removed_start_of_counts_ne hsub omega hne
    calc
      _ = if startAt omega x L then (fullUniformPMF C).prob omega else 0 := (if_pos hs).symm
      _ ≤ _ := by
        apply Finset.single_le_sum (s := mask\small)
          (f := fun y => if startAt omega y L then (fullUniformPMF C).prob omega else 0)
        · intro y _
          split_ifs
          · exact (fullUniformPMF C).nonneg omega
          · exact le_rfl
        · exact hx
  · rw [if_neg hne]
    exact Finset.sum_nonneg fun x _ => by
      split_ifs
      · exact (fullUniformPMF C).nonneg omega
      · exact le_rfl

theorem finiteLaw_good_tv_le {C L Y : ℕ} (mask : Finset ℕ) (hL : 0<L)
    (hpos : ∀ x∈mask,2≤x) (hcut : ∀ x∈mask,x+L≤C) :
    natTotalVariation (finiteLaw C L mask) (finiteLaw C L (goodMask L Y mask)) ≤
      ((fullDefectMass L mask : ℝ)+(badMask L Y mask).card)/(2 : ℝ)^L := by
  have hset : mask\goodMask L Y mask = badMask L Y mask := Finset.sdiff_sdiff_eq_self (badMask_subset L Y mask)
  have hc := finiteLaw_subset_tv_le (C := C) (L := L) (goodMask_subset L Y mask)
  rw [hset] at hc
  have hb := sum_uniform_start_le (badMask L Y mask) hL
    (fun x hx => hpos x (badMask_subset L Y mask hx))
    (fun x hx => hcut x (badMask_subset L Y mask hx))
  have hbr : (∑ x∈badMask L Y mask,((uniformEventProbability
      (fun omega : SampleSpace C => startAt omega x L) : ℚ) : ℝ)) ≤
      ((fullDefectMass L (badMask L Y mask) : ℝ)+(badMask L Y mask).card)/(2 : ℝ)^L := by
    have h := (Rat.cast_le (K := ℝ)).mpr hb
    push_cast at h
    exact h
  apply (hc.trans hbr).trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hd : (fullDefectMass L (badMask L Y mask) : ℝ) ≤ fullDefectMass L mask := by
    exact_mod_cast fullDefectMass_mono (L := L) (badMask_subset L Y mask)
  exact add_le_add hd le_rfl

theorem abs_maskRate_sub_eq {L : ℕ} {small mask : Finset ℕ} (hsub : small⊆mask) :
    |(maskRate L small : ℝ)-(maskRate L mask : ℝ)|=(mask\small).card/(2 : ℝ)^L := by
  have hc : (small.card : ℝ)+(mask\small).card=mask.card := by
    have h := Finset.card_sdiff_add_card_eq_card hsub
    have h' : small.card+(mask\small).card=mask.card := by omega
    exact_mod_cast h'
  change |(small.card : ℝ)/2^L-mask.card/2^L|=_
  rw [← hc]
  have he : (small.card : ℝ)/2^L-(small.card+(mask\small).card)/2^L =
      -((mask\small).card/(2 : ℝ)^L) := by ring
  rw [he,abs_neg,abs_of_nonneg (by positivity)]

theorem good_poisson_tv_le (L Y : ℕ) (mask : Finset ℕ) :
    natTotalVariation (poissonMass (maskRate L (goodMask L Y mask))) (poissonMass (maskRate L mask)) ≤
      (badMask L Y mask).card/(2 : ℝ)^L := by
  rw [poissonMass_eq_poissonPMFReal,poissonMass_eq_poissonPMFReal]
  have h := (natTotalVariation_poisson_le_abs_rate_sub (maskRate L (goodMask L Y mask)) (maskRate L mask)).trans_eq
    (abs_maskRate_sub_eq (goodMask_subset L Y mask))
  have he : mask\goodMask L Y mask=badMask L Y mask := Finset.sdiff_sdiff_eq_self (badMask_subset L Y mask)
  simpa only [he] using h

end
end PaperC.V282.FiniteStartMaskDeletion
