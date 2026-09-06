import PaperCV282.InfiniteMaskedScalarTransfer

/-!
# Scalar transfer for the entire small-prime sigma-algebra at every cutoff

The conditioning cylinder is max(Y,2N+L), so it always contains every
prime at most Y. Below the dyadic cutoff the sharp retained argument
applies. Above it every start is bad: deleting the whole actual count and
target costs at most its true first moment plus the target mean. This
closes the large-Y case without an extra Stein or arithmetic assumption.
-/

namespace PaperC.V282.MaskedScalarFullConditioning

open MeasureTheory Set
open InfiniteRademacher InfiniteCylinderTransfer InfiniteStartProbabilityTransfer
open InfiniteExactLengthProbabilityTransfer InfiniteConditionalWords InfiniteMaskedScalarTransfer
open ArratiaGoldsteinGordonInput ConditionalStartProbability ConditionalAGGInstantiation
open ConditionalAGGAverage ConditionalDependencyGraph SectionThirteenFiniteBound SectionThirteenCouplings
open SectionTwelveMoments LargePrimeDependencyGraph MaskedPoissonCritical
open MaskedArithmeticGeometry MaskedPairGeometry MaskedBadMass MaskedScalarRetained ScalarSteinInput
open MaskedScalarCoupling MaskedScalarTransfer TwoWindowParity DefectivePredicate
open scoped BigOperators ENNReal NNReal

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

noncomputable section

local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

/-- Literal masked count on any adequate prime cylinder. -/
def cylinderMaskedCount (C L : ℕ) (mask : Finset ℕ) (omega : SampleSpace C) : ℕ :=
  ∑ x ∈ mask, if startAt omega x L then 1 else 0

/-- Actual conditional count law at an arbitrary ambient prime cutoff. -/
def conditionalCylinderMaskedLaw (C L Y : ℕ) (mask : Finset ℕ)
    (sigma : SmallSample C Y) : ℕ → ℝ :=
  finiteNatLaw (largeUniformPMF C Y) (fun eta => cylinderMaskedCount C L mask (assemble C Y sigma eta))

/-- At the dyadic cutoff this is the exact law already used by the retained transfer. -/
theorem conditionalCylinderMaskedLaw_at_dyadic (N L Y : ℕ) (mask : Finset ℕ)
    (sigma : SmallSample (dyadicCutoff N L) Y) :
    conditionalCylinderMaskedLaw (dyadicCutoff N L) L Y mask sigma =
      conditionalMaskedLaw N L Y mask sigma := by
  rfl

/-- Adequate arbitrary cylinders preserve every event of the source masked count. -/
theorem infiniteMaskedCount_event_eq_preimage_cutoff {C L : ℕ} (mask : Finset ℕ)
    (hcut : ∀ x ∈ mask, x + L ≤ C) (k : ℕ) :
    {omega | infiniteMaskedCount L mask omega = k} =
      restrictToFinite C ⁻¹' {sigma | cylinderMaskedCount C L mask sigma = k} := by
  have hcount (omega : InfiniteSample) :
      cylinderMaskedCount C L mask (restrictToFinite C omega) = infiniteMaskedCount L mask omega := by
    unfold cylinderMaskedCount infiniteMaskedCount
    apply Finset.sum_congr rfl
    intro x hx
    have hiff := startAt_restrictToFinite_iff omega (hcut x hx)
    by_cases hs : StartEvent (infiniteValueBit omega) x L
    · simp [hs,hiff.mpr hs]
    · have hf : ¬startAt (restrictToFinite C omega) x L := fun h => hs (hiff.mp h)
      simp [hs,hf]
  ext omega
  simp only [Set.mem_setOf_eq,Set.mem_preimage,hcount]

/-- The conditional law at any adequate cutoff is a genuine source atom ratio. -/
theorem conditionalCylinderMaskedLaw_eq_infinite_atom_ratio {C L Y : ℕ} (mask : Finset ℕ)
    (hcut : ∀ x ∈ mask, x + L ≤ C) (sigma : SmallSample C Y) (k : ℕ) :
    conditionalCylinderMaskedLaw C L Y mask sigma k =
      (infiniteRademacherMeasure
        ({omega | infiniteMaskedCount L mask omega = k} ∩ infiniteSmallPrimeAtom C Y sigma)).toReal /
      (infiniteRademacherMeasure (infiniteSmallPrimeAtom C Y sigma)).toReal := by
  rw [infiniteMaskedCount_event_eq_preimage_cutoff mask hcut k]
  have h := eventProbability_eq_infinite_atom_ratio C Y
    (fun omega => cylinderMaskedCount C L mask omega = k) sigma
  have heq : conditionalCylinderMaskedLaw C L Y mask sigma k =
      eventProbability (largeUniformPMF C Y)
        (fun eta => cylinderMaskedCount C L mask (assemble C Y sigma eta) = k) := by
    unfold conditionalCylinderMaskedLaw finiteNatLaw eventProbability
    apply Finset.sum_congr rfl
    intro eta heta
    by_cases hk : cylinderMaskedCount C L mask (assemble C Y sigma eta) = k <;> simp [hk]
  exact heq.trans h

/-- A constant-zero count has the actual zero-rate Poisson law. -/
theorem finiteNatLaw_zero_eq_poissonMass {Omega : Type*} [Fintype Omega]
    (mu : FinitePMF Omega) : finiteNatLaw mu (fun _ => 0) = poissonMass 0 := by
  funext k
  rw [poissonMass_zero]
  unfold finiteNatLaw
  by_cases hk : k = 0
  · simp [hk,mu.sum_prob]
  · have hk' : (0 : ℕ) ≠ k := Ne.symm hk
    simp [hk,hk']

/-- Deleting an arbitrary count to zero and shifting the Poisson target is a true coupling. -/
theorem scalar_tv_le_probability_nonzero_add_rate {Omega : Type*} [Fintype Omega]
    (mu : FinitePMF Omega) (Z : Omega → ℕ) (rate : ℝ≥0) :
    natTotalVariation (finiteNatLaw mu Z) (poissonMass rate) ≤
      eventProbability mu (fun omega => Z omega ≠ 0) + (rate : ℝ) := by
  have hdelete := natTotalVariation_finiteNatLaw_le_disagreement mu Z (fun _ => 0)
  rw [finiteNatLaw_zero_eq_poissonMass] at hdelete
  have hshift : natTotalVariation (poissonMass 0) (poissonMass rate) ≤ (rate : ℝ) := by
    rw [poissonMass_eq_poissonPMFReal,poissonMass_eq_poissonPMFReal]
    have h := natTotalVariation_poisson_le_abs_rate_sub 0 rate
    simpa using h
  have htriangle := natTotalVariation_triangle (summable_finiteNatLaw mu Z)
    (hasSum_poissonMass 0).summable (hasSum_poissonMass rate).summable
    (finiteNatLaw_nonneg mu Z) (poissonMass_nonneg 0) (poissonMass_nonneg rate)
  have hdis : disagreementProbability mu Z (fun _ => 0) =
      eventProbability mu (fun omega => Z omega ≠ 0) := by
    unfold disagreementProbability eventProbability
    apply Finset.sum_congr rfl
    intro omega homega
    by_cases hz : Z omega = 0 <;> simp [hz]
  rw [hdis] at hdelete
  exact htriangle.trans (add_le_add hdelete hshift)

/-- The conditional union bound uses precisely the actual masked start events. -/
theorem conditionalCylinderMaskedLaw_tv_le_start_sum (C L Y : ℕ) (mask : Finset ℕ)
    (sigma : SmallSample C Y) :
    natTotalVariation (conditionalCylinderMaskedLaw C L Y mask sigma)
      (poissonMass (maskedTargetPoissonRate L mask)) ≤
        (∑ x ∈ mask, eventProbability (largeUniformPMF C Y)
          (fun eta => startAt (assemble C Y sigma eta) x L)) + (maskedTargetPoissonRate L mask : ℝ) := by
  have h := scalar_tv_le_probability_nonzero_add_rate (largeUniformPMF C Y)
    (fun eta => cylinderMaskedCount C L mask (assemble C Y sigma eta)) (maskedTargetPoissonRate L mask)
  apply h.trans
  apply add_le_add _ (le_refl _)
  unfold eventProbability
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro eta heta
  by_cases hz : cylinderMaskedCount C L mask (assemble C Y sigma eta) = 0
  · simp only [hz,ne_eq,not_true_eq_false,if_false]
    exact Finset.sum_nonneg fun x hx => by
      split_ifs
      · exact (largeUniformPMF C Y).nonneg eta
      · exact le_rfl
  · simp only [hz,ne_eq,not_false_eq_true,if_true]
    have hex : ∃ x ∈ mask, startAt (assemble C Y sigma eta) x L := by
      by_contra hn
      push Not at hn
      apply hz
      unfold cylinderMaskedCount
      exact Finset.sum_eq_zero fun x hx => if_neg (hn x hx)
    obtain ⟨x,hx,hs⟩ := hex
    calc
      _ = if startAt (assemble C Y sigma eta) x L then (largeUniformPMF C Y).prob eta else 0 := (if_pos hs).symm
      _ ≤ _ := by
        apply Finset.single_le_sum (s := mask)
          (f := fun z => if startAt (assemble C Y sigma eta) z L then (largeUniformPMF C Y).prob eta else 0)
        · intro z hz
          split_ifs
          · exact (largeUniformPMF C Y).nonneg eta
          · exact le_rfl
        · exact hx

/-- The source identity transports one probability between any adequate cylinders. -/
theorem finite_start_probability_eq_dyadic {N L C x : ℕ} (hx : x ∈ dyadicBlock N)
    (hcut : x + L ≤ C) :
    ((uniformEventProbability (fun omega : SampleSpace C => startAt omega x L) : ℚ) : ℝ) =
      (startProbability N L x : ℝ) := by
  have hsource : infiniteRademacherMeasure (infiniteStartEvent x L) =
      ENNReal.ofReal (((uniformEventProbability (fun omega : SampleSpace C => startAt omega x L) : ℚ) : ℝ)) := by
    rw [infiniteStartEvent_eq_preimage hcut,
      ← Measure.map_apply (measurable_restrictToFinite C) (measurableSet_finiteStartEvent C x L),
      map_infiniteRademacherMeasure_restrictToFinite]
    exact finiteRademacherMeasure_event_eq_uniformEventProbability _
  have hr := infiniteStartProbability_eq_startProbability (L := L) hx
  unfold infiniteStartProbability at hr
  rw [hsource,ENNReal.toReal_ofReal] at hr
  · exact hr
  · apply Rat.cast_nonneg.mpr
    unfold uniformEventProbability
    positivity

/-- Whole-count deletion averaged over any adequate conditioning cylinder. -/
theorem average_conditionalCylinderMaskedLaw_tv_le_delete {N L C Y : ℕ} (mask : Finset ℕ)
    (hmask : mask ⊆ dyadicBlock N) (hcut : ∀ x ∈ mask, x + L ≤ C)
    (hN : 2 ≤ N) (hL : 0 < L) :
    finiteUniformAverage (fun sigma : SmallSample C Y =>
      natTotalVariation (conditionalCylinderMaskedLaw C L Y mask sigma)
        (poissonMass (maskedTargetPoissonRate L mask))) ≤
      ((fullDefectMass L mask : ℝ) + 2 * mask.card) / (2 : ℝ) ^ L := by
  have h := finiteUniformAverage_mono (fun sigma : SmallSample C Y =>
    conditionalCylinderMaskedLaw_tv_le_start_sum C L Y mask sigma)
  have hsplit (f : SmallSample C Y → ℝ) (c : ℝ) :
      finiteUniformAverage (fun sigma => f sigma + c) = finiteUniformAverage f + c := by
    unfold finiteUniformAverage
    rw [Finset.sum_add_distrib,add_div]
    simp
  rw [hsplit,finiteUniformAverage_finsetSum] at h
  have heach (x : ℕ) : finiteUniformAverage (fun sigma : SmallSample C Y =>
      eventProbability (largeUniformPMF C Y) (fun eta => startAt (assemble C Y sigma eta) x L)) =
        ((uniformEventProbability (fun omega : SampleSpace C => startAt omega x L) : ℚ) : ℝ) :=
    finiteUniformAverage_largeEventProbability_eq_full C Y (fun omega => startAt omega x L)
  simp_rw [heach] at h
  have hsum : (∑ x ∈ mask,
      ((uniformEventProbability (fun omega : SampleSpace C => startAt omega x L) : ℚ) : ℝ)) =
      ((∑ x ∈ mask, startProbability N L x : ℚ) : ℝ) := by
    push_cast
    apply Finset.sum_congr rfl
    intro x hx
    exact finite_start_probability_eq_dyadic (hmask hx) (hcut x hx)
  rw [hsum] at h
  have hmass := (Rat.cast_le (K := ℝ)).mpr (startProbabilityMass_le_mask_defects hN hL mask hmask)
  simp only [Rat.cast_div,Rat.cast_add,Rat.cast_natCast,Rat.cast_pow,Rat.cast_ofNat] at hmass
  apply h.trans
  change ((∑ x ∈ mask, startProbability N L x : ℚ) : ℝ) + mask.card / (2 : ℝ) ^ L ≤ _
  convert add_le_add_right hmass ((mask.card : ℝ) / (2 : ℝ) ^ L) using 1 <;>
    first | rfl | ring

/-- Once Y exceeds the event cylinder every masked site belongs to the whole-support bad set. -/
theorem fullBadMask_eq_mask_of_large_cutoff {N L Y : ℕ} (mask : Finset ℕ)
    (hmask : mask ⊆ dyadicBlock N) (hN : 2 ≤ N) (hY : dyadicCutoff N L < Y) :
    fullBadMask N L Y mask = mask := by
  ext x
  constructor
  · intro hx
    exact fullBadMask_subset_mask N L Y mask hx
  · intro hx
    apply mem_fullBadMask.mpr
    refine ⟨hx,mem_fullBadStarts.mpr ⟨hmask hx,x - 1,?_,?_⟩⟩
    · exact mem_startTreeSupport.mpr (Or.inl rfl)
    · intro p hp hpY
      have hxb := Finset.mem_Ico.mp (hmask hx)
      have hpos : 0 < x - 1 := by omega
      have hlt : x - 1 < p := by unfold dyadicCutoff at hY; omega
      have hnot : ¬p ∣ x - 1 := fun hd => (Nat.not_le_of_lt hlt) (Nat.le_of_dvd hpos hd)
      simp [parityVec_apply,Nat.factorization_eq_zero_of_not_dvd hnot]

/-- The sharp masked scalar budget holds at the cylinder containing every small prime, for all Y. -/
theorem average_full_conditioning_scalar_tv_le (hStein : ScalarSteinFactorsStatement)
    {N L Y : ℕ} (mask : Finset ℕ) (hmask : mask ⊆ dyadicBlock N)
    (hN : 2 ≤ N) (hL : 0 < L) (hY : 2 * L ≤ Y) :
    finiteUniformAverage (fun sigma : SmallSample (max (dyadicCutoff N L) Y) Y =>
      natTotalVariation (conditionalCylinderMaskedLaw (max (dyadicCutoff N L) Y) L Y mask sigma)
        (poissonMass (maskedTargetPoissonRate L mask))) ≤
      ((fullDefectMass L mask : ℝ) + 2 * (fullBadMask N L Y mask).card) / (2 : ℝ) ^ L +
        2 * firstSteinFactor (retainedRate N L Y mask) *
          (((mask.card : ℝ) + (maskedSupportEdges L Y mask).card +
            (jointDefectMass N L (separatedPairs mask L) : ℝ)) / (2 : ℝ) ^ (2 * L)) := by
  by_cases hYM : Y ≤ dyadicCutoff N L
  · rw [max_eq_left hYM]
    simp_rw [conditionalCylinderMaskedLaw_at_dyadic]
    exact theorem_four_one_scalar_conditional hStein mask hmask hN hL hY
  · have hMY : dyadicCutoff N L < Y := Nat.lt_of_not_ge hYM
    rw [max_eq_right hMY.le,fullBadMask_eq_mask_of_large_cutoff mask hmask hN hMY]
    have hcut : ∀ x ∈ mask, x + L ≤ Y := by
      intro x hx
      have hb := Finset.mem_Ico.mp (hmask hx)
      unfold dyadicCutoff at hMY
      omega
    apply (average_conditionalCylinderMaskedLaw_tv_le_delete (Y := Y) mask hmask hcut hN hL).trans
    exact le_add_of_nonneg_right (mul_nonneg
      (mul_nonneg (by norm_num) (firstSteinFactor_nonneg _)) (by positivity))

/-- All source conditioning atoms have exactly uniform positive mass. -/
theorem conditioningAtoms_equiprobable (C Y : ℕ) (sigma : SmallSample C Y) :
    infiniteRademacherMeasure (infiniteSmallPrimeAtom C Y sigma) =
      ENNReal.ofReal (1 / (Fintype.card (SmallSample C Y) : ℝ)) := by
  rw [infiniteSmallPrimeAtom_measure,card_sampleSpace_eq_mul C Y]
  congr 1
  push_cast
  have hlarge : (Fintype.card (LargeSample C Y) : ℝ) ≠ 0 := by positivity
  field_simp

/-- Theorem 4.1 on true F_Y atoms for every Y, with no missing small-prime coordinates. -/
theorem theorem_four_one_scalar_full_FY (hStein : ScalarSteinFactorsStatement)
    {N L Y : ℕ} (mask : Finset ℕ) (hmask : mask ⊆ dyadicBlock N)
    (hN : 2 ≤ N) (hL : 0 < L) (hY : 2 * L ≤ Y) :
    smallPrimeSigmaAlgebra (max (dyadicCutoff N L) Y) Y =
        MeasurableSpace.comap (restrictToFinite Y) inferInstance ∧
    finiteUniformAverage (fun sigma : SmallSample (max (dyadicCutoff N L) Y) Y =>
      natTotalVariation
        (fun k => (infiniteRademacherMeasure
          ({omega | infiniteMaskedCount L mask omega = k} ∩
            infiniteSmallPrimeAtom (max (dyadicCutoff N L) Y) Y sigma)).toReal /
          (infiniteRademacherMeasure (infiniteSmallPrimeAtom (max (dyadicCutoff N L) Y) Y sigma)).toReal)
        (poissonMass (maskedTargetPoissonRate L mask))) ≤
      ((fullDefectMass L mask : ℝ) + 2 * (fullBadMask N L Y mask).card) / (2 : ℝ) ^ L +
        2 * firstSteinFactor (retainedRate N L Y mask) *
          (((mask.card : ℝ) + (maskedSupportEdges L Y mask).card +
            (jointDefectMass N L (separatedPairs mask L) : ℝ)) / (2 : ℝ) ^ (2 * L)) := by
  refine ⟨smallPrimeSigmaAlgebra_eq_primeCylinder (le_max_right _ _),?_⟩
  have hcut : ∀ x ∈ mask, x + L ≤ max (dyadicCutoff N L) Y := by
    intro x hx
    apply le_trans _ (le_max_left _ _)
    have hb := Finset.mem_Ico.mp (hmask hx)
    unfold dyadicCutoff
    omega
  simp_rw [← conditionalCylinderMaskedLaw_eq_infinite_atom_ratio mask hcut]
  exact average_full_conditioning_scalar_tv_le hStein mask hmask hN hL hY

end
end PaperC.V282.MaskedScalarFullConditioning
