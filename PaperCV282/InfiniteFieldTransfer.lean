import PaperCV282.AllStartFieldTransfer
import PaperCV282.MaskedScalarFullConditioning

/-!
# Theorem 4.1 for the actual joint source field and all F_Y atoms

The state space is the whole vector of masked start indicators, with a
product Poisson target on the same finite set of sites. The conditioning
cylinder is max(dyadicCutoff,Y), so no prime at most Y is omitted. For Y
larger than the event cylinder the proved whole-field deletion bound closes
the estimate. The process AGG input remains an explicit published premise.
-/

namespace PaperC.V282.InfiniteFieldTransfer

open MeasureTheory Set
open InfiniteRademacher InfiniteCylinderTransfer InfiniteStartProbabilityTransfer
open InfiniteConditionalWords InfiniteMaskedScalarTransfer MaskedScalarFullConditioning
open InfiniteExactLengthProbabilityTransfer
open ArratiaGoldsteinGordonInput ConditionalStartProbability ConditionalDependencyGraph
open ConditionalAGGInstantiation ConditionalAGGAverage SectionThirteenFiniteBound SectionThirteenCouplings
open LargePrimeDependencyGraph SectionTwelveMoments MaskedPoissonCritical
open MaskedArithmeticGeometry MaskedBadMass MaskedPairGeometry TwoWindowParity
open AllStartConditionalDependency AllStartFieldTransfer
open FiniteFieldTotalVariation FiniteFieldPoissonCoupling ProcessAGGInput
open scoped BigOperators ENNReal NNReal

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

noncomputable section

@[reducible]
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

def cylinderMaskedField (C N L : ℕ) (mask : Finset ℕ) (omega : SampleSpace C)
    (x : {x : ℕ // x ∈ dyadicBlock N}) : ℕ :=
  if x.val ∈ mask ∧ startAt omega x.val L then 1 else 0

def conditionalCylinderFieldLaw (C N L Y : ℕ) (mask : Finset ℕ)
    (sigma : SmallSample C Y) : ({x : ℕ // x ∈ dyadicBlock N} → ℕ) → ℝ :=
  finiteFieldLaw (largeUniformPMF C Y)
    (fun eta => cylinderMaskedField C N L mask (assemble C Y sigma eta))

def infiniteMaskedField (N L : ℕ) (mask : Finset ℕ) (omega : InfiniteSample)
    (x : {x : ℕ // x ∈ dyadicBlock N}) : ℕ :=
  if x.val ∈ mask ∧ StartEvent (infiniteValueBit omega) x.val L then 1 else 0

def infiniteMaskedFieldLaw (N L : ℕ) (mask : Finset ℕ)
    (k : {x : ℕ // x ∈ dyadicBlock N} → ℕ) : ℝ :=
  (infiniteRademacherMeasure {omega | infiniteMaskedField N L mask omega = k}).toReal

theorem finiteFieldLaw_eq_eventProbability {Omega alpha : Type*} [Fintype Omega]
    (mu : FinitePMF Omega) (W : Omega → alpha) (k : alpha) :
    finiteFieldLaw mu W k = eventProbability mu (fun omega => W omega = k) := by
  unfold finiteFieldLaw eventProbability
  apply Finset.sum_congr rfl
  intro omega homega
  by_cases h : W omega = k <;> simp [h]

theorem finiteFieldLaw_zero_eq_poissonFieldMass {Omega iota : Type*}
    [Fintype Omega] [Fintype iota] (mu : FinitePMF Omega) :
    finiteFieldLaw mu (fun _ => (0 : iota → ℕ)) = poissonFieldMass 0 := by
  funext k
  rw [poissonFieldMass_zero]
  unfold finiteFieldLaw
  by_cases hk : k = 0
  · simp [hk, mu.sum_prob]
  · have hk' : (0 : iota → ℕ) ≠ k := Ne.symm hk
    simp [hk, hk']

theorem field_tv_le_active_sum_add_rates {Omega iota : Type*}
    [Fintype Omega] [Fintype iota] (mu : FinitePMF Omega)
    (W : Omega → iota → ℕ) (rate : iota → ℝ≥0) :
    massTotalVariation (finiteFieldLaw mu W) (poissonFieldMass rate) ≤
      (∑ i, eventProbability mu (fun omega => W omega i ≠ 0)) + ∑ i, (rate i : ℝ) := by
  have hdelete := massTotalVariation_finiteFieldLaw_le_coordinate_disagreements mu W (fun _ => 0)
  rw [finiteFieldLaw_zero_eq_poissonFieldMass] at hdelete
  have hshift := massTotalVariation_poissonField_le_of_le
    (fun i => show (0 : iota → ℝ≥0) i ≤ rate i from bot_le)
  simp only [Pi.zero_apply, NNReal.coe_zero, sub_zero] at hshift
  have htriangle := massTotalVariation_triangle (summable_finiteFieldLaw mu W)
    (summable_poissonFieldMass (0 : iota → ℝ≥0)) (summable_poissonFieldMass rate)
    (finiteFieldLaw_nonneg mu W) (poissonFieldMass_nonneg 0) (poissonFieldMass_nonneg rate)
  exact htriangle.trans (add_le_add hdelete hshift)

theorem sum_allFieldRates {N L : ℕ} (mask : Finset ℕ) (hmask : mask ⊆ dyadicBlock N) :
    (∑ x : {x : ℕ // x ∈ dyadicBlock N}, (allFieldRates N L mask x : ℝ)) =
      mask.card / (2 : ℝ) ^ L := by
  have heach (x : {x : ℕ // x ∈ dyadicBlock N}) :
      (allFieldRates N L mask x : ℝ) = if x.val ∈ mask then (1 : ℝ) / 2 ^ L else 0 := by
    by_cases hx : x.val ∈ mask <;> simp [allFieldRates, hx]
    rfl
  simp_rw [heach]
  rw [← Finset.sum_subtype (dyadicBlock N) (fun _ => Iff.rfl)
    (fun x => if x ∈ mask then (1 : ℝ) / 2 ^ L else 0), ← Finset.sum_filter]
  have hf : (dyadicBlock N).filter (fun x => x ∈ mask) = mask := by
    ext x
    simp only [Finset.mem_filter]
    exact ⟨And.right, fun hx => ⟨hmask hx, hx⟩⟩
  rw [hf]
  simp [div_eq_mul_inv]

theorem conditionalCylinderFieldLaw_tv_le_start_sum {C N L Y : ℕ}
    (mask : Finset ℕ) (hmask : mask ⊆ dyadicBlock N) (sigma : SmallSample C Y) :
    massTotalVariation (conditionalCylinderFieldLaw C N L Y mask sigma)
      (poissonFieldMass (allFieldRates N L mask)) ≤
      (∑ x ∈ mask, eventProbability (largeUniformPMF C Y)
        (fun eta => startAt (assemble C Y sigma eta) x L)) + mask.card / (2 : ℝ) ^ L := by
  have h := field_tv_le_active_sum_add_rates (largeUniformPMF C Y)
    (fun eta => cylinderMaskedField C N L mask (assemble C Y sigma eta)) (allFieldRates N L mask)
  rw [sum_allFieldRates mask hmask] at h
  have heach (x : {x : ℕ // x ∈ dyadicBlock N}) :
      eventProbability (largeUniformPMF C Y)
        (fun eta => cylinderMaskedField C N L mask (assemble C Y sigma eta) x ≠ 0) =
      if x.val ∈ mask then eventProbability (largeUniformPMF C Y)
        (fun eta => startAt (assemble C Y sigma eta) x.val L) else 0 := by
    by_cases hx : x.val ∈ mask
    · simp only [if_pos hx]
      unfold eventProbability
      apply Finset.sum_congr rfl
      intro eta heta
      by_cases hs : startAt (assemble C Y sigma eta) x.val L <;> simp [cylinderMaskedField, hx, hs]
    · simp [cylinderMaskedField, hx, eventProbability]
  simp_rw [heach] at h
  rw [← Finset.sum_subtype (dyadicBlock N) (fun _ => Iff.rfl)
    (fun x => if x ∈ mask then eventProbability (largeUniformPMF C Y)
      (fun eta => startAt (assemble C Y sigma eta) x L) else 0), ← Finset.sum_filter] at h
  have hf : (dyadicBlock N).filter (fun x => x ∈ mask) = mask := by
    ext x
    simp only [Finset.mem_filter]
    exact ⟨And.right, fun hx => ⟨hmask hx, hx⟩⟩
  rw [hf] at h
  exact h

theorem average_conditionalCylinderFieldLaw_tv_le_delete {C N L Y : ℕ}
    (mask : Finset ℕ) (hmask : mask ⊆ dyadicBlock N)
    (hcut : ∀ x ∈ mask, x + L ≤ C) (hN : 2 ≤ N) (hL : 0 < L) :
    finiteUniformAverage (fun sigma : SmallSample C Y =>
      massTotalVariation (conditionalCylinderFieldLaw C N L Y mask sigma)
        (poissonFieldMass (allFieldRates N L mask))) ≤
      ((fullDefectMass L mask : ℝ) + 2 * mask.card) / (2 : ℝ) ^ L := by
  have h := finiteUniformAverage_mono (fun sigma : SmallSample C Y =>
    conditionalCylinderFieldLaw_tv_le_start_sum (L := L) mask hmask sigma)
  have hsplit (f : SmallSample C Y → ℝ) (c : ℝ) :
      finiteUniformAverage (fun sigma => f sigma + c) = finiteUniformAverage f + c := by
    unfold finiteUniformAverage
    rw [Finset.sum_add_distrib, add_div]
    simp
  rw [hsplit, finiteUniformAverage_finsetSum] at h
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
  simp only [Rat.cast_div, Rat.cast_add, Rat.cast_natCast, Rat.cast_pow, Rat.cast_ofNat] at hmass
  apply h.trans
  convert add_le_add_right hmass ((mask.card : ℝ) / (2 : ℝ) ^ L) using 1 <;> first | rfl | ring

theorem conditionalCylinderFieldLaw_at_dyadic (N L Y : ℕ) (mask : Finset ℕ)
    (sigma : SmallSample (dyadicCutoff N L) Y) :
    conditionalCylinderFieldLaw (dyadicCutoff N L) N L Y mask sigma =
      finiteFieldLaw (largeUniformPMF (dyadicCutoff N L) Y)
        (indicatorField (maskedConditionedAllStartIndicator N L Y mask sigma)) := by
  unfold conditionalCylinderFieldLaw
  congr 1
  funext eta x
  by_cases hx : x.val ∈ mask <;>
    by_cases hs : startAt (assemble (dyadicCutoff N L) Y sigma eta) x.val L <;>
    simp [cylinderMaskedField, indicatorField, maskedConditionedAllStartIndicator,
      conditionedAllStartIndicator, hx, hs]

theorem average_full_conditioning_field_tv_le (hAGG : ProcessAGGStatement)
    {N L Y : ℕ} (mask : Finset ℕ) (hmask : mask ⊆ dyadicBlock N)
    (hN : 2 ≤ N) (hL : 0 < L) (hY : 2 * L ≤ Y) :
    finiteUniformAverage (fun sigma : SmallSample (max (dyadicCutoff N L) Y) Y =>
      massTotalVariation (conditionalCylinderFieldLaw (max (dyadicCutoff N L) Y) N L Y mask sigma)
        (poissonFieldMass (allFieldRates N L mask))) ≤
      ((fullDefectMass L mask : ℝ) + 2 * (fullBadMask N L Y mask).card) / (2 : ℝ) ^ L +
        2 * (((mask.card : ℝ) + 2 * (maskedSupportEdges L Y mask).card +
          (jointDefectMass N L (separatedPairs mask L) : ℝ)) / (2 : ℝ) ^ (2 * L)) := by
  by_cases hYM : Y ≤ dyadicCutoff N L
  · rw [max_eq_left hYM]
    simp_rw [conditionalCylinderFieldLaw_at_dyadic]
    exact average_allStart_field_le_arithmetic hAGG mask hmask hN hL hY
  · have hMY : dyadicCutoff N L < Y := Nat.lt_of_not_ge hYM
    rw [max_eq_right hMY.le, fullBadMask_eq_mask_of_large_cutoff mask hmask hN hMY]
    have hcut : ∀ x ∈ mask, x + L ≤ Y := by
      intro x hx
      have hb := Finset.mem_Ico.mp (hmask hx)
      unfold dyadicCutoff at hMY
      omega
    apply (average_conditionalCylinderFieldLaw_tv_le_delete (Y := Y) mask hmask hcut hN hL).trans
    exact le_add_of_nonneg_right (by positivity)

theorem infiniteMaskedField_event_eq_preimage {C N L : ℕ} (mask : Finset ℕ)
    (hcut : ∀ x ∈ mask, x + L ≤ C) (k : {x : ℕ // x ∈ dyadicBlock N} → ℕ) :
    {omega | infiniteMaskedField N L mask omega = k} =
      restrictToFinite C ⁻¹' {sigma | cylinderMaskedField C N L mask sigma = k} := by
  have hfield (omega : InfiniteSample) :
      cylinderMaskedField C N L mask (restrictToFinite C omega) = infiniteMaskedField N L mask omega := by
    funext x
    by_cases hx : x.val ∈ mask
    · have hiff := startAt_restrictToFinite_iff omega (hcut x.val hx)
      by_cases hs : StartEvent (infiniteValueBit omega) x.val L
      · simp [cylinderMaskedField, infiniteMaskedField, hx, hs, hiff.mpr hs]
      · have hf : ¬startAt (restrictToFinite C omega) x.val L := fun h => hs (hiff.mp h)
        simp [cylinderMaskedField, infiniteMaskedField, hx, hs, hf]
    · simp [cylinderMaskedField, infiniteMaskedField, hx]
  ext omega
  simp only [Set.mem_setOf_eq, Set.mem_preimage, hfield]

theorem conditionalCylinderFieldLaw_eq_infinite_atom_ratio {C N L Y : ℕ} (mask : Finset ℕ)
    (hcut : ∀ x ∈ mask, x + L ≤ C) (sigma : SmallSample C Y)
    (k : {x : ℕ // x ∈ dyadicBlock N} → ℕ) :
    conditionalCylinderFieldLaw C N L Y mask sigma k =
      (infiniteRademacherMeasure
        ({omega | infiniteMaskedField N L mask omega = k} ∩ infiniteSmallPrimeAtom C Y sigma)).toReal /
      (infiniteRademacherMeasure (infiniteSmallPrimeAtom C Y sigma)).toReal := by
  rw [infiniteMaskedField_event_eq_preimage mask hcut k]
  exact (finiteFieldLaw_eq_eventProbability _ _ _).trans
    (eventProbability_eq_infinite_atom_ratio C Y (fun omega => cylinderMaskedField C N L mask omega = k) sigma)

theorem theorem_four_one_field_full_FY (hAGG : ProcessAGGStatement)
    {N L Y : ℕ} (mask : Finset ℕ) (hmask : mask ⊆ dyadicBlock N)
    (hN : 2 ≤ N) (hL : 0 < L) (hY : 2 * L ≤ Y) :
    smallPrimeSigmaAlgebra (max (dyadicCutoff N L) Y) Y =
        MeasurableSpace.comap (restrictToFinite Y) inferInstance ∧
    finiteUniformAverage (fun sigma : SmallSample (max (dyadicCutoff N L) Y) Y =>
      massTotalVariation
        (fun k => (infiniteRademacherMeasure
          ({omega | infiniteMaskedField N L mask omega = k} ∩
            infiniteSmallPrimeAtom (max (dyadicCutoff N L) Y) Y sigma)).toReal /
          (infiniteRademacherMeasure (infiniteSmallPrimeAtom (max (dyadicCutoff N L) Y) Y sigma)).toReal)
        (poissonFieldMass (allFieldRates N L mask))) ≤
      ((fullDefectMass L mask : ℝ) + 2 * (fullBadMask N L Y mask).card) / (2 : ℝ) ^ L +
        2 * (((mask.card : ℝ) + 2 * (maskedSupportEdges L Y mask).card +
          (jointDefectMass N L (separatedPairs mask L) : ℝ)) / (2 : ℝ) ^ (2 * L)) := by
  refine ⟨smallPrimeSigmaAlgebra_eq_primeCylinder (le_max_right _ _), ?_⟩
  have hcut : ∀ x ∈ mask, x + L ≤ max (dyadicCutoff N L) Y := by
    intro x hx
    apply le_trans _ (le_max_left _ _)
    have hb := Finset.mem_Ico.mp (hmask hx)
    unfold dyadicCutoff
    omega
  simp_rw [← conditionalCylinderFieldLaw_eq_infinite_atom_ratio mask hcut]
  exact average_full_conditioning_field_tv_le hAGG mask hmask hN hL hY


theorem cylinderFieldLaw_eq_uniformMixture (C N L Y : ℕ) (mask : Finset ℕ) :
    finiteFieldLaw (fullUniformPMF C) (cylinderMaskedField C N L mask) =
      fun k => uniformAverage (fun sigma : SmallSample C Y =>
        conditionalCylinderFieldLaw C N L Y mask sigma k) := by
  funext k
  have h := finiteUniformAverage_largeEventProbability_eq_full C Y
    (fun omega => cylinderMaskedField C N L mask omega = k)
  rw [← finiteUniformProbability_eq_uniformEventProbability, ← eventProbability_fullUniformPMF_eq] at h
  simp only [conditionalCylinderFieldLaw, finiteFieldLaw_eq_eventProbability]
  exact h.symm

theorem measurableSet_infiniteMaskedField_event {C N L : ℕ} (mask : Finset ℕ)
    (hcut : ∀ x ∈ mask, x + L ≤ C) (k : {x : ℕ // x ∈ dyadicBlock N} → ℕ) :
    MeasurableSet {omega | infiniteMaskedField N L mask omega = k} := by
  rw [infiniteMaskedField_event_eq_preimage mask hcut k]
  exact (measurable_restrictToFinite _) (Set.toFinite _ |>.measurableSet)

theorem infiniteMaskedFieldLaw_eq_finiteFieldLaw {C N L : ℕ} (mask : Finset ℕ)
    (hcut : ∀ x ∈ mask, x + L ≤ C) :
    infiniteMaskedFieldLaw N L mask = finiteFieldLaw (fullUniformPMF C) (cylinderMaskedField C N L mask) := by
  funext k
  unfold infiniteMaskedFieldLaw
  rw [infiniteMaskedField_event_eq_preimage mask hcut k,
    ← Measure.map_apply (measurable_restrictToFinite C) (Set.toFinite _ |>.measurableSet),
    map_infiniteRademacherMeasure_restrictToFinite,
    finiteRademacherMeasure_event_eq_uniformEventProbability, ENNReal.toReal_ofReal]
  · rw [finiteFieldLaw_eq_eventProbability, eventProbability_fullUniformPMF_eq,
      finiteUniformProbability_eq_uniformEventProbability]
  · apply Rat.cast_nonneg.mpr
    unfold uniformEventProbability
    positivity

theorem hasSum_infiniteMaskedFieldLaw {N L : ℕ} (mask : Finset ℕ)
    (hmask : mask ⊆ dyadicBlock N) : HasSum (infiniteMaskedFieldLaw N L mask) 1 := by
  have hcut : ∀ x ∈ mask, x + L ≤ dyadicCutoff N L := by
    intro x hx
    have hb := Finset.mem_Ico.mp (hmask hx)
    unfold dyadicCutoff
    omega
  rw [infiniteMaskedFieldLaw_eq_finiteFieldLaw mask hcut]
  exact hasSum_finiteFieldLaw _ _

theorem hasSum_source_conditional_field {C N L Y : ℕ} (mask : Finset ℕ)
    (hcut : ∀ x ∈ mask, x + L ≤ C) (sigma : SmallSample C Y) :
    HasSum (fun k : {x : ℕ // x ∈ dyadicBlock N} → ℕ =>
      (infiniteRademacherMeasure
        ({omega | infiniteMaskedField N L mask omega = k} ∩ infiniteSmallPrimeAtom C Y sigma)).toReal /
      (infiniteRademacherMeasure (infiniteSmallPrimeAtom C Y sigma)).toReal) 1 := by
  simp_rw [← conditionalCylinderFieldLaw_eq_infinite_atom_ratio mask hcut]
  exact hasSum_finiteFieldLaw _ _

theorem theorem_four_one_field_unconditional (hAGG : ProcessAGGStatement)
    {N L Y : ℕ} (mask : Finset ℕ) (hmask : mask ⊆ dyadicBlock N)
    (hN : 2 ≤ N) (hL : 0 < L) (hY : 2 * L ≤ Y) :
    massTotalVariation (infiniteMaskedFieldLaw N L mask) (poissonFieldMass (allFieldRates N L mask)) ≤
      ((fullDefectMass L mask : ℝ) + 2 * (fullBadMask N L Y mask).card) / (2 : ℝ) ^ L +
        2 * (((mask.card : ℝ) + 2 * (maskedSupportEdges L Y mask).card +
          (jointDefectMass N L (separatedPairs mask L) : ℝ)) / (2 : ℝ) ^ (2 * L)) := by
  have hcut : ∀ x ∈ mask, x + L ≤ max (dyadicCutoff N L) Y := by
    intro x hx
    apply le_trans _ (le_max_left _ _)
    have hb := Finset.mem_Ico.mp (hmask hx)
    unfold dyadicCutoff
    omega
  rw [infiniteMaskedFieldLaw_eq_finiteFieldLaw mask hcut,
    cylinderFieldLaw_eq_uniformMixture (max (dyadicCutoff N L) Y) N L Y mask]
  have hmix := massTotalVariation_uniformMixture_le
    (fun sigma : SmallSample (max (dyadicCutoff N L) Y) Y =>
      conditionalCylinderFieldLaw (max (dyadicCutoff N L) Y) N L Y mask sigma)
    (poissonFieldMass (allFieldRates N L mask))
    (fun sigma => FiniteFieldTotalVariation.summable_abs_sub_of_nonneg
      (summable_finiteFieldLaw _ _) (summable_poissonFieldMass _)
      (finiteFieldLaw_nonneg _ _) (poissonFieldMass_nonneg _))
  exact hmix.trans (average_full_conditioning_field_tv_le hAGG mask hmask hN hL hY)

end

end PaperC.V282.InfiniteFieldTransfer
