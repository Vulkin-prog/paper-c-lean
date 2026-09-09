import PaperCV282.ProcessAGGInput
import PaperCV282.AllStartFieldCosts

/-!
# Joint conditional approximation on every masked dyadic site

The actual field, its retained field and both product Poisson targets live on
one common all-site carrier. The only approximation input is the explicit
published process AGG statement. All graph costs and both deletion costs are
proved from the actual indicators. No factor depending on the total intensity
is inserted into the process bound.
-/

namespace PaperC.V282.AllStartFieldTransfer

open ArratiaGoldsteinGordonInput ConditionalStartProbability ConditionalDependencyGraph
open ConditionalAGGInstantiation ConditionalAGGAverage MaskedPoissonCritical
open LargePrimeDependencyGraph SectionTwelveMoments SectionThirteenFiniteBound
open MaskedArithmeticGeometry MaskedArithmeticCosts MaskedPairGeometry TwoWindowParity
open AllStartConditionalDependency AllStartFieldCosts
open FiniteFieldTotalVariation FiniteFieldPoissonCoupling ProcessAGGInput
open scoped BigOperators NNReal

noncomputable section

@[reducible]
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

def allFieldRates (N L : ℕ) (mask : Finset ℕ)
    (x : {x : ℕ // x ∈ dyadicBlock N}) : ℝ≥0 :=
  if x.val ∈ mask then ⟨1 / (2 : ℝ) ^ L, by positivity⟩ else 0

def retainedAllSites (N L Y : ℕ) (mask : Finset ℕ) :
    Finset {x : ℕ // x ∈ dyadicBlock N} :=
  Finset.univ.filter (fun x => x.val ∈ fullGoodMask N L Y mask)

theorem retainedIndicators_allStart_eq (N L Y : ℕ) (mask : Finset ℕ)
    (sigma : SmallSample (dyadicCutoff N L) Y) :
    retainedIndicators (retainedAllSites N L Y mask)
      (maskedConditionedAllStartIndicator N L Y mask sigma) =
      maskedConditionedAllStartIndicator N L Y (fullGoodMask N L Y mask) sigma := by
  classical
  funext x eta
  by_cases hx : x.val ∈ fullGoodMask N L Y mask
  · have hxm := fullGoodMask_subset_mask N L Y mask hx
    simp [retainedIndicators, retainedAllSites, maskedConditionedAllStartIndicator, hx, hxm]
  · simp [retainedIndicators, retainedAllSites, maskedConditionedAllStartIndicator, hx]

theorem retainedRates_allFieldRates_eq (N L Y : ℕ) (mask : Finset ℕ) :
    retainedRates (retainedAllSites N L Y mask) (allFieldRates N L mask) =
      allFieldRates N L (fullGoodMask N L Y mask) := by
  classical
  funext x
  by_cases hx : x.val ∈ fullGoodMask N L Y mask
  · have hxm := fullGoodMask_subset_mask N L Y mask hx
    simp [retainedRates, retainedAllSites, allFieldRates, hx, hxm]
    rfl
  · simp [retainedRates, retainedAllSites, allFieldRates, hx]

theorem fieldRates_fullGood_allStart_eq {N L Y : ℕ} (mask : Finset ℕ)
    (hN : 2 ≤ N) (hL : 0 < L) (hLY : L + 1 ≤ Y)
    (sigma : SmallSample (dyadicCutoff N L) Y) :
    fieldRates (largeUniformPMF (dyadicCutoff N L) Y)
      (maskedConditionedAllStartIndicator N L Y (fullGoodMask N L Y mask) sigma) =
      allFieldRates N L (fullGoodMask N L Y mask) := by
  classical
  funext x
  apply NNReal.eq
  change marginal (largeUniformPMF (dyadicCutoff N L) Y)
    (maskedConditionedAllStartIndicator N L Y (fullGoodMask N L Y mask) sigma) x = _
  rw [marginal_maskedConditionedAllStartIndicator]
  by_cases hx : x.val ∈ fullGoodMask N L Y mask
  · rw [if_pos hx, marginal_conditionedAllStartIndicator_of_not_fullBad hN hL hLY sigma x
      (mem_fullGoodMask.mp hx).2]
    have hrate : allFieldRates N L (fullGoodMask N L Y mask) x =
        ⟨1 / (2 : ℝ) ^ L, by positivity⟩ := if_pos hx
    exact congrArg (fun r : ℝ≥0 => (r : ℝ)) hrate.symm
  · simp [allFieldRates, hx]

theorem badSite_marginal_sum_eq (N L Y : ℕ) (mask : Finset ℕ)
    (sigma : SmallSample (dyadicCutoff N L) Y) :
    (∑ x ∈ badFieldSites (retainedAllSites N L Y mask),
      marginal (largeUniformPMF (dyadicCutoff N L) Y)
        (maskedConditionedAllStartIndicator N L Y mask sigma) x) =
      ∑ x : {x : ℕ // x ∈ dyadicBlock N},
        if x.val ∈ fullBadMask N L Y mask then
          marginal (largeUniformPMF (dyadicCutoff N L) Y)
            (maskedConditionedAllStartIndicator N L Y mask sigma) x else 0 := by
  classical
  rw [badFieldSites, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hm : x.val ∈ mask <;> by_cases hb : x.val ∈ fullBadStarts N L Y <;>
    simp [retainedAllSites, mem_fullGoodMask, mem_fullBadMask, hm, hb,
      marginal_maskedConditionedAllStartIndicator]

theorem badSite_target_sum_eq {N L Y : ℕ} (mask : Finset ℕ)
    (hmask : mask ⊆ dyadicBlock N) :
    (∑ x ∈ badFieldSites (retainedAllSites N L Y mask), (allFieldRates N L mask x : ℝ)) =
      (fullBadMask N L Y mask).card / (2 : ℝ) ^ L := by
  classical
  rw [badFieldSites, Finset.sum_filter]
  trans ∑ x : {x : ℕ // x ∈ dyadicBlock N},
    if x.val ∈ fullBadMask N L Y mask then (1 : ℝ) / 2 ^ L else 0
  · apply Finset.sum_congr rfl
    intro x hx
    by_cases hm : x.val ∈ mask <;> by_cases hb : x.val ∈ fullBadStarts N L Y <;>
      simp [retainedAllSites, allFieldRates, mem_fullGoodMask, mem_fullBadMask, hm, hb]
    rfl
  rw [← Finset.sum_subtype (dyadicBlock N) (fun _ => Iff.rfl)
    (fun x => if x ∈ fullBadMask N L Y mask then (1 : ℝ) / 2 ^ L else 0),
    ← Finset.sum_filter]
  have hf : (dyadicBlock N).filter (fun x => x ∈ fullBadMask N L Y mask) =
      fullBadMask N L Y mask := by
    ext x
    simp only [Finset.mem_filter]
    exact ⟨And.right, fun hx => ⟨hmask (fullBadMask_subset_mask N L Y mask hx), hx⟩⟩
  rw [hf]
  simp [div_eq_mul_inv]

theorem allStart_field_process_with_deletion (hAGG : ProcessAGGStatement)
    {N L Y : ℕ} (mask : Finset ℕ) (hmask : mask ⊆ dyadicBlock N)
    (hN : 2 ≤ N) (hL : 0 < L) (hLY : L + 1 ≤ Y)
    (sigma : SmallSample (dyadicCutoff N L) Y) :
    massTotalVariation
      (finiteFieldLaw (largeUniformPMF (dyadicCutoff N L) Y)
        (indicatorField (maskedConditionedAllStartIndicator N L Y mask sigma)))
      (poissonFieldMass (allFieldRates N L mask)) ≤
      (∑ x : {x : ℕ // x ∈ dyadicBlock N},
        if x.val ∈ fullBadMask N L Y mask then
          marginal (largeUniformPMF (dyadicCutoff N L) Y)
            (maskedConditionedAllStartIndicator N L Y mask sigma) x else 0) +
      2 * (bOne (largeUniformPMF (dyadicCutoff N L) Y)
        (maskedConditionedGoodIndicator N L Y (fullGoodMask N L Y mask) sigma)
        (largePrimeDependencyGraph N L Y) +
        bTwo (largeUniformPMF (dyadicCutoff N L) Y)
        (maskedConditionedGoodIndicator N L Y (fullGoodMask N L Y mask) sigma)
        (largePrimeDependencyGraph N L Y)) +
      (fullBadMask N L Y mask).card / (2 : ℝ) ^ L := by
  classical
  have hdep := hasExactDependencyGraph_maskedConditionedAllStartIndicator
    (fullGoodMask N L Y mask) hL sigma
  rw [← retainedIndicators_allStart_eq] at hdep
  have hrates : fieldRates (largeUniformPMF (dyadicCutoff N L) Y)
      (retainedIndicators (retainedAllSites N L Y mask)
        (maskedConditionedAllStartIndicator N L Y mask sigma)) =
      retainedRates (retainedAllSites N L Y mask) (allFieldRates N L mask) := by
    rw [retainedIndicators_allStart_eq, fieldRates_fullGood_allStart_eq mask hN hL hLY sigma,
      retainedRates_allFieldRates_eq]
  have h := process_totalVariation_via_retention hAGG (largeUniformPMF (dyadicCutoff N L) Y)
    (maskedConditionedAllStartIndicator N L Y mask sigma) (retainedAllSites N L Y mask)
    (allFieldRates N L mask) (allStartDependencyGraph N L Y) hdep hrates
  rw [retainedIndicators_allStart_eq, bOne_fullGood_allStart_eq mask hmask,
    bTwo_fullGood_allStart_eq mask hmask, badSite_marginal_sum_eq, badSite_target_sum_eq mask hmask] at h
  exact h

theorem average_allStart_field_le_arithmetic (hAGG : ProcessAGGStatement)
    {N L Y : ℕ} (mask : Finset ℕ) (hmask : mask ⊆ dyadicBlock N)
    (hN : 2 ≤ N) (hL : 0 < L) (hY : 2 * L ≤ Y) :
    finiteUniformAverage (fun sigma : SmallSample (dyadicCutoff N L) Y =>
      massTotalVariation
        (finiteFieldLaw (largeUniformPMF (dyadicCutoff N L) Y)
          (indicatorField (maskedConditionedAllStartIndicator N L Y mask sigma)))
        (poissonFieldMass (allFieldRates N L mask))) ≤
      ((fullDefectMass L mask : ℝ) + 2 * (fullBadMask N L Y mask).card) / (2 : ℝ) ^ L +
      2 * (((mask.card : ℝ) + 2 * (maskedSupportEdges L Y mask).card +
        (jointDefectMass N L (separatedPairs mask L) : ℝ)) / (2 : ℝ) ^ (2 * L)) := by
  classical
  have hLY : L + 1 ≤ Y := by omega
  have h := finiteUniformAverage_mono
    (fun sigma => allStart_field_process_with_deletion hAGG mask hmask hN hL hLY sigma)
  have hsum {ι : Type} [Fintype ι] [Nonempty ι] (f g : ι → ℝ) (c : ℝ) :
      finiteUniformAverage (fun i => f i + 2 * g i + c) =
        finiteUniformAverage f + 2 * finiteUniformAverage g + c := by
    unfold finiteUniformAverage
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hc : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    field_simp
  rw [hsum, average_bad_marginal_sum_eq] at h
  have hgraph := average_stein_terms_le mask hmask hN hL hY
  have hdel := (Rat.cast_le (K := ℝ)).mpr
    (MaskedBadMass.masked_total_deletion_cost_le (Y := Y) hN hL mask hmask)
  push_cast at hdel
  linarith

theorem mixed_allStart_field_le_arithmetic (hAGG : ProcessAGGStatement)
    {N L Y : ℕ} (mask : Finset ℕ) (hmask : mask ⊆ dyadicBlock N)
    (hN : 2 ≤ N) (hL : 0 < L) (hY : 2 * L ≤ Y) :
    massTotalVariation
      (fun k => uniformAverage (fun sigma : SmallSample (dyadicCutoff N L) Y =>
        finiteFieldLaw (largeUniformPMF (dyadicCutoff N L) Y)
          (indicatorField (maskedConditionedAllStartIndicator N L Y mask sigma)) k))
      (poissonFieldMass (allFieldRates N L mask)) ≤
      ((fullDefectMass L mask : ℝ) + 2 * (fullBadMask N L Y mask).card) / (2 : ℝ) ^ L +
      2 * (((mask.card : ℝ) + 2 * (maskedSupportEdges L Y mask).card +
        (jointDefectMass N L (separatedPairs mask L) : ℝ)) / (2 : ℝ) ^ (2 * L)) := by
  have hmix := massTotalVariation_uniformMixture_le
    (fun sigma : SmallSample (dyadicCutoff N L) Y =>
      finiteFieldLaw (largeUniformPMF (dyadicCutoff N L) Y)
        (indicatorField (maskedConditionedAllStartIndicator N L Y mask sigma)))
    (poissonFieldMass (allFieldRates N L mask))
    (fun sigma => FiniteFieldTotalVariation.summable_abs_sub_of_nonneg
      (summable_finiteFieldLaw _ _) (summable_poissonFieldMass _)
      (finiteFieldLaw_nonneg _ _) (poissonFieldMass_nonneg _))
  exact hmix.trans (average_allStart_field_le_arithmetic hAGG mask hmask hN hL hY)

end

end PaperC.V282.AllStartFieldTransfer
