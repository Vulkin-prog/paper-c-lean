import PaperCV282.MaskedScalarTransfer
import PaperCV282.InfiniteConditionalWords

/-!
# The masked scalar transfer in the infinite source model

The random variable below is the literal finite sum of source start events.
Its law agrees exactly with the finite-cylinder law in Theorem 4.1. A
separate atom identity identifies every represented conditional law; when
the cylinder covers Y, the partition generates the whole sigma-algebra F_Y.
-/

namespace PaperC.V282.InfiniteMaskedScalarTransfer

open MeasureTheory Set
open InfiniteRademacher InfiniteCylinderTransfer InfiniteStartProbabilityTransfer
open InfiniteExactLengthProbabilityTransfer InfiniteConditionalWords
open ArratiaGoldsteinGordonInput ConditionalStartProbability ConditionalAGGInstantiation
open ConditionalAGGAverage ConditionalDependencyGraph SectionThirteenFiniteBound SectionThirteenCouplings
open SectionTwelveMoments LargePrimeDependencyGraph MaskedPoissonCritical
open MaskedArithmeticGeometry MaskedPairGeometry MaskedScalarRetained ScalarSteinInput
open MaskedScalarCoupling MaskedScalarTransfer TwoWindowParity
open scoped BigOperators ENNReal NNReal

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

noncomputable section

local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

/-- Literal complete masked start count under the infinite Rademacher source law. -/
def infiniteMaskedCount (L : ℕ) (mask : Finset ℕ) (omega : InfiniteSample) : ℕ :=
  ∑ x ∈ mask, if StartEvent (infiniteValueBit omega) x L then 1 else 0

/-- The actual source mass function of the masked count. -/
def infiniteMaskedLaw (L : ℕ) (mask : Finset ℕ) (k : ℕ) : ℝ :=
  (infiniteRademacherMeasure {omega | infiniteMaskedCount L mask omega = k}).toReal

/-- The canonical dyadic cylinder observes every start in the literal mask. -/
theorem fullMaskedDyadicCount_restrict_eq {N L : ℕ} (mask : Finset ℕ)
    (hmask : mask ⊆ dyadicBlock N) (omega : InfiniteSample) :
    fullMaskedDyadicCount N L mask (restrictToFinite (dyadicCutoff N L) omega) =
      infiniteMaskedCount L mask omega := by
  classical
  unfold fullMaskedDyadicCount infiniteMaskedCount
  apply Finset.sum_congr rfl
  intro x hx
  have hcut : x + L ≤ dyadicCutoff N L := by
    have hb := Finset.mem_Ico.mp (hmask hx)
    unfold dyadicCutoff
    omega
  have hiff := startAt_restrictToFinite_iff omega hcut
  by_cases hs : StartEvent (infiniteValueBit omega) x L
  · simp [hs,hiff.mpr hs]
  · have hf : ¬startAt (restrictToFinite (dyadicCutoff N L) omega) x L := fun h => hs (hiff.mp h)
    simp [hs,hf]

/-- Every atom of the source masked count is exactly a finite-cylinder preimage. -/
theorem infiniteMaskedCount_event_eq_preimage {N L : ℕ} (mask : Finset ℕ)
    (hmask : mask ⊆ dyadicBlock N) (k : ℕ) :
    {omega | infiniteMaskedCount L mask omega = k} =
      restrictToFinite (dyadicCutoff N L) ⁻¹'
        {sigma | fullMaskedDyadicCount N L mask sigma = k} := by
  ext omega
  simp only [Set.mem_setOf_eq,Set.mem_preimage,fullMaskedDyadicCount_restrict_eq mask hmask]

/-- Source count atoms are measurable for every finite mask in the dyadic block. -/
theorem measurableSet_infiniteMaskedCount_event {N L : ℕ} (mask : Finset ℕ)
    (hmask : mask ⊆ dyadicBlock N) (k : ℕ) :
    MeasurableSet {omega | infiniteMaskedCount L mask omega = k} := by
  rw [infiniteMaskedCount_event_eq_preimage mask hmask k]
  exact (measurable_restrictToFinite _) (Set.toFinite _ |>.measurableSet)

/-- The actual infinite masked count law is precisely the finite law used in the transfer. -/
theorem infiniteMaskedLaw_eq_fullMaskedDyadicStartLaw {N L : ℕ} (mask : Finset ℕ)
    (hmask : mask ⊆ dyadicBlock N) :
    infiniteMaskedLaw L mask = fullMaskedDyadicStartLaw N L mask := by
  classical
  funext k
  unfold infiniteMaskedLaw
  rw [infiniteMaskedCount_event_eq_preimage mask hmask k,
    ← Measure.map_apply (measurable_restrictToFinite (dyadicCutoff N L))
      (Set.toFinite _ |>.measurableSet),
    map_infiniteRademacherMeasure_restrictToFinite,
    finiteRademacherMeasure_event_eq_uniformEventProbability,
    ENNReal.toReal_ofReal]
  · rw [← finiteUniformProbability_eq_uniformEventProbability,
      ← eventProbability_fullUniformPMF_eq]
    unfold fullMaskedDyadicStartLaw finiteNatLaw eventProbability
    apply Finset.sum_congr rfl
    intro omega homega
    by_cases hk : fullMaskedDyadicCount N L mask omega = k <;> simp [hk]
  · apply Rat.cast_nonneg.mpr
    unfold uniformEventProbability
    positivity

/-- Finite event/atom factorization for an arbitrary observable, not only prescribed words. -/
theorem finite_event_atom_probability (M Y : ℕ) (P : SampleSpace M → Prop)
    (sigma : SmallSample M Y) :
    uniformEventProbability (fun omega : SampleSpace M => P omega ∧ restrictSmall M Y omega = sigma) =
      ((Fintype.card (LargeSample M Y) : ℚ) / Fintype.card (SampleSpace M)) *
        finiteUniformProbability (fun eta : LargeSample M Y => P (assemble M Y sigma eta)) := by
  classical
  rw [uniformEventProbability_eq_card,
    ← Fintype.card_congr (completionEventEquiv M Y sigma P)]
  unfold finiteUniformProbability
  rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card]
  have hc : (Fintype.card (LargeSample M Y) : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp

/-- The actual infinite atom ratio equals the uniform large-prime fibre probability. -/
theorem eventProbability_eq_infinite_atom_ratio (M Y : ℕ) (P : SampleSpace M → Prop)
    (sigma : SmallSample M Y) :
    eventProbability (largeUniformPMF M Y) (fun eta => P (assemble M Y sigma eta)) =
      (infiniteRademacherMeasure
        ((restrictToFinite M ⁻¹' {omega | P omega}) ∩ infiniteSmallPrimeAtom M Y sigma)).toReal /
      (infiniteRademacherMeasure (infiniteSmallPrimeAtom M Y sigma)).toReal := by
  classical
  have hinter : (restrictToFinite M ⁻¹' {omega | P omega}) ∩ infiniteSmallPrimeAtom M Y sigma =
      restrictToFinite M ⁻¹' {omega | P omega ∧ restrictSmall M Y omega = sigma} := by
    ext omega
    rfl
  have hc : (0 : ℝ) < (((Fintype.card (LargeSample M Y) : ℚ) / Fintype.card (SampleSpace M) : ℚ) : ℝ) := by
    exact_mod_cast (div_pos
      (show (0 : ℚ) < Fintype.card (LargeSample M Y) by exact_mod_cast Fintype.card_pos)
      (show (0 : ℚ) < Fintype.card (SampleSpace M) by exact_mod_cast Fintype.card_pos))
  have hp : (0 : ℝ) ≤ ((finiteUniformProbability
      (fun eta : LargeSample M Y => P (assemble M Y sigma eta)) : ℚ) : ℝ) := by
    unfold finiteUniformProbability
    positivity
  rw [hinter,← Measure.map_apply (measurable_restrictToFinite M) (Set.toFinite _ |>.measurableSet),
    map_infiniteRademacherMeasure_restrictToFinite,
    finiteRademacherMeasure_event_eq_uniformEventProbability,
    finite_event_atom_probability,infiniteSmallPrimeAtom_measure,
    eventProbability_largeUniformPMF_eq,Rat.cast_mul,
    ENNReal.toReal_ofReal (mul_nonneg hc.le hp),ENNReal.toReal_ofReal hc.le]
  rw [mul_comm,mul_div_cancel_right₀ _ (ne_of_gt hc)]

/-- The complete masked conditional law is a literal positive-atom source conditional law. -/
theorem conditionalMaskedLaw_eq_infinite_atom_ratio {N L Y : ℕ} (mask : Finset ℕ)
    (hmask : mask ⊆ dyadicBlock N)
    (sigma : SmallSample (dyadicCutoff N L) Y) (k : ℕ) :
    conditionalMaskedLaw N L Y mask sigma k =
      (infiniteRademacherMeasure
        ({omega | infiniteMaskedCount L mask omega = k} ∩
          infiniteSmallPrimeAtom (dyadicCutoff N L) Y sigma)).toReal /
        (infiniteRademacherMeasure (infiniteSmallPrimeAtom (dyadicCutoff N L) Y sigma)).toReal := by
  classical
  rw [infiniteMaskedCount_event_eq_preimage mask hmask k]
  have heq : conditionalMaskedLaw N L Y mask sigma k =
      eventProbability (largeUniformPMF (dyadicCutoff N L) Y)
        (fun eta => fullMaskedDyadicCount N L mask (assemble (dyadicCutoff N L) Y sigma eta) = k) := by
    unfold conditionalMaskedLaw finiteNatLaw eventProbability
    apply Finset.sum_congr rfl
    intro eta heta
    by_cases hk : conditionalMaskedCount N L Y mask sigma eta = k <;>
      simp [conditionalMaskedCount] at hk ⊢
  rw [heq]
  exact eventProbability_eq_infinite_atom_ratio (dyadicCutoff N L) Y
    (fun omega => fullMaskedDyadicCount N L mask omega = k) sigma

/-- Theorem 4.1 for the genuine infinite masked count, with the same explicit budget. -/
theorem theorem_four_one_scalar_infinite (hStein : ScalarSteinFactorsStatement)
    {N L Y : ℕ} (mask : Finset ℕ) (hmask : mask ⊆ dyadicBlock N)
    (hN : 2 ≤ N) (hL : 0 < L) (hY : 2 * L ≤ Y) :
    natTotalVariation (infiniteMaskedLaw L mask) (poissonMass (maskedTargetPoissonRate L mask)) ≤
      ((fullDefectMass L mask : ℝ) + 2 * (fullBadMask N L Y mask).card) / (2 : ℝ) ^ L +
        2 * firstSteinFactor (retainedRate N L Y mask) *
          (((mask.card : ℝ) + (maskedSupportEdges L Y mask).card +
            (jointDefectMass N L (separatedPairs mask L) : ℝ)) / (2 : ℝ) ^ (2 * L)) := by
  rw [infiniteMaskedLaw_eq_fullMaskedDyadicStartLaw mask hmask]
  exact theorem_four_one_scalar hStein mask hmask hN hL hY

end
end PaperC.V282.InfiniteMaskedScalarTransfer
