import PaperCV282.FiniteStartMaskTransfer
import PaperCV282.InfiniteMaskedScalarTransfer

/-! # Arbitrary finite start populations in the infinite source probability space -/
namespace PaperC.V282.FiniteStartMaskSource

open MeasureTheory Set InfiniteRademacher InfiniteCylinderTransfer InfiniteStartProbabilityTransfer
open InfiniteExactLengthProbabilityTransfer
open Affine ArratiaGoldsteinGordonInput SectionThirteenFiniteBound ScalarSteinInput
open FiniteStartMaskModel FiniteStartMaskAverages FiniteStartMaskTransfer InfiniteMaskedScalarTransfer
open MacroscopicMaskGeometry MaskedArithmeticGeometry MaskedPairGeometry HostRankMass TwoWindowParity
open scoped BigOperators NNReal ENNReal

noncomputable section
local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

theorem finiteStartCount_restrict_eq {C L : ℕ} (mask : Finset ℕ)
    (hcut : ∀ x∈mask,x+L≤C) (omega : InfiniteSample) :
    finiteStartCount C L mask (restrictToFinite C omega)=infiniteMaskedCount L mask omega := by
  unfold finiteStartCount infiniteMaskedCount
  apply Finset.sum_congr rfl
  intro x hx
  have hiff := startAt_restrictToFinite_iff omega (hcut x hx)
  by_cases hs : StartEvent (infiniteValueBit omega) x L
  · simp [hs,hiff.mpr hs]
  · have hf : ¬startAt (restrictToFinite C omega) x L := fun h => hs (hiff.mp h)
    simp [hs,hf]

theorem count_event_eq_preimage {C L : ℕ} (mask : Finset ℕ)
    (hcut : ∀ x∈mask,x+L≤C) (k : ℕ) :
    {omega | infiniteMaskedCount L mask omega=k} =
      restrictToFinite C ⁻¹' {sigma | finiteStartCount C L mask sigma=k} := by
  ext omega
  simp only [Set.mem_setOf_eq,Set.mem_preimage,finiteStartCount_restrict_eq mask hcut]

theorem measurableSet_count_event {C L : ℕ} (mask : Finset ℕ)
    (hcut : ∀ x∈mask,x+L≤C) (k : ℕ) :
    MeasurableSet {omega | infiniteMaskedCount L mask omega=k} := by
  rw [count_event_eq_preimage mask hcut k]
  exact (measurable_restrictToFinite _) (Set.toFinite _ |>.measurableSet)

theorem infiniteMaskedLaw_eq_finiteLaw {C L : ℕ} (mask : Finset ℕ)
    (hcut : ∀ x∈mask,x+L≤C) : infiniteMaskedLaw L mask=finiteLaw C L mask := by
  funext k
  rw [infiniteMaskedLaw,count_event_eq_preimage mask hcut k,
    ← Measure.map_apply (measurable_restrictToFinite C) (Set.toFinite _ |>.measurableSet),
    map_infiniteRademacherMeasure_restrictToFinite,
    finiteRademacherMeasure_event_eq_uniformEventProbability,ENNReal.toReal_ofReal]
  · exact (finiteLaw_apply C L mask k).symm
  · apply Rat.cast_nonneg.mpr
    unfold uniformEventProbability
    positivity

theorem summable_infiniteMaskedLaw (L : ℕ) (mask : Finset ℕ) : Summable (infiniteMaskedLaw L mask) := by
  rw [infiniteMaskedLaw_eq_finiteLaw mask (C := mask.sup id+L)
    (by intro x hx; exact Nat.add_le_add_right (Finset.le_sup (f := id) hx) L)]
  exact summable_finiteNatLaw _ _

theorem hasSum_infiniteMaskedLaw (L : ℕ) (mask : Finset ℕ) : HasSum (infiniteMaskedLaw L mask) 1 := by
  rw [infiniteMaskedLaw_eq_finiteLaw mask (C := mask.sup id+L)
    (by intro x hx; exact Nat.add_le_add_right (Finset.le_sup (f := id) hx) L)]
  exact hasSum_finiteNatLaw _ _

theorem infiniteMaskedLaw_nonneg (L : ℕ) (mask : Finset ℕ) (k : ℕ) :
    0 ≤ infiniteMaskedLaw L mask k := ENNReal.toReal_nonneg

theorem source_scalar_tv_le (hStein : ScalarSteinFactorsStatement) {C L Y : ℕ}
    (mask : Finset ℕ) (hL : 0<L) (hY : 2*L≤Y)
    (hpos : ∀ x∈mask,2≤x) (hcut : ∀ x∈mask,x+L≤C) :
    natTotalVariation (infiniteMaskedLaw L mask) (poissonMass (maskRate L mask)) ≤
      ((fullDefectMass L mask : ℝ)+2*(badMask L Y mask).card)/(2 : ℝ)^L +
      2*firstSteinFactor (maskRate L (goodMask L Y mask))*
        (((mask.card : ℝ)+(maskedSupportEdges L Y mask).card+
          (relationWeightMass C L (separatedPairs mask L) : ℝ))/(2 : ℝ)^(2*L)) := by
  rw [infiniteMaskedLaw_eq_finiteLaw mask hcut]
  exact finite_scalar_tv_le hStein mask hL hY hpos hcut

end
end PaperC.V282.FiniteStartMaskSource
