import PaperCV282.MacroTransportHardRetained
import PaperCV282.MacroTransportRestoration
import PaperCV282.PrefixScalarGeometry

/-! # Complete contained macroscopic fields at the hard cutoff

The restored low starts are actual source events, including the microscopic
region. Their conditional cost keeps the exact inverse probability of A.
-/
namespace PaperC.V282.MacroTransportHardComparison

open MeasureTheory ProbabilityTheory Filter Topology InfiniteRademacher InfiniteCylinderTransfer
open MacroTransportModel MacroTransportHardRetained MacroTransportRestoration BulkMarkedGeometry
open BulkMarkedSource BulkMarkedTarget MesoscopicPrefixMass FiniteStartMaskAverages
open HardPoissonRates SaddleParameters SaddleScales PrimeEulerPNT ProcessAGGInput AllStartSoftPoisson
open InfiniteStartProbabilityTransfer
open LaishramUniformInput PostQuadraticLiterature SharpConditioning InfiniteConditionalWords
open scoped BigOperators NNReal ENNReal

noncomputable section
local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤
local instance instProbabilityInfinite : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

theorem removed_contained_subset_prefix (M L : ℕ) (delta : ℝ) :
    containedStarts M L\bulkStarts M L delta⊆realPrefix M delta := by
  intro x hx
  obtain ⟨ht,hnot⟩ := Finset.mem_sdiff.mp hx
  obtain ⟨hxlo,hxhi⟩ := mem_containedStarts.mp ht
  apply mem_realPrefix.mpr
  refine ⟨hxlo,?_⟩
  by_contra hr
  apply hnot
  exact (mem_bulkStarts M L x delta).mpr ⟨Nat.ceil_le.mpr (le_of_not_gt hr),hxhi⟩

theorem removed_contained_rate_le (M L : ℕ) (delta : ℝ) :
    (maskRate L (containedStarts M L\bulkStarts M L delta) : ℝ)≤(M : ℝ)^delta/(2 : ℝ)^L := by
  have hc : ((containedStarts M L\bulkStarts M L delta).card : ℝ)≤(M : ℝ)^delta :=
    (show ((containedStarts M L\bulkStarts M L delta).card : ℝ)≤(realPrefix M delta).card from
      by exact_mod_cast Finset.card_le_card (removed_contained_subset_prefix M L delta)).trans
      (card_realPrefix_le M delta)
  exact div_le_div_of_nonneg_right hc (by positivity)

/-- A true all-marks, all-signs comparison on the base-contained interval, uniform before A. -/
theorem contained_event_hard_bound_eventually
    (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (hLS : UniformPrimeDivisorStatement) (hShorey : ShoreySquareProductStatement)
    (hNR : PellInput.NicolasRobinDivisorLogBoundStatement)
    (betaMin betaMax epsilon eta : ℝ) (hbetaMin : 0<betaMin) (hbeta : betaMin<betaMax)
    (hepsilon : 0<epsilon) (heta : 0<eta) :
    ∃ Mzero : ℕ, ∀ M≥Mzero, ∀ L : ℕ,
      betaMin*Real.log M≤(L+1 : ℝ) → (L+1 : ℝ)≤betaMax*Real.log M →
      ∀ A : Set InfiniteSample,
      MeasurableSet[MeasurableSpace.comap (restrictToFinite (hardCutoff M)) inferInstance] A →
      0 < infiniteRademacherMeasure.real A →
      conditionalDistance M L A ≤
      (37*(fullRate M L : ℝ)*(1+(fullRate M L : ℝ))*
        (Real.exp (-saddleCutoff 1 (Real.log M)+eta*saddleNu 1 (Real.log M)) +
          (M : ℝ)^(-(1/(3 : ℝ))+epsilon)) +
        2*Real.exp (-(betaMin*Real.log 2/8)*(Real.log M/Real.log (Real.log M))))/
          infiniteRademacherMeasure.real A := by
  obtain ⟨Nr,hr⟩ := retained_event_hard_bound_eventually hAGG hPNT betaMin betaMax (1/2) epsilon eta
    hbetaMin hbeta (by norm_num) hepsilon heta
  obtain ⟨Np,hp⟩ := equation_seven_seven betaMin betaMax hbetaMin hbeta hLS hShorey hPNT hNR
  refine ⟨max 2 (max Nr Np),?_⟩
  intro M hM L hlo hhi A hA hpos
  have hAm : MeasurableSet A := by
    have hm := hA
    rw [← smallPrimeSigmaAlgebra_eq_primeCylinder (le_refl (hardCutoff M))] at hm
    exact smallPrimeSigmaAlgebra_le _ _ A hm
  have hrest := conditional_restoration_le (bulkStarts_subset_contained (M := M) (L := L)
    (by omega) (by norm_num : (0 : ℝ)<1/2)) L A hAm hpos
  have hret := hr M (by omega) L hlo hhi A hA hpos
  have hpre := hp M (by omega) L (by simpa using hlo) (by simpa using hhi) (1/2) (by norm_num) (by norm_num)
  have hsum : (∑ x∈containedStarts M L\bulkStarts M L (1/2), infiniteStartProbability x L)≤
      (M : ℝ)^(1/2 : ℝ)/(2 : ℝ)^L +
        2*Real.exp (-(betaMin*Real.log 2/8)*(Real.log M/Real.log (Real.log M))) := by
    exact (Finset.sum_le_sum_of_subset_of_nonneg (removed_contained_subset_prefix M L (1/2))
      (fun x _ _ => ENNReal.toReal_nonneg)).trans hpre
  have htar := removed_contained_rate_le M L (1/2)
  have hprob : infiniteRademacherMeasure.real A≤1 := by
    have hh := measureReal_mono (μ := infiniteRademacherMeasure) (Set.subset_univ A)
    simpa only [probReal_univ] using hh
  have hsquare := PrefixScalarGeometry.squareRoot_restoration_le (L := L) (by omega : 1≤M) hepsilon.le
  have hpoly : (fullRate M L : ℝ)*(M : ℝ)^(-(1/(3 : ℝ))+epsilon)≤
      (fullRate M L : ℝ)*(1+(fullRate M L : ℝ))*
        (Real.exp (-saddleCutoff 1 (Real.log M)+eta*saddleNu 1 (Real.log M))+
          (M : ℝ)^(-(1/(3 : ℝ))+epsilon)) := by
    apply mul_le_mul
    · nlinarith [show (0 : ℝ)≤(fullRate M L : ℝ) by positivity]
    · exact le_add_of_nonneg_left (Real.exp_nonneg _)
    · positivity
    · positivity
  have hsmall := hsquare.trans hpoly
  have htar' : (maskRate L (containedStarts M L\bulkStarts M L (1/2)) : ℝ)≤
      ((M : ℝ)^(1/2 : ℝ)/(2 : ℝ)^L)/infiniteRademacherMeasure.real A := by
    apply htar.trans
    apply (le_div_iff₀ hpos).mpr
    exact mul_le_of_le_one_right (by positivity) hprob
  have hsum' := div_le_div_of_nonneg_right hsum hpos.le
  have hsmall' := div_le_div_of_nonneg_right hsmall hpos.le
  change conditionalDistance M L A≤_ at hrest
  apply (le_div_iff₀ hpos).mpr
  have hh := mul_le_mul_of_nonneg_right hrest hpos.le
  have hrp := (le_div_iff₀ hpos).mp hret
  have htp := (le_div_iff₀ hpos).mp htar'
  simp only [add_mul,div_mul_cancel₀ _ hpos.ne'] at hh
  nlinarith only [hh,hrp,htp,hsum,hsmall]

end
end PaperC.V282.MacroTransportHardComparison
