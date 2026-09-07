import PaperCV282.PrefixContainedBounds
import PaperCV282.DyadicPrefixBudget
import PaperC.Probability.PoissonVoidApproximation

/-! # The genuine longest-run void probability and its quantitative error -/
namespace PaperC.V282.PrefixVoidBounds

open MeasureTheory InfiniteRademacher CorollaryPrefixLaw PrefixLongestGeometry
open SectionThirteenFiniteBound ScalarSteinInput PoissonVoidApproximation
open PrefixContainedBounds MesoscopicPrefixMass AllStartSoftPoisson HardPoissonRates
open scoped NNReal
open DyadicPrefixBudget PrimeEulerPNT LaishramUniformInput PostQuadraticLiterature

noncomputable section
local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

/-- The mass at zero is exactly the longest-run void event, including the initial run. -/
theorem prefix_mass_zero_eq_void {M L : ℕ} (hLM : L≤M) :
    infinitePrefixStartLaw M L 0 =
      infiniteRademacherMeasure.real {omega | infinitePrefixLongestConstantStretch M omega<L} := by
  have he : infinitePrefixStartCountEvent M L 0=
      {omega | infinitePrefixLongestConstantStretch M omega<L} := by
    ext omega
    exact infinitePrefixStartCount_eq_zero_iff_longest_lt hLM omega
  rw [infinitePrefixStartLaw,he,measureReal_def]

theorem poisson_mass_zero (rate : ℝ≥0) : poissonMass rate 0=Real.exp (-(rate : ℝ)) := by
  rw [poissonMass_formula]
  simp

/-- All terms of the quantitative void estimate come from proved source comparisons. -/
theorem void_bound_eventually
    (hStein : ScalarSteinFactorsStatement) (hLS : UniformPrimeDivisorStatement)
    (hShorey : ShoreySquareProductStatement) (hPNT : PrimeNumberTheoremRemainder)
    (hNR : PellInput.NicolasRobinDivisorLogBoundStatement)
    (betaMin betaMax epsilon eta : ℝ) (hbetaMin : 0<betaMin)
    (hbeta : betaMin<betaMax) (hepsilon : 0<epsilon) (heta : 0<eta) :
    ∃ Mzero : ℕ, ∀ M≥Mzero, ∀ L : ℕ,
      betaMin*Real.log M≤(L+1 : ℝ) → (L+1 : ℝ)≤betaMax*Real.log M →
      |infiniteRademacherMeasure.real {omega | infinitePrefixLongestConstantStretch M omega<L}-
        Real.exp (-((M : ℝ)/(2 : ℝ)^L))| ≤
        86*hardRate M L epsilon eta+
          9*Real.exp (-(betaMin*Real.log 2/8)*(Real.log M/Real.log (Real.log M)))+
          ((2 : ℝ)⁻¹)^Nat.primeCounting L+2*(L : ℝ)/(2 : ℝ)^L := by
  obtain ⟨Nt,ht⟩ := theorem_seven_four_contained_prefix hStein hLS hShorey hPNT hNR
    betaMin betaMax epsilon eta hbetaMin hbeta hepsilon heta
  obtain ⟨Nb,hb⟩ := border_mass_ambient_scale_eventually betaMin betaMax hbetaMin hbeta hPNT
  obtain ⟨Nc,hc⟩ := logarithmic_containment_eventually betaMin betaMax hbetaMin (hbetaMin.trans hbeta).le
  refine ⟨max Nt (max Nb Nc),?_⟩
  intro M hM L hlo hhi
  have ht' := ht M (by omega) L hlo hhi
  have hb' := hb M (by omega) L (by simpa using hlo) (by simpa using hhi)
  have hLM := (hc M (by omega) L hlo hhi).2
  have hmass := abs_mass_zero_sub_le_two_mul_natTotalVariation
    (p := infinitePrefixStartLaw M L) (q := poissonMass (fullRate M L))
    (by rw [infinitePrefixStartCount_law_eq_prefixStartLaw]; exact summable_finiteNatLaw _ _)
    (hasSum_poissonMass _).summable (fun _ => ENNReal.toReal_nonneg) (poissonMass_nonneg _)
  rw [prefix_mass_zero_eq_void hLM,poisson_mass_zero] at hmass
  have hmin := min_le_right (1 : ℝ) (hardRate M L epsilon eta)
  have he : 2*(L : ℝ)/(2 : ℝ)^L=2*((L : ℝ)/(2 : ℝ)^L) := by ring
  rw [he]
  change |infiniteRademacherMeasure.real _-Real.exp (-(fullRate M L : ℝ))|≤_
  linarith

/-- The explicit budget needed for the literal dyadic envelopes, with numerical constant 100. -/
theorem prefix_budget_bound_eventually
    (hStein : ScalarSteinFactorsStatement) (hLS : UniformPrimeDivisorStatement)
    (hShorey : ShoreySquareProductStatement) (hPNT : PrimeNumberTheoremRemainder)
    (hNR : PellInput.NicolasRobinDivisorLogBoundStatement)
    (betaMin betaMax eta : ℝ) (hbetaMin : 0<betaMin)
    (hbeta : betaMin<betaMax) (heta : 0<eta) :
    ∃ Mzero : ℕ, ∀ M≥Mzero, ∀ L : ℕ,
      betaMin*Real.log M≤(L+1 : ℝ) → (L+1 : ℝ)≤betaMax*Real.log M →
      |infiniteRademacherMeasure.real {omega | infinitePrefixLongestConstantStretch M omega<L}-
        Real.exp (-((M : ℝ)/(2 : ℝ)^L))| ≤
        prefixBudget 100 (betaMin*Real.log 2/8) eta M L := by
  obtain ⟨Mzero,h⟩ := void_bound_eventually hStein hLS hShorey hPNT hNR
    betaMin betaMax (1/12) eta hbetaMin hbeta (by norm_num) heta
  refine ⟨Mzero,?_⟩
  intro M hM L hlo hhi
  apply (h M hM L hlo hhi).trans
  unfold prefixBudget hardRate
  norm_num only [show -(1/3 : ℝ)+1/12= -1/4 by norm_num]
  change 86*(((M : ℝ)/(2 : ℝ)^L)*_)+9*_+_+_≤_
  have hs : (0 : ℝ)≤(M : ℝ)/(2 : ℝ)^L*
      (Real.exp (-SaddleParameters.saddleCutoff 1 (Real.log M)+eta*SaddleScales.saddleNu 1 (Real.log M))+
        (M : ℝ)^(-(1/4 : ℝ))) := by positivity
  have hd := Real.exp_nonneg (-(betaMin*Real.log 2/8)*(Real.log M/Real.log (Real.log M)))
  have hl : (0 : ℝ)≤(L : ℝ)/(2 : ℝ)^L := by positivity
  have hp : (0 : ℝ)≤100/(2 : ℝ)^L*(M : ℝ)^(7/12 : ℝ) := by positivity
  simp only [div_eq_mul_inv] at hs hd hl hp ⊢
  nlinarith only [hs,hd,hl,hp]

end
end PaperC.V282.PrefixVoidBounds
