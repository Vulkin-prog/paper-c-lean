import PaperCV282.PrefixScalarBounds

/-! # The contained prefix count, with its exact boundary contribution -/
namespace PaperC.V282.PrefixContainedBounds

open MeasureTheory InfiniteRademacher InfiniteStartProbabilityTransfer
open ArratiaGoldsteinGordonInput SectionThirteenFiniteBound ScalarSteinInput
open FiniteStartMaskSource InfiniteMaskedScalarTransfer PrefixScalarCouplings PrefixScalarBounds
open TheoremSixteenTwo CorollaryPrefixLaw MesoscopicPrefixMass AllStartSoftPoisson HardPoissonRates
open PrimeEulerPNT LaishramUniformInput PostQuadraticLiterature
open scoped BigOperators

noncomputable section

theorem logarithmic_containment_eventually (betaMin betaMax : ℝ)
    (hbetaMin : 0<betaMin) (hbetaMax : 0≤betaMax) :
    ∃ Mzero : ℕ, ∀ M≥Mzero, ∀ L : ℕ,
      betaMin*Real.log M≤(L+1 : ℝ) → (L+1 : ℝ)≤betaMax*Real.log M → 2≤L ∧ L≤M := by
  obtain ⟨Nl,hl⟩ := MacroscopicShallowSigma.length_ge_eventually_of_logarithmic_lower betaMin hbetaMin 3
  obtain ⟨Nu,hu⟩ := LogarithmicWordPowers.polynomial_factor_le_rpow_eventually betaMax hbetaMax 1 1 1 (by norm_num)
  refine ⟨max Nl Nu,?_⟩
  intro M hM L hlo hhi
  have hl' : (3 : ℝ)≤(L+1 : ℝ) := by simpa using hl M (by omega) L (by simpa using hlo)
  have hu' : (L+1 : ℝ)≤M := by
    simpa only [pow_one,one_mul,abs_of_nonneg (by positivity : (0 : ℝ)≤L+1),Real.rpow_one] using
      hu M (by omega) L (by simpa using hhi)
  constructor
  · have hh : (2 : ℝ)≤L := by linarith
    exact_mod_cast hh
  · have hh : (L : ℝ)≤M := by linarith
    exact_mod_cast hh

/-- A stronger overflow estimate is available once the complete prefix first moment is proved. -/
theorem overflow_mass_eventually
    (hLS : UniformPrimeDivisorStatement) (hShorey : ShoreySquareProductStatement)
    (hPNT : PrimeNumberTheoremRemainder) (hNR : PellInput.NicolasRobinDivisorLogBoundStatement)
    (betaMin betaMax : ℝ) (hbetaMin : 0<betaMin) (hbeta : betaMin<betaMax) :
    ∃ Mzero : ℕ, ∀ M≥Mzero, ∀ L : ℕ,
      betaMin*Real.log M≤(L+1 : ℝ) → (L+1 : ℝ)≤betaMax*Real.log M →
      (∑ x∈prefixOverflowStartIndices M L,infiniteStartProbability x L) ≤
        (L : ℝ)/(2 : ℝ)^L+
          2*Real.exp (-(betaMin*Real.log 2/8)*(Real.log M/Real.log (Real.log M))) := by
  obtain ⟨Np,hp⟩ := masked_prefix_mass_eventually betaMin betaMax hbetaMin hbeta hLS hShorey hPNT hNR
  refine ⟨Np,?_⟩
  intro M hM L hlo hhi
  have h := hp M hM L (by simpa using hlo) (by simpa using hhi) (prefixOverflowStartIndices M L) (by
    intro x hx
    have hh := Finset.mem_Ico.mp hx
    exact ⟨by omega,by omega⟩)
  apply h.trans
  apply add_le_add _ le_rfl
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast prefixOverflowStartIndices_card_le M L

/-- Theorem 7.4 for W: the exact border is explicit and the overflow remainder is smaller
than the displayed expression (7.11), after changing the deep-error constant. -/
theorem theorem_seven_four_contained_prefix
    (hStein : ScalarSteinFactorsStatement) (hLS : UniformPrimeDivisorStatement)
    (hShorey : ShoreySquareProductStatement) (hPNT : PrimeNumberTheoremRemainder)
    (hNR : PellInput.NicolasRobinDivisorLogBoundStatement)
    (betaMin betaMax epsilon eta : ℝ) (hbetaMin : 0<betaMin)
    (hbeta : betaMin<betaMax) (hepsilon : 0<epsilon) (heta : 0<eta) :
    ∃ Mzero : ℕ, ∀ M≥Mzero, ∀ L : ℕ,
      betaMin*Real.log M≤(L+1 : ℝ) → (L+1 : ℝ)≤betaMax*Real.log M →
      natTotalVariation (infinitePrefixStartLaw M L) (poissonMass (fullRate M L)) ≤
        43*min 1 (hardRate M L epsilon eta) +
          4*Real.exp (-(betaMin*Real.log 2/8)*(Real.log M/Real.log (Real.log M))) +
          ((2 : ℝ)⁻¹)^Nat.primeCounting L+(L : ℝ)/(2 : ℝ)^L := by
  obtain ⟨Ng,hg⟩ := theorem_seven_four_open_prefix hStein hLS hShorey hPNT hNR
    betaMin betaMax epsilon eta hbetaMin hbeta hepsilon heta
  obtain ⟨No,ho⟩ := overflow_mass_eventually hLS hShorey hPNT hNR betaMin betaMax hbetaMin hbeta
  obtain ⟨Nc,hc⟩ := logarithmic_containment_eventually betaMin betaMax hbetaMin (hbetaMin.trans hbeta).le
  refine ⟨max Ng (max No Nc),?_⟩
  intro M hM L hlo hhi
  obtain ⟨hL,hLM⟩ := hc M (by omega) L hlo hhi
  have hcouple := source_prefix_global_tv_le hL hLM
  have hglobal := hg M (by omega) L hlo hhi
  have hoverflow := ho M (by omega) L hlo hhi
  have htri := natTotalVariation_triangle
    (p := infinitePrefixStartLaw M L) (q := infiniteMaskedLaw L (Finset.Ico 2 M))
    (r := poissonMass (fullRate M L))
    (by rw [infinitePrefixStartCount_law_eq_prefixStartLaw]; exact summable_finiteNatLaw _ _)
    (summable_infiniteMaskedLaw _ _) (hasSum_poissonMass _).summable
    (fun _ => ENNReal.toReal_nonneg) (infiniteMaskedLaw_nonneg _ _) (poissonMass_nonneg _)
  linarith

end
end PaperC.V282.PrefixContainedBounds
