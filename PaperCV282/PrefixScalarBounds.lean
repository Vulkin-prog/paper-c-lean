import PaperCV282.PrefixScalarGeometry
import PaperCV282.MacroscopicScalarLedger

/-! # Quantitative Poisson comparison for the complete open prefix

The retained population is exactly [ceil(sqrt M),M). The discarded starts
are restored using Proposition 7.3, and the target is exactly M*2^(-L).
-/
namespace PaperC.V282.PrefixScalarBounds

open Affine ArratiaGoldsteinGordonInput SectionThirteenFiniteBound ScalarSteinInput
open FiniteStartMaskModel FiniteStartMaskAverages FiniteStartMaskSource InfiniteMaskedScalarTransfer
open PrefixScalarCouplings PrefixScalarGeometry MacroscopicGeometry MacroscopicRetentionBounds
open MacroscopicScalarLedger MesoscopicPrefixMass AllStartSoftPoisson HardPoissonRates
open InfiniteStartProbabilityTransfer PrimeEulerPNT LaishramUniformInput PostQuadraticLiterature
open scoped BigOperators

noncomputable section

/-- The true source comparison on the retained square-root population. -/
theorem macroscopic_source_hard_rate_eventually
    (hStein : ScalarSteinFactorsStatement) (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax epsilon eta : ℝ) (hbetaMin : 0<betaMin)
    (hbeta : betaMin<betaMax) (hepsilon : 0<epsilon) (heta : 0<eta) :
    ∃ Mzero : ℕ, ∀ M≥Mzero, ∀ L : ℕ,
      betaMin*Real.log M≤(L+1 : ℝ) → (L+1 : ℝ)≤betaMax*Real.log M →
      natTotalVariation (infiniteMaskedLaw L (macroscopicStarts M (1/2)))
        (poissonMass (maskRate L (macroscopicStarts M (1/2)))) ≤ 40*hardRate M L epsilon eta := by
  obtain ⟨Nb,hb⟩ := finite_scalar_hard_rate_eventually hStein hPNT
    betaMin betaMax (1/2) epsilon eta hbetaMin hbeta (by norm_num) hepsilon heta
  obtain ⟨Nc,hc⟩ := card_macroscopicStarts_ge_half_eventually (1/2) (by norm_num)
  refine ⟨max Nb Nc,?_⟩
  intro M hM L hlo hhi
  rw [infiniteMaskedLaw_eq_finiteLaw (macroscopicStarts M (1/2)) (C := M+L) (by
    intro x hx
    have hh := (mem_macroscopicStarts _ _ _).mp hx
    omega)]
  exact hb M (by omega) L hlo hhi (M+L) (le_refl _) _
    (macro_subset_closed M (1/2)) (hc M (by omega))

/-- Equation 7.10 before the harmless truncation at one; the constants are numerical. -/
theorem global_source_hard_rate_eventually
    (hStein : ScalarSteinFactorsStatement) (hLS : UniformPrimeDivisorStatement)
    (hShorey : ShoreySquareProductStatement) (hPNT : PrimeNumberTheoremRemainder)
    (hNR : PellInput.NicolasRobinDivisorLogBoundStatement)
    (betaMin betaMax epsilon eta : ℝ) (hbetaMin : 0<betaMin)
    (hbeta : betaMin<betaMax) (hepsilon : 0<epsilon) (heta : 0<eta) :
    ∃ Mzero : ℕ, ∀ M≥Mzero, ∀ L : ℕ,
      betaMin*Real.log M≤(L+1 : ℝ) → (L+1 : ℝ)≤betaMax*Real.log M →
      natTotalVariation (infiniteMaskedLaw L (Finset.Ico 2 M)) (poissonMass (fullRate M L)) ≤
        43*hardRate M L epsilon eta +
          2*Real.exp (-(betaMin*Real.log 2/8)*(Real.log M/Real.log (Real.log M))) := by
  obtain ⟨Nm,hm⟩ := macroscopic_source_hard_rate_eventually hStein hPNT
    betaMin betaMax epsilon eta hbetaMin hbeta hepsilon heta
  obtain ⟨Np,hp⟩ := MesoscopicPrefixMass.equation_seven_seven betaMin betaMax
    hbetaMin hbeta hLS hShorey hPNT hNR
  refine ⟨max 2 (max Nm Np),?_⟩
  intro M hM L hlo hhi
  have hmacro := hm M (by omega) L hlo hhi
  have hrestore := source_subset_tv_le (L := L) (macro_subset_global (M := M) (delta := 1/2) (by omega) (by norm_num))
  have hlow := hp M (by omega) L (by simpa using hlo) (by simpa using hhi) (1/2) (by norm_num) (by norm_num)
  have hsum : (∑ x∈Finset.Ico 2 M\macroscopicStarts M (1/2),infiniteStartProbability x L) ≤
      ∑ x∈realPrefix M (1/2),infiniteStartProbability x L :=
    Finset.sum_le_sum_of_subset_of_nonneg (removed_global_subset_realPrefix M (1/2))
      (fun x _ _ => ENNReal.toReal_nonneg)
  have hshift := macro_full_poisson_tv_le (M := M) (L := L) (delta := 1/2) (by omega) (by norm_num) (by norm_num)
  have hfirst := natTotalVariation_triangle
    (p := infiniteMaskedLaw L (Finset.Ico 2 M)) (q := infiniteMaskedLaw L (macroscopicStarts M (1/2)))
    (r := poissonMass (fullRate M L))
    (summable_infiniteMaskedLaw _ _) (summable_infiniteMaskedLaw _ _) (hasSum_poissonMass _).summable
    (infiniteMaskedLaw_nonneg _ _) (infiniteMaskedLaw_nonneg _ _) (poissonMass_nonneg _)
  have hsecond := natTotalVariation_triangle
    (p := infiniteMaskedLaw L (macroscopicStarts M (1/2)))
    (q := poissonMass (maskRate L (macroscopicStarts M (1/2)))) (r := poissonMass (fullRate M L))
    (summable_infiniteMaskedLaw _ _) (hasSum_poissonMass _).summable (hasSum_poissonMass _).summable
    (infiniteMaskedLaw_nonneg _ _) (poissonMass_nonneg _) (poissonMass_nonneg _)
  have hsqrt := squareRoot_restoration_le (M := M) (L := L) (by omega) hepsilon.le
  have hpoly : (fullRate M L : ℝ)*(M : ℝ)^(-(1/3 : ℝ)+epsilon) ≤ hardRate M L epsilon eta := by
    unfold hardRate
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (Real.exp_nonneg _)) (by positivity)
  have hlowbound := hrestore.trans (hsum.trans hlow)
  have hreal : 2*(M : ℝ)^(1/2 : ℝ)/(2 : ℝ)^L = 2*((M : ℝ)^(1/2 : ℝ)/(2 : ℝ)^L) := by ring
  rw [hreal] at hshift
  linarith

/-- Equation 7.10 with its literal minimum and the additive microscopic remainder. -/
theorem theorem_seven_four_open_prefix
    (hStein : ScalarSteinFactorsStatement) (hLS : UniformPrimeDivisorStatement)
    (hShorey : ShoreySquareProductStatement) (hPNT : PrimeNumberTheoremRemainder)
    (hNR : PellInput.NicolasRobinDivisorLogBoundStatement)
    (betaMin betaMax epsilon eta : ℝ) (hbetaMin : 0<betaMin)
    (hbeta : betaMin<betaMax) (hepsilon : 0<epsilon) (heta : 0<eta) :
    ∃ Mzero : ℕ, ∀ M≥Mzero, ∀ L : ℕ,
      betaMin*Real.log M≤(L+1 : ℝ) → (L+1 : ℝ)≤betaMax*Real.log M →
      natTotalVariation (infiniteMaskedLaw L (Finset.Ico 2 M)) (poissonMass (fullRate M L)) ≤
        43*min 1 (hardRate M L epsilon eta) +
          2*Real.exp (-(betaMin*Real.log 2/8)*(Real.log M/Real.log (Real.log M))) := by
  obtain ⟨Mzero,h⟩ := global_source_hard_rate_eventually hStein hLS hShorey hPNT hNR
    betaMin betaMax epsilon eta hbetaMin hbeta hepsilon heta
  refine ⟨Mzero,?_⟩
  intro M hM L hlo hhi
  by_cases hr : hardRate M L epsilon eta≤1
  · rw [min_eq_right hr]
    exact h M hM L hlo hhi
  · rw [min_eq_left (by linarith)]
    have hone : natTotalVariation (infiniteMaskedLaw L (Finset.Ico 2 M)) (poissonMass (fullRate M L))≤1 :=
      FiniteFieldTotalVariation.massTotalVariation_le_one
        (hasSum_infiniteMaskedLaw _ _) (hasSum_poissonMass _)
        (infiniteMaskedLaw_nonneg _ _) (poissonMass_nonneg _)
    have he := Real.exp_nonneg (-(betaMin*Real.log 2/8)*(Real.log M/Real.log (Real.log M)))
    linarith

end
end PaperC.V282.PrefixScalarBounds
