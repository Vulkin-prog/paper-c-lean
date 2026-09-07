import PaperCV282.FinitePrimeEnvironment
import PaperCV282.HardPoissonRates
import PaperCV282.QuenchedSaddleBudget

/-! # The actual scalar conditional mean, including intensities below one -/
namespace PaperC.V282.MeanScalarBudget

open MeasureTheory Filter Topology InfiniteRademacher InfiniteCylinderTransfer InfiniteConditionalWords
open FinitePrimeEnvironment CountablePrimeEventTransfer ConditionedCountableLaw
open DyadicPoissonDistance InfiniteMaskedScalarTransfer AllStartSoftPoisson
open SectionThirteenFiniteBound ConditionalAGGAverage HardPoissonRates
open SectionThirteenCouplings
open ConditionalStartProbability
open QuenchedSaddleBudget LabelledInformationBudget SaddleParameters SaddleScales SaddleCutoffAdmissibility
open ScalarSteinInput PrimeEulerPNT

noncomputable section

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤
local instance instProbabilityInfiniteRademacher : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

/-- Exact agreement with the source-atom ratios of the scalar theorem. -/
theorem mean_scalar_eq (N L Y : ℕ) :
    meanAtomDistance (dyadicCutoff N L) Y (infiniteMaskedCount L (dyadicBlock N))
      (poissonMass (fullRate N L)) = conditionalDistance N L Y := by
  rw [conditionalDistance_eq_source_atom_average]
  unfold meanAtomDistance
  apply congrArg (fun f : SmallSample (dyadicCutoff N L) Y → ℝ => finiteUniformAverage f)
  funext sigma
  have he : conditionalObservableLaw infiniteRademacherMeasure
      (infiniteSmallPrimeAtom (dyadicCutoff N L) Y sigma) (infiniteMaskedCount L (dyadicBlock N)) =
      (fun k => (infiniteRademacherMeasure
        ({omega | infiniteMaskedCount L (dyadicBlock N) omega=k} ∩
          infiniteSmallPrimeAtom (dyadicCutoff N L) Y sigma)).toReal /
        (infiniteRademacherMeasure (infiniteSmallPrimeAtom (dyadicCutoff N L) Y sigma)).toReal) := by
    funext k
    exact conditionalObservableLaw_eq_ratio _ _
      (measurableSet_infiniteSmallPrimeAtom (dyadicCutoff N L) Y sigma) _ k
  rw [he]
  rfl

/-- Uniform decay under the one-intensity budget, without a lower bound on the intensity. -/
theorem mean_scalar_hard_rate (hStein : ScalarSteinFactorsStatement)
    (hPNT : PrimeNumberTheoremRemainder) (betaMin betaMax c c' : ℝ)
    (hbetaMin : 0<betaMin) (hbeta : betaMin<betaMax) (hc' : 0<c') (hcc : c'<c) :
    ∃ Nzero : ℕ, ∀ N≥Nzero, ∀ L : ℕ,
      betaMin*Real.log N≤(L+1 : ℝ) → (L+1 : ℝ)≤betaMax*Real.log N →
      max 0 (Real.log (fullRate N L))≤
        saddleCutoff 1 (Real.log N)-c*saddleNu 1 (Real.log N) →
      meanAtomDistance (hardCutoff N) (hardCutoff N)
        (infiniteMaskedCount L (dyadicBlock N)) (poissonMass (fullRate N L)) ≤
          40*Real.exp (-c'*saddleNu 1 (Real.log N)) := by
  obtain ⟨Nr,hr⟩ := hard_conditional_rate_eventually hStein hPNT betaMin betaMax (1/6) (c-c')
    hbetaMin hbeta (by norm_num) (by linarith)
  obtain ⟨Np,hp⟩ := hard_polynomial_factor_eventually
  obtain ⟨Nt,ht⟩ := eventually_atTop.1 (remainders_le_margin c' (1/12) hc' (by norm_num))
  have hl : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨Ns,hs⟩ := eventually_atTop.1 (hl.eventually (eventually_ge_atTop (saddleThreshold 1)))
  refine ⟨max Nr (max Np (max Nt (max Ns 2))),?_⟩
  intro N hN L hlo hhi hbu
  obtain ⟨hY,hd⟩ := hr N (by omega) L hlo hhi
  rw [← meanAtomDistance_eq_canonical hY,mean_scalar_eq]
  have hv := saddleCutoff_pos (a := 1) (by norm_num) (hs N (by omega))
  have hNp : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hn : 0≤saddleNu 1 (Real.log N) := by
    unfold saddleNu
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast (show 1≤N by omega))) hv.le
  have hrate : 0<(fullRate N L : ℝ) := by
    change 0 < (N : ℝ)/2^L
    exact div_pos hNp (by positivity)
  have hlograte := (le_max_right 0 (Real.log (fullRate N L))).trans hbu
  have he : (fullRate N L : ℝ)≤Real.exp (saddleCutoff 1 (Real.log N)-c*saddleNu 1 (Real.log N)) := by
    rw [← Real.exp_log hrate]
    exact Real.exp_le_exp.mpr hlograte
  have heV : (fullRate N L : ℝ)≤Real.exp (saddleCutoff 1 (Real.log N)) :=
    he.trans (Real.exp_le_exp.mpr (by nlinarith [mul_nonneg (hc'.trans hcc).le hn]))
  have hfirst : (fullRate N L : ℝ)*
      Real.exp (-saddleCutoff 1 (Real.log N)+(c-c')*saddleNu 1 (Real.log N)) ≤
        Real.exp (-c'*saddleNu 1 (Real.log N)) := by
    apply (mul_le_mul_of_nonneg_right he (Real.exp_nonneg _)).trans
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    ring_nf
    exact le_rfl
  have hpoly := (mul_le_mul_of_nonneg_right heV
    (Real.rpow_nonneg hNp.le (-(1/(6 : ℝ))))).trans (hp N (by omega))
  have hpoly' := hpoly.trans (ht N (by omega)).2
  unfold hardRate at hd
  norm_num only [show -(1/(3 : ℝ))+1/6= -(1/(6 : ℝ)) by norm_num] at hd
  nlinarith

end
end PaperC.V282.MeanScalarBudget
