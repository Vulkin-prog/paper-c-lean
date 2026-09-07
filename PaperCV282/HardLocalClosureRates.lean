import PaperCV282.HardLocalClosureBudget
import PaperCV282.SoftLocalClosureRates
import PaperCV282.SmallIntensityConditioning

/-! # Actual local relative probabilities under the hard D.1 budget -/
namespace PaperC.V282.HardLocalClosureRates

open MeasureTheory ProbabilityTheory Filter Topology Real
open InfiniteRademacher InfiniteCylinderTransfer InfiniteConditionalWords
open RestrictedPoissonTransfer RareConditioningRates HardPoissonRates
open AllStartSoftPoisson ScalarSteinInput PrimeEulerPNT SaddleParameters SaddleScales
open ArratiaGoldsteinGordonInput SectionThirteenFiniteBound
open HardLocalClosureBudget SoftLocalClosureRates PoissonResolutionBudget SmallIntensityConditioning
open SharpConditioning PoissonRareProbabilities PoissonGaussianSource InfiniteMassCoupling ConditionedCountableLaw

noncomputable section

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤
local instance instProbabilityInfiniteRademacher : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

theorem hard_local_relative_bound_eventually
    (hStein : ScalarSteinFactorsStatement) (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax c : ℝ) (hbetaMin : 0<betaMin) (hbeta : betaMin<betaMax) (hc : 0<c) :
    ∃ Nzero : ℕ, ∀ N≥Nzero, ∀ L : ℕ,
      betaMin*log N≤(L+1 : ℝ) → (L+1 : ℝ)≤betaMax*log N →
      ∀ C : Set InfiniteSample,
      MeasurableSet[MeasurableSpace.comap (restrictToFinite (hardCutoff N)) inferInstance] C →
      0 < infiniteRademacherMeasure.real C → ∀ n : ℕ, 0<n →
      hardLocalCost (eventInformation C) (fullRate N L) n ≤
        saddleCutoff 1 (log N)-c*saddleNu 1 (log N) →
      natTotalVariation (restrictedCountLaw N L C) (poissonMass (fullRate N L)) /
        (poissonMeasure (fullRate N L)).real {n} ≤ hardLocalRemainder N c := by
  obtain ⟨Nr,hr⟩ := hard_event_rate_eventually hStein hPNT
    betaMin betaMax (1/12) (c/2) hbetaMin hbeta (by norm_num) (by linarith)
  obtain ⟨Np,hp⟩ := eventually_atTop.1 (hard_polynomial_div_atom_eventually c hc.le)
  refine ⟨max Nr (max Np 2),?_⟩
  intro N hN L hlo hhi C hC hpos n hn hb
  have hrate : 0<(fullRate N L : ℝ) := by
    rw [fullRate_coe]
    have hnpos : 0<N := by omega
    positivity
  have hatom : 0<exp (-(fullRate N L : ℝ))*(fullRate N L : ℝ)^n/n.factorial := by positivity
  have hlead := hard_leading_div_atom_le (eta := c/2) hrate hn hb
  have hpoly := hp N (by omega) (eventInformation C) (fullRate N L) n hrate hn hb
  have hraw := hr N (by omega) L hlo hhi C hC hpos
  have hmin : (20 : ℝ)*min 1 (hardRate N L (1/12) (c/2))≤20*hardRate N L (1/12) (c/2) :=
    mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num)
  have hraw' := hraw.trans (div_le_div_of_nonneg_right hmin hpos.le)
  have hraw'' := div_le_div_of_nonneg_right hraw' hatom.le
  simp only [div_eq_mul_inv] at hraw''
  rw [← exp_eventInformation C hpos] at hraw''
  rw [poissonMeasure_real_singleton]
  unfold hardLocalRemainder
  have heq : c-c/2=c/2 := by ring
  rw [heq] at hlead
  apply hraw''.trans
  unfold hardRate
  convert (mul_le_mul_of_nonneg_left (add_le_add hlead hpoly) (by norm_num : (0 : ℝ)≤20)) using 1
  ring_nf

/-- D.1 local hard, for arbitrary moving positive observations and source events. -/
theorem hard_local_ratio_tendsto_one
    (hStein : ScalarSteinFactorsStatement) (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax c : ℝ) (hbetaMin : 0<betaMin) (hbeta : betaMin<betaMax) (hc : 0<c)
    (sizes lengths counts : ℕ→ℕ) (C : ℕ→Set InfiniteSample)
    (hsizes : Tendsto sizes atTop atTop)
    (hadmissible : ∀ᶠ k in atTop,
      betaMin*log (sizes k)≤(lengths k+1 : ℝ) ∧
      (lengths k+1 : ℝ)≤betaMax*log (sizes k) ∧
      MeasurableSet[MeasurableSpace.comap (restrictToFinite (hardCutoff (sizes k))) inferInstance] (C k) ∧
      0 < infiniteRademacherMeasure.real (C k) ∧ 0<counts k ∧
      hardLocalCost (eventInformation (C k)) (fullRate (sizes k) (lengths k)) (counts k) ≤
        saddleCutoff 1 (log (sizes k))-c*saddleNu 1 (log (sizes k))) :
    Tendsto (fun k => restrictedCountLaw (sizes k) (lengths k) (C k) (counts k) /
      (poissonMeasure (fullRate (sizes k) (lengths k))).real {counts k}) atTop (𝓝 1) := by
  obtain ⟨Nzero,hzero⟩ := hard_local_relative_bound_eventually
    hStein hPNT betaMin betaMax c hbetaMin hbeta hc
  have habs : Tendsto (fun k => |restrictedCountLaw (sizes k) (lengths k) (C k) (counts k) /
      (poissonMeasure (fullRate (sizes k) (lengths k))).real {counts k}-1|) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) _
      ((hardLocalRemainder_tendsto_zero hc).comp hsizes)
    filter_upwards [hsizes.eventually (eventually_ge_atTop (max Nzero 2)),hadmissible]
      with k hk ha
    have hCm : MeasurableSet (C k) := by
      have hm := ha.2.2.1
      rw [← smallPrimeSigmaAlgebra_eq_primeCylinder (M := hardCutoff (sizes k)) le_rfl] at hm
      exact smallPrimeSigmaAlgebra_le _ _ (C k) hm
    exact (source_local_relative_error_le (by omega) (C k) hCm ha.2.2.2.1).trans
      (hzero (sizes k) (by omega) (lengths k) ha.1 ha.2.1 (C k) ha.2.2.1
        ha.2.2.2.1 (counts k) ha.2.2.2.2.1 ha.2.2.2.2.2)
  exact tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using habs)

end
end PaperC.V282.HardLocalClosureRates
