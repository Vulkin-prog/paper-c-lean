import PaperCV282.HardLocalClosureRates
import PaperCV282.CentralResolutionBudget
import PaperCV282.PoissonQuantitativeCentral
import PaperC.Probability.CriticalRunWindow

/-! # The hard central local regime of companion D.1, including bounded rounding -/
namespace PaperC.V282.HardLocalClosureCentral

open MeasureTheory ProbabilityTheory Filter Topology Real
open InfiniteRademacher InfiniteCylinderTransfer
open AllStartSoftPoisson RareConditioningRates HardPoissonRates RestrictedPoissonTransfer
open HardLocalClosureBudget HardLocalClosureRates PoissonResolutionBudget PoissonStirlingBounds PoissonCentralAsymptotics
open PoissonQuantitativeCentral PoissonQuantitativeLocal CriticalRunWindow
open ScalarSteinInput PrimeEulerPNT SaddleParameters SaddleScales SaddleCutoffAdmissibility

noncomputable section
local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

theorem hard_central_cost_budget_eventually (c c' : ℝ) (hcc : c'<c) :
    ∀ᶠ N : ℕ in atTop, ∀ I rate t : ℝ, ∀ n : ℕ, 1≤rate →
      I+(3/2 : ℝ)*log rate+t^2/2 ≤ saddleCutoff 1 (log N)-c*saddleNu 1 (log N) →
      |log (n : ℝ)-log rate|≤1 →
      |rate*poissonEntropy (n/rate)-t^2/2|≤1 →
      hardLocalCost I rate n ≤ saddleCutoff 1 (log N)-c'*saddleNu 1 (log N) := by
  have hnu := (tendsto_saddleNu_atTop (a := 1) (by norm_num)).comp
    (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hm := hnu.const_mul_atTop (by linarith : 0<c-c')
  filter_upwards [hm.eventually (eventually_ge_atTop (3 : ℝ))] with N hN
  intro I rate t n hr hb hl he
  dsimp only [Function.comp_def] at hN
  unfold hardLocalCost poissonLocalCost
  rw [max_eq_right (log_nonneg hr)]
  linarith [(abs_le.mp hl).2,(abs_le.mp he).2]

/-- Both local Poisson and local Gaussian probabilities for the actual conditioned count.
The length band and positivity of the observation are derived from the printed budget. -/
theorem hard_central_local_probabilities
    (hStein : ScalarSteinFactorsStatement) (hPNT : PrimeNumberTheoremRemainder)
    (c c' : ℝ) (hc' : 0<c') (hcc : c'<c)
    (sizes lengths counts : ℕ→ℕ) (C : ℕ→Set InfiniteSample) (t : ℕ→ℝ) (K : ℝ)
    (hsizes : Tendsto sizes atTop atTop)
    (hrate : Tendsto (fun k => (fullRate (sizes k) (lengths k) : ℝ)) atTop atTop)
    (ht : Tendsto (fun k => t k/(fullRate (sizes k) (lengths k) : ℝ)^(1/6 : ℝ)) atTop (𝓝 0))
    (hround : ∀ᶠ k in atTop, |(counts k : ℝ)-((fullRate (sizes k) (lengths k) : ℝ)+
      t k*sqrt (fullRate (sizes k) (lengths k) : ℝ))|≤K)
    (hC : ∀ᶠ k in atTop,
      MeasurableSet[MeasurableSpace.comap (restrictToFinite (hardCutoff (sizes k))) inferInstance] (C k))
    (hpos : ∀ᶠ k in atTop, 0 < infiniteRademacherMeasure.real (C k))
    (hbudget : ∀ᶠ k in atTop,
      eventInformation (C k)+(3/2 : ℝ)*log (fullRate (sizes k) (lengths k) : ℝ)+(t k)^2/2 ≤
        saddleCutoff 1 (log (sizes k))-c*saddleNu 1 (log (sizes k))) :
    Tendsto (fun k => restrictedCountLaw (sizes k) (lengths k) (C k) (counts k) /
      (poissonMeasure (fullRate (sizes k) (lengths k))).real {counts k}) atTop (𝓝 1) ∧
    Tendsto (fun k => restrictedCountLaw (sizes k) (lengths k) (C k) (counts k) /
      gaussianLatticeMass (fullRate (sizes k) (lengths k)) (t k)) atTop (𝓝 1) := by
  obtain ⟨hlogerr,hentropyerr⟩ := bounded_rounding_central_errors
    (fun k => (fullRate (sizes k) (lengths k) : ℝ)) counts t K hrate ht hround
  have hlogs := hlogerr.abs.eventually (gt_mem_nhds (by norm_num : |(0 : ℝ)|<1))
  have hentropies := hentropyerr.abs.eventually (gt_mem_nhds (by norm_num : |(0 : ℝ)|<1))
  have hnu := ((tendsto_saddleNu_atTop (a := 1) (by norm_num)).comp
    (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).comp hsizes
  have hadmissible : ∀ᶠ k in atTop,
      lowerConstant*log (sizes k)≤(lengths k+1 : ℝ) ∧
      (lengths k+1 : ℝ)≤upperConstant*log (sizes k) ∧
      MeasurableSet[MeasurableSpace.comap (restrictToFinite (hardCutoff (sizes k))) inferInstance] (C k) ∧
      0 < infiniteRademacherMeasure.real (C k) ∧ 0<counts k ∧
      hardLocalCost (eventInformation (C k)) (fullRate (sizes k) (lengths k)) (counts k) ≤
        saddleCutoff 1 (log (sizes k))-c'*saddleNu 1 (log (sizes k)) := by
    filter_upwards [hsizes.eventually (hard_central_cost_budget_eventually c c' hcc),
      hsizes.eventually CentralResolutionBudget.central_common_band_eventually,
      hrate.eventually (eventually_ge_atTop (1 : ℝ)),
      (tendsto_log_atTop.comp hrate).eventually (eventually_ge_atTop (2 : ℝ)),
      hnu.eventually (eventually_ge_atTop (0 : ℝ)),hC,hpos,hbudget,hlogs,hentropies]
      with k hcost hband hr hlr hnu0 hmeas hpositive hb hel hee
    dsimp only [Function.comp_def] at hlr hnu0
    have hI := eventInformation_nonneg (C k) hpositive
    have hn : 0<counts k := by
      by_contra hn
      have hz : counts k=0 := by omega
      simp only [hz,Nat.cast_zero,log_zero,zero_sub,abs_neg] at hel
      have hh := le_abs_self (log (fullRate (sizes k) (lengths k) : ℝ))
      linarith
    have hlogle : log (fullRate (sizes k) (lengths k) : ℝ)≤saddleCutoff 1 (log (sizes k)) := by
      have hrl := log_nonneg hr
      nlinarith [sq_nonneg (t k),mul_nonneg (show 0≤c by linarith) hnu0]
    obtain ⟨hlo,hhi⟩ := hband (lengths k) hr hlogle
    exact ⟨hlo,hhi,hmeas,hpositive,hn,
      hcost (eventInformation (C k)) (fullRate (sizes k) (lengths k)) (t k) (counts k)
        hr hb hel.le hee.le⟩
  have hlocal := hard_local_ratio_tendsto_one hStein hPNT lowerConstant upperConstant c'
    lowerConstant_pos lowerConstant_lt_upperConstant hc' sizes lengths counts C hsizes hadmissible
  refine ⟨hlocal, ?_⟩
  have htarget := poisson_gaussian_local_ratio_tendsto_one
    (fun k => fullRate (sizes k) (lengths k)) counts t K hrate ht hround
  have hproduct := hlocal.mul htarget
  simp only [one_mul] at hproduct
  apply hproduct.congr'
  filter_upwards [hrate.eventually (eventually_gt_atTop (0 : ℝ))] with k hr
  have hp : (poissonMeasure (fullRate (sizes k) (lengths k))).real {counts k}≠0 := by
    rw [poissonMeasure_real_singleton]
    positivity
  exact div_mul_div_cancel₀ hp

end
end PaperC.V282.HardLocalClosureCentral
