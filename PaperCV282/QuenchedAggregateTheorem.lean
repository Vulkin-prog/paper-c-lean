import PaperCV282.MeanAggregateBudget
import PaperCV282.QuenchedBorelCantelli
import PaperCV282.GeometricScaleInstances
import PaperCV282.UnsignedAggregateComparison

/-!
# Corollary 6.4 for the actual complete conditional staircase

All environments live on the original infinite Rademacher space. The finite
prime partitions may overlap arbitrarily from one scale to another. Actual
mean bounds, Markov amplification and proved summability give the result.
-/
namespace PaperC.V282.QuenchedAggregateTheorem

open MeasureTheory Filter Topology InfiniteRademacher InfiniteCylinderTransfer InfiniteConditionalWords
open FinitePrimeEnvironment MeanAggregateBudget GeometricSaddleSummability GeometricScaleInstances
open QuenchedBorelCantelli SignedAggregateTruncation UnsignedAggregateComparison
open SignedAggregateHardBudget GrowingLevelParameters AllStartSoftPoisson SaddleParameters SaddleScales
open DirectionalSteinInput PrimeEulerPNT HardPoissonRates FiniteFieldTotalVariation
open ConditionedCountableLaw MassPushforward ThresholdPathEquivalence InfiniteStartProbabilityTransfer

noncomputable section

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤
local instance instProbabilityInfiniteRademacher : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

def quenchedSignedAggregateDistance (N L : ℕ) : InfiniteSample → ℝ :=
  environmentDistance (hardCutoff N) (hardCutoff N) (signedAggregateSource N L) (signedAggregateTargetLaw N L)

def quenchedUnsignedAggregateDistance (N L : ℕ) : InfiniteSample → ℝ :=
  environmentDistance (hardCutoff N) (hardCutoff N) (unsignedAggregateSource N L)
    (geometricConfigurationLaw (fullRate N L))

def quenchedThresholdDistance (N L : ℕ) : InfiniteSample → ℝ :=
  environmentDistance (hardCutoff N) (hardCutoff N)
    (fun omega m => infiniteDyadicStartCount N (L+m) omega)
    (pushforwardMass thresholdFunction (geometricConfigurationLaw (fullRate N L)))

theorem quenched_unsigned_le_signed (N L : ℕ) (omega : InfiniteSample) :
    quenchedUnsignedAggregateDistance N L omega ≤ quenchedSignedAggregateDistance N L omega := by
  apply conditional_unsigned_le_signed
  rw [PrimeFieldEventConditioning.real_atom_mass]
  positivity

theorem quenched_threshold_eq_unsigned {N L : ℕ} (hN : 2≤N) (omega : InfiniteSample) :
    quenchedThresholdDistance N L omega=quenchedUnsignedAggregateDistance N L omega :=
  conditional_path_distance_eq hN _

/-- The almost-sure conditional bound for every excess and both signs. -/
theorem corollary_six_four_signed (hStein : DirectionalSteinFactorsStatement)
    (hPNT : PrimeNumberTheoremRemainder) (sizes depths : ℕ → ℕ)
    (hg : GeometricLowerGrowth sizes)
    (hdepths : Tendsto (fun k => (depths k : ℝ)/Real.log (sizes k)) atTop (𝓝 0))
    (c beta : ℝ) (hbeta : 0<beta) (hcb : beta<c)
    (hbudget : ∀ᶠ k in atTop, Real.log (fullRate (sizes k) (movingLength (sizes k) (depths k)))≤
      saddleCutoff 1 (Real.log (sizes k))-c*saddleNu 1 (Real.log (sizes k))) :
    ∀ᵐ omega ∂infiniteRademacherMeasure, ∀ᶠ k in atTop,
      quenchedSignedAggregateDistance (sizes k) (movingLength (sizes k) (depths k)) omega ≤
        Real.exp (-beta*saddleNu 1 (Real.log (sizes k))) := by
  have hsizes := sizes_tendsto_atTop hg
  have hlog2 : 0<Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  let lo := 1/(2*Real.log 2)
  let hi := 2/Real.log 2
  have hlo : 0<lo := by dsimp [lo];positivity
  have hlomid : lo<1/Real.log 2 := by dsimp [lo];apply (div_lt_div_iff₀ (by positivity) hlog2).mpr;nlinarith
  have hhimid : 1/Real.log 2<hi := by dsimp [hi];exact div_lt_div_of_pos_right (by norm_num) hlog2
  have hband := moving_sequence_domain_eventually sizes depths hsizes hdepths lo hi hlomid hhimid
  obtain ⟨Nzero,hzero⟩ := integral_environment_aggregate_hard_rate hStein hPNT lo hi c ((c+beta)/2) (1/6)
    hlo (hlomid.trans hhimid) (by linarith) (by linarith) (by norm_num)
  have hmean : ∀ᶠ k in atTop,
      (∫ omega, quenchedSignedAggregateDistance (sizes k) (movingLength (sizes k) (depths k)) omega
        ∂infiniteRademacherMeasure) ≤
      2*Real.exp (-((c+beta)/2)*saddleNu 1 (Real.log (sizes k)))+(sizes k : ℝ)^(-(1/6 : ℝ)) := by
    filter_upwards [hband,hbudget,hsizes.eventually (eventually_ge_atTop Nzero)] with k hb hbu hn
    have hh := hzero (sizes k) hn (movingLength (sizes k) (depths k)) hb.2.2.1 hb.2.2.2.1 hb.2.2.2.2 hbu
    norm_num at hh ⊢
    exact hh
  exact ae_eventually_saddle_bound infiniteRademacherMeasure
    (fun k => quenchedSignedAggregateDistance (sizes k) (movingLength (sizes k) (depths k)))
    (fun _ => integrable_environmentDistance _ _ _ _) (fun _ => environmentDistance_nonneg _ _ _ _)
    sizes hg 1 ((c+beta)/2) beta (1/6) 2 (by norm_num) (by linarith) (by norm_num) hmean

/-- The literal complete staircase and the exact counts obey the same bound almost surely. -/
theorem corollary_six_four (hStein : DirectionalSteinFactorsStatement)
    (hPNT : PrimeNumberTheoremRemainder) (sizes depths : ℕ → ℕ)
    (hg : GeometricLowerGrowth sizes)
    (hdepths : Tendsto (fun k => (depths k : ℝ)/Real.log (sizes k)) atTop (𝓝 0))
    (c beta : ℝ) (hbeta : 0<beta) (hcb : beta<c)
    (hbudget : ∀ᶠ k in atTop, Real.log (fullRate (sizes k) (movingLength (sizes k) (depths k)))≤
      saddleCutoff 1 (Real.log (sizes k))-c*saddleNu 1 (Real.log (sizes k))) :
    ∀ᵐ omega ∂infiniteRademacherMeasure, ∀ᶠ k in atTop,
      quenchedThresholdDistance (sizes k) (movingLength (sizes k) (depths k)) omega ≤
        Real.exp (-beta*saddleNu 1 (Real.log (sizes k))) ∧
      quenchedUnsignedAggregateDistance (sizes k) (movingLength (sizes k) (depths k)) omega ≤
        Real.exp (-beta*saddleNu 1 (Real.log (sizes k))) := by
  filter_upwards [corollary_six_four_signed hStein hPNT sizes depths hg hdepths c beta hbeta hcb hbudget]
    with omega h
  filter_upwards [h,(sizes_tendsto_atTop hg).eventually (eventually_ge_atTop (2 : ℕ))] with k hk hN
  have hu := (quenched_unsigned_le_signed (sizes k) (movingLength (sizes k) (depths k)) omega).trans hk
  exact ⟨(quenched_threshold_eq_unsigned hN omega).le.trans hu,hu⟩

/-- In particular the exact geometric-scale hypothesis of the manuscript is sufficient. -/
theorem corollary_six_four_geometric (hStein : DirectionalSteinFactorsStatement)
    (hPNT : PrimeNumberTheoremRemainder) (sizes depths : ℕ → ℕ)
    (q D : ℝ) (hq : 1<q) (hD : 0<D)
    (hscale : ∀ᶠ k : ℕ in atTop, D*q^k≤(sizes k : ℝ))
    (hdepths : Tendsto (fun k => (depths k : ℝ)/Real.log (sizes k)) atTop (𝓝 0))
    (c beta : ℝ) (hbeta : 0<beta) (hcb : beta<c)
    (hbudget : ∀ᶠ k in atTop, Real.log (fullRate (sizes k) (movingLength (sizes k) (depths k)))≤
      saddleCutoff 1 (Real.log (sizes k))-c*saddleNu 1 (Real.log (sizes k))) :
    ∀ᵐ omega ∂infiniteRademacherMeasure, ∀ᶠ k in atTop,
      quenchedThresholdDistance (sizes k) (movingLength (sizes k) (depths k)) omega ≤
        Real.exp (-beta*saddleNu 1 (Real.log (sizes k))) ∧
      quenchedUnsignedAggregateDistance (sizes k) (movingLength (sizes k) (depths k)) omega ≤
        Real.exp (-beta*saddleNu 1 (Real.log (sizes k))) :=
  corollary_six_four hStein hPNT sizes depths
    (geometricLowerGrowth_of_geometric_lower_bound sizes q D hq hD hscale) hdepths c beta hbeta hcb hbudget

end
end PaperC.V282.QuenchedAggregateTheorem
