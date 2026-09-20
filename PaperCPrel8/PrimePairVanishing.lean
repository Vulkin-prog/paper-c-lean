import PaperCPrel8.AbsolutePairTheorem
import PaperCPrel8.CategoricalPairBridge
import PaperCPrel8.PrimeActivityDivergence
import PaperCV282.SaddleRateConvergence

/-! # Vanishing of the actual pair layer on the prime obstruction windows -/
namespace PaperC.Prel8.PrimePairVanishing
open Filter Topology PrimeWindowScales PrimeWindowBudget PrimeWindowGeometry PrimeRetainedDensity
open AbsolutePairTheorem CategoricalPairBridge CumulantActivityLayers ArithmeticLowCategory
open ActualSignedPalm MicroscopicProfileBudget MicroscopicActualGeometry RoughKernelDeletion
open ConditionalStartProbability ArratiaGoldsteinGordonInput IndependentThinning FiniteConditioning
open V282.PrimeEulerPNT V282.SaddleScales V282.SaddleRateConvergence
noncomputable section
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem probability_true {Ω : Type*} [Fintype Ω] (mu : FinitePMF Ω) :
    eventProbability mu (fun _ ↦ True)=1 := by
  simpa only [eventProbability,ite_true] using mu.sum_prob

theorem conditional_true {Ω : Type*} [Fintype Ω] (mu : FinitePMF Ω)
    (hp : 0<eventProbability mu (fun _ ↦ True)) : conditional mu (fun _ ↦ True) hp=mu := by
  cases mu
  simp only [conditional,probability_true,ite_true,div_one]

def pair (q : ℕ) (G : Finset ℕ) : ℝ :=
  pairActivity (FinitePMF.uniform (SampleSpace (cylinder q)))
    (retainedCategory (cylinder q) (q-1) (excess q) G)

/-- Every deterministic subset of G0 has a vanishing pair layer, with actual means. -/
theorem good_subsets_tendsto (hPNT : PrimeNumberTheoremRemainder)
    (G : ℕ → Finset ℕ) (hG : ∀ q, G q⊆original q) :
    Tendsto (fun q ↦ pair q (G q)) atTop (𝓝 0) := by
  obtain ⟨M0,hM⟩ := pair_margin_eventually hPNT betaMin betaMax 2 1 (1/6)
    band_constants.1 band_constants.2 (by norm_num) (by norm_num) (by norm_num)
  have he := (margin_exponential_nat_tendsto_zero 1 2 0 (by norm_num) (by norm_num)).const_mul 4
  have hp := (polynomial_error_nat_tendsto_zero (1/6) (by norm_num)).const_mul 2
  have hh : Tendsto (fun q ↦ 4*Real.exp (-saddleNu 1 (Real.log (window q)))+
      2*(window q:ℝ)^(-(1/(3:ℝ))+(1/6))) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (he.add hp).comp window_tendsto
  apply squeeze_zero' (Eventually.of_forall (fun q ↦ pair_nonneg _ _)) _ hh
  filter_upwards [scalar_regime 2,window_tendsto.eventually (eventually_ge_atTop M0),eventually_ge_atTop 2]
    with q hq hM0 hq2
  have hA : 0<eventProbability (FinitePMF.uniform (SampleSpace (cylinder q)))
      (fun w ↦ (fun _ : SmallSample (cylinder q) (primeCutoff (window q)) ↦ True)
        (restrictSmall (cylinder q) (primeCutoff (window q)) w)) := by rw [probability_true]; norm_num
  have hb := hM (window q) hM0 (q-1) 0 (by exact_mod_cast hq.1) (by exact_mod_cast hq.2.1)
    hq.2.2.1 hq.2.2.2.1 hq.2.2.2.2 (cylinder q) (by rfl) (G q) (hG q)
    (fun _ ↦ True) hA (by rw [probability_true]; simp)
  have heq : sourceLaw (fun _ : SmallSample (cylinder q) (primeCutoff (window q)) ↦ True) hA=
      FinitePMF.uniform (SampleSpace (cylinder q)) := conditional_true _ hA
  rw [heq] at hb
  rw [arithmetic_pair_activity (by omega)]
  simpa only [excess,neg_zero,one_mul,zero_sub,Real.exp_zero,mul_one] using hb

theorem original_tendsto (hPNT : PrimeNumberTheoremRemainder) :
    Tendsto (fun q ↦ pair q (original q)) atTop (𝓝 0) :=
  good_subsets_tendsto hPNT original (fun _ ↦ Finset.Subset.refl _)

theorem retained_tendsto (hPNT : PrimeNumberTheoremRemainder) (theta : ℝ) :
    Tendsto (fun q ↦ pair q (retained q theta)) atTop (𝓝 0) :=
  good_subsets_tendsto hPNT (fun q ↦ retained q theta) (fun q ↦ retained_subset_original q theta)

end
end PaperC.Prel8.PrimePairVanishing
