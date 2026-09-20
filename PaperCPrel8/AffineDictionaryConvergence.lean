import PaperCPrel8.AffineDictionaryConsequences
import PaperCPrel8.AffineDictionaryDescription

/-! # Both genuine field distances converge in dictionary-selection probability -/
namespace PaperC.Prel8.AffineDictionaryConvergence
open Filter Topology
open PaperC.V282.RandomDictionary PaperC.V282.DictionaryFieldInfinite
open PaperC.V282.FiniteFieldTotalVariation PaperC.V282.IidWordInfinite
open PaperC.V282.ProcessAGGInput PaperC.V282.PrimeEulerPNT PaperC.V282.HardPoissonRates
open PaperC.Prel8.AffineDictionarySample PaperC.Prel8.AffineDictionaryInclusion
open PaperC.Prel8.AffineDictionaryMoments PaperC.Prel8.AffineDictionaryUniform
open PaperC.Prel8.AffineDictionaryExceptional PaperC.Prel8.AffineDictionaryConsequences
open PaperC.SectionThirteenFiniteBound
noncomputable section

/-- The iid remainder is uniform throughout the logarithmic band and intensity cap. -/
theorem iid_remainder_le {betaMin betaMax K : ℝ} {N L r : ℕ}
    (hN : 1 ≤ N) (hreg : Regime betaMin betaMax K N L r) :
    8*((N:ℝ)*((((2^(L+1-r):ℕ):ℝ))/(2:ℝ)^(L+1)))^2*(L+1:ℝ)/(N:ℝ) ≤
      (8*K^2*betaMax)*(Real.log N/N) := by
  have ha : 0 ≤ (N:ℝ)*((((2^(L+1-r):ℕ):ℝ))/(2:ℝ)^(L+1)) := by positivity
  have hs : ((N:ℝ)*((((2^(L+1-r):ℕ):ℝ))/(2:ℝ)^(L+1)))^2 ≤ K^2 := by nlinarith [hreg.2.2.2]
  calc
    _ ≤ 8*K^2*(betaMax*Real.log N)/(N:ℝ) := by gcongr; exact hreg.2.1
    _ = _ := by ring

/-- The mean distance to the actual independent-sign field tends to zero. -/
theorem mean_iid_tendsto_zero (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax K : ℝ) (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax) (hK : 0 ≤ K)
    (L r : ℕ → ℕ) (hreg : ∀ᶠ N in atTop, Regime betaMin betaMax K N (L N) (r N)) :
    Tendsto (fun N => affineAverage (L N+1) (r N) (fun W =>
      massTotalVariation (infiniteDictionaryLaw N (L N) W) (infiniteIidFieldLaw N (L N) W))) atTop (𝓝 0) := by
  have hlog : Tendsto (fun N : ℕ => Real.log N/(N:ℝ)) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hlim := (uniformRate_tendsto_zero hAGG hPNT betaMin betaMax K hbetaMin hbeta hK).add
    (hlog.const_mul (8*K^2*betaMax))
  simp only [mul_zero,add_zero] at hlim
  apply squeeze_zero' (Eventually.of_forall (fun N =>
    div_nonneg (Finset.sum_nonneg (fun s _ => massTotalVariation_nonneg _ _)) (Nat.cast_nonneg _))) ?_ hlim
  filter_upwards [hreg,eventually_ge_atTop 1] with N hr hn
  exact (uniform_arithmetic_iid_bound hAGG hn hr).trans (add_le_add (le_refl _) (iid_remainder_le hn hr))

/-- The affine version of part (ii) of the introduction, for the Poisson comparison with the dictionary fixed. -/
theorem poisson_in_selection_probability (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax K : ℝ) (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax) (hK : 0 ≤ K)
    (L r : ℕ → ℕ) (hreg : ∀ᶠ N in atTop, Regime betaMin betaMax K N (L N) (r N))
    {t : ℝ} (ht : 0 < t) :
    Tendsto (fun N => affineFraction (L N+1) (r N) (fun W => t < dictionaryDistance N (L N) W))
      atTop (𝓝 0) := by
  have hlim := (uniformRate_tendsto_zero hAGG hPNT betaMin betaMax K hbetaMin hbeta hK).div_const t
  simp only [zero_div] at hlim
  apply squeeze_zero' (Eventually.of_forall (fun N => fraction_nonneg _ _ _)) ?_ hlim
  filter_upwards [hreg] with N hr
  exact (fraction_gt_le hr.2.2.1 _ (fun s => dictionaryDistance_nonneg N (L N) (dictionary s)) ht
    (mean_unconditional_le hr.2.2.1 (mean_le_uniformRate hr))).trans (min_le_right _ _)

/-- The affine corollary also compares the two actual sources, not just two Poisson targets. -/
theorem iid_in_selection_probability (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax K : ℝ) (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax) (hK : 0 ≤ K)
    (L r : ℕ → ℕ) (hreg : ∀ᶠ N in atTop, Regime betaMin betaMax K N (L N) (r N))
    {t : ℝ} (ht : 0 < t) :
    Tendsto (fun N => affineFraction (L N+1) (r N) (fun W => t <
      massTotalVariation (infiniteDictionaryLaw N (L N) W) (infiniteIidFieldLaw N (L N) W))) atTop (𝓝 0) := by
  have hlim := (mean_iid_tendsto_zero hAGG hPNT betaMin betaMax K hbetaMin hbeta hK L r hreg).div_const t
  simp only [zero_div] at hlim
  apply squeeze_zero' (Eventually.of_forall (fun N => fraction_nonneg _ _ _)) ?_ hlim
  filter_upwards [hreg] with N hr
  exact (fraction_gt_le hr.2.2.1 _ (fun s => massTotalVariation_nonneg _ _) ht (le_refl _)).trans (min_le_right _ _)

end
end PaperC.Prel8.AffineDictionaryConvergence
