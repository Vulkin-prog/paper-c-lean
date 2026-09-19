import PaperCPrel8.TypicalDictionaryConsequences

/-! # Both genuine field distances converge in dictionary-selection probability -/
namespace PaperC.Prel8.TypicalDictionaryConvergence
open Filter Topology
open PaperC.V282.RandomDictionary PaperC.V282.DictionaryFieldInfinite
open PaperC.V282.FiniteFieldTotalVariation PaperC.V282.IidWordInfinite
open PaperC.V282.ProcessAGGInput PaperC.V282.PrimeEulerPNT PaperC.V282.HardPoissonRates
open PaperC.Prel8.DictionaryAverage PaperC.Prel8.TypicalDictionaryUniform
open PaperC.Prel8.TypicalDictionaryTheorem PaperC.Prel8.TypicalDictionaryConsequences
noncomputable section

/-- The iid remainder is uniform throughout the logarithmic band and intensity cap. -/
theorem iid_remainder_le {betaMin betaMax K : ℝ} {N L m : ℕ}
    (hN : 1 ≤ N) (hreg : Regime betaMin betaMax K N L m) :
    8*((N:ℝ)*((m:ℝ)/(2:ℝ)^(L+1)))^2*(L+1:ℝ)/(N:ℝ) ≤
      (8*K^2*betaMax)*(Real.log N/N) := by
  have ha : 0 ≤ (N:ℝ)*((m:ℝ)/(2:ℝ)^(L+1)) := by positivity
  have hs : ((N:ℝ)*((m:ℝ)/(2:ℝ)^(L+1)))^2 ≤ K^2 := by nlinarith [hreg.2.2.2.2]
  calc
    _ ≤ 8*K^2*(betaMax*Real.log N)/(N:ℝ) := by gcongr; exact hreg.2.1
    _ = _ := by ring

/-- The mean distance to the actual independent-sign field tends to zero. -/
theorem mean_iid_tendsto_zero (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax K : ℝ) (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax) (hK : 0 ≤ K)
    (L m : ℕ → ℕ) (hreg : ∀ᶠ N in atTop, Regime betaMin betaMax K N (L N) (m N)) :
    Tendsto (fun N => dictionaryAverage (L N+1) (m N) (fun W =>
      massTotalVariation (infiniteDictionaryLaw N (L N) W) (infiniteIidFieldLaw N (L N) W))) atTop (𝓝 0) := by
  have hlog : Tendsto (fun N : ℕ => Real.log N/(N:ℝ)) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hlim := (uniformRate_tendsto_zero hAGG hPNT betaMin betaMax K hbetaMin hbeta hK).add
    (hlog.const_mul (8*K^2*betaMax))
  simp only [mul_zero,add_zero] at hlim
  apply squeeze_zero' (Eventually.of_forall (fun N =>
    div_nonneg (Finset.sum_nonneg (fun W _ => massTotalVariation_nonneg _ _)) (Nat.cast_nonneg _))) ?_ hlim
  filter_upwards [hreg,eventually_ge_atTop 1] with N hr hn
  exact (uniform_arithmetic_iid_bound hAGG hn hr).trans (add_le_add (le_refl _) (iid_remainder_le hn hr))

/-- Part (ii) of the introduction, for the Poisson comparison with the dictionary fixed. -/
theorem poisson_in_selection_probability (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax K : ℝ) (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax) (hK : 0 ≤ K)
    (L m : ℕ → ℕ) (hreg : ∀ᶠ N in atTop, Regime betaMin betaMax K N (L N) (m N))
    {t : ℝ} (ht : 0 < t) :
    Tendsto (fun N => dictionaryFraction (L N+1) (m N) (fun W => t < dictionaryDistance N (L N) W))
      atTop (𝓝 0) := by
  have hlim := (uniformRate_tendsto_zero hAGG hPNT betaMin betaMax K hbetaMin hbeta hK).div_const t
  simp only [zero_div] at hlim
  apply squeeze_zero' (Eventually.of_forall (fun N => by unfold dictionaryFraction; positivity)) ?_ hlim
  filter_upwards [hreg] with N hr
  exact (fraction_gt_le hr.2.2.2.1 _ (fun W _ => dictionaryDistance_nonneg N (L N) W) ht
    (mean_unconditional_le (mean_le_uniformRate hr))).trans (min_le_right _ _)

/-- Part (ii) also compares the two actual sources, not just two Poisson targets. -/
theorem iid_in_selection_probability (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax K : ℝ) (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax) (hK : 0 ≤ K)
    (L m : ℕ → ℕ) (hreg : ∀ᶠ N in atTop, Regime betaMin betaMax K N (L N) (m N))
    {t : ℝ} (ht : 0 < t) :
    Tendsto (fun N => dictionaryFraction (L N+1) (m N) (fun W => t <
      massTotalVariation (infiniteDictionaryLaw N (L N) W) (infiniteIidFieldLaw N (L N) W))) atTop (𝓝 0) := by
  have hlim := (mean_iid_tendsto_zero hAGG hPNT betaMin betaMax K hbetaMin hbeta hK L m hreg).div_const t
  simp only [zero_div] at hlim
  apply squeeze_zero' (Eventually.of_forall (fun N => by unfold dictionaryFraction; positivity)) ?_ hlim
  filter_upwards [hreg] with N hr
  exact (fraction_gt_le hr.2.2.2.1 _ (fun W _ => massTotalVariation_nonneg _ _) ht (le_refl _)).trans (min_le_right _ _)

end
end PaperC.Prel8.TypicalDictionaryConvergence
