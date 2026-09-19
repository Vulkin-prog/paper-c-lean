import PaperCPrel8.AffineDictionaryUniform
import PaperCPrel8.AffineDictionaryIid
import PaperCPrel8.TypicalDictionaryConsequences
import PaperCV282.DictionaryFieldStatistics

/-! # Typical classes, deterministic readouts and independent-source comparison -/
namespace PaperC.Prel8.AffineDictionaryConsequences
open Filter Topology
open PaperC.ConditionalStartProbability PaperC.SectionTwelveMoments PaperC.SectionThirteenFiniteBound
open PaperC.ConditionalAGGAverage
open PaperC.V282.RandomDictionary PaperC.V282.DictionaryFieldInfinite
open PaperC.V282.DictionaryFieldStatistics PaperC.V282.DictionaryFieldModel
open PaperC.V282.DictionaryFieldTransfer PaperC.V282.MassPushforward
open PaperC.V282.FiniteFieldTotalVariation PaperC.V282.FiniteFieldPoissonCoupling
open PaperC.V282.ProcessAGGInput PaperC.V282.HardPoissonRates PaperC.V282.IidWordInfinite
open PaperC.Prel8.AffineDictionaryUniform PaperC.Prel8.AffineDictionaryExceptional
open PaperC.Prel8.AffineDictionaryIid PaperC.Prel8.AffineDictionarySample
open PaperC.Prel8.AffineDictionaryInclusion PaperC.Prel8.AffineDictionaryMoments
open PaperC.Prel8.TypicalDictionaryConsequences
noncomputable section

/-- The rate applies to the actual mean conditional distance of every admissible sampled size. -/
theorem uniform_exceptional_fraction {betaMin betaMax K : ℝ} {N L r : ℕ}
    (hreg : Regime betaMin betaMax K N L r) {t : ℝ} (ht : 0 < t) :
    affineFraction (L+1) r (fun W => t < dictionaryConditionalDistance N L (hardCutoff N) W) ≤
      min 1 (uniformRate betaMin betaMax K N/t) :=
  exceptional_fraction_le hreg.2.2.1 ht (mean_le_uniformRate hreg)

/-- Any threshold with r_N/t_N -> 0 has vanishing exceptional proportion. -/
theorem exceptional_fraction_tendsto_zero (betaMin betaMax K : ℝ) (L r : ℕ → ℕ) (t : ℕ → ℝ)
    (hreg : ∀ᶠ N in atTop, Regime betaMin betaMax K N (L N) (r N))
    (ht : ∀ᶠ N in atTop, 0 < t N)
    (hr : Tendsto (fun N => uniformRate betaMin betaMax K N/t N) atTop (𝓝 0)) :
    Tendsto (fun N => affineFraction (L N+1) (r N)
      (fun W => t N < dictionaryConditionalDistance N (L N) (hardCutoff N) W)) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun N => fraction_nonneg _ _ _)) ?_ hr
  filter_upwards [hreg,ht] with N hN htN
  exact (uniform_exceptional_fraction hN htN).trans (min_le_right _ _)

/-- Selection averaging also contracts for an arbitrary family of deterministic readouts. -/
theorem averaged_statistic_le {T : Type*} {betaMin betaMax K : ℝ} {N L r : ℕ}
    (hreg : Regime betaMin betaMax K N L r)
    (f : (W : Finset (Fin (L+1) → PaperC.F₂)) → (DictionaryIndex N L W → ℕ) → T) :
    affineAverage (L+1) r (fun W => statisticDistance N L (hardCutoff N) W (f W)) ≤
      uniformRate betaMin betaMax K N :=
  (affine_mono hreg.2.2.1 (f := fun W => statisticDistance N L (hardCutoff N) W (f W)) (g := dictionaryConditionalDistance N L (hardCutoff N)) (fun s => statisticDistance_le N L (hardCutoff N) (dictionary s) (f (dictionary s)))).trans (mean_le_uniformRate hreg)

/-- The two actual infinite word fields obey the same uniform rate plus the stated iid cost. -/
theorem uniform_arithmetic_iid_bound (hAGG : ProcessAGGStatement)
    {betaMin betaMax K : ℝ} {N L r : ℕ} (hN : 1 ≤ N) (hreg : Regime betaMin betaMax K N L r) :
    affineAverage (L+1) r (fun W =>
      massTotalVariation (infiniteDictionaryLaw N L W) (infiniteIidFieldLaw N L W)) ≤
      uniformRate betaMin betaMax K N+
        8*((N:ℝ)*((((2^(L+1-r):ℕ):ℝ))/(2:ℝ)^(L+1)))^2*(L+1:ℝ)/(N:ℝ) := by
  have h := averaged_arithmetic_iid_le hAGG hN hreg.2.2.1 (mean_le_uniformRate hreg)
  rwa [PaperC.Prel8.TypicalDictionaryIid.iid_remainder_normalized (by omega)] at h

end
end PaperC.Prel8.AffineDictionaryConsequences
