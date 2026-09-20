import PaperCPrel8.TypicalDictionaryUniform
import PaperCPrel8.TypicalDictionaryIid
import PaperCV282.DictionaryFieldStatistics

/-! # Typical classes, deterministic readouts and independent-source comparison -/
namespace PaperC.Prel8.TypicalDictionaryConsequences
open Filter Topology
open PaperC.ConditionalStartProbability PaperC.SectionTwelveMoments PaperC.SectionThirteenFiniteBound
open PaperC.ConditionalAGGAverage
open PaperC.V282.RandomDictionary PaperC.V282.DictionaryFieldInfinite
open PaperC.V282.DictionaryFieldStatistics PaperC.V282.DictionaryFieldModel
open PaperC.V282.DictionaryFieldTransfer PaperC.V282.MassPushforward
open PaperC.V282.FiniteFieldTotalVariation PaperC.V282.FiniteFieldPoissonCoupling
open PaperC.V282.ProcessAGGInput PaperC.V282.HardPoissonRates PaperC.V282.IidWordInfinite
open PaperC.Prel8.TypicalDictionaryUniform PaperC.Prel8.TypicalDictionaryTheorem
open PaperC.Prel8.TypicalDictionaryIid PaperC.Prel8.DictionaryAverage
noncomputable section

/-- The rate applies to the actual mean conditional distance of every admissible sampled size. -/
theorem uniform_exceptional_fraction {betaMin betaMax K : ℝ} {N L m : ℕ}
    (hreg : Regime betaMin betaMax K N L m) {t : ℝ} (ht : 0 < t) :
    dictionaryFraction (L+1) m (fun W => t < dictionaryConditionalDistance N L (hardCutoff N) W) ≤
      min 1 (uniformRate betaMin betaMax K N/t) :=
  exceptional_fraction_le hreg.2.2.2.1 ht (mean_le_uniformRate hreg)

/-- Any threshold with r_N/t_N -> 0 has vanishing exceptional proportion. -/
theorem exceptional_fraction_tendsto_zero (betaMin betaMax K : ℝ) (L m : ℕ → ℕ) (t : ℕ → ℝ)
    (hreg : ∀ᶠ N in atTop, Regime betaMin betaMax K N (L N) (m N))
    (ht : ∀ᶠ N in atTop, 0 < t N)
    (hr : Tendsto (fun N => uniformRate betaMin betaMax K N/t N) atTop (𝓝 0)) :
    Tendsto (fun N => dictionaryFraction (L N+1) (m N)
      (fun W => t N < dictionaryConditionalDistance N (L N) (hardCutoff N) W)) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun N => by unfold dictionaryFraction; positivity)) ?_ hr
  filter_upwards [hreg,ht] with N hN htN
  exact (uniform_exceptional_fraction hN htN).trans (min_le_right _ _)

/-- A statistic may depend on the independently selected dictionary, which remains fixed in the law. -/
def statisticDistance {T : Type*} (N L Y : ℕ) (W : Finset (Fin (L+1) → PaperC.F₂))
    (f : (DictionaryIndex N L W → ℕ) → T) : ℝ :=
  finiteUniformAverage (fun sigma : SmallSample (dyadicCutoff N L) Y =>
    massTotalVariation (pushforwardMass f (conditionalDictionaryLaw (dyadicCutoff N L) N L Y W sigma))
      (pushforwardMass f (poissonFieldMass (allWordRates N L W (dyadicBlock N)))))

/-- All deterministic coordinate restrictions contract before either average. -/
theorem statisticDistance_le {T : Type*} (N L Y : ℕ) (W : Finset (Fin (L+1) → PaperC.F₂))
    (f : (DictionaryIndex N L W → ℕ) → T) :
    statisticDistance N L Y W f ≤ dictionaryConditionalDistance N L Y W :=
  finiteUniformAverage_mono (fun sigma => conditional_statistic_distance_le W f sigma)

/-- Each nonexceptional dictionary simultaneously certifies every deterministic readout. -/
theorem nonexceptional_readout {T : Type*} {N L Y : ℕ} (W : Finset (Fin (L+1) → PaperC.F₂))
    (f : (DictionaryIndex N L W → ℕ) → T) {t : ℝ}
    (hW : ¬t < dictionaryConditionalDistance N L Y W) : statisticDistance N L Y W f ≤ t :=
  (statisticDistance_le N L Y W f).trans (le_of_not_gt hW)

/-- Selection averaging also contracts for an arbitrary family of deterministic readouts. -/
theorem averaged_statistic_le {T : Type*} {betaMin betaMax K : ℝ} {N L m : ℕ}
    (hreg : Regime betaMin betaMax K N L m)
    (f : (W : Finset (Fin (L+1) → PaperC.F₂)) → (DictionaryIndex N L W → ℕ) → T) :
    dictionaryAverage (L+1) m (fun W => statisticDistance N L (hardCutoff N) W (f W)) ≤
      uniformRate betaMin betaMax K N :=
  (average_mono (fun W _ => statisticDistance_le N L (hardCutoff N) W (f W))).trans (mean_le_uniformRate hreg)

/-- The two actual infinite word fields obey the same uniform rate plus the stated iid cost. -/
theorem uniform_arithmetic_iid_bound (hAGG : ProcessAGGStatement)
    {betaMin betaMax K : ℝ} {N L m : ℕ} (hN : 1 ≤ N) (hreg : Regime betaMin betaMax K N L m) :
    dictionaryAverage (L+1) m (fun W =>
      massTotalVariation (infiniteDictionaryLaw N L W) (infiniteIidFieldLaw N L W)) ≤
      uniformRate betaMin betaMax K N+
        8*((N:ℝ)*((m:ℝ)/(2:ℝ)^(L+1)))^2*(L+1:ℝ)/(N:ℝ) := by
  have h := averaged_arithmetic_iid_le hAGG hN hreg.2.2.1 hreg.2.2.2.1 (mean_le_uniformRate hreg)
  rwa [iid_remainder_normalized (by omega)] at h

end
end PaperC.Prel8.TypicalDictionaryConsequences
