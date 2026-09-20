import PaperCPrel8.PrimePairVanishing
import PaperCPrel8.PrimeMicroscopicComparison

/-! # G.9: the divergence is carried by orders at least three -/
namespace PaperC.Prel8.PrimeHigherDivergence
open Filter Topology PrimeWindowGeometry PrimeRetainedDensity PrimeCumulantObstruction
open PrimeActivityDivergence PrimePairVanishing CumulantActivityLayers ArithmeticLowCategory
open ConditionalStartProbability IndependentThinning V282.PrimeEulerPNT
noncomputable section

def higher (q : ℕ) (G : Finset ℕ) : ℝ :=
  higherActivity (FinitePMF.uniform (SampleSpace (cylinder q)))
    (retainedCategory (cylinder q) (q-1) (excess q) G)

theorem original_higher_diverges (hPNT : PrimeNumberTheoremRemainder)
    (qs : ℕ → ℕ) (hqs : Tendsto qs atTop atTop) (hp : ∀ᶠ n in atTop, (qs n).Prime) :
    Tendsto (fun n ↦ higher (qs n) (original (qs n))) atTop atTop := by
  apply higher_diverges_of_pair_tendsto (original_diverges hPNT qs hqs hp)
    ((original_tendsto hPNT).comp hqs)
  intro n
  exact activity_split _ _

/-- The actual arithmetic orders >=3 diverge for each fixed nonnegative stronger cutoff. -/
theorem retained_higher_diverges (hPNT : PrimeNumberTheoremRemainder) {theta : ℝ} (htheta : 0≤theta)
    (qs : ℕ → ℕ) (hqs : Tendsto qs atTop atTop) (hp : ∀ᶠ n in atTop, (qs n).Prime) :
    Tendsto (fun n ↦ higher (qs n) (retained (qs n) theta)) atTop atTop := by
  apply higher_diverges_of_pair_tendsto (retained_diverges hPNT htheta qs hqs hp)
    ((retained_tendsto hPNT theta).comp hqs)
  intro n
  exact activity_split _ _

end
end PaperC.Prel8.PrimeHigherDivergence
