import PaperCPrel8.PrimeWindowBudget
import PaperCPrel8.StrongerDeletionTheorem

/-! # The literal low-mark cutoff and sampling cylinder on the prime windows -/
namespace PaperC.Prel8.PrimeWindowGeometry
open Filter Topology PrimeWindowScales PrimeWindowErrors PrimeWindowBudget
open MicroscopicActualGeometry MicroscopicProfileBudget MicroscopicGoodField ActualSignedPalm
noncomputable section

def excess (q : ℕ) : ℕ := paperExcess (window q) (q-1) 0
def support (q : ℕ) : ℕ := q-1+excess q+1
def cylinder (q : ℕ) : ℕ := window q+support q

theorem actual_geometry : ∀ᶠ q : ℕ in atTop,
    GeometryFacts (window q) (q-1) 0 betaMin betaMax := by
  obtain ⟨M0,hM⟩ := actual_geometry_eventually betaMin betaMax 1 band_constants.1 band_constants.2 (by norm_num)
  filter_upwards [scalar_regime 1,window_tendsto.eventually (eventually_ge_atTop M0)] with q hq hM0
  exact hM (window q) hM0 (q-1) 0 (by exact_mod_cast hq.1) (by exact_mod_cast hq.2.1) hq.2.2.1 hq.2.2.2.1 hq.2.2.2.2

/-- The witness only fixes primes through M+Q, avoiding a spurious factor two in its entropy. -/
theorem support_ratio : Tendsto (fun q ↦ (support q:ℝ)/(window q:ℝ)) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun q ↦ by positivity)) _
    (show Tendsto (fun q ↦ (betaMax+1)*(Real.log (window q)/(window q:ℝ))) atTop (𝓝 0) by
      simpa using log_div_window.const_mul (betaMax+1))
  filter_upwards [actual_geometry] with q hq
  have hs : (support q:ℝ)≤(betaMax+1)*Real.log (window q) := by
    have hh := hq.shifted_upper
    dsimp [support,excess]
    push_cast at hh ⊢
    linarith
  have hh := div_le_div_of_nonneg_right hs (show (0:ℝ)≤window q by positivity)
  convert hh using 1 <;> ring

/-- All original good sites have private pivots already in the minimal witness cylinder. -/
theorem original_geometry : ∀ᶠ q : ℕ in atTop,
    GoodGeometry (cylinder q) (primeCutoff (window q)) (q-1) (excess q)
      (StrongerDeletionTheorem.originalGood (window q) (q-1) 0) := by
  filter_upwards [actual_geometry] with q hq
  apply goodSites_geometry hq.length_pos
  · have := hq.strong_prime
    omega
  · have := hq.strong_prime
    dsimp [excess]
    omega
  · dsimp [cylinder,support]
    have := Nat.sub_le (window q) (q-1)
    omega

end
end PaperC.Prel8.PrimeWindowGeometry
