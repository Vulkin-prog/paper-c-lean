import PaperCPrel8.PrimeActivityAsymptotics
import PaperCPrel8.PrimeRetainedDensity

/-! # G.9's arithmetic obstruction for the named original and stronger good sets -/
namespace PaperC.Prel8.PrimeCumulantObstruction
open Finset Filter Topology PrimeWindowScales PrimeWindowErrors PrimeWindowIntensity
open PrimeWindowGeometry PrimeRetainedDensity PrimeActivityAsymptotics
open ArithmeticLowCategory ArithmeticLowMarginals MicroscopicFiniteLedger
open ConditionalStartProbability CategoricalCumulantBound CategoricalOccupancyEnvelope
open ArratiaGoldsteinGordonInput IndependentThinning V282.PrimeEulerPNT
noncomputable section

def actualActivity (q : ℕ) (G : Finset ℕ) : ℝ :=
  activity (FinitePMF.uniform (SampleSpace (cylinder q)))
    (retainedCategory (cylinder q) (q-1) (excess q) G)

/-- The paper's exact marginals are proved from good-site geometry on the minimal cylinder. -/
theorem good_subsets_obstruction (hPNT : PrimeNumberTheoremRemainder)
    (G : ℕ → Finset ℕ) (hG : ∀ q, G q⊆original q)
    (hD : Tendsto (fun q ↦ (((Icc 1 (window q))\G q).card:ℝ)*
      Real.log (window q)/(window q:ℝ)) atTop (𝓝 0))
    {epsilon : ℝ} (hepsilon : 0<epsilon) :
    ∀ᶠ q : ℕ in atTop, q.Prime → obstructionConstant-epsilon ≤
      Real.log (window q)/(window q:ℝ)*actualActivity q (G q) := by
  let r := fun q ↦ retainedRate (q-1) (excess q)
  have hcard (q : ℕ) : (G q).card≤window q := by
    have hc := card_le_card ((hG q).trans (original_subset q))
    simp only [Nat.card_Icc] at hc
    omega
  have hmean : ∀ᶠ q : ℕ in atTop, q.Prime → 0≤r q ∧ r q≤1/4 ∧
      ∀ i : G q, finitePMFExpectation (FinitePMF.uniform (SampleSpace (window q+support q)))
        (occupancy (retainedCategory (window q+support q) (q-1) (excess q) (G q)) i)=r q := by
    filter_upwards [original_geometry,eventually_ge_atTop 3] with q hq hq3 hp
    have hr := retainedRate_le_base (q-1) (excess q)
    refine ⟨hr.1,hr.2.trans (referenceRate_quarter hq3),?_⟩
    intro i
    exact occupancy_expectation (geometry_subset hq (hG q)) i
  have hB := marginal_error_tendsto (fun q ↦ (G q).card) r (Eventually.of_forall (fun q ↦
    ⟨hcard q,(retainedRate_le_base (q-1) (excess q)).1,(retainedRate_le_base (q-1) (excess q)).2⟩))
  exact arithmetic_obstruction hPNT support excess G r support_ratio hD hB hmean hepsilon

/-- The announced positive normalized lower limit for the original G0. -/
theorem original_obstruction (hPNT : PrimeNumberTheoremRemainder)
    {epsilon : ℝ} (hepsilon : 0<epsilon) :
    ∀ᶠ q : ℕ in atTop, q.Prime → obstructionConstant-epsilon ≤
      Real.log (window q)/(window q:ℝ)*actualActivity q (original q) :=
  good_subsets_obstruction hPNT original (fun _ ↦ Subset.refl _)
    (original_density hPNT) hepsilon

/-- The same leading constant for every fixed admissible stronger retained set. -/
theorem retained_obstruction (hPNT : PrimeNumberTheoremRemainder)
    {theta : ℝ} (htheta : 0≤theta) {epsilon : ℝ} (hepsilon : 0<epsilon) :
    ∀ᶠ q : ℕ in atTop, q.Prime → obstructionConstant-epsilon ≤
      Real.log (window q)/(window q:ℝ)*actualActivity q (retained q theta) :=
  good_subsets_obstruction hPNT (fun q ↦ retained q theta) (fun q ↦ retained_subset_original q theta)
    (retained_density hPNT htheta) hepsilon

end
end PaperC.Prel8.PrimeCumulantObstruction
