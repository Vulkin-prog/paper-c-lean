import PaperCPrel8.ArithmeticLowCategory

/-! # A simpler finite lower bound for the prime witness

The occupancy ratio is at least three; no asymptotic expansion of its logarithm
is needed. The only loss from the empty-site factors is four times the mean mass.
-/
namespace PaperC.Prel8.PrimeActivityLower
open Finset ArithmeticLowCategory PrimeWitnessRetention ConditionalStartProbability
open CategoricalOccupancyEnvelope CategoricalCumulantBound ArratiaGoldsteinGordonInput IndependentThinning
noncomputable section

theorem baseline_log_lower {r : ℝ} (hr : 0 ≤ r) (hrq : r ≤ 1/4) :
    -4*r ≤ Real.log (1-2*r) := by
  have ha : 0 < 1-2*r := by linarith
  have hh := Real.one_sub_inv_le_log_of_pos ha
  have hi : (1-2*r)⁻¹ ≤ 1+4*r := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ ha).mpr
    nlinarith
  linarith

theorem occupied_log_lower {r : ℝ} (hr : 0 ≤ r) (hrq : r < 1/2) :
    Real.log 3 ≤ Real.log ((3-2*r)/(1-2*r)) := by
  apply Real.log_le_log (by norm_num)
  apply (le_div_iff₀ (by linarith : 0 < 1-2*r)).mpr
  linarith

/-- The exact original arithmetic activity, with a linear mean-mass error. -/
theorem arithmetic_linear_lower {C q M E : ℕ} (hq : q.Prime) (p : PrimeUpTo C) (hp : p.val.val=q)
    (G : Finset ℕ) {r : ℝ} (hr : 0 ≤ r) (hrq : r ≤ 1/4)
    (hmean : ∀ i : G, finitePMFExpectation (FinitePMF.uniform (SampleSpace C))
      (occupancy (retainedCategory C (q-1) E G) i)=r) :
    ((((certifiedSites q M).card-((Icc 1 M)\G).card:ℕ):ℝ)*Real.log 3-
      (Nat.primeCounting C:ℝ)*Real.log 2-4*(G.card:ℝ)*r)/2 ≤
        activity (FinitePMF.uniform (SampleSpace C)) (retainedCategory C (q-1) E G) := by
  have hh := arithmetic_activity_lower (M:=M) hq p hp G (by linarith) hmean
  have hb := mul_le_mul_of_nonneg_left (baseline_log_lower hr hrq)
    (show (0:ℝ) ≤ G.card by positivity)
  have ho := mul_le_mul_of_nonneg_left (occupied_log_lower hr (by linarith))
    (show (0:ℝ) ≤ (((certifiedSites q M).card-((Icc 1 M)\G).card:ℕ):ℝ) by positivity)
  linarith

end
end PaperC.Prel8.PrimeActivityLower
