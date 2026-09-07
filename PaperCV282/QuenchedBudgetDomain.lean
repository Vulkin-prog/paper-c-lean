import PaperCV282.QuenchedAggregateTheorem
import PaperCV282.SaddleCutoffAdmissibility

/-!
# The printed quenched budget supplies its own moving-level domain

The intensity budget rules out truncated lengths and forces the depth to be
o(log N). Thus Corollary 6.4 does not need that extra hypothesis.
-/
namespace PaperC.V282.QuenchedBudgetDomain

open MeasureTheory Filter Topology GrowingLevelParameters AllStartSoftPoisson
open SaddleParameters SaddleScales SaddleCutoffAdmissibility
open GeometricSaddleSummability GeometricScaleInstances QuenchedAggregateTheorem
open InfiniteRademacher DirectionalSteinInput PrimeEulerPNT

noncomputable section

/-- A sub-logarithmic upper budget for log intensity rules out natural-subtraction truncation. -/
theorem depth_le_base_eventually_of_log_budget (sizes depths : ℕ → ℕ)
    (hsizes : Tendsto sizes atTop atTop) (w : ℕ → ℝ)
    (hw : Tendsto (fun k => w k / Real.log (sizes k)) atTop (𝓝 0))
    (hbudget : ∀ᶠ k in atTop,
      Real.log (fullRate (sizes k) (movingLength (sizes k) (depths k))) ≤ w k) :
    ∀ᶠ k in atTop, depths k ≤ criticalBase (sizes k) := by
  filter_upwards [hsizes.eventually (eventually_ge_atTop (2 : ℕ)), hbudget,
    hw.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with k hN hb hwk
  have hlog : 0 < Real.log (sizes k : ℝ) := Real.log_pos (by exact_mod_cast hN)
  have hwlt : w k < Real.log (sizes k) := (div_lt_one hlog).mp hwk
  by_contra hd
  have hzero : movingLength (sizes k) (depths k) = 0 := by
    unfold movingLength
    exact Nat.sub_eq_zero_of_le (by omega)
  rw [hzero, fullRate_coe] at hb
  norm_num at hb
  linarith

/-- The same budget bounds the actual depth, including the dyadic phase. -/
theorem depth_div_log_tendsto_zero_of_log_budget (sizes depths : ℕ → ℕ)
    (hsizes : Tendsto sizes atTop atTop) (w : ℕ → ℝ)
    (hw : Tendsto (fun k => w k / Real.log (sizes k)) atTop (𝓝 0))
    (hbudget : ∀ᶠ k in atTop,
      Real.log (fullRate (sizes k) (movingLength (sizes k) (depths k))) ≤ w k) :
    Tendsto (fun k => (depths k : ℝ) / Real.log (sizes k)) atTop (𝓝 0) := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hupper : Tendsto (fun k => (w k / Real.log (sizes k)) / Real.log 2)
      atTop (𝓝 0) := by simpa using hw.div_const (Real.log 2)
  apply squeeze_zero' _ _ hupper
  · filter_upwards [hsizes.eventually (eventually_ge_atTop (2 : ℕ))] with k hN
    exact div_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast (show 1 ≤ sizes k by omega)))
  · filter_upwards [depth_le_base_eventually_of_log_budget sizes depths hsizes w hw hbudget,
      hsizes.eventually (eventually_ge_atTop (2 : ℕ)), hbudget] with k hd hN hb
    have hlog : 0 < Real.log (sizes k : ℝ) := Real.log_pos (by exact_mod_cast hN)
    rw [fullRate_eq_phase (by omega) hd, Real.log_rpow (by norm_num : (0 : ℝ) < 2)] at hb
    have hp := (phase_bounds (by omega : 1 ≤ sizes k)).1
    have hdw : (depths k : ℝ) * Real.log 2 ≤ w k := by nlinarith
    apply (le_div_iff₀ hlog2).mpr
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right hdw hlog.le

/-- Every fixed positive saddle budget forces the printed moving-level regime. -/
theorem depth_div_log_tendsto_zero_of_saddle_budget (sizes depths : ℕ → ℕ)
    (hsizes : Tendsto sizes atTop atTop) (a c : ℝ) (ha : 0 < a) (hc : 0 ≤ c)
    (hbudget : ∀ᶠ k in atTop,
      Real.log (fullRate (sizes k) (movingLength (sizes k) (depths k))) ≤
        saddleCutoff a (Real.log (sizes k)) - c * saddleNu a (Real.log (sizes k))) :
    Tendsto (fun k => (depths k : ℝ) / Real.log (sizes k)) atTop (𝓝 0) := by
  have hheight : Tendsto (fun k => Real.log (sizes k : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hsizes)
  apply depth_div_log_tendsto_zero_of_log_budget sizes depths hsizes
    (fun k => saddleCutoff a (Real.log (sizes k)))
    ((tendsto_saddleCutoff_div_height ha).comp hheight)
  filter_upwards [hbudget, ((tendsto_saddleNu_atTop ha).comp hheight).eventually
    (eventually_ge_atTop (0 : ℝ))] with k hb hnu
  exact hb.trans (sub_le_self _ (mul_nonneg hc hnu))

/-- The printed budget alone supplies the moving-depth domain in Corollary 6.4. -/
theorem corollary_six_four_signed (hStein : DirectionalSteinFactorsStatement)
    (hPNT : PrimeNumberTheoremRemainder) (sizes depths : ℕ → ℕ)
    (hg : GeometricLowerGrowth sizes)
    (c beta : ℝ) (hbeta : 0<beta) (hcb : beta<c)
    (hbudget : ∀ᶠ k in atTop, Real.log (fullRate (sizes k) (movingLength (sizes k) (depths k)))≤
      saddleCutoff 1 (Real.log (sizes k))-c*saddleNu 1 (Real.log (sizes k))) :
    ∀ᵐ omega ∂infiniteRademacherMeasure, ∀ᶠ k in atTop,
      quenchedSignedAggregateDistance (sizes k) (movingLength (sizes k) (depths k)) omega ≤
        Real.exp (-beta*saddleNu 1 (Real.log (sizes k))) := by
  have hdepths := depth_div_log_tendsto_zero_of_saddle_budget sizes depths
    (sizes_tendsto_atTop hg) 1 c (by norm_num) (by linarith) hbudget
  exact QuenchedAggregateTheorem.corollary_six_four_signed hStein hPNT sizes depths hg hdepths c beta hbeta hcb hbudget

/-- The printed budget alone supplies the moving-depth domain in Corollary 6.4. -/
theorem corollary_six_four (hStein : DirectionalSteinFactorsStatement)
    (hPNT : PrimeNumberTheoremRemainder) (sizes depths : ℕ → ℕ)
    (hg : GeometricLowerGrowth sizes)
    (c beta : ℝ) (hbeta : 0<beta) (hcb : beta<c)
    (hbudget : ∀ᶠ k in atTop, Real.log (fullRate (sizes k) (movingLength (sizes k) (depths k)))≤
      saddleCutoff 1 (Real.log (sizes k))-c*saddleNu 1 (Real.log (sizes k))) :
    ∀ᵐ omega ∂infiniteRademacherMeasure, ∀ᶠ k in atTop,
      quenchedThresholdDistance (sizes k) (movingLength (sizes k) (depths k)) omega ≤
        Real.exp (-beta*saddleNu 1 (Real.log (sizes k))) ∧
      quenchedUnsignedAggregateDistance (sizes k) (movingLength (sizes k) (depths k)) omega ≤
        Real.exp (-beta*saddleNu 1 (Real.log (sizes k))) := by
  have hdepths := depth_div_log_tendsto_zero_of_saddle_budget sizes depths
    (sizes_tendsto_atTop hg) 1 c (by norm_num) (by linarith) hbudget
  exact QuenchedAggregateTheorem.corollary_six_four hStein hPNT sizes depths hg hdepths c beta hbeta hcb hbudget

/-- The printed budget alone supplies the moving-depth domain in Corollary 6.4. -/
theorem corollary_six_four_geometric (hStein : DirectionalSteinFactorsStatement)
    (hPNT : PrimeNumberTheoremRemainder) (sizes depths : ℕ → ℕ)
    (q D : ℝ) (hq : 1<q) (hD : 0<D)
    (hscale : ∀ᶠ k : ℕ in atTop, D*q^k≤(sizes k : ℝ))
    (c beta : ℝ) (hbeta : 0<beta) (hcb : beta<c)
    (hbudget : ∀ᶠ k in atTop, Real.log (fullRate (sizes k) (movingLength (sizes k) (depths k)))≤
      saddleCutoff 1 (Real.log (sizes k))-c*saddleNu 1 (Real.log (sizes k))) :
    ∀ᵐ omega ∂infiniteRademacherMeasure, ∀ᶠ k in atTop,
      quenchedThresholdDistance (sizes k) (movingLength (sizes k) (depths k)) omega ≤
        Real.exp (-beta*saddleNu 1 (Real.log (sizes k))) ∧
      quenchedUnsignedAggregateDistance (sizes k) (movingLength (sizes k) (depths k)) omega ≤
        Real.exp (-beta*saddleNu 1 (Real.log (sizes k))) := by
  have hdepths := depth_div_log_tendsto_zero_of_saddle_budget sizes depths
    (sizes_tendsto_atTop (geometricLowerGrowth_of_geometric_lower_bound sizes q D hq hD hscale)) 1 c (by norm_num) (by linarith) hbudget
  exact QuenchedAggregateTheorem.corollary_six_four_geometric hStein hPNT sizes depths q D hq hD hscale hdepths c beta hbeta hcb hbudget

end
end PaperC.V282.QuenchedBudgetDomain
