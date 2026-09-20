import PaperCPrel8.PrimeCumulantObstruction

/-! # Divergence on every sequence of primes tending to infinity -/
namespace PaperC.Prel8.PrimeActivityDivergence
open Filter Topology PrimeWindowScales PrimeWindowErrors PrimeWindowBudget
open PrimeRetainedDensity PrimeCumulantObstruction V282.PrimeEulerPNT
noncomputable section

theorem inverse_normalization_atTop :
    Tendsto (fun q ↦ (window q:ℝ)/Real.log (window q)) atTop atTop := by
  have hpos : ∀ᶠ q : ℕ in atTop, 0<Real.log (window q)/(window q:ℝ) := by
    filter_upwards [log_window_atTop.eventually (eventually_gt_atTop (0:ℝ))] with q hq
    exact div_pos hq (by exact_mod_cast window_pos q)
  have hh : Tendsto (fun q ↦ Real.log (window q)/(window q:ℝ)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨log_div_window,hpos⟩
  apply hh.inv_tendsto_nhdsGT_zero.congr
  intro q
  change (Real.log (window q)/(window q:ℝ))⁻¹=_
  rw [inv_div]

/-- A positive normalized lower limit forces the original (unscaled) activity to infinity. -/
theorem of_normalized_lower (K : ℕ → ℝ)
    (hK : ∀ᶠ q : ℕ in atTop, q.Prime → obstructionConstant/2≤
      Real.log (window q)/(window q:ℝ)*K q)
    (qs : ℕ → ℕ) (hqs : Tendsto qs atTop atTop) (hp : ∀ᶠ n in atTop, (qs n).Prime) :
    Tendsto (fun n ↦ K (qs n)) atTop atTop := by
  have hg := (inverse_normalization_atTop.const_mul_atTop
    (show 0<obstructionConstant/2 from div_pos obstructionConstant_pos (by norm_num))).comp hqs
  apply tendsto_atTop_mono' atTop _ hg
  filter_upwards [hqs.eventually hK,hp,
    hqs.eventually (log_window_atTop.eventually (eventually_gt_atTop (0:ℝ)))] with n hn hp hlog
  have hw : (0:ℝ)<window (qs n) := by exact_mod_cast window_pos (qs n)
  have hh := (div_le_iff₀ (div_pos hlog hw)).mpr (by simpa only [mul_comm] using hn hp)
  convert hh using 1
  dsimp only [Function.comp_def]
  field_simp

theorem original_diverges (hPNT : PrimeNumberTheoremRemainder)
    (qs : ℕ → ℕ) (hqs : Tendsto qs atTop atTop) (hp : ∀ᶠ n in atTop, (qs n).Prime) :
    Tendsto (fun n ↦ actualActivity (qs n) (original (qs n))) atTop atTop := by
  have hh := original_obstruction hPNT (epsilon:=obstructionConstant/2) (div_pos obstructionConstant_pos (by norm_num))
  have he : obstructionConstant-obstructionConstant/2=obstructionConstant/2 := by ring
  rw [he] at hh
  exact of_normalized_lower _ hh qs hqs hp

theorem retained_diverges (hPNT : PrimeNumberTheoremRemainder) {theta : ℝ} (htheta : 0≤theta)
    (qs : ℕ → ℕ) (hqs : Tendsto qs atTop atTop) (hp : ∀ᶠ n in atTop, (qs n).Prime) :
    Tendsto (fun n ↦ actualActivity (qs n) (retained (qs n) theta)) atTop atTop := by
  have hh := retained_obstruction hPNT htheta (epsilon:=obstructionConstant/2) (div_pos obstructionConstant_pos (by norm_num))
  have he : obstructionConstant-obstructionConstant/2=obstructionConstant/2 := by ring
  rw [he] at hh
  exact of_normalized_lower _ hh qs hqs hp

end
end PaperC.Prel8.PrimeActivityDivergence
