import PaperCV282.GrowingLevelParameters
import PaperC.Probability.CriticalRunWindow
import Mathlib.Topology.Algebra.Order.Floor

/-! # The genuine moving extreme threshold is a bounded critical shift -/
namespace PaperC.V282.D4ClosureExtremeParameters

open Real Filter Topology AllStartSoftPoisson CriticalRunWindow

noncomputable section

def intensityLog (N L : ℕ) : ℝ := log (fullRate N L : ℝ)/log 2

def intensityPhase (N L : ℕ) : ℝ := Int.fract (intensityLog N L)

def extremeThreshold (N L : ℕ) (j : ℤ) : ℕ := (⌊intensityLog N L⌋+j).toNat

theorem intensityLog_eq {N : ℕ} (hN : 0<N) (L : ℕ) :
    intensityLog N L=log N/log 2-(L : ℝ) := by
  have hn : (0 : ℝ)<N := by exact_mod_cast hN
  unfold intensityLog
  rw [fullRate_coe,log_div hn.ne' (by positivity),log_pow]
  have htwo : log (2 : ℝ)≠0 := (log_pos (by norm_num)).ne'
  field_simp

theorem extremeThreshold_cast {N L : ℕ} {j : ℤ}
    (hj : 0≤⌊intensityLog N L⌋+j) :
    (extremeThreshold N L j : ℝ)=intensityLog N L-intensityPhase N L+(j : ℝ) := by
  have hnat : (extremeThreshold N L j : ℤ)=⌊intensityLog N L⌋+j := by
    exact Int.toNat_of_nonneg hj
  have hr := congrArg (fun z : ℤ => (z : ℝ)) hnat
  push_cast at hr
  rw [hr]
  unfold intensityPhase Int.fract
  ring

/-- Exact cancellation of the arbitrary base length in the critical window. -/
theorem shifted_length_in_window {N L : ℕ} (hN : 0<N) (j : ℤ)
    (hj : 0≤⌊intensityLog N L⌋+j) :
    InRunLengthWindow (|(j : ℝ)|+2) N (L+extremeThreshold N L j+1) := by
  have hphase0 := Int.fract_nonneg (intensityLog N L)
  have hphase1 := Int.fract_lt_one (intensityLog N L)
  have hs := extremeThreshold_cast hj
  rw [intensityLog_eq hN L] at hs
  unfold InRunLengthWindow
  push_cast
  rw [hs]
  change |(L : ℝ)+(log N/log 2-(L : ℝ)-intensityPhase N L+(j : ℝ))+1-log N/log 2|≤_
  unfold intensityPhase
  apply abs_le.mpr
  constructor <;> linarith [le_abs_self (j : ℝ),neg_abs_le (j : ℝ)]

/-- The target intensity at the longer-start threshold is exactly the phase formula. -/
theorem shifted_rate_eq_phase {N L : ℕ} (hN : 0<N) (j : ℤ)
    (hj : 0≤⌊intensityLog N L⌋+j) :
    (fullRate N (L+extremeThreshold N L j+1) : ℝ)=
      (2 : ℝ)^(intensityPhase N L-(j : ℝ)-1) := by
  have hr : 0<(fullRate N L : ℝ) := by rw [fullRate_coe];positivity
  have hbase : (fullRate N L : ℝ)=(2 : ℝ)^(intensityLog N L) :=
    (Real.rpow_logb (by norm_num) (by norm_num) hr).symm
  have hsplit : (fullRate N (L+extremeThreshold N L j+1) : ℝ)=
      (fullRate N L : ℝ)/(2 : ℝ)^(extremeThreshold N L j+1) := by
    simp only [fullRate_coe,pow_add,pow_one]
    ring
  rw [hsplit,hbase,← Real.rpow_natCast,← Real.rpow_sub (by norm_num : (0 : ℝ)<2)]
  congr 1
  push_cast
  rw [extremeThreshold_cast hj]
  ring

/-- Positive base intensity tending to infinity makes the natural threshold conversion exact. -/
theorem threshold_nonnegative_eventually (sizes lengths : ℕ→ℕ)
    (hrate : Tendsto (fun k => (fullRate (sizes k) (lengths k) : ℝ)) atTop atTop) (j : ℤ) :
    ∀ᶠ k in atTop, 0≤⌊intensityLog (sizes k) (lengths k)⌋+j := by
  have hlog := (tendsto_log_atTop.comp hrate).atTop_div_const (log_pos (by norm_num : (1 : ℝ)<2))
  have hf := (tendsto_floor_atTop.comp hlog).eventually (eventually_ge_atTop (-j))
  exact hf.mono fun k hk => by change -j≤⌊intensityLog (sizes k) (lengths k)⌋ at hk;omega

/-- The phase can converge along arbitrary subsequences, including either endpoint of [0,1]. -/
theorem shifted_rate_tendsto (sizes lengths : ℕ→ℕ) (theta : ℝ) (j : ℤ)
    (hsizes : Tendsto sizes atTop atTop)
    (hrate : Tendsto (fun k => (fullRate (sizes k) (lengths k) : ℝ)) atTop atTop)
    (hphase : Tendsto (fun k => intensityPhase (sizes k) (lengths k)) atTop (𝓝 theta)) :
    Tendsto (fun k => (fullRate (sizes k)
      (lengths k+extremeThreshold (sizes k) (lengths k) j+1) : ℝ))
      atTop (𝓝 ((2 : ℝ)^(theta-(j : ℝ)-1))) := by
  have hc : Continuous (fun x : ℝ => (2 : ℝ)^(x-(j : ℝ)-1)) := by fun_prop (disch := norm_num)
  apply (hc.continuousAt.tendsto.comp hphase).congr'
  filter_upwards [hsizes.eventually (eventually_ge_atTop (1 : ℕ)),
    threshold_nonnegative_eventually sizes lengths hrate j] with k hN hj
  exact (shifted_rate_eq_phase (by omega) j hj).symm

end
end PaperC.V282.D4ClosureExtremeParameters
