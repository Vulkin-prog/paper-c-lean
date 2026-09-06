import PaperCV282.MovingMarkedLevels
import PaperCV282.AllStartSoftPoisson
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Exact moving-level parameters and intensities

The floor and its phase are actual functions of N. Integer subtraction is
used only under d <= floor(log_2 N), so physical lengths are not silently
truncated. No critical-window assumption is imposed on the depth.
-/
namespace PaperC.V282.GrowingLevelParameters

open MovingMarkedLevels AllStartSoftPoisson Filter Topology

noncomputable section

def criticalBase (N : ℕ) : ℕ := ⌊Real.log N/Real.log 2⌋₊

def dyadicPhase (N : ℕ) : ℝ := Real.log N/Real.log 2-criticalBase N

def movingLength (N d : ℕ) : ℕ := criticalBase N-d

theorem phase_bounds {N : ℕ} (hN : 1 ≤ N) :
    0 ≤ dyadicPhase N ∧ dyadicPhase N < 1 := by
  have hlog : 0 ≤ Real.log (N : ℝ)/Real.log 2 := by
    apply div_nonneg
    · exact Real.log_nonneg (by exact_mod_cast hN)
    · exact le_of_lt (Real.log_pos (by norm_num))
  have hlo := Nat.floor_le hlog
  have hhi := Nat.lt_floor_add_one (Real.log (N : ℝ)/Real.log 2)
  change 0 ≤ Real.log N/Real.log 2-⌊Real.log N/Real.log 2⌋₊ ∧
    Real.log N/Real.log 2-⌊Real.log N/Real.log 2⌋₊ < 1
  constructor <;> linarith

theorem two_rpow_logRatio {N : ℕ} (hN : 1 ≤ N) :
    (2 : ℝ)^(Real.log N/Real.log 2) = N := by
  exact Real.rpow_logb (by norm_num) (by norm_num)
    (by exact_mod_cast (show 0 < N by omega))

theorem fullRate_eq_phase {N d : ℕ} (hN : 1 ≤ N) (hd : d ≤ criticalBase N) :
    (fullRate N (movingLength N d) : ℝ) = (2 : ℝ)^(dyadicPhase N+d) := by
  rw [fullRate_coe]
  conv_lhs => lhs; rw [← two_rpow_logRatio hN]
  rw [← Real.rpow_natCast,← Real.rpow_sub (by norm_num : (0 : ℝ)<2)]
  congr 1
  unfold dyadicPhase movingLength
  rw [Nat.cast_sub hd]
  ring

/-- The target level mean is independent of how its excess is written. -/
theorem exact_level_mean {N d : ℕ} (hN : 1 ≤ N) (hd : d ≤ criticalBase N) (e : ℕ) :
    (fullRate N (movingLength N d) : ℝ)/(2 : ℝ)^(e+1) =
      (2 : ℝ)^(dyadicPhase N-((levelEquiv d e).val : ℝ)-1) := by
  rw [fullRate_eq_phase hN hd,← Real.rpow_natCast,
    ← Real.rpow_sub (by norm_num : (0 : ℝ)<2)]
  congr 1
  rw [levelEquiv_val]
  push_cast
  ring

theorem signed_level_mean {N d : ℕ} (hN : 1 ≤ N) (hd : d ≤ criticalBase N) (e : ℕ) :
    (fullRate N (movingLength N d) : ℝ)/(2 : ℝ)^(e+2) =
      (2 : ℝ)^(dyadicPhase N-((levelEquiv d e).val : ℝ)-2) := by
  rw [fullRate_eq_phase hN hd,← Real.rpow_natCast,
    ← Real.rpow_sub (by norm_num : (0 : ℝ)<2)]
  congr 1
  rw [levelEquiv_val]
  push_cast
  ring

/-- The labelled spatial atom has mean 2^(-b-r-1). -/
theorem exact_site_mean {N d : ℕ} (hd : d ≤ criticalBase N) (e : ℕ) :
    (1 : ℝ)/(2 : ℝ)^(movingLength N d+e+1) =
      (2 : ℝ)^(-(criticalBase N : ℝ)-((levelEquiv d e).val : ℝ)-1) := by
  rw [one_div,← Real.rpow_natCast,← Real.rpow_neg (by norm_num : (0 : ℝ)≤2)]
  congr 1
  rw [levelEquiv_val]
  unfold movingLength
  push_cast
  rw [Nat.cast_sub hd]
  ring

theorem signed_site_mean {N d : ℕ} (hd : d ≤ criticalBase N) (e : ℕ) :
    (1 : ℝ)/(2 : ℝ)^(movingLength N d+e+2) =
      (2 : ℝ)^(-(criticalBase N : ℝ)-((levelEquiv d e).val : ℝ)-2) := by
  rw [one_div,← Real.rpow_natCast,← Real.rpow_neg (by norm_num : (0 : ℝ)≤2)]
  congr 1
  rw [levelEquiv_val]
  unfold movingLength
  push_cast
  rw [Nat.cast_sub hd]
  ring

/-- In particular depth zero has intensity in [1,2), with no limit assumed for the phase. -/
theorem fullRate_depth_bounds {N d : ℕ} (hN : 1 ≤ N) (hd : d ≤ criticalBase N) :
    (2 : ℝ)^d ≤ (fullRate N (movingLength N d) : ℝ) ∧
      (fullRate N (movingLength N d) : ℝ) < 2*(2 : ℝ)^d := by
  rw [fullRate_eq_phase hN hd]
  obtain ⟨hlo,hhi⟩ := phase_bounds hN
  constructor
  · rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  · have h := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ)<2)
      (show dyadicPhase N+d < (d : ℝ)+1 by linarith)
    simpa [Real.rpow_add (by norm_num : (0 : ℝ)<2),Real.rpow_natCast,mul_comm] using h

/-- A finite explicit depth bound yields the subpolynomial intensity budget. -/
theorem fullRate_le_rpow_of_depth_bound {N d : ℕ} (hN : 1 ≤ N)
    (hd : d ≤ criticalBase N) (epsilon : ℝ)
    (hdepth : ((d : ℝ)+1)*Real.log 2 ≤ epsilon*Real.log N) :
    (fullRate N (movingLength N d) : ℝ) ≤ (N : ℝ)^epsilon := by
  have hupper := (fullRate_depth_bounds hN hd).2.le
  have hNpos : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hp : 2*(2 : ℝ)^d = (2 : ℝ)^((d : ℝ)+1) := by
    rw [Real.rpow_add (by norm_num : (0 : ℝ)<2),Real.rpow_natCast,Real.rpow_one,mul_comm]
  rw [hp] at hupper
  apply hupper.trans
  rw [← Real.log_le_log_iff (Real.rpow_pos_of_pos (by norm_num) _) (Real.rpow_pos_of_pos hNpos _)]
  simpa only [Real.log_rpow (by norm_num : (0 : ℝ)<2),Real.log_rpow hNpos] using hdepth


/-- The literal assumption d_N=o(log N) gives a common eventual arithmetic domain
and a subpolynomial intensity. The depth is not restricted to be bounded. -/
theorem growing_intensity_eventually (d : ℕ → ℕ)
    (hd : Tendsto (fun N : ℕ => (d N : ℝ)/Real.log N) atTop (𝓝 0))
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero,
      d N+1 ≤ criticalBase N ∧ 1 ≤ movingLength N (d N) ∧
      (fullRate N (movingLength N (d N)) : ℝ) ≤ (N : ℝ)^epsilon := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hplus : Tendsto (fun N : ℕ => ((d N : ℝ)+1)/Real.log N) atTop (𝓝 0) := by
    simpa only [add_div,add_zero] using hd.add ((tendsto_const_nhds (x := (1 : ℝ))).div_atTop hlog)
  have htwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  let a := min (epsilon/Real.log 2) (1/Real.log 2)
  have ha : 0<a := lt_min (div_pos hepsilon htwo) (div_pos (by norm_num) htwo)
  obtain ⟨Nzero,hzero⟩ := eventually_atTop.mp (hplus.eventually (gt_mem_nhds ha))
  refine ⟨max Nzero 2,?_⟩
  intro N hN
  have hn : 2 ≤ N := by omega
  have hln : 0<Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hh := hzero N (by omega)
  have hbase : ((d N : ℝ)+1) ≤ Real.log N/Real.log 2 := by
    have h := hh.trans_le (min_le_right _ _)
    have h' := (div_lt_iff₀ hln).mp h
    simpa only [one_div,mul_comm,div_eq_mul_inv,one_mul] using h'.le
  have hb : d N+1 ≤ criticalBase N := by
    unfold criticalBase
    apply (Nat.le_floor_iff (div_nonneg hln.le htwo.le)).mpr
    simpa only [Nat.cast_add,Nat.cast_one] using hbase
  refine ⟨hb,by unfold movingLength; omega,?_⟩
  apply fullRate_le_rpow_of_depth_bound (by omega) (by omega) epsilon
  have h := hh.trans_le (min_le_left _ _)
  have h' := (div_lt_iff₀ hln).mp h
  have h'' := mul_lt_mul_of_pos_right h' htwo
  have heq : (epsilon/Real.log 2*Real.log N)*Real.log 2 = epsilon*Real.log N := by
    field_simp
  rw [heq] at h''
  exact h''.le


/-- Moving depths o(log N) preserve the full logarithmic length scale. -/
theorem moving_length_div_log_tendsto (d : ℕ → ℕ)
    (hd : Tendsto (fun N : ℕ => (d N : ℝ)/Real.log N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => ((movingLength N (d N) : ℝ)+1)/Real.log N)
      atTop (𝓝 (1/Real.log 2)) := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hone : Tendsto (fun N : ℕ => (1 : ℝ)/Real.log N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  have hphase : Tendsto (fun N : ℕ => dyadicPhase N/Real.log N) atTop (𝓝 0) := by
    apply squeeze_zero' _ _ hone
    · filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
      exact div_nonneg (phase_bounds (by omega)).1
        (Real.log_nonneg (by exact_mod_cast (show 1≤N by omega)))
    · filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
      exact div_le_div_of_nonneg_right (phase_bounds (by omega)).2.le
        (Real.log_nonneg (by exact_mod_cast (show 1≤N by omega)))
  have hbase : Tendsto (fun N : ℕ => (criticalBase N : ℝ)/Real.log N)
      atTop (𝓝 (1/Real.log 2)) := by
    have h := (tendsto_const_nhds (x := 1/Real.log 2)).sub hphase
    simp only [sub_zero] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
    have hn : Real.log (N : ℝ)≠0 := (Real.log_pos (by exact_mod_cast (show 1<N by omega))).ne'
    unfold dyadicPhase
    field_simp
    ring
  have h := (hbase.sub hd).add hone
  simp only [sub_zero,add_zero] at h
  obtain ⟨Nzero,hzero⟩ := growing_intensity_eventually d hd 1 (by norm_num)
  apply h.congr'
  filter_upwards [eventually_ge_atTop Nzero] with N hN
  have hdep : d N≤criticalBase N := by have hh := (hzero N hN).1;omega
  unfold movingLength
  rw [Nat.cast_sub hdep]
  ring

/-- Every fixed band straddling log_2 N eventually covers the actual moving length. -/
theorem growing_length_band_eventually (d : ℕ → ℕ)
    (hd : Tendsto (fun N : ℕ => (d N : ℝ)/Real.log N) atTop (𝓝 0))
    (betaMin betaMax : ℝ) (hmin : betaMin<1/Real.log 2) (hmax : 1/Real.log 2<betaMax) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero,
      betaMin*Real.log N ≤ (movingLength N (d N) : ℝ)+1 ∧
      (movingLength N (d N) : ℝ)+1 ≤ betaMax*Real.log N := by
  have hlim := moving_length_div_log_tendsto d hd
  obtain ⟨Nlo,hlo⟩ := eventually_atTop.mp (hlim.eventually (lt_mem_nhds hmin))
  obtain ⟨Nhi,hhi⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hmax))
  refine ⟨max 2 (max Nlo Nhi),?_⟩
  intro N hN
  have hn : 0<Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1<N by omega))
  exact ⟨((lt_div_iff₀ hn).mp (hlo N (by omega))).le,
    ((div_lt_iff₀ hn).mp (hhi N (by omega))).le⟩

end
end PaperC.V282.GrowingLevelParameters
