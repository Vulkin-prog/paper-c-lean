import PaperCPrel8.RegularCloudSaddle

/-! # The literal rounded conditioning cutoff and count cutoff in G.3 -/
namespace PaperC.Prel8.RegularCloudCutoff
open Filter Topology V282.SaddleParameters V282.SaddleScales RegularCloudSaddle RoughKernelThreshold
noncomputable section

/-- Rounding exp(V) loses at most log 2 in the logarithmic cutoff, for exp(V)>=2. -/
theorem log_floor_exp_bounds (V : ℝ) (hV : Real.log 2≤V) :
    0<(⌊Real.exp V⌋₊:ℝ) ∧ V-Real.log 2≤Real.log (⌊Real.exp V⌋₊:ℝ) ∧
      Real.log (⌊Real.exp V⌋₊:ℝ)≤V := by
  have he : (2:ℝ)≤Real.exp V := by
    simpa only [Real.exp_log (by norm_num : (0:ℝ)<2)] using Real.exp_le_exp.mpr hV
  have hf := Nat.lt_floor_add_one (Real.exp V)
  have hp : 0<(⌊Real.exp V⌋₊:ℝ) := by linarith
  have hhalf : Real.exp V/2≤(⌊Real.exp V⌋₊:ℝ) := by linarith
  refine ⟨hp,?_,?_⟩
  · have h := Real.log_le_log (by positivity : 0<Real.exp V/2) hhalf
    simpa [Real.log_div,Real.log_exp] using h
  · simpa using Real.log_le_log hp (Nat.floor_le (Real.exp_pos V).le)

/-- Exact ceiling control at every intensity >=1. -/
theorem ceil_twice_le (rate : ℝ) (hrate : 1≤rate) :
    1≤(⌈2*rate⌉₊:ℝ) ∧ (⌈2*rate⌉₊:ℝ)≤3*rate := by
  have hlo := Nat.le_ceil (2*rate)
  have hhi := Nat.ceil_lt_add_one (show 0≤2*rate by linarith)
  constructor <;> linarith

/-- The information margin pays the rounded logarithmic CRT gap uniformly
before the intensity and maximal support size are chosen. -/
theorem cutoff_gap_eventually (c B : ℝ) (hc : 0<c) (hB : 0<B) :
    ∀ᶠ H : ℝ in atTop, ∀ rate : ℝ, ∀ Q : ℕ,
      1≤rate → (Q+1:ℝ)≤B*H → Real.log rate≤saddleCutoff 1 H-c*saddleNu 1 H →
      3*(⌈2*rate⌉₊:ℝ)*(Q+1)<(⌊Real.exp (saddleCutoff 1 H)⌋₊:ℝ) ∧
      c*saddleNu 1 H/(2*saddleCutoff 1 H)≤
        1-Real.log (3*(⌈2*rate⌉₊:ℝ)*(Q+1))/Real.log (⌊Real.exp (saddleCutoff 1 H)⌋₊:ℝ) := by
  have hnu := tendsto_saddleNu_atTop (by norm_num : (0:ℝ)<1)
  have hov : Tendsto (fun H ↦ (Real.log (18*B)+Real.log H)/saddleNu 1 H) atTop (𝓝 0) := by
    simpa [add_div] using ((tendsto_const_nhds (x := Real.log (18*B))).div_atTop hnu).add
      (tendsto_log_div_saddleNu (by norm_num : (0:ℝ)<1))
  filter_upwards [eventually_ge_atTop (saddleThreshold 1),eventually_gt_atTop (0:ℝ),
    (V282.PrimeEulerSaddle.tendsto_saddleCutoff_atTop (by norm_num : (0:ℝ)<1)).eventually
      (eventually_gt_atTop (Real.log 2)),
    hov.eventually (gt_mem_nhds (show 0<c/2 by positivity))] with H hH hHp hV hover
  intro rate Q hr hQ hbudget
  let V := saddleCutoff 1 H
  let nu := saddleNu 1 H
  let Y : ℝ := ⌊Real.exp V⌋₊
  let z : ℝ := 3*(⌈2*rate⌉₊:ℝ)*(Q+1)
  have hVp : 0<V := saddleCutoff_pos (by norm_num) hH
  have hnup : 0<nu := div_pos hHp hVp
  have hrp : 0<rate := by linarith
  obtain ⟨hKlo,hKhi⟩ := ceil_twice_le rate hr
  have hzp : 0<z := by dsimp [z]; positivity
  obtain ⟨hYp,hYlo,hYhi⟩ := log_floor_exp_bounds V hV.le
  have hlogY : 0<Real.log Y := by dsimp [Y]; linarith
  have hzbound : z≤9*B*rate*H := by
    have hq0 : (0:ℝ)<Q+1 := by positivity
    have ht := mul_le_mul hKhi hQ (by positivity) (by positivity : 0≤3*rate)
    dsimp [z]
    nlinarith
  have hlz := Real.log_le_log hzp hzbound
  have hlogprod : Real.log (9*B*rate*H) = Real.log rate+Real.log (9*B)+Real.log H := by
    rw [Real.log_mul (by positivity : 9*B*rate≠0) hHp.ne',Real.log_mul (by positivity : 9*B≠0) hrp.ne']
    ring
  rw [hlogprod] at hlz
  have hover' := (div_lt_iff₀ hnup).mp hover
  have h18 : Real.log (18*B)=Real.log (9*B)+Real.log 2 := by
    rw [show 18*B=9*B*2 by ring,Real.log_mul (by positivity : 9*B≠0) (by norm_num : (2:ℝ)≠0)]
  rw [h18] at hover'
  have hgap : c*nu/2≤Real.log Y-Real.log z := by dsimp only [Y] at *; linarith
  have hlogs : Real.log z<Real.log Y := by nlinarith
  have hsmall : z<Y := (Real.log_lt_log_iff hzp hYp).mp hlogs
  refine ⟨hsmall,?_⟩
  have hd := div_le_div_of_nonneg_left (show 0≤c*nu/2 by positivity) hlogY hYhi
  have he := div_le_div_of_nonneg_right hgap hlogY.le
  calc
    c*nu/(2*V) = (c*nu/2)/V := by ring
    _ ≤ (c*nu/2)/Real.log Y := hd
    _ ≤ (Real.log Y-Real.log z)/Real.log Y := he
    _ = 1-Real.log z/Real.log Y := by field_simp

/-- The literal threshold converts the logarithmic CRT gap to the claimed
unabsorbed exponent, with no asymptotic replacement of u, V or nu. -/
theorem threshold_power_le (c theta H z Y : ℝ) (hH : saddleThreshold 1≤H)
    (htheta : 0≤theta)
    (hgap : c*saddleNu 1 H/(2*saddleCutoff 1 H)≤1-Real.log z/Real.log Y) :
    threshold theta H^(-1+Real.log z/Real.log Y)≤
      Real.exp (-c*theta*saddleNu 1 H^2/(2*saddleParameter 1 H)) := by
  have hu := (saddleParameter_spec (by norm_num : (0:ℝ)<1) hH).1
  have hup : 0<saddleParameter 1 H := by linarith [saddleParameterBase_ge_two]
  have hHp := (saddleThreshold_pos (by norm_num : (0:ℝ)<1)).trans_le hH
  rw [threshold,Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp,Real.exp_le_exp]
  have he := mul_le_mul_of_nonneg_left
    (show -1+Real.log z/Real.log Y≤ -c*saddleNu 1 H/(2*saddleCutoff 1 H) by simpa only [neg_mul,neg_div] using (show -1+Real.log z/Real.log Y≤ -(c*saddleNu 1 H/(2*saddleCutoff 1 H)) by linarith))
    (show 0≤theta*H/saddleParameter 1 H by positivity)
  apply he.trans_eq
  unfold saddleNu
  ring

/-- A bound V+2 log H for the actual K*(Q+1) prefactor, uniform in rate and Q. -/
theorem prefactor_log_eventually (c B : ℝ) (hc : 0<c) (hB : 0<B) :
    ∀ᶠ H : ℝ in atTop, ∀ rate : ℝ, ∀ Q : ℕ,
      1≤rate → (Q+1:ℝ)≤B*H → Real.log rate≤saddleCutoff 1 H-c*saddleNu 1 H →
      Real.log ((⌈2*rate⌉₊:ℝ)*(Q+1))≤saddleCutoff 1 H+2*Real.log H := by
  filter_upwards [eventually_ge_atTop (saddleThreshold 1),eventually_ge_atTop (3*B)] with H hH hBH
  intro rate Q hr hQ hbudget
  have hHp : 0<H := lt_of_lt_of_le (by positivity : 0<3*B) hBH
  have hrp : 0<rate := by linarith
  have hnu : 0<saddleNu 1 H := div_pos hHp (saddleCutoff_pos (by norm_num) hH)
  obtain ⟨hKlo,hKhi⟩ := ceil_twice_le rate hr
  have hp : 0<(⌈2*rate⌉₊:ℝ)*(Q+1) := by positivity
  have hb : (⌈2*rate⌉₊:ℝ)*(Q+1)≤3*B*rate*H := by
    have ht := mul_le_mul hKhi hQ (by positivity) (by positivity : 0≤3*rate)
    nlinarith
  have hl := Real.log_le_log hp hb
  rw [Real.log_mul (by positivity : 3*B*rate≠0) hHp.ne',
    Real.log_mul (by positivity : 3*B≠0) hrp.ne'] at hl
  have hlog := Real.log_le_log (by positivity : 0<3*B) hBH
  nlinarith

/-- The entire CRT cloud cost is absorbed at the actual rounded cutoffs.
The threshold is chosen before the intensity and maximal support length. -/
theorem cloud_cost_eventually (c theta B : ℝ) (hc : 0<c) (htheta : 0<theta) (hB : 0<B) :
    ∀ᶠ H : ℝ in atTop, ∀ rate : ℝ, ∀ Q : ℕ,
      1≤rate → (Q+1:ℝ)≤B*H → Real.log rate≤saddleCutoff 1 H-c*saddleNu 1 H →
      (⌈2*rate⌉₊:ℝ)*(Q+1)*threshold theta H^
        (-1+Real.log (3*(⌈2*rate⌉₊:ℝ)*(Q+1))/Real.log (⌊Real.exp (saddleCutoff 1 H)⌋₊:ℝ)) ≤
          Real.exp (-c*theta*saddleNu 1 H^2/(4*saddleParameter 1 H)) := by
  filter_upwards [eventually_ge_atTop (saddleThreshold 1),cutoff_gap_eventually c B hc hB,
    prefactor_log_eventually c B hc hB,prefactor_absorption_eventually c theta 2 hc htheta] with H hH hgap hlog habs
  intro rate Q hr hQ hbudget
  have hp : 0<(⌈2*rate⌉₊:ℝ)*(Q+1) := by
    have hk := (ceil_twice_le rate hr).1
    positivity
  exact (mul_le_mul_of_nonneg_left
    (threshold_power_le c theta H _ _ hH htheta.le (hgap rate Q hr hQ hbudget).2) hp.le).trans
      (habs _ hp (hlog rate Q hr hQ hbudget))

end
end PaperC.Prel8.RegularCloudCutoff
