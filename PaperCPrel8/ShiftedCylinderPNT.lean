import PaperCV282.PostQuadraticPrimeBounds

/-! # PNT normalization on a sublinearly enlarged sampling cylinder -/
namespace PaperC.Prel8.ShiftedCylinderPNT
open Filter Topology V282.PrimeEulerPNT V282.PostQuadraticPrimeBounds
noncomputable section

theorem cylinder_tendsto (M Q : ℕ → ℕ) (hM : Tendsto M atTop atTop) :
    Tendsto (fun n ↦ M n+Q n) atTop atTop := by
  apply tendsto_atTop_atTop.mpr
  intro b
  obtain ⟨N,hN⟩ := tendsto_atTop_atTop.mp hM b
  exact ⟨N,fun n hn ↦ (hN n hn).trans (Nat.le_add_right _ _)⟩

theorem cylinder_ratio (M Q : ℕ → ℕ) (hM : Tendsto M atTop atTop)
    (hQ : Tendsto (fun n ↦ (Q n:ℝ)/M n) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ((M n+Q n:ℕ):ℝ)/M n) atTop (𝓝 1) := by
  have h := hQ.const_add 1
  apply (show Tendsto (fun n ↦ 1+(Q n:ℝ)/M n) atTop (𝓝 1) by simpa using h).congr'
  filter_upwards [hM.eventually (eventually_ge_atTop 1)] with n hn
  have hm : (M n:ℝ)≠0 := by positivity
  push_cast
  rw [add_div,div_self hm]

theorem log_cylinder_ratio (M Q : ℕ → ℕ) (hM : Tendsto M atTop atTop)
    (hQ : Tendsto (fun n ↦ (Q n:ℝ)/M n) atTop (𝓝 0)) :
    Tendsto (fun n ↦ Real.log ((M n+Q n:ℕ):ℝ)/Real.log (M n)) atTop (𝓝 1) := by
  have hlog : Tendsto (fun n ↦ Real.log (M n)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hM)
  have hr := (Real.continuousAt_log (by norm_num : (1:ℝ)≠0)).tendsto.comp (cylinder_ratio M Q hM hQ)
  have he : Tendsto (fun n ↦ Real.log (((M n+Q n:ℕ):ℝ)/M n) / Real.log (M n)) atTop (𝓝 0) := by
    have hi := tendsto_inv_atTop_zero.comp hlog
    simpa [div_eq_mul_inv] using hr.mul hi
  have hh := he.const_add 1
  apply (show Tendsto (fun n ↦ 1+Real.log (((M n+Q n:ℕ):ℝ)/M n)/Real.log (M n))
    atTop (𝓝 1) by simpa using hh).congr'
  filter_upwards [hM.eventually (eventually_ge_atTop 2)] with n hn
  have hm : (0:ℝ)<M n := by positivity
  have hc : (0:ℝ)<(M n+Q n:ℕ) := by positivity
  have hl : Real.log (M n)≠0 := (Real.log_pos (by exact_mod_cast (show 1<M n by omega))).ne'
  rw [Real.log_div hc.ne' hm.ne']
  field_simp
  ring

/-- No fresh PNT premise is needed when the queried cylinder is M+o(M). -/
theorem prime_count_shifted (hPNT : PrimeNumberTheoremRemainder) (M Q : ℕ → ℕ)
    (hM : Tendsto M atTop atTop)
    (hQ : Tendsto (fun n ↦ (Q n:ℝ)/M n) atTop (𝓝 0)) :
    Tendsto (fun n ↦ (Nat.primeCounting (M n+Q n):ℝ)*Real.log (M n)/M n) atTop (𝓝 1) := by
  have hp := (primeCounting_normalized_tendsto_one hPNT).comp (cylinder_tendsto M Q hM)
  have hc := cylinder_ratio M Q hM hQ
  have hl := (log_cylinder_ratio M Q hM hQ).inv₀ (by norm_num : (1:ℝ)≠0)
  have hh := (hp.mul hc).mul hl
  apply (show Tendsto (fun n ↦
    ((Nat.primeCounting (M n+Q n):ℝ)*Real.log (M n+Q n)/(M n+Q n))*
      (((M n+Q n:ℕ):ℝ)/M n)*(Real.log (M n+Q n)/Real.log (M n))⁻¹) atTop (𝓝 1) by
        simpa only [Function.comp_def,Nat.cast_add,one_mul,inv_one] using hh).congr'
  filter_upwards [hM.eventually (eventually_ge_atTop 2)] with n hn
  have hm : (0:ℝ)<M n := by positivity
  have hc : (0:ℝ)<M n+Q n := by positivity
  have hl : Real.log ((M n:ℝ)+Q n)≠0 := (Real.log_pos (by
    have : (2:ℝ)≤M n := by exact_mod_cast hn
    have : (0:ℝ)≤Q n := by positivity
    linarith)).ne'
  push_cast
  field_simp

end
end PaperC.Prel8.ShiftedCylinderPNT
