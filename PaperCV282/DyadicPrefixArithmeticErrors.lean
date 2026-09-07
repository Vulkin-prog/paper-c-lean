import PaperCV282.DyadicPrefixRemainders
import PaperCV282.PostQuadraticPrimeBounds
import PaperCV282.SaddlePoissonScales

/-! # Summability of the actual prime and saddle errors at the dyadic envelope lengths -/
namespace PaperC.V282.DyadicPrefixArithmeticErrors

open Filter Topology PrimeEulerPNT PostQuadraticPrimeBounds
open DyadicPrefixThresholds DyadicPrefixRemainders GeometricScaleInstances
open GeometricSaddleSummability SaddleScales SaddlePoissonScales SaddleParameters

noncomputable section

/-- Every asymptotically equivalent length is eventually between k/2 and2k. -/
theorem length_bounds_eventually (lengths : ℕ → ℕ)
    (h : Tendsto (fun k => (lengths k : ℝ)/(k : ℝ)) atTop (𝓝 1)) :
    ∀ᶠ k : ℕ in atTop, (k : ℝ)/2 ≤ lengths k ∧ (lengths k : ℝ) ≤ 2*k := by
  filter_upwards [h.eventually (eventually_gt_nhds (by norm_num : (1/2 : ℝ)<1)),
    h.eventually (eventually_lt_nhds (by norm_num : (1 : ℝ)<2)),
    eventually_ge_atTop (1 : ℕ)] with k hlo hhi hk
  have hk0 : (0 : ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hlo' := (lt_div_iff₀ hk0).mp hlo
  have hhi' := (div_lt_iff₀ hk0).mp hhi
  constructor <;> linarith

theorem lengths_tendsto_atTop (lengths : ℕ → ℕ)
    (h : Tendsto (fun k => (lengths k : ℝ)/(k : ℝ)) atTop (𝓝 1)) :
    Tendsto lengths atTop atTop := by
  have hr : Tendsto (fun k => (lengths k : ℝ)) atTop atTop :=
    tendsto_atTop_mono' atTop ((length_bounds_eventually lengths h).mono (fun _ h => h.1))
      (tendsto_natCast_atTop_atTop.atTop_div_const (by norm_num : (0 : ℝ)<2))
  exact tendsto_natCast_atTop_iff.mp hr

/-- Only the existing PNT argument is used to make the exact boundary cylinder summable. -/
theorem boundary_prime_count_lower_eventually (hPNT : PrimeNumberTheoremRemainder)
    (lengths : ℕ → ℕ) (h : Tendsto (fun k => (lengths k : ℝ)/(k : ℝ)) atTop (𝓝 1)) :
    ∀ᶠ k : ℕ in atTop, (k : ℝ)/(8*Real.log k) ≤ Nat.primeCounting (lengths k) := by
  have hlen := lengths_tendsto_atTop lengths h
  have hp := (primeCounting_normalized_tendsto_one hPNT).comp hlen
  filter_upwards [length_bounds_eventually lengths h,
    hp.eventually (eventually_gt_nhds (by norm_num : (1/2 : ℝ)<1)),
    hlen.eventually (eventually_ge_atTop (2 : ℕ)),eventually_ge_atTop (2 : ℕ)] with k hlenb hp hlen2 hk2
  have hk0 : (0 : ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hl0 : (0 : ℝ)<lengths k := by exact_mod_cast (show 0<lengths k by omega)
  have hlogk : 0<Real.log (k : ℝ) := Real.log_pos (by exact_mod_cast hk2)
  have hlogl : Real.log (lengths k : ℝ) ≤ 2*Real.log k := by
    have hh := Real.log_le_log hl0 hlenb.2
    rw [Real.log_mul (by norm_num : (2 : ℝ)≠0) hk0.ne'] at hh
    have hh2 : Real.log (2 : ℝ) ≤ Real.log k := Real.log_le_log (by norm_num) (by exact_mod_cast hk2)
    linarith
  have hp' := (lt_div_iff₀ hl0).mp hp
  apply (div_le_iff₀ (mul_pos (by norm_num) hlogk)).mpr
  have hm := mul_le_mul_of_nonneg_left hlogl (Nat.cast_nonneg (Nat.primeCounting (lengths k)) : (0 : ℝ)≤_)
  nlinarith [hlenb.1]

/-- Exact powers 2^(-pi(L_k)) are summable for the two envelope sequences. -/
theorem summable_boundary_probability (hPNT : PrimeNumberTheoremRemainder)
    (lengths : ℕ → ℕ) (h : Tendsto (fun k => (lengths k : ℝ)/(k : ℝ)) atTop (𝓝 1)) :
    Summable (fun k : ℕ => ((2 : ℝ)⁻¹)^Nat.primeCounting (lengths k)) := by
  have hc : 0<Real.log 2/8 := by positivity
  have hs := summable_polynomial_deep (Real.log 2/8) hc 0
  simp only [pow_zero,one_mul] at hs
  apply hs.of_norm_bounded_eventually_nat
  filter_upwards [boundary_prime_count_lower_eventually hPNT lengths h] with k hk
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity),← Real.rpow_natCast,
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ)<(2 : ℝ)⁻¹),Real.log_inv]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left hk (Real.log_nonneg (by norm_num : (1 : ℝ)≤2))
  calc
    -Real.log 2*(Nat.primeCounting (lengths k) : ℝ) ≤ -Real.log 2*((k : ℝ)/(8*Real.log k)) := by linarith
    _ = -(Real.log 2/8)*((k : ℝ)/Real.log k) := by ring

/-- Exact dyadic prefixes have the geometric lower growth used in the earlier summability proof. -/
theorem geometricLowerGrowth_two_pow : GeometricLowerGrowth (fun k => 2^k) := by
  apply geometricLowerGrowth_of_geometric_lower_bound (fun k => 2^k) 2 1 (by norm_num) (by norm_num)
  exact Filter.Eventually.of_forall (fun k => by norm_num)

/-- The genuine hard saddle, including an arbitrary fixed eta*nu remainder, is summable with every polynomial. -/
theorem summable_actual_saddle_error (eta : ℝ) (p : ℕ) :
    Summable (fun k : ℕ => (k : ℝ)^p *
      Real.exp (-saddleCutoff 1 (Real.log (2^k : ℕ))+eta*saddleNu 1 (Real.log (2^k : ℕ)))) := by
  have hH := log_sizes_tendsto_atTop geometricLowerGrowth_two_pow
  have hnu := (tendsto_saddleNu_atTop (by norm_num : (0 : ℝ)<1)).comp hH
  have hV := (tendsto_saddleCutoff_div_nu (by norm_num : (0 : ℝ)<1)).comp hH
  apply (Real.summable_nat_rpow.mpr (by norm_num : (-2 : ℝ)< -1)).of_norm_bounded_eventually_nat
  filter_upwards [hnu.eventually (eventually_gt_atTop (0 : ℝ)),
    hV.eventually (eventually_ge_atTop (eta+1)),
    exp_neg_nu_le_index_rpow geometricLowerGrowth_two_pow (by norm_num : (0 : ℝ)<1)
      (by norm_num : (0 : ℝ)<1) ((p : ℝ)+2) (by positivity),
    eventually_ge_atTop (1 : ℕ)] with k hn hv hex hk
  have hk0 : (0 : ℝ)<k := by exact_mod_cast (show 0<k by omega)
  simp only [Function.comp_def] at hn hv
  have hv' := (le_div_iff₀ hn).mp hv
  have he : Real.exp (-saddleCutoff 1 (Real.log (2^k : ℕ))+eta*saddleNu 1 (Real.log (2^k : ℕ))) ≤
      (k : ℝ)^(-((p : ℝ)+2)) := by
    apply (Real.exp_le_exp.mpr (show -saddleCutoff 1 (Real.log (2^k : ℕ))+
      eta*saddleNu 1 (Real.log (2^k : ℕ)) ≤ -1*saddleNu 1 (Real.log (2^k : ℕ)) by linarith)).trans
    exact hex
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  calc
    _ ≤ (k : ℝ)^p * (k : ℝ)^(-((p : ℝ)+2)) := mul_le_mul_of_nonneg_left he (by positivity)
    _ = (k : ℝ)^(-2 : ℝ) := by
      rw [← Real.rpow_natCast,← Real.rpow_add hk0]
      congr 1
      ring

/-- The actual log(M)/loglog(M) deep-start scale is summable on M=2^k. -/
theorem summable_actual_deep_error (c : ℝ) (hc : 0<c) (p : ℕ) :
    Summable (fun k : ℕ => (k : ℝ)^p *
      Real.exp (-c*(Real.log (2^k : ℕ)/Real.log (Real.log (2^k : ℕ))))) := by
  have hH := log_sizes_tendsto_atTop geometricLowerGrowth_two_pow
  have hHH := Real.tendsto_log_atTop.comp hH
  apply summable_polynomial_exponential _ ?_ ?_ c hc p
  · filter_upwards [hH.eventually (eventually_gt_atTop (0 : ℝ)),
      hHH.eventually (eventually_gt_atTop (0 : ℝ))] with k h1 h2
    exact div_pos h1 h2
  · have hh := (log_squared_div_nat_tendsto_zero.add
        (log_div_nat_tendsto_zero.const_mul (Real.log (Real.log 2)))).div_const (Real.log 2)
    simp only [mul_zero,add_zero,zero_div] at hh
    apply hh.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with k hk
    have hk0 : (0 : ℝ)<k := by exact_mod_cast (show 0<k by omega)
    have hc2 : 0<Real.log 2 := Real.log_pos (by norm_num)
    simp only [Nat.cast_pow,Nat.cast_ofNat,Real.log_pow]
    rw [Real.log_mul hk0.ne' hc2.ne']
    field_simp

end
end PaperC.V282.DyadicPrefixArithmeticErrors
