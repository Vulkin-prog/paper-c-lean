import PaperCV282.DyadicPrefixArithmeticErrors

/-! # The complete quantitative prefix budget is summable at the two envelope thresholds -/
namespace PaperC.V282.DyadicPrefixBudget

open Filter Topology PrimeEulerPNT SaddleScales SaddleParameters
open DyadicPrefixThresholds DyadicPrefixRemainders DyadicPrefixArithmeticErrors

noncomputable section

/-- Equation7.10 plus the border and overflow terms in7.11, with epsilon0=1/12. -/
def prefixBudget (C c eta : ℝ) (M L : ℕ) : ℝ :=
  C*((M : ℝ)/(2 : ℝ)^L)*
      (Real.exp (-saddleCutoff 1 (Real.log M)+eta*saddleNu 1 (Real.log M))+(M : ℝ)^(-1/4 : ℝ))+
  C*Real.exp (-c*(Real.log M/Real.log (Real.log M)))+
  ((2 : ℝ)⁻¹)^Nat.primeCounting L+
  C*(L : ℝ)/(2 : ℝ)^L+C/(2 : ℝ)^L*(M : ℝ)^(7/12 : ℝ)

theorem dyadic_size_rpow (k : ℕ) (a : ℝ) :
    (((2^k : ℕ) : ℝ))^a = (2 : ℝ)^(a*(k : ℝ)) := by
  rw [Nat.cast_pow,Nat.cast_ofNat,← Real.rpow_natCast,← Real.rpow_mul (by norm_num : (0 : ℝ)≤2)]
  congr 1
  ring

/-- A polynomial intensity bound suffices for each negative size power. -/
theorem summable_intensity_size_power (lengths : ℕ → ℕ)
    (hLambda : ∀ᶠ k : ℕ in atTop, ((2^k : ℕ) : ℝ)/(2 : ℝ)^(lengths k) ≤ (k : ℝ))
    (delta : ℝ) (hdelta : 0<delta) :
    Summable (fun k : ℕ => (((2^k : ℕ) : ℝ)/(2 : ℝ)^(lengths k))*
      ((2^k : ℕ) : ℝ)^(-delta)) := by
  apply (summable_polynomial_dyadic_power delta hdelta 1).of_norm_bounded_eventually_nat
  filter_upwards [hLambda] with k hk
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity),dyadic_size_rpow,pow_one]
  exact mul_le_mul_of_nonneg_right hk (by positivity)

/-- The finite-prefix budget really is summable; no final probability is an assumption here. -/
theorem summable_prefixBudget (hPNT : PrimeNumberTheoremRemainder)
    (C c eta : ℝ) (hc : 0<c) (lengths : ℕ → ℕ)
    (hLength : Tendsto (fun k => (lengths k : ℝ)/(k : ℝ)) atTop (𝓝 1))
    (hLambda : ∀ᶠ k : ℕ in atTop, ((2^k : ℕ) : ℝ)/(2 : ℝ)^(lengths k) ≤ (k : ℝ)) :
    Summable (fun k => prefixBudget C c eta (2^k) (lengths k)) := by
  have hsaddle : Summable (fun k : ℕ => (((2^k : ℕ) : ℝ)/(2 : ℝ)^(lengths k))*
      Real.exp (-saddleCutoff 1 (Real.log (2^k : ℕ))+eta*saddleNu 1 (Real.log (2^k : ℕ)))) := by
    apply (summable_actual_saddle_error eta 1).of_norm_bounded_eventually_nat
    filter_upwards [hLambda] with k hk
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity),pow_one]
    exact mul_le_mul_of_nonneg_right hk (by positivity)
  have hsize := summable_intensity_size_power lengths hLambda (1/4) (by norm_num)
  have hdeep := summable_actual_deep_error c hc 0
  simp only [pow_zero,one_mul] at hdeep
  have hborder := summable_boundary_probability hPNT lengths hLength
  have hoverflow : Summable (fun k : ℕ => (lengths k : ℝ)/(2 : ℝ)^(lengths k)) := by
    have hs := (summable_polynomial_dyadic_power 1 (by norm_num) 2).mul_left 2
    apply hs.of_norm_bounded_eventually_nat
    filter_upwards [hLambda,length_bounds_eventually lengths hLength] with k hk hlen
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    have hM : (0 : ℝ)<((2^k : ℕ) : ℝ) := by positivity
    calc
      _ = (lengths k : ℝ)*(((2^k : ℕ) : ℝ)/(2 : ℝ)^(lengths k))*((2^k : ℕ) : ℝ)^(-1 : ℝ) := by
        rw [Real.rpow_neg_one]
        field_simp
      _ ≤ (2*(k : ℝ))*(k : ℝ)*((2^k : ℕ) : ℝ)^(-1 : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul hlen.2 hk (by positivity) (by positivity)
      _ = 2*((k : ℝ)^2*(2 : ℝ)^(-1*(k : ℝ))) := by rw [dyadic_size_rpow]; ring
  have htail : Summable (fun k : ℕ => 1/(2 : ℝ)^(lengths k)*((2^k : ℕ) : ℝ)^(7/12 : ℝ)) := by
    have hs := summable_intensity_size_power lengths hLambda (5/12) (by norm_num)
    apply hs.congr
    intro k
    have hM : (0 : ℝ)<((2^k : ℕ) : ℝ) := by positivity
    have he : ((2^k : ℕ) : ℝ)^(-(5/12 : ℝ)) =
        ((2^k : ℕ) : ℝ)^(7/12 : ℝ)/((2^k : ℕ) : ℝ) := by
      have hr := Real.rpow_sub hM (7/12 : ℝ) 1
      norm_num at hr
      simpa only [Nat.cast_pow,Nat.cast_ofNat] using hr
    rw [he]
    field_simp
  apply (((((hsaddle.add hsize).mul_left C).add (hdeep.mul_left C)).add hborder).add
    (hoverflow.mul_left C) |>.add (htail.mul_left C)).congr
  intro k
  unfold prefixBudget
  ring_nf

/-- Both literal thresholds have at most polynomial target intensity. -/
theorem threshold_intensity_le_index (epsilon : ℝ) (hepsilon : 0<epsilon) :
    ∀ᶠ k : ℕ in atTop,
      ((2^k : ℕ) : ℝ)/(2 : ℝ)^(lowerThreshold k) ≤ (k : ℝ) ∧
      ((2^k : ℕ) : ℝ)/(2 : ℝ)^(upperThreshold epsilon k) ≤ (k : ℝ) := by
  have hlog : Tendsto (fun k : ℕ => Real.log k) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [lower_intensity_bounds,
    log_div_nat_tendsto_zero.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ)<1/4)),
    hlog.eventually (eventually_ge_atTop (1 : ℝ)),eventually_ge_atTop (2 : ℕ)] with k hl hk hlogk hk2
  have hk0 : (0 : ℝ)<k := by exact_mod_cast (show 0<k by omega)
  constructor
  · have hh := (div_lt_iff₀ hk0).mp hk
    linarith [hl.2]
  · apply (upper_intensity_le epsilon (by omega : 1<k)).trans
    have hp : 1≤(Real.log k)^(1+epsilon) := Real.one_le_rpow hlogk (by linarith)
    have hden : (1 : ℝ)≤(k : ℝ)*(Real.log k)^(1+epsilon) := by
      have hk1 : (1 : ℝ)≤k := by exact_mod_cast (show 1≤k by omega)
      nlinarith [mul_le_mul_of_nonneg_left hp hk0.le]
    apply (one_div_le_one_div_of_le (by norm_num : (0 : ℝ)<1) hden).trans
    simpa using (show (1 : ℝ)≤k by exact_mod_cast (show 1≤k by omega))

/-- The two printed dyadic choices make every genuine arithmetic remainder summable. -/
theorem summable_threshold_budgets (hPNT : PrimeNumberTheoremRemainder)
    (C c eta epsilon : ℝ) (hc : 0<c) (hepsilon : 0<epsilon) :
    Summable (fun k => prefixBudget C c eta (2^k) (lowerThreshold k)) ∧
    Summable (fun k => prefixBudget C c eta (2^k) (upperThreshold epsilon k)) := by
  have hlength := threshold_ratio_tendsto_one epsilon
  have hlambda := threshold_intensity_le_index epsilon hepsilon
  exact ⟨summable_prefixBudget hPNT C c eta hc _ hlength.1 (hlambda.mono (fun _ h => h.1)),
    summable_prefixBudget hPNT C c eta hc _ hlength.2 (hlambda.mono (fun _ h => h.2))⟩

end
end PaperC.V282.DyadicPrefixBudget
