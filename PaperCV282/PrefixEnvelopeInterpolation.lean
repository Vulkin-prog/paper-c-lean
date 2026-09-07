import PaperCV282.DyadicPrefixThresholds
import Mathlib.Data.Nat.Log

/-! # Deterministic interpolation of the dyadic asymmetric envelopes

The additive constants below are deterministic. Monotonicity of the true
longest-prefix run transports one almost-sure dyadic event to every large M.
-/
namespace PaperC.V282.PrefixEnvelopeInterpolation

open Filter Topology MeasureTheory CorollaryPrefixLaw InfiniteRademacher
open PrefixLongestGeometry DyadicPrefixThresholds PrefixEnvelopeSummability

noncomputable section

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤
local instance instProbabilityInfinite : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

/-- The natural dyadic block index grows without bound. -/
theorem nat_log_two_tendsto_atTop : Tendsto (Nat.log 2) atTop atTop := by
  apply tendsto_atTop.2
  intro k
  filter_upwards [eventually_ge_atTop (2^k)] with M hM
  exact Nat.le_log_of_pow_le (by norm_num) hM

/-- Exact comparison of the real and integer logarithmic block indices. -/
theorem log_bounds_of_dyadic {k M : ℕ} (hlo : 2^k ≤ M) (hhi : M < 2^(k+1)) :
    (k : ℝ)*Real.log 2 ≤ Real.log M ∧
    Real.log M < ((k : ℝ)+1)*Real.log 2 := by
  have hM : (0 : ℝ)<M := by exact_mod_cast (lt_of_lt_of_le (by positivity : 0<2^k) hlo)
  constructor
  · have hh := Real.log_le_log (by positivity : (0 : ℝ)<(2 : ℝ)^k)
      (by exact_mod_cast hlo : (2 : ℝ)^k ≤ M)
    simpa only [Real.log_pow] using hh
  · have hh := Real.log_lt_log hM
      (by exact_mod_cast hhi : (M : ℝ)<(2 : ℝ)^(k+1))
    simpa only [Real.log_pow,Nat.cast_add,Nat.cast_one] using hh

/-- The nested logarithms differ by bounded additive constants throughout each dyadic block. -/
theorem nested_log_comparison_eventually : ∀ᶠ k : ℕ in atTop, ∀ M : ℕ,
    2^k ≤ M → M < 2^(k+1) →
    Real.log (Real.log k) ≤ Real.log (Real.log (Real.log M))+Real.log 2 ∧
    Real.log (k+1 : ℕ) ≤ Real.log (Real.log M)+Real.log (2/Real.log 2) ∧
    Real.log (Real.log (k+1 : ℕ)) ≤ Real.log (Real.log (Real.log M))+Real.log 2 := by
  have hc : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hA : 0<(2 : ℝ)/Real.log 2 := by positivity
  have hlog : Tendsto (fun k : ℕ => Real.log k) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually (eventually_ge_atTop
    (2*|Real.log (Real.log 2)|+2*|Real.log (2/Real.log 2)|+4)),
    eventually_ge_atTop (2 : ℕ)] with k hk hk2 M hlo hhi
  have hk0 : (0 : ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hkp : (0 : ℝ)<(k+1 : ℕ) := by positivity
  have hlogk : 0<Real.log (k : ℝ) := Real.log_pos (by exact_mod_cast hk2)
  obtain ⟨hHlo,hHhi⟩ := log_bounds_of_dyadic hlo hhi
  have hH : 0<Real.log (M : ℝ) := lt_of_lt_of_le (mul_pos hk0 hc) hHlo
  have hHHlo : Real.log (k : ℝ)+Real.log (Real.log 2) ≤ Real.log (Real.log M) := by
    have hh := Real.log_le_log (mul_pos hk0 hc) hHlo
    simpa only [Real.log_mul hk0.ne' hc.ne'] using hh
  have hHH : 0<Real.log (Real.log M) := by
    linarith [neg_abs_le (Real.log (Real.log 2)),abs_nonneg (Real.log (2/Real.log 2))]
  have hhalf : Real.log (k : ℝ) ≤ 2*Real.log (Real.log M) := by
    linarith [neg_abs_le (Real.log (Real.log 2)),abs_nonneg (Real.log (2/Real.log 2))]
  have hlower : Real.log (Real.log k) ≤ Real.log (Real.log (Real.log M))+Real.log 2 := by
    have hh := Real.log_le_log hlogk hhalf
    rw [Real.log_mul (by norm_num : (2 : ℝ)≠0) hHH.ne'] at hh
    linarith
  have hkpH : ((k+1 : ℕ) : ℝ) ≤ (2/Real.log 2)*Real.log M := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hc).mpr
    push_cast
    have hk1 : (1 : ℝ)≤k := by exact_mod_cast (show 1≤k by omega)
    nlinarith
  have hupper : Real.log (k+1 : ℕ) ≤ Real.log (Real.log M)+Real.log (2/Real.log 2) := by
    have hh := Real.log_le_log hkp hkpH
    rw [Real.log_mul hA.ne' hH.ne'] at hh
    linarith
  have hhalf' : Real.log (k+1 : ℕ) ≤ 2*Real.log (Real.log M) := by
    linarith [neg_abs_le (Real.log (Real.log 2)),le_abs_self (Real.log (2/Real.log 2)),
      abs_nonneg (Real.log (Real.log 2))]
  have hupper' : Real.log (Real.log (k+1 : ℕ)) ≤ Real.log (Real.log (Real.log M))+Real.log 2 := by
    have hh := Real.log_le_log (Real.log_pos (by exact_mod_cast (show 1<k+1 by omega))) hhalf'
    rw [Real.log_mul (by norm_num : (2 : ℝ)≠0) hHH.ne'] at hh
    linarith
  exact ⟨hlower,hupper,hupper'⟩

/-- The bounded additive error in the upper envelope. -/
def upperAdditiveConstant (epsilon : ℝ) : ℝ :=
  3+epsilon+Real.log (2/Real.log 2)/Real.log 2

/-- The exact dyadic floor/ceiling thresholds imply the displayed real-logarithm envelopes. -/
theorem interpolate_thresholds_eventually (epsilon : ℝ) (hepsilon : 0<epsilon) :
    ∀ᶠ k : ℕ in atTop, ∀ M R : ℕ, 2^k ≤ M → M < 2^(k+1) →
      lowerThreshold k ≤ R → R < upperThreshold epsilon (k+1) →
      -Real.log (Real.log (Real.log M))/Real.log 2-4 ≤ (R : ℝ)-Real.log M/Real.log 2 ∧
      (R : ℝ)-Real.log M/Real.log 2 ≤
        Real.log (Real.log M)/Real.log 2+
        (1+epsilon)*Real.log (Real.log (Real.log M))/Real.log 2+upperAdditiveConstant epsilon := by
  have hc : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hshift : ∀ᶠ k : ℕ in atTop,
      (upperThreshold epsilon (k+1) : ℝ) ≤ upperCenter epsilon (k+1)+1 := by
    exact (tendsto_add_atTop_nat 1).eventually
      ((threshold_rounding epsilon).mono (fun _ h => h.2.2.2))
  filter_upwards [nested_log_comparison_eventually,threshold_rounding epsilon,hshift]
    with k hlogs hround hupper M R hlo hhi hRlo hRhi
  obtain ⟨hHlo,hHhi⟩ := log_bounds_of_dyadic hlo hhi
  obtain ⟨hloglo,hloghi,hloghhi⟩ := hlogs M hlo hhi
  have hcenterlo : lowerCenter k-1 ≤ (R : ℝ) := hround.1.trans (by exact_mod_cast hRlo)
  have hcenterhi : (R : ℝ) ≤ upperCenter epsilon (k+1)+1 :=
    (by exact_mod_cast hRhi.le : (R : ℝ)≤upperThreshold epsilon (k+1)).trans hupper
  have hscaleLo : (k : ℝ) ≤ Real.log M/Real.log 2 := (le_div_iff₀ hc).mpr hHlo
  have hscaleHi : Real.log M/Real.log 2 < (k : ℝ)+1 := (div_lt_iff₀ hc).mpr hHhi
  have hloglo' := div_le_div_of_nonneg_right hloglo hc.le
  have hloghi' := div_le_div_of_nonneg_right hloghi hc.le
  have hloghhi' := mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right hloghhi hc.le) (by linarith : 0≤1+epsilon)
  simp only [add_div,div_self hc.ne'] at hloglo' hloghi' hloghhi'
  unfold lowerCenter at hcenterlo
  unfold upperCenter at hcenterhi
  push_cast at hcenterhi hloghi' hloghhi'
  unfold upperAdditiveConstant
  constructor
  · simp only [neg_div]
    linarith only [hcenterlo,hscaleHi,hloglo']
  · simp only [mul_div_assoc] at hcenterhi ⊢
    nlinarith only [hcenterhi,hscaleLo,hloghi',hloghhi']

/-- The deterministic interpolation needs only monotonicity of the true prefix observable. -/
theorem longest_dyadic_interpolation (omega : InfiniteSample) {K M : ℕ}
    (hM : 2^K ≤ M) (lower upper : ℕ → ℕ)
    (hdyadic : ∀ k ≥ K, lower k ≤ infinitePrefixLongestConstantStretch (2^k) omega ∧
      infinitePrefixLongestConstantStretch (2^k) omega < upper k) :
    lower (Nat.log 2 M) ≤ infinitePrefixLongestConstantStretch M omega ∧
      infinitePrefixLongestConstantStretch M omega < upper (Nat.log 2 M+1) := by
  have hM0 : M≠0 := ne_of_gt (lt_of_lt_of_le (by positivity : 0<2^K) hM)
  have hk : K≤Nat.log 2 M := Nat.le_log_of_pow_le (by norm_num) hM
  have hm := infinitePrefixLongestConstantStretch_mono omega
  exact ⟨(hdyadic _ hk).1.trans (hm (Nat.pow_log_le_self 2 hM0)),
    (hm (Nat.lt_pow_succ_log_self (by norm_num : 1<2) M).le).trans_lt (hdyadic _ (by omega)).2⟩

/-- First Borel--Cantelli plus deterministic interpolation, with no cross-scale independence. -/
theorem ae_asymmetric_envelopes_of_summable (epsilon : ℝ) (hepsilon : 0<epsilon)
    (hlower : Summable (fun k => infiniteRademacherMeasure.real
      {omega | infinitePrefixLongestConstantStretch (2^k) omega < lowerThreshold k}))
    (hupper : Summable (fun k => infiniteRademacherMeasure.real
      {omega | upperThreshold epsilon k ≤ infinitePrefixLongestConstantStretch (2^k) omega})) :
    ∀ᵐ omega ∂infiniteRademacherMeasure, ∀ᶠ M : ℕ in atTop,
      -Real.log (Real.log (Real.log M))/Real.log 2-4 ≤
        (infinitePrefixLongestConstantStretch M omega : ℝ)-Real.log M/Real.log 2 ∧
      (infinitePrefixLongestConstantStretch M omega : ℝ)-Real.log M/Real.log 2 ≤
        Real.log (Real.log M)/Real.log 2+
        (1+epsilon)*Real.log (Real.log (Real.log M))/Real.log 2+upperAdditiveConstant epsilon := by
  filter_upwards [ae_eventually_dyadic_envelopes _ _ hlower hupper] with omega hdyadic
  obtain ⟨K,hK⟩ := eventually_atTop.mp hdyadic
  have hi := nat_log_two_tendsto_atTop.eventually (interpolate_thresholds_eventually epsilon hepsilon)
  filter_upwards [hi,eventually_ge_atTop (2^K)] with M hi hM
  have hM0 : M≠0 := ne_of_gt (lt_of_lt_of_le (by positivity : 0<2^K) hM)
  obtain ⟨hlo,hhi⟩ := longest_dyadic_interpolation omega hM _ _ hK
  exact hi M _ (Nat.pow_log_le_self 2 hM0)
    (Nat.lt_pow_succ_log_self (by norm_num : 1<2) M) hlo hhi

end
end PaperC.V282.PrefixEnvelopeInterpolation
