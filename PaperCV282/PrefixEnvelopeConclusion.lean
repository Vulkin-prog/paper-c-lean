import PaperCV282.DyadicPrefixBudget

/-! # Complete envelope deductions from the quantitative finite-prefix bound

The source observable, the error summability and the passage to every M
are explicit. The final finite-prefix approximation is supplied separately.
-/
namespace PaperC.V282.PrefixEnvelopeConclusion

open Filter Topology MeasureTheory CorollaryPrefixLaw InfiniteRademacher PrimeEulerPNT
open DyadicPrefixThresholds DyadicPrefixProbability DyadicPrefixBudget PrefixEnvelopeInterpolation

noncomputable section

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤
local instance instProbabilityInfinite : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

/-- The full fixed-band prefix bound implies both displayed almost-sure inequalities. -/
theorem asymmetric_envelopes_of_prefix_bound (hPNT : PrimeNumberTheoremRemainder)
    (C c eta epsilon : ℝ) (hc : 0<c) (hepsilon : 0<epsilon)
    (hprefix : ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      (1/(2*Real.log 2))*Real.log M ≤ (L : ℝ)+1 →
      (L : ℝ)+1 ≤ (2/Real.log 2)*Real.log M →
      |infiniteRademacherMeasure.real {omega | infinitePrefixLongestConstantStretch M omega < L}-
        Real.exp (-((M : ℝ)/(2 : ℝ)^L))| ≤ prefixBudget C c eta M L) :
    ∀ᵐ omega ∂infiniteRademacherMeasure, ∀ᶠ M : ℕ in atTop,
      -Real.log (Real.log (Real.log M))/Real.log 2-4 ≤
        (infinitePrefixLongestConstantStretch M omega : ℝ)-Real.log M/Real.log 2 ∧
      (infinitePrefixLongestConstantStretch M omega : ℝ)-Real.log M/Real.log 2 ≤
        Real.log (Real.log M)/Real.log 2+
        (1+epsilon)*Real.log (Real.log (Real.log M))/Real.log 2+upperAdditiveConstant epsilon := by
  obtain ⟨Mzero,hMzero⟩ := hprefix
  obtain ⟨hl,hu⟩ := summable_threshold_budgets hPNT C c eta epsilon hc hepsilon
  have hpow : Tendsto (fun k : ℕ => 2^k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  apply asymmetric_envelopes_of_summable_void_errors epsilon hepsilon _ _ hl hu
  · filter_upwards [threshold_band_eventually epsilon,hpow.eventually (eventually_ge_atTop Mzero)]
      with k hb hk
    exact hMzero (2^k) hk (lowerThreshold k) (hb _ (by simp)).1 (hb _ (by simp)).2
  · filter_upwards [threshold_band_eventually epsilon,hpow.eventually (eventually_ge_atTop Mzero)]
      with k hb hk
    exact hMzero (2^k) hk (upperThreshold epsilon k) (hb _ (by simp)).1 (hb _ (by simp)).2

/-- The two asymmetric estimates imply the usual O(loglog M) envelope for the same sample. -/
theorem loglog_envelope_of_asymmetric (epsilon : ℝ) (hepsilon : 0<epsilon)
    (R : ℕ → ℝ)
    (h : ∀ᶠ M : ℕ in atTop,
      -Real.log (Real.log (Real.log M))/Real.log 2-4 ≤ R M-Real.log M/Real.log 2 ∧
      R M-Real.log M/Real.log 2 ≤ Real.log (Real.log M)/Real.log 2+
        (1+epsilon)*Real.log (Real.log (Real.log M))/Real.log 2+upperAdditiveConstant epsilon) :
    (fun M : ℕ => R M-Real.log M/Real.log 2) =O[atTop] (fun M : ℕ => Real.log (Real.log M)) := by
  have hc : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hH : Tendsto (fun M : ℕ => Real.log (Real.log M)) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  let D : ℝ := (3+epsilon)/Real.log 2+|upperAdditiveConstant epsilon|+4
  apply Asymptotics.IsBigO.of_bound D
  filter_upwards [h,hH.eventually (eventually_ge_atTop (1 : ℝ))] with M hM hH
  have hlog : 0≤Real.log (Real.log (Real.log M)) := Real.log_nonneg hH
  have hlogle : Real.log (Real.log (Real.log M)) ≤ Real.log (Real.log M) := by
    linarith [Real.log_le_sub_one_of_pos (by linarith : 0<Real.log (Real.log M))]
  have hdiv := div_le_div_of_nonneg_right hlogle hc.le
  have hmul := mul_le_mul_of_nonneg_left hdiv (by linarith : 0≤1+epsilon)
  have hK := le_abs_self (upperAdditiveConstant epsilon)
  have hKmul := mul_le_mul_of_nonneg_left hH (abs_nonneg (upperAdditiveConstant epsilon))
  have hHmul := mul_le_mul_of_nonneg_left hH (by norm_num : (0 : ℝ)≤4)
  have hco : 0≤(2+epsilon)/Real.log 2 := by positivity
  have hcoH := mul_nonneg hco (by linarith : 0≤Real.log (Real.log M))
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (by linarith : 0≤Real.log (Real.log M))]
  apply abs_le.mpr
  dsimp only [D]
  have hbase : 0≤Real.log (Real.log M)/Real.log 2 := div_nonneg (by linarith) hc.le
  simp only [div_eq_mul_inv] at hM hdiv hmul hcoH hbase ⊢
  constructor <;> nlinarith [hM.1,hM.2,abs_nonneg (upperAdditiveConstant epsilon)]

/-- The customary logarithmic envelope follows on the same probability-one event. -/
theorem ae_loglog_envelope_of_prefix_bound (hPNT : PrimeNumberTheoremRemainder)
    (C c eta epsilon : ℝ) (hc : 0<c) (hepsilon : 0<epsilon)
    (hprefix : ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      (1/(2*Real.log 2))*Real.log M ≤ (L : ℝ)+1 →
      (L : ℝ)+1 ≤ (2/Real.log 2)*Real.log M →
      |infiniteRademacherMeasure.real {omega | infinitePrefixLongestConstantStretch M omega < L}-
        Real.exp (-((M : ℝ)/(2 : ℝ)^L))| ≤ prefixBudget C c eta M L) :
    ∀ᵐ omega ∂infiniteRademacherMeasure,
      (fun M : ℕ => (infinitePrefixLongestConstantStretch M omega : ℝ)-Real.log M/Real.log 2)
        =O[atTop] (fun M : ℕ => Real.log (Real.log M)) := by
  filter_upwards [asymmetric_envelopes_of_prefix_bound hPNT C c eta epsilon hc hepsilon hprefix]
    with omega h
  exact loglog_envelope_of_asymmetric epsilon hepsilon _ h

end
end PaperC.V282.PrefixEnvelopeConclusion
