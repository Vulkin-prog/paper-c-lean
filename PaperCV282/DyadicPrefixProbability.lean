import PaperCV282.PrefixEnvelopeInterpolation

/-! # Quantitative void errors give both asymmetric almost-sure envelopes

This is a generic deduction from actual event probabilities. Its error
premises will be supplied by the proved finite-prefix approximation.
-/
namespace PaperC.V282.DyadicPrefixProbability

open MeasureTheory Filter Topology CorollaryPrefixLaw InfiniteRademacher
open PrefixLongestGeometry PrefixEnvelopeSummability DyadicPrefixThresholds PrefixEnvelopeInterpolation

noncomputable section

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤
local instance instProbabilityInfinite : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

/-- The upper exceptional event is the exact complement of the longest-run void event. -/
theorem longest_hit_probability (M L : ℕ) :
    infiniteRademacherMeasure.real {omega | L ≤ infinitePrefixLongestConstantStretch M omega} =
      1-infiniteRademacherMeasure.real {omega | infinitePrefixLongestConstantStretch M omega < L} := by
  have he : {omega | L ≤ infinitePrefixLongestConstantStretch M omega} =
      {omega | infinitePrefixLongestConstantStretch M omega < L}ᶜ := by
    ext omega
    simp
  rw [he,measureReal_compl (measurableSet_longest_lt M L),probReal_univ]

/-- A scalar void approximation simultaneously controls the hit probability. -/
theorem longest_hit_le_of_void_error (M L : ℕ) (err : ℝ)
    (h : |infiniteRademacherMeasure.real {omega | infinitePrefixLongestConstantStretch M omega < L}-
      Real.exp (-((M : ℝ)/(2 : ℝ)^L))| ≤ err) :
    infiniteRademacherMeasure.real {omega | L ≤ infinitePrefixLongestConstantStretch M omega} ≤
      (M : ℝ)/(2 : ℝ)^L+err := by
  rw [longest_hit_probability]
  have hh := (abs_le.mp h).1
  have hexp := Real.add_one_le_exp (-((M : ℝ)/(2 : ℝ)^L))
  linarith

/-- The lower dyadic exceptional probabilities are summable once the quantitative errors are. -/
theorem summable_lower_exception (err : ℕ → ℝ) (hs : Summable err)
    (h : ∀ᶠ k : ℕ in atTop,
      |infiniteRademacherMeasure.real
        {omega | infinitePrefixLongestConstantStretch (2^k) omega < lowerThreshold k}-
        Real.exp (-(((2^k : ℕ) : ℝ)/(2 : ℝ)^(lowerThreshold k)))| ≤ err k) :
    Summable (fun k => infiniteRademacherMeasure.real
      {omega | infinitePrefixLongestConstantStretch (2^k) omega < lowerThreshold k}) := by
  apply ((Real.summable_nat_rpow.mpr (by norm_num : (-2 : ℝ)< -1)).add hs).of_norm_bounded_eventually_nat
  filter_upwards [h,lower_target_void_le] with k hk ht
  rw [Real.norm_eq_abs,abs_of_nonneg measureReal_nonneg]
  have hh := (abs_le.mp hk).2
  linarith

/-- The upper dyadic exceptional probabilities retain the exact logarithmic harmonic term. -/
theorem summable_upper_exception (epsilon : ℝ) (hepsilon : 0<epsilon)
    (err : ℕ → ℝ) (hs : Summable err)
    (h : ∀ᶠ k : ℕ in atTop,
      |infiniteRademacherMeasure.real
        {omega | infinitePrefixLongestConstantStretch (2^k) omega < upperThreshold epsilon k}-
        Real.exp (-(((2^k : ℕ) : ℝ)/(2 : ℝ)^(upperThreshold epsilon k)))| ≤ err k) :
    Summable (fun k => infiniteRademacherMeasure.real
      {omega | upperThreshold epsilon k ≤ infinitePrefixLongestConstantStretch (2^k) omega}) := by
  apply ((summable_logarithmic_harmonic (by linarith : 1<1+epsilon)).add hs).of_norm_bounded_eventually_nat
  filter_upwards [h,eventually_ge_atTop (2 : ℕ)] with k hk hk2
  rw [Real.norm_eq_abs,abs_of_nonneg measureReal_nonneg]
  exact (longest_hit_le_of_void_error (2^k) (upperThreshold epsilon k) (err k) hk).trans
    (add_le_add (upper_intensity_le epsilon (k := k) (by omega)) le_rfl)

/-- Complete deterministic/probabilistic deduction; no independence across scales is required. -/
theorem asymmetric_envelopes_of_summable_void_errors (epsilon : ℝ) (hepsilon : 0<epsilon)
    (lowerError upperError : ℕ → ℝ) (hlower : Summable lowerError) (hupper : Summable upperError)
    (hlow : ∀ᶠ k : ℕ in atTop,
      |infiniteRademacherMeasure.real
        {omega | infinitePrefixLongestConstantStretch (2^k) omega < lowerThreshold k}-
        Real.exp (-(((2^k : ℕ) : ℝ)/(2 : ℝ)^(lowerThreshold k)))| ≤ lowerError k)
    (hup : ∀ᶠ k : ℕ in atTop,
      |infiniteRademacherMeasure.real
        {omega | infinitePrefixLongestConstantStretch (2^k) omega < upperThreshold epsilon k}-
        Real.exp (-(((2^k : ℕ) : ℝ)/(2 : ℝ)^(upperThreshold epsilon k)))| ≤ upperError k) :
    ∀ᵐ omega ∂infiniteRademacherMeasure, ∀ᶠ M : ℕ in atTop,
      -Real.log (Real.log (Real.log M))/Real.log 2-4 ≤
        (infinitePrefixLongestConstantStretch M omega : ℝ)-Real.log M/Real.log 2 ∧
      (infinitePrefixLongestConstantStretch M omega : ℝ)-Real.log M/Real.log 2 ≤
        Real.log (Real.log M)/Real.log 2+
        (1+epsilon)*Real.log (Real.log (Real.log M))/Real.log 2+upperAdditiveConstant epsilon :=
  ae_asymmetric_envelopes_of_summable epsilon hepsilon
    (summable_lower_exception lowerError hlower hlow)
    (summable_upper_exception epsilon hepsilon upperError hupper hup)

end
end PaperC.V282.DyadicPrefixProbability
