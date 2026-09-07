import PaperCV282.MicroscopicInteriorBounds
import PaperCV282.MicroscopicNonvacancy
import PaperCV282.PrimeClockMicroscopicTransfer

/-! # Theorem 7.1: actual microscopic non-vacancy is localized at the border

The exact event probability q_L, conditional uniqueness, and total variation
are all controlled by the same prime-scale error. Every bibliographic
dependency is explicit in the theorem arguments.
-/

namespace PaperC.V282.MicroscopicBoundaryDominance

open MeasureTheory ProbabilityTheory Filter InfiniteRademacher
open MicroscopicNonvacancy MicroscopicBorderEvents MicroscopicInteriorBounds
open LaishramUniformInput PostQuadraticLiterature PrimeEulerPNT
open HarmonicIncidenceSurplus MicroscopicExponentialScale SharpConditioning
open PrimeClockMicroscopicTransfer GeometricClusterTarget
open scoped Topology BigOperators

noncomputable section

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤
local instance instProbabilityInfinite : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

/-- Dividing the interior bound by the exact border mass removes its first prime exponent. -/
theorem interior_bound_div_border (L : ℕ) (delta : ℝ) :
    (2 : ℝ) ^ (-(1 + delta) * Nat.primeCounting L) / ((2 : ℝ)⁻¹) ^ Nat.primeCounting L =
      (2 : ℝ) ^ (-delta * Nat.primeCounting L) := by
  rw [inv_pow,div_inv_eq_mul,← Real.rpow_natCast,← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  congr 1
  ring

/-- The complete non-vacancy and localization assertions of source Theorem 7.1. -/
theorem theorem_seven_one (hLS : UniformPrimeDivisorStatement)
    (hShorey : ShoreySquareProductStatement) (hPNT : PrimeNumberTheoremRemainder)
    {delta : ℝ} (hdelta : 0 < delta) (hstar : delta < (surplus 11 : ℝ)) :
    ∃ Lzero : ℕ, ∀ L : ℕ, Lzero ≤ L →
      (∑ x ∈ Finset.Icc 2 (2 * L ^ 2), InfiniteStartProbabilityTransfer.infiniteStartProbability x L) ≤
        (2 : ℝ) ^ (-(1 + delta) * Nat.primeCounting L) ∧
      0 ≤ microscopicProbability L / ((2 : ℝ)⁻¹) ^ Nat.primeCounting L - 1 ∧
      microscopicProbability L / ((2 : ℝ)⁻¹) ^ Nat.primeCounting L - 1 ≤
        (2 : ℝ) ^ (-delta * Nat.primeCounting L) ∧
      1 - (2 : ℝ) ^ (-delta * Nat.primeCounting L) ≤
        (cond infiniteRademacherMeasure (microscopicEvent L)).real (uniqueBorderEvent L) ∧
      measureTotalVariation (cond infiniteRademacherMeasure (microscopicEvent L))
        (cond infiniteRademacherMeasure (borderEvent L)) ≤
          (2 : ℝ) ^ (-delta * Nat.primeCounting L) := by
  obtain ⟨N,hN⟩ := theorem_seven_one_interior_sum hLS hShorey hPNT hdelta hstar
  refine ⟨N,fun L hL => ?_⟩
  have hs := hN L hL
  have hq := microscopic_probability_bounds hs
  have ha : 0 < ((2 : ℝ)⁻¹) ^ Nat.primeCounting L := by positivity
  have hratio0 : 0 ≤ microscopicProbability L / ((2 : ℝ)⁻¹) ^ Nat.primeCounting L - 1 := by
    have hh : 1 ≤ microscopicProbability L / ((2 : ℝ)⁻¹) ^ Nat.primeCounting L :=
      (le_div_iff₀ ha).mpr (by simpa only [one_mul] using hq.1)
    linarith
  have hratio : microscopicProbability L / ((2 : ℝ)⁻¹) ^ Nat.primeCounting L - 1 ≤
      (2 : ℝ) ^ (-delta * Nat.primeCounting L) := by
    have hh := div_le_div_of_nonneg_right hq.2 ha.le
    rw [add_div,div_self ha.ne',interior_bound_div_border] at hh
    linarith
  have hu := conditional_unique_border_probability_ge hs
  have ht := microscopic_conditional_tv_le hs
  rw [interior_bound_div_border] at hu ht
  exact ⟨hs,hratio0,hratio,hu,ht⟩

/-- The explicitly stated source choice delta_0=1/12 is admissible. -/
theorem theorem_seven_one_one_twelfth (hLS : UniformPrimeDivisorStatement)
    (hShorey : ShoreySquareProductStatement) (hPNT : PrimeNumberTheoremRemainder) :
    ∃ Lzero : ℕ, ∀ L : ℕ, Lzero ≤ L →
      microscopicProbability L / ((2 : ℝ)⁻¹) ^ Nat.primeCounting L - 1 ≤
        (2 : ℝ) ^ (-(1 / 12 : ℝ) * Nat.primeCounting L) ∧
      1 - (2 : ℝ) ^ (-(1 / 12 : ℝ) * Nat.primeCounting L) ≤
        (cond infiniteRademacherMeasure (microscopicEvent L)).real (uniqueBorderEvent L) := by
  have hstar : (1 / 12 : ℝ) < (surplus 11 : ℝ) := by
    rw [surplus_eleven_eq]
    norm_num
  obtain ⟨N,hN⟩ := theorem_seven_one hLS hShorey hPNT (by norm_num : (0 : ℝ) < 1 / 12) hstar
  exact ⟨N,fun L hL => ⟨(hN L hL).2.2.1,(hN L hL).2.2.2.1⟩⟩

/-- In particular, q_L divided by its exact border scale tends to one. -/
theorem microscopic_probability_ratio_tendsto_one (hLS : UniformPrimeDivisorStatement)
    (hShorey : ShoreySquareProductStatement) (hPNT : PrimeNumberTheoremRemainder) :
    Tendsto (fun L : ℕ => microscopicProbability L / ((2 : ℝ)⁻¹) ^ Nat.primeCounting L)
      atTop (𝓝 1) := by
  obtain ⟨N,hN⟩ := theorem_seven_one_one_twelfth hLS hShorey hPNT
  have hlo : ∀ᶠ L : ℕ in atTop,
      0 ≤ microscopicProbability L / ((2 : ℝ)⁻¹) ^ Nat.primeCounting L - 1 := by
    filter_upwards [] with L
    have ha : 0 < ((2 : ℝ)⁻¹) ^ Nat.primeCounting L := by positivity
    have hh : 1 ≤ microscopicProbability L / ((2 : ℝ)⁻¹) ^ Nat.primeCounting L := (le_div_iff₀ ha).mpr
      (by simpa only [one_mul] using border_probability_le_microscopic_probability L)
    linarith
  have hhi : ∀ᶠ L : ℕ in atTop,
      microscopicProbability L / ((2 : ℝ)⁻¹) ^ Nat.primeCounting L - 1 ≤
        (2 : ℝ) ^ (-(1 / 12 : ℝ) * Nat.primeCounting L) :=
    eventually_atTop.mpr ⟨N,fun L hL => (hN L hL).1⟩
  have hz := squeeze_zero' hlo hhi (prime_exponential_tendsto_zero (by norm_num : (0 : ℝ) < 1 / 12))
  simpa only [sub_add_cancel,zero_add] using hz.add_const 1

/-- The full microscopic interior first moment is negligible relative to the border. -/
theorem interior_mass_relative_tendsto_zero (hLS : UniformPrimeDivisorStatement)
    (hShorey : ShoreySquareProductStatement) (hPNT : PrimeNumberTheoremRemainder) :
    Tendsto (fun L : ℕ =>
      (∑ x ∈ Finset.Icc 2 (2 * L ^ 2), InfiniteStartProbabilityTransfer.infiniteStartProbability x L) /
        ((2 : ℝ)⁻¹) ^ Nat.primeCounting L) atTop (𝓝 0) := by
  have hstar : (1 / 12 : ℝ) < (surplus 11 : ℝ) := by rw [surplus_eleven_eq]; norm_num
  obtain ⟨N,hN⟩ := theorem_seven_one_interior_sum hLS hShorey hPNT
    (by norm_num : (0 : ℝ) < 1 / 12) hstar
  apply squeeze_zero' (Eventually.of_forall (fun L => by
    apply div_nonneg _ (by positivity)
    exact Finset.sum_nonneg (fun x hx => ENNReal.toReal_nonneg))) _
    (prime_exponential_tendsto_zero (by norm_num : (0 : ℝ) < 1 / 12))
  filter_upwards [eventually_ge_atTop N] with L hL
  have h := div_le_div_of_nonneg_right (hN L hL)
    (show 0 ≤ ((2 : ℝ)⁻¹) ^ Nat.primeCounting L by positivity)
  rwa [interior_bound_div_border] at h

/-- Prime-clock localization under actual microscopic non-vacancy, with the arithmetic hypotheses discharged. -/
theorem microscopic_prime_clock_limit (hLS : UniformPrimeDivisorStatement)
    (hShorey : ShoreySquareProductStatement) (hPNT : PrimeNumberTheoremRemainder) :
    Tendsto (fun L : ℕ => measureTotalVariation (microscopicPrimeClockLaw L)
      (geometricMeasure halfSuccess)) atTop (𝓝 0) :=
  microscopic_prime_clock_tendsto_geometric (interior_mass_relative_tendsto_zero hLS hShorey hPNT)

end
end PaperC.V282.MicroscopicBoundaryDominance
