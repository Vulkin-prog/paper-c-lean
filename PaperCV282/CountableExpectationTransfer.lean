import PaperCV282.CountableLawTransfer
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# From discrete total variation to actual bounded test integrals

This is the bridge from a common-lattice comparison to weak limits after
mapping configurations to continuous positions. The statistic need only
be bounded; no unbounded moment convergence is inferred.
-/
namespace PaperC.V282.CountableExpectationTransfer

open MeasureTheory InfiniteMassCoupling FiniteFieldTotalVariation CountableLawTransfer

noncomputable section

theorem summable_bounded_weight {α : Type*} {p : α → ℝ} (hp : Summable p)
    (hp0 : ∀ a, 0 ≤ p a) (f : α → ℝ) (M : ℝ) (hf : ∀ a, |f a| ≤ M) :
    Summable (fun a => p a*f a) := by
  apply (hp.mul_right M).of_norm_bounded
  intro a
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (hp0 a)]
  exact mul_le_mul_of_nonneg_left (hf a) (hp0 a)

/-- The exact half-L1 convention yields the factor two for arbitrary bounded signed tests. -/
theorem abs_weighted_sum_sub_le_tv {α : Type*} {p q : α → ℝ}
    (hp : Summable p) (hq : Summable q) (hp0 : ∀ a, 0 ≤ p a) (hq0 : ∀ a, 0 ≤ q a)
    (f : α → ℝ) (M : ℝ) (hf : ∀ a, |f a| ≤ M) :
    |(∑' a, p a*f a)-(∑' a, q a*f a)| ≤ 2*M*massTotalVariation p q := by
  have hpw := summable_bounded_weight hp hp0 f M hf
  have hqw := summable_bounded_weight hq hq0 f M hf
  have habs := summable_abs_sub_of_nonneg hp hq hp0 hq0
  rw [← hpw.tsum_sub hqw]
  calc
    _ ≤ ∑' a, |p a*f a-q a*f a| := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm (hpw.sub hqw).norm
    _ ≤ ∑' a, |p a-q a| * M := (hpw.sub hqw).norm.tsum_le_tsum
      (fun a => by
        rw [← sub_mul,abs_mul]
        exact mul_le_mul_of_nonneg_left (hf a) (abs_nonneg _)) (habs.mul_right M)
    _ = _ := by
      rw [tsum_mul_right]
      unfold massTotalVariation
      ring

/-- A bounded observable has precisely the expectation obtained from its actual singleton masses. -/
theorem integral_observable_eq_tsum {Ω α : Type*} [MeasurableSpace Ω]
    [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {f : Ω → α} (hf : Measurable f)
    (stat : α → ℝ) (M : ℝ) (hstat : ∀ a, |stat a| ≤ M) :
    (∫ ω, stat (f ω) ∂μ) = ∑' a, observableLaw μ f a*stat a := by
  letI : IsProbabilityMeasure (μ.map f) := Measure.isProbabilityMeasure_map hf.aemeasurable
  have hmeas : StronglyMeasurable stat := (measurable_of_countable stat).stronglyMeasurable
  have hint : Integrable stat (μ.map f) := (integrable_const M).mono' hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun a => by simpa only [Real.norm_eq_abs] using hstat a))
  rw [← integral_map_of_stronglyMeasurable hf hmeas,integral_countable hint]
  apply tsum_congr
  intro a
  rw [observableLaw_eq_map μ hf]
  rfl

/-- Complete discrete-field TV controls the actual integrals of all bounded configuration tests. -/
theorem integral_difference_le_tv {Ω Ω' α : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : Ω → α} {g : Ω' → α} (hf : Measurable f) (hg : Measurable g)
    (stat : α → ℝ) (M : ℝ) (hstat : ∀ a, |stat a| ≤ M) :
    |(∫ ω, stat (f ω) ∂μ)-(∫ ω, stat (g ω) ∂ν)| ≤
      2*M*massTotalVariation (observableLaw μ f) (observableLaw ν g) := by
  rw [integral_observable_eq_tsum μ hf stat M hstat,integral_observable_eq_tsum ν hg stat M hstat]
  exact abs_weighted_sum_sub_le_tv (hasSum_observableLaw μ hf).summable (hasSum_observableLaw ν hg).summable
    (observableLaw_nonneg μ f) (observableLaw_nonneg ν g) stat M hstat

end
end PaperC.V282.CountableExpectationTransfer
