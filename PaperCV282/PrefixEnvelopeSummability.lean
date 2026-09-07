import PaperCV282.PrefixLongestGeometry
import PaperCV282.GeometricScaleInstances
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-! # Summable exceptional probabilities for the asymmetric prefix envelopes -/
namespace PaperC.V282.PrefixEnvelopeSummability

open MeasureTheory Filter Topology CorollaryPrefixLaw InfiniteRademacher
open scoped ENNReal

noncomputable section

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤
local instance instProbabilityInfinite : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

/-- The logarithmic harmonic series converges with every exponent strictly above one. -/
theorem summable_logarithmic_harmonic {p : ℝ} (hp : 1 < p) :
    Summable (fun k : ℕ => 1 / ((k : ℝ)*(Real.log k)^p)) := by
  have hp0 : 0 < p := lt_trans (by norm_num) hp
  apply (summable_condensed_iff_of_eventually_nonneg
    (Filter.Eventually.of_forall (fun k => by positivity)) ?_).mp
  · have hs := (Real.summable_nat_rpow.mpr (by linarith : -p < -1)).mul_left
      ((Real.log 2)^(-p))
    apply hs.congr
    intro k
    simp only [Nat.cast_pow,Nat.cast_ofNat,Real.log_pow]
    rw [Real.mul_rpow (Nat.cast_nonneg k) (Real.log_nonneg (by norm_num)),
      Real.rpow_neg (Nat.cast_nonneg k),Real.rpow_neg (Real.log_nonneg (by norm_num))]
    have h2 : (2 : ℝ)^k ≠ 0 := by positivity
    field_simp
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with k hk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0<k by omega)
    have hl : 0 < Real.log (k : ℝ) := Real.log_pos (by exact_mod_cast hk)
    have hlog : Real.log (k : ℝ) ≤ Real.log (k+1 : ℕ) := by
      apply Real.log_le_log hk0
      exact_mod_cast Nat.le_succ k
    apply one_div_le_one_div_of_le (mul_pos hk0 (Real.rpow_pos_of_pos hl p))
    exact mul_le_mul (by exact_mod_cast Nat.le_succ k)
      (Real.rpow_le_rpow hl.le hlog hp0.le) (Real.rpow_nonneg hl.le _)
      (by positivity)

/-- First Borel--Cantelli expressed directly with real event probabilities. -/
theorem ae_eventually_notMem_of_summable_real {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (events : ℕ → Set Ω)
    (hs : Summable (fun k => μ.real (events k))) :
    ∀ᵐ omega ∂μ, ∀ᶠ k in atTop, omega ∉ events k := by
  have he : (∑' k, μ (events k)) ≠ ⊤ := by
    have h := ENNReal.ofReal_tsum_of_nonneg
      (fun k => measureReal_nonneg (μ := μ) (s := events k)) hs
    simp only [Measure.real,ENNReal.ofReal_toReal (measure_ne_top _ _)] at h
    rw [← h]
    exact ENNReal.ofReal_ne_top
  exact ae_eventually_notMem he

/-- Summable upper and lower exceptional probabilities give simultaneous dyadic bounds. -/
theorem ae_eventually_dyadic_envelopes (lower upper : ℕ → ℕ)
    (hlower : Summable (fun k => infiniteRademacherMeasure.real
      {omega | infinitePrefixLongestConstantStretch (2^k) omega < lower k}))
    (hupper : Summable (fun k => infiniteRademacherMeasure.real
      {omega | upper k ≤ infinitePrefixLongestConstantStretch (2^k) omega})) :
    ∀ᵐ omega ∂infiniteRademacherMeasure, ∀ᶠ k in atTop,
      lower k ≤ infinitePrefixLongestConstantStretch (2^k) omega ∧
      infinitePrefixLongestConstantStretch (2^k) omega < upper k := by
  filter_upwards [ae_eventually_notMem_of_summable_real infiniteRademacherMeasure _ hlower,
    ae_eventually_notMem_of_summable_real infiniteRademacherMeasure _ hupper] with omega hl hu
  filter_upwards [hl,hu] with k hk hlk
  exact ⟨Nat.le_of_not_gt hk,Nat.lt_of_not_ge hlk⟩

end
end PaperC.V282.PrefixEnvelopeSummability
