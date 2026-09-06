import PaperCV282.GeometricSaddleSummability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# Almost-sure bounds from genuine averaged conditional errors

Markov's inequality and the first Borel--Cantelli lemma do not require
independence between environments or scales.
-/
namespace PaperC.V282.QuenchedBorelCantelli

open MeasureTheory Filter Topology GeometricSaddleSummability SaddleScales

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- An integrable nonnegative error is eventually below any threshold with summable mean ratio. -/
theorem ae_eventually_le_of_summable_ratios (μ : Measure Ω) [IsFiniteMeasure μ]
    (f : ℕ → Ω → ℝ) (hf : ∀ k, Integrable (f k) μ)
    (hf0 : ∀ k omega, 0 ≤ f k omega) (b t : ℕ → ℝ) (ht : ∀ k, 0 < t k)
    (hb : ∀ᶠ k in atTop, (∫ omega, f k omega ∂μ) ≤ b k)
    (hsum : Summable (fun k => b k/t k)) :
    ∀ᵐ omega ∂μ, ∀ᶠ k in atTop, f k omega ≤ t k := by
  have hm : ∀ᶠ k in atTop, μ.real {omega | t k < f k omega} ≤ b k/t k := by
    filter_upwards [hb] with k hb
    apply (measureReal_mono (μ := μ) (show {omega | t k < f k omega} ⊆
      {omega | t k ≤ f k omega} from fun omega h => (show t k < f k omega from h).le)).trans
    apply (le_div_iff₀ (ht k)).mpr
    have hh := mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall (hf0 k)) (hf k) (t k)
    nlinarith
  have hs : Summable (fun k => μ.real {omega | t k < f k omega}) := by
    apply hsum.of_norm_bounded_eventually_nat
    filter_upwards [hm] with k hk
    simpa only [Real.norm_eq_abs,abs_of_nonneg (measureReal_nonneg)] using hk
  have he : (∑' k, μ {omega | t k < f k omega}) ≠ ⊤ := by
    have h := ENNReal.ofReal_tsum_of_nonneg (fun k => measureReal_nonneg (μ := μ)
      (s := {omega | t k < f k omega})) hs
    simp only [Measure.real,ENNReal.ofReal_toReal (measure_ne_top _ _)] at h
    rw [← h]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_eventually_notMem he] with omega h
  filter_upwards [h] with k hk
  exact le_of_not_gt hk

/-- Actual saddle errors imply the stated almost-sure rate on geometric scales. -/
theorem ae_eventually_saddle_bound (μ : Measure Ω) [IsFiniteMeasure μ]
    (f : ℕ → Ω → ℝ) (hf : ∀ k, Integrable (f k) μ) (hf0 : ∀ k omega, 0 ≤ f k omega)
    (sizes : ℕ → ℕ) (hg : GeometricLowerGrowth sizes)
    (a c beta delta K : ℝ) (ha : 0<a) (hcb : beta<c) (hd : 0<delta)
    (hmean : ∀ᶠ k in atTop, (∫ omega, f k omega ∂μ) ≤
      K*Real.exp (-c*saddleNu a (Real.log (sizes k)))+(sizes k : ℝ)^(-delta)) :
    ∀ᵐ omega ∂μ, ∀ᶠ k in atTop,
      f k omega ≤ Real.exp (-beta*saddleNu a (Real.log (sizes k))) := by
  apply ae_eventually_le_of_summable_ratios μ f hf hf0
    (fun k => K*Real.exp (-c*saddleNu a (Real.log (sizes k)))+(sizes k : ℝ)^(-delta))
    (fun k => Real.exp (-beta*saddleNu a (Real.log (sizes k))))
    (fun _ => Real.exp_pos _) hmean
  have hs := ((summable_exp_neg_nu hg ha (by linarith : 0<c-beta)).mul_left K).add
    (summable_exp_nu_mul_size_rpow hg ha hd beta)
  apply hs.congr
  intro k
  rw [add_div,mul_div_assoc,← Real.exp_sub,div_eq_mul_inv,← Real.exp_neg]
  congr 1 <;> ring_nf

end
end PaperC.V282.QuenchedBorelCantelli
