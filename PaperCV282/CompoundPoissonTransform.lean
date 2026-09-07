import PaperCV282.CompoundPoissonTarget

/-!
# Complex transforms identifying the actual compound law

These transforms will identify a compound random sum with its independent
Poisson coordinates by equality of laws, beyond equality of their means.
-/

namespace PaperC.V282.CompoundPoissonTransform

open MeasureTheory ProbabilityTheory CompoundPoissonTarget
open scoped BigOperators NNReal ENNReal

noncomputable section

theorem integrable_complex_unit_powers {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu] (f : Omega → ℕ) (hf : Measurable f)
    {z : ℂ} (hz : ‖z‖ ≤ 1) : Integrable (fun omega => z ^ f omega) mu := by
  refine ⟨((measurable_of_countable (fun n : ℕ => z ^ n)).comp hf).aestronglyMeasurable, ?_⟩
  apply HasFiniteIntegral.of_bounded (C := 1)
  exact Filter.Eventually.of_forall fun omega => by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) hz

theorem integral_fixed_mark_sum_complex (mu : Measure ℕ) [IsProbabilityMeasure mu]
    (z : ℂ) (n : ℕ) :
    (∫ marks, z ^ (∑ i ∈ Finset.range n, marks i) ∂markSequenceMeasure mu) =
      (∫ h, z ^ h ∂mu) ^ n := by
  have hdep : iIndepFun (fun i : ℕ => fun marks : ℕ → ℕ => z ^ marks i)
      (markSequenceMeasure mu) :=
    iIndepFun_infinitePi (fun _ => measurable_of_countable _)
  have hn := hdep.precomp (fun i j (h : (i : ℕ) = (j : ℕ)) => Fin.ext h)
    (g := fun i : Fin n => i.val)
  have hp := hn.integral_fun_prod_eq_prod_integral
    (fun i => ((measurable_of_countable (fun h : ℕ => z ^ h)).comp
      (measurable_pi_apply i.val)).aestronglyMeasurable)
  have hcoord (i : Fin n) :
      (∫ marks : ℕ → ℕ, z ^ marks i.val ∂markSequenceMeasure mu) = ∫ h, z ^ h ∂mu :=
    (hasLaw_mark_coordinate mu i.val).integral_comp
      (measurable_of_countable _).aestronglyMeasurable
  simp_rw [hcoord] at hp
  calc
    _ = ∫ marks : ℕ → ℕ, ∏ i : Fin n, z ^ marks i.val ∂markSequenceMeasure mu := by
      congr 1
      funext marks
      rw [← Finset.prod_pow_eq_pow_sum]
      exact (Fin.prod_univ_eq_prod_range (fun i => z ^ marks i) n).symm
    _ = _ := by simpa using hp

theorem integral_poisson_complex_powers (rate : ℝ≥0) (t : ℂ) :
    (∫ n, t ^ n ∂poissonMeasure rate) = Complex.exp ((rate : ℂ) * (t - 1)) := by
  rw [integral_poissonMeasure]
  simp only [Complex.real_smul]
  calc
    (∑' n : ℕ, ((Real.exp (-(rate : ℝ)) * (rate : ℝ) ^ n / n.factorial : ℝ) : ℂ) * t ^ n) =
        Complex.exp (-(rate : ℂ)) * ∑' n : ℕ, ((rate : ℂ) * t) ^ n / n.factorial := by
      rw [← tsum_mul_left]
      congr 1
      funext n
      push_cast
      rw [mul_pow]
      ring
    _ = Complex.exp ((rate : ℂ) * (t - 1)) := by
      rw [(NormedSpace.expSeries_div_hasSum_exp ((rate : ℂ) * t)).tsum_eq,
        ← Complex.exp_eq_exp_ℂ, ← Complex.exp_add]
      congr 1
      ring

theorem compound_complex_transform (rate : ℝ≥0) (mu : Measure ℕ)
    [IsProbabilityMeasure mu] {z : ℂ} (hz : ‖z‖ ≤ 1) :
    (∫ n, z ^ n ∂compoundMeasure rate mu) =
      Complex.exp ((rate : ℂ) * ((∫ h, z ^ h ∂mu) - 1)) := by
  rw [← (hasLaw_stoppedMarkSum rate mu).integral_comp
    (measurable_of_countable (fun n : ℕ => z ^ n)).aestronglyMeasurable]
  simp only [Function.comp_apply]
  rw [compoundSampleMeasure, integral_prod _
    (integrable_complex_unit_powers _ stoppedMarkSum measurable_stoppedMarkSum hz)]
  simp_rw [stoppedMarkSum, integral_fixed_mark_sum_complex]
  exact integral_poisson_complex_powers _ _

/-- Equality of the transforms on the unit circle identifies the whole natural-valued law. -/
theorem natural_law_eq_of_unit_transforms (mu nu : Measure ℕ)
    [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (h : ∀ z : ℂ, ‖z‖ = 1 → (∫ n, z ^ n ∂mu) = ∫ n, z ^ n ∂nu) : mu = nu := by
  apply (MeasurableEmbedding.natCast (α := ℝ)).map_injective
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_apply, charFun_apply,
    integral_map (measurable_of_countable (fun n : ℕ => (n : ℝ))).aemeasurable (by fun_prop),
    integral_map (measurable_of_countable (fun n : ℕ => (n : ℝ))).aemeasurable (by fun_prop)]
  have hz : ‖Complex.exp ((t : ℂ) * Complex.I)‖ = 1 := by simp
  have heq (n : ℕ) : Complex.exp ((↑((n : ℝ) * t) : ℂ) * Complex.I) =
      (Complex.exp ((t : ℂ) * Complex.I)) ^ n := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  simpa only [Real.inner_apply, heq] using h _ hz

end
end PaperC.V282.CompoundPoissonTransform
