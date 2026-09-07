import PaperCV282.PoissonFieldMeasure
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Integration

/-!
# A compound Poisson law from an independent Poisson count and iid marks

The sample space contains an actual infinite sequence of marks, independent
of the Poisson count. Only its finite initial segment is summed. The resulting
law on the natural numbers is countable; the sample space is not asserted to be.
-/

namespace PaperC.V282.CompoundPoissonTarget

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

noncomputable section

def markSequenceMeasure (mu : Measure ℕ) [IsProbabilityMeasure mu] : Measure (ℕ → ℕ) :=
  Measure.infinitePi (fun _ : ℕ => mu)

instance instProbabilityMarkSequence (mu : Measure ℕ) [IsProbabilityMeasure mu] :
    IsProbabilityMeasure (markSequenceMeasure mu) := by
  unfold markSequenceMeasure
  infer_instance

def compoundSampleMeasure (rate : ℝ≥0) (mu : Measure ℕ) [IsProbabilityMeasure mu] :
    Measure (ℕ × (ℕ → ℕ)) :=
  (poissonMeasure rate).prod (markSequenceMeasure mu)

instance instProbabilityCompoundSample (rate : ℝ≥0) (mu : Measure ℕ)
    [IsProbabilityMeasure mu] : IsProbabilityMeasure (compoundSampleMeasure rate mu) := by
  unfold compoundSampleMeasure
  infer_instance

def stoppedMarkSum (sample : ℕ × (ℕ → ℕ)) : ℕ :=
  ∑ i ∈ Finset.range sample.1, sample.2 i

theorem measurable_stoppedMarkSum : Measurable stoppedMarkSum := by
  apply measurable_from_prod_countable_right
  intro n
  change Measurable (fun marks : ℕ → ℕ => ∑ i ∈ Finset.range n, marks i)
  exact Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)

def compoundMeasure (rate : ℝ≥0) (mu : Measure ℕ) [IsProbabilityMeasure mu] : Measure ℕ :=
  (compoundSampleMeasure rate mu).map stoppedMarkSum

instance instProbabilityCompound (rate : ℝ≥0) (mu : Measure ℕ)
    [IsProbabilityMeasure mu] : IsProbabilityMeasure (compoundMeasure rate mu) := by
  unfold compoundMeasure
  exact Measure.isProbabilityMeasure_map measurable_stoppedMarkSum.aemeasurable

def compoundPMF (rate : ℝ≥0) (mu : Measure ℕ) [IsProbabilityMeasure mu] : PMF ℕ :=
  (compoundMeasure rate mu).toPMF

theorem compoundPMF_toMeasure (rate : ℝ≥0) (mu : Measure ℕ) [IsProbabilityMeasure mu] :
    (compoundPMF rate mu).toMeasure = compoundMeasure rate mu :=
  Measure.toPMF_toMeasure _

theorem hasLaw_stoppedMarkSum (rate : ℝ≥0) (mu : Measure ℕ) [IsProbabilityMeasure mu] :
    HasLaw stoppedMarkSum (compoundMeasure rate mu) (compoundSampleMeasure rate mu) :=
  ⟨measurable_stoppedMarkSum.aemeasurable, rfl⟩

theorem hasLaw_poisson_count (rate : ℝ≥0) (mu : Measure ℕ) [IsProbabilityMeasure mu] :
    HasLaw Prod.fst (poissonMeasure rate) (compoundSampleMeasure rate mu) := by
  refine ⟨measurable_fst.aemeasurable, ?_⟩
  simp [compoundSampleMeasure, Measure.map_fst_prod]

theorem hasLaw_mark_sequence (rate : ℝ≥0) (mu : Measure ℕ) [IsProbabilityMeasure mu] :
    HasLaw Prod.snd (markSequenceMeasure mu) (compoundSampleMeasure rate mu) := by
  refine ⟨measurable_snd.aemeasurable, ?_⟩
  simp [compoundSampleMeasure, Measure.map_snd_prod]

def mappedMarkMeasure (mu : Measure ℕ) (f : ℕ → ℕ) : Measure ℕ := mu.map f

instance instProbabilityMappedMark (mu : Measure ℕ) [IsProbabilityMeasure mu] (f : ℕ → ℕ) :
    IsProbabilityMeasure (mappedMarkMeasure mu f) := by
  unfold mappedMarkMeasure
  exact Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable

/-- Applying the same measurable map to every mark preserves the independent construction. -/
theorem hasLaw_mapped_mark_sum (rate : ℝ≥0) (mu : Measure ℕ) [IsProbabilityMeasure mu]
    (f : ℕ → ℕ) :
    HasLaw (fun sample : ℕ × (ℕ → ℕ) => ∑ i ∈ Finset.range sample.1, f (sample.2 i))
      (compoundMeasure rate (mappedMarkMeasure mu f)) (compoundSampleMeasure rate mu) := by
  have hf : Measurable f := measurable_of_countable _
  have hmap : HasLaw (fun sample : ℕ × (ℕ → ℕ) =>
      (sample.1, fun i : ℕ => f (sample.2 i)))
      (compoundSampleMeasure rate (mappedMarkMeasure mu f)) (compoundSampleMeasure rate mu) := by
    refine ⟨(measurable_fst.prodMk (measurable_pi_lambda _ (fun i =>
      hf.comp ((measurable_pi_apply i).comp measurable_snd)))).aemeasurable, ?_⟩
    change ((poissonMeasure rate).prod (markSequenceMeasure mu)).map
      (Prod.map id (fun marks : ℕ → ℕ => fun i => f (marks i))) = _
    rw [← Measure.map_prod_map _ _ measurable_id (by fun_prop), Measure.map_id]
    unfold compoundSampleMeasure markSequenceMeasure mappedMarkMeasure
    rw [Measure.infinitePi_map_pi _ (fun _ => hf)]
  exact (hasLaw_stoppedMarkSum rate (mappedMarkMeasure mu f)).fun_comp hmap

theorem count_independent_mark_sequence (rate : ℝ≥0) (mu : Measure ℕ)
    [IsProbabilityMeasure mu] :
    IndepFun Prod.fst Prod.snd (compoundSampleMeasure rate mu) :=
  indepFun_prod measurable_id measurable_id

theorem independent_marks (mu : Measure ℕ) [IsProbabilityMeasure mu] :
    iIndepFun (fun i (marks : ℕ → ℕ) => marks i) (markSequenceMeasure mu) :=
  iIndepFun_infinitePi (fun _ => measurable_id)

theorem hasLaw_mark_coordinate (mu : Measure ℕ) [IsProbabilityMeasure mu] (i : ℕ) :
    HasLaw (fun marks : ℕ → ℕ => marks i) mu (markSequenceMeasure mu) :=
  (measurePreserving_eval_infinitePi (fun _ : ℕ => mu) i).hasLaw

theorem integrable_unit_powers {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu] (f : Omega → ℕ) (hf : Measurable f)
    {z : ℝ} (hz : 0 ≤ z) (hzOne : z ≤ 1) :
    Integrable (fun omega => z ^ f omega) mu := by
  refine ⟨((measurable_of_countable (fun n : ℕ => z ^ n)).comp hf).aestronglyMeasurable, ?_⟩
  apply HasFiniteIntegral.of_bounded (C := 1)
  exact Filter.Eventually.of_forall fun omega => by
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hz _)]
    exact pow_le_one₀ hz hzOne

/-- The fixed initial segment really has the product of the mark generating functions. -/
theorem integral_fixed_mark_sum (mu : Measure ℕ) [IsProbabilityMeasure mu]
    (z : ℝ) (n : ℕ) :
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

theorem integral_poisson_powers (rate : ℝ≥0) (t : ℝ) :
    (∫ n, t ^ n ∂poissonMeasure rate) = Real.exp ((rate : ℝ) * (t - 1)) := by
  rw [integral_poissonMeasure]
  simp only [smul_eq_mul]
  calc
    (∑' n : ℕ, (Real.exp (-(rate : ℝ)) * (rate : ℝ) ^ n / n.factorial) * t ^ n) =
        Real.exp (-(rate : ℝ)) * ∑' n : ℕ, ((rate : ℝ) * t) ^ n / n.factorial := by
      rw [← tsum_mul_left]
      congr 1
      funext n
      rw [mul_pow]
      ring
    _ = Real.exp ((rate : ℝ) * (t - 1)) := by
      rw [(NormedSpace.expSeries_div_hasSum_exp ((rate : ℝ) * t)).tsum_eq,
        ← Real.exp_eq_exp_ℝ, ← Real.exp_add]
      congr 1
      ring

/-- Probability generating function of the actual independent random sum. -/
theorem compound_pgf (rate : ℝ≥0) (mu : Measure ℕ) [IsProbabilityMeasure mu]
    {z : ℝ} (hz : 0 ≤ z) (hzOne : z ≤ 1) :
    (∫ n, z ^ n ∂compoundMeasure rate mu) =
      Real.exp ((rate : ℝ) * ((∫ h, z ^ h ∂mu) - 1)) := by
  rw [← (hasLaw_stoppedMarkSum rate mu).integral_comp
    (measurable_of_countable (fun n : ℕ => z ^ n)).aestronglyMeasurable]
  simp only [Function.comp_apply]
  rw [compoundSampleMeasure, integral_prod _
    (integrable_unit_powers _ stoppedMarkSum measurable_stoppedMarkSum hz hzOne)]
  simp_rw [stoppedMarkSum, integral_fixed_mark_sum]
  exact integral_poisson_powers _ _

end
end PaperC.V282.CompoundPoissonTarget
