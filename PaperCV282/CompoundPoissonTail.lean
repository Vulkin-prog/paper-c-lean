import PaperCV282.CompoundPoissonTarget
import PaperCV282.InfiniteMassCoupling

/-!
# A coupling bound for deleting marks of a compound Poisson sample

The probability of encountering a forbidden mark is computed in the actual
Poisson-times-iid sample space. No boundedness of the mark sizes is needed.
-/

namespace PaperC.V282.CompoundPoissonTail

open MeasureTheory ProbabilityTheory CompoundPoissonTarget InfiniteMassCoupling
open scoped BigOperators NNReal ENNReal

noncomputable section

local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

def badMarkIndicator (bad : Set ℕ) (h : ℕ) : ℕ := if h ∈ bad then 1 else 0

def sampledBadMark (bad : Set ℕ) : Set (ℕ × (ℕ → ℕ)) :=
  {sample | ∃ i < sample.1, sample.2 i ∈ bad}

def badMarkCount (bad : Set ℕ) (sample : ℕ × (ℕ → ℕ)) : ℕ :=
  ∑ i ∈ Finset.range sample.1, badMarkIndicator bad (sample.2 i)

theorem measurable_badMarkCount (bad : Set ℕ) : Measurable (badMarkCount bad) := by
  apply measurable_from_prod_countable_right
  intro n
  change Measurable (fun marks : ℕ → ℕ => ∑ i ∈ Finset.range n, badMarkIndicator bad (marks i))
  exact Finset.measurable_sum _ (fun i _ =>
    (measurable_of_countable (badMarkIndicator bad)).comp (measurable_pi_apply i))

theorem badMarkCount_eq_zero_iff (bad : Set ℕ) (sample : ℕ × (ℕ → ℕ)) :
    badMarkCount bad sample = 0 ↔ sample ∉ sampledBadMark bad := by
  simp [badMarkCount, badMarkIndicator, sampledBadMark]

theorem measurableSet_sampledBadMark (bad : Set ℕ) : MeasurableSet (sampledBadMark bad) := by
  have heq : sampledBadMark bad = {sample | badMarkCount bad sample = 0}ᶜ := by
    ext sample
    simp [badMarkCount_eq_zero_iff]
  rw [heq]
  exact ((measurable_badMarkCount bad) (measurableSet_singleton 0)).compl

theorem integral_zero_powers {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu] (f : Omega → ℕ) (hf : Measurable f) :
    (∫ omega, (0 : ℝ) ^ f omega ∂mu) = mu.real {omega | f omega = 0} := by
  have heq : (fun omega => (0 : ℝ) ^ f omega) =
      {omega | f omega = 0}.indicator (fun _ => (1 : ℝ)) := by
    funext omega
    by_cases h : f omega = 0 <;> simp [h]
  rw [heq]
  have hset : MeasurableSet {omega | f omega = 0} := hf (measurableSet_singleton 0)
  simpa only [smul_eq_mul, mul_one] using
    integral_indicator_const (μ := mu) (s := {omega | f omega = 0}) (1 : ℝ) hset

theorem bad_mark_zero_transform (mu : Measure ℕ) [IsProbabilityMeasure mu] (bad : Set ℕ) :
    (∫ h, (0 : ℝ) ^ h ∂mappedMarkMeasure mu (badMarkIndicator bad)) = 1 - mu.real bad := by
  rw [mappedMarkMeasure, integral_map (measurable_of_countable _).aemeasurable
    (measurable_of_countable (fun h : ℕ => (0 : ℝ) ^ h)).aestronglyMeasurable,
    integral_zero_powers mu _ (measurable_of_countable _)]
  have heq : {h : ℕ | badMarkIndicator bad h = 0} = badᶜ := by
    ext h
    simp [badMarkIndicator]
  rw [heq, measureReal_compl (Set.to_countable bad).measurableSet, probReal_univ]

/-- Exact probability that at least one sampled mark lies in a given set. -/
theorem sampled_bad_probability (rate : ℝ≥0) (mu : Measure ℕ)
    [IsProbabilityMeasure mu] (bad : Set ℕ) :
    (compoundSampleMeasure rate mu).real (sampledBadMark bad) =
      1 - Real.exp (-(rate : ℝ) * mu.real bad) := by
  have hpgf := compound_pgf rate (mappedMarkMeasure mu (badMarkIndicator bad))
    (z := 0) (by norm_num) (by norm_num)
  rw [bad_mark_zero_transform] at hpgf
  have hi := integral_zero_powers (compoundMeasure rate
    (mappedMarkMeasure mu (badMarkIndicator bad))) id measurable_id
  change (∫ n : ℕ, (0 : ℝ) ^ n ∂compoundMeasure rate
    (mappedMarkMeasure mu (badMarkIndicator bad))) = _ at hi
  rw [hi] at hpgf
  have hLaw := hasLaw_mapped_mark_sum rate mu (badMarkIndicator bad)
  have hzero := hLaw.measureReal_eq (measurableSet_singleton 0)
  have heq : {sample : ℕ × (ℕ → ℕ) |
      (∑ i ∈ Finset.range sample.1, badMarkIndicator bad (sample.2 i)) = 0} =
      (sampledBadMark bad)ᶜ := by
    ext sample
    exact badMarkCount_eq_zero_iff bad sample
  change (compoundSampleMeasure rate mu).real {sample |
    (∑ i ∈ Finset.range sample.1, badMarkIndicator bad (sample.2 i)) = 0} = _ at hzero
  rw [heq, measureReal_compl (measurableSet_sampledBadMark bad), probReal_univ] at hzero
  change 1 - (compoundSampleMeasure rate mu).real (sampledBadMark bad) =
    (compoundMeasure rate (mappedMarkMeasure mu (badMarkIndicator bad))).real {0} at hzero
  have hexp : (rate : ℝ) * (1 - mu.real bad - 1) = -(rate : ℝ) * mu.real bad := by ring
  rw [hexp] at hpgf
  change (compoundMeasure rate (mappedMarkMeasure mu (badMarkIndicator bad))).real {0} = _ at hpgf
  linarith

theorem sampled_bad_probability_le (rate : ℝ≥0) (mu : Measure ℕ)
    [IsProbabilityMeasure mu] (bad : Set ℕ) :
    (compoundSampleMeasure rate mu).real (sampledBadMark bad) ≤ (rate : ℝ) * mu.real bad := by
  rw [sampled_bad_probability]
  have h := Real.add_one_le_exp (-(rate : ℝ) * mu.real bad)
  linarith

/-- Any two observables agreeing unless a deleted mark occurs inherit the tail budget. -/
theorem massTotalVariation_le_bad_mark_budget {alpha : Type*} [Countable alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    (rate : ℝ≥0) (mu : Measure ℕ) [IsProbabilityMeasure mu] (bad : Set ℕ)
    {f g : (ℕ × (ℕ → ℕ)) → alpha} (hf : Measurable f) (hg : Measurable g)
    (hagree : ∀ sample, sample ∉ sampledBadMark bad → f sample = g sample) :
    FiniteFieldTotalVariation.massTotalVariation
      (observableLaw (compoundSampleMeasure rate mu) f)
      (observableLaw (compoundSampleMeasure rate mu) g) ≤ (rate : ℝ) * mu.real bad :=
  (massTotalVariation_observableLaw_le_event _ hf hg hagree).trans
    (sampled_bad_probability_le rate mu bad)

end
end PaperC.V282.CompoundPoissonTail
