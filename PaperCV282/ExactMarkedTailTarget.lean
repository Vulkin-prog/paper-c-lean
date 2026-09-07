import PaperCV282.GeometricClusterTruncation
import PaperCV282.CompoundPoissonTail

/-!
# The exact geometric target tail in total variation

Both complete and truncated targets are coupled on the actual independent
Poisson-times-geometric sample space. No moment or bounded-size argument is
used when passing to the unbounded sum of cluster sizes.
-/

namespace PaperC.V282.ExactMarkedTailTarget

open MeasureTheory ProbabilityTheory CompoundPoissonTarget GeometricClusterTarget
open GeometricClusterTruncation CompoundPoissonTail InfiniteMassCoupling
open FiniteFieldTotalVariation
open scoped BigOperators NNReal ENNReal

noncomputable section

def truncatedClusterSum (E : ℕ) (sample : ℕ × (ℕ → ℕ)) : ℕ :=
  ∑ i ∈ Finset.range sample.1, truncateMark E (sample.2 i)

theorem measurable_truncatedClusterSum (E : ℕ) : Measurable (truncatedClusterSum E) := by
  apply measurable_from_prod_countable_right
  intro n
  change Measurable (fun marks : ℕ → ℕ => ∑ i ∈ Finset.range n, truncateMark E (marks i))
  exact Finset.measurable_sum _ (fun i _ =>
    (measurable_of_countable (truncateMark E)).comp (measurable_pi_apply i))

theorem hasLaw_truncatedClusterSum (rate : ℝ≥0) (E : ℕ) :
    HasLaw (truncatedClusterSum E) (weightedGeometricPoissonMeasure rate E)
      (compoundSampleMeasure rate geometricClusterMeasure) := by
  rw [weightedGeometricPoisson_eq_compound]
  exact hasLaw_mapped_mark_sum rate geometricClusterMeasure (truncateMark E)

theorem stopped_sum_eq_truncated_outside_tail (E : ℕ) (sample : ℕ × (ℕ → ℕ))
    (h : sample ∉ sampledBadMark {k : ℕ | E + 1 < k}) :
    stoppedMarkSum sample = truncatedClusterSum E sample := by
  apply Finset.sum_congr rfl
  intro i hi
  have hle : sample.2 i ≤ E + 1 := by
    by_contra hn
    exact h ⟨i, Finset.mem_range.mp hi, Nat.lt_of_not_ge hn⟩
  simp [truncateMark, hle]

theorem geometric_sample_tail_probability (rate : ℝ≥0) (E : ℕ) :
    (compoundSampleMeasure rate geometricClusterMeasure).real
      (sampledBadMark {h : ℕ | E + 1 < h}) =
      1 - Real.exp (-(rate : ℝ) / (2 : ℝ) ^ (E + 1)) := by
  rw [sampled_bad_probability, geometricCluster_tail_real]
  congr 2
  ring

/-- Exact half-L1 comparison between the full compound target and all finite Poisson coordinates. -/
theorem compound_target_truncation_tv_le (rate : ℝ≥0) (E : ℕ) :
    massTotalVariation (fun n => (geometricCompoundMeasure rate).real {n})
      (fun n => (weightedGeometricPoissonMeasure rate E).real {n}) ≤
        (rate : ℝ) / (2 : ℝ) ^ (E + 1) := by
  have h := massTotalVariation_le_bad_mark_budget rate geometricClusterMeasure
    {h : ℕ | E + 1 < h} measurable_stoppedMarkSum (measurable_truncatedClusterSum E)
    (stopped_sum_eq_truncated_outside_tail E)
  rw [geometricCluster_tail_real] at h
  have hfull : observableLaw (compoundSampleMeasure rate geometricClusterMeasure)
      stoppedMarkSum = fun n => (geometricCompoundMeasure rate).real {n} := by
    funext n
    exact (hasLaw_geometric_random_sum rate).measureReal_eq (measurableSet_singleton n)
  have htrunc : observableLaw (compoundSampleMeasure rate geometricClusterMeasure)
      (truncatedClusterSum E) = fun n => (weightedGeometricPoissonMeasure rate E).real {n} := by
    funext n
    exact (hasLaw_truncatedClusterSum rate E).measureReal_eq (measurableSet_singleton n)
  rw [hfull, htrunc] at h
  simpa only [mul_one_div] using h

end
end PaperC.V282.ExactMarkedTailTarget
