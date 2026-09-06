import PaperCV282.GeometricMarkedConfiguration

/-!
# Total counts and actual tails of a geometric Poisson configuration

These are statements about the finite-support configuration law constructed
from an independent Poisson count and geometric marks, including its full tail.
-/
namespace PaperC.V282.GeometricConfigurationCounts

open MeasureTheory ProbabilityTheory GeometricMarkedConfiguration GeometricClusterTarget
open CompoundPoissonTarget CompoundPoissonTail ExactMarkedTailTarget
open scoped BigOperators NNReal ENNReal

noncomputable section

def configurationSize (config : ℕ →₀ ℕ) : ℕ := config.sum (fun _ n => n)

theorem configurationSize_clusterConfiguration (sample : ℕ × (ℕ → ℕ)) :
    configurationSize (clusterConfiguration sample) =
      ∑ i ∈ Finset.range sample.1, if 0 < sample.2 i then 1 else 0 := by
  classical
  unfold configurationSize clusterConfiguration
  rw [← Finsupp.sum_finsetSum_index]
  · apply Finset.sum_congr rfl
    intro i hi
    split_ifs <;> simp
  · intro e
    rfl
  · intro e n m
    rfl

theorem configurationSize_eq_count_ae (rate : ℝ≥0) :
    (fun sample => configurationSize (clusterConfiguration sample)) =ᵐ[
      compoundSampleMeasure rate geometricClusterMeasure] Prod.fst := by
  have hcoord (i : ℕ) : ∀ᵐ sample ∂compoundSampleMeasure rate geometricClusterMeasure,
      1 ≤ sample.2 i :=
    ((hasLaw_mark_coordinate geometricClusterMeasure i).fun_comp
      (hasLaw_mark_sequence rate geometricClusterMeasure)).ae_iff
        (measurable_of_countable _) |>.mpr geometricClusterMeasure_positive
  filter_upwards [ae_all_iff.mpr hcoord] with sample hs
  rw [configurationSize_clusterConfiguration]
  simp [show ∀ i, 0 < sample.2 i from fun i => by have := hs i; omega]

theorem hasLaw_configurationSize (rate : ℝ≥0) :
    HasLaw configurationSize (poissonMeasure rate) (configurationMeasure rate) := by
  have h := (hasLaw_poisson_count rate geometricClusterMeasure).congr
    (configurationSize_eq_count_ae rate)
  refine ⟨(measurable_of_countable _).aemeasurable, ?_⟩
  rw [configurationMeasure, Measure.map_map (measurable_of_countable _) measurable_clusterConfiguration]
  exact h.map_eq

def configurationTail (E : ℕ) : Set (ℕ →₀ ℕ) := {config | ∃ e, E < e ∧ config e ≠ 0}

theorem clusterConfiguration_preimage_tail (E : ℕ) :
    clusterConfiguration ⁻¹' configurationTail E = sampledBadMark {h : ℕ | E + 1 < h} := by
  classical
  ext sample
  change (∃ e, E < e ∧ clusterConfiguration sample e ≠ 0) ↔
    ∃ i < sample.1, E + 1 < sample.2 i
  constructor
  · rintro ⟨e,he,hne⟩
    by_contra hn
    push Not at hn
    apply hne
    rw [clusterConfiguration_apply]
    apply Finset.sum_eq_zero
    intro i hi
    have hh := hn i (Finset.mem_range.mp hi)
    rw [if_neg (by omega)]
  · rintro ⟨i,hi,hh⟩
    refine ⟨sample.2 i - 1, by omega, ?_⟩
    rw [clusterConfiguration_apply]
    apply Nat.ne_of_gt
    apply Finset.sum_pos'
    · intro j hj
      exact Nat.zero_le _
    · refine ⟨i, Finset.mem_range.mpr hi, ?_⟩
      rw [if_pos (show sample.2 i = sample.2 i - 1 + 1 by omega)]
      decide

theorem configuration_tail_probability (rate : ℝ≥0) (E : ℕ) :
    (configurationMeasure rate).real (configurationTail E) =
      1 - Real.exp (-(rate : ℝ) / (2 : ℝ) ^ (E + 1)) := by
  have h := (hasLaw_configuration rate).measureReal_eq
    ((Set.to_countable (configurationTail E)).measurableSet)
  change (compoundSampleMeasure rate geometricClusterMeasure).real
    (clusterConfiguration ⁻¹' configurationTail E) =
      (configurationMeasure rate).real (configurationTail E) at h
  rw [clusterConfiguration_preimage_tail] at h
  exact h.symm.trans (geometric_sample_tail_probability rate E)

theorem configuration_tail_probability_le (rate : ℝ≥0) (E : ℕ) :
    (configurationMeasure rate).real (configurationTail E) ≤
      (rate : ℝ) / (2 : ℝ) ^ (E + 1) := by
  have h := (hasLaw_configuration rate).measureReal_eq
    ((Set.to_countable (configurationTail E)).measurableSet)
  change (compoundSampleMeasure rate geometricClusterMeasure).real
    (clusterConfiguration ⁻¹' configurationTail E) =
      (configurationMeasure rate).real (configurationTail E) at h
  rw [clusterConfiguration_preimage_tail] at h
  rw [← h]
  have hb := sampled_bad_probability_le rate geometricClusterMeasure {h : ℕ | E + 1 < h}
  rw [geometricCluster_tail_real] at hb
  simpa only [mul_one_div] using hb

end
end PaperC.V282.GeometricConfigurationCounts
