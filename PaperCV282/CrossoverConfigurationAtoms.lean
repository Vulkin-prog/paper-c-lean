import PaperCV282.PoissonResolvedTarget
import Mathlib.Algebra.BigOperators.Finsupp.Basic

/-! # Exact empty and one-point atoms of the geometric Poisson configuration -/
namespace PaperC.V282.CrossoverConfigurationAtoms

open MeasureTheory ProbabilityTheory GeometricMarkedConfiguration GeometricConfigurationCounts
open GeometricClusterTarget CompoundPoissonTarget PoissonResolvedTarget SharpConditioning ConditionedCountableLaw
open scoped BigOperators NNReal ENNReal

noncomputable section
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

theorem configurationSize_eq_zero_iff (c : ℕ →₀ ℕ) : configurationSize c=0 ↔ c=0 := by
  constructor
  · intro h
    ext e
    have he : c e≤configurationSize c := by
      by_cases hm : e∈c.support
      · exact Finset.single_le_sum (fun i hi => Nat.zero_le _) hm
      · simp only [Finsupp.mem_support_iff,ne_eq,not_not] at hm
        rw [hm]
        exact Nat.zero_le _
    simp only [Finsupp.zero_apply]
    omega
  · rintro rfl
    simp [configurationSize]

theorem configurationSize_single (e : ℕ) : configurationSize (Finsupp.single e 1)=1 := by
  simp [configurationSize]

theorem configuration_zero_mass (rate : ℝ≥0) :
    (configurationMeasure rate).real {0}=Real.exp (-(rate : ℝ)) := by
  have he : {c : ℕ →₀ ℕ | configurationSize c=0}={0} := by
    ext c
    exact configurationSize_eq_zero_iff c
  have h := configuration_size_probability rate 0
  simpa only [he,pow_zero,Nat.factorial_zero,Nat.cast_one,mul_one,div_one] using h

theorem cluster_one_eq_single_iff (marks : ℕ → ℕ) (e : ℕ) :
    clusterConfiguration (1,marks)=Finsupp.single e 1 ↔ marks 0=e+1 := by
  simp only [clusterConfiguration,Finset.range_one,Finset.sum_singleton]
  by_cases hp : 0<marks 0
  · rw [if_pos hp]
    rw [(Finsupp.single_left_injective (by decide : (1 : ℕ)≠0)).eq_iff]
    omega
  · rw [if_neg hp]
    have hn : (0 : ℕ →₀ ℕ)≠Finsupp.single e 1 := by
      intro h
      have := congrArg (fun c : ℕ →₀ ℕ => c e) h
      simp at this
    simp only [hn,false_iff]
    omega

theorem thin_one_singleton (e : ℕ) :
    (thinConfigurationMeasure 1).real {Finsupp.single e 1}=1/(2 : ℝ)^(e+1) := by
  rw [thinConfigurationMeasure,Measure.real,Measure.map_apply (measurable_fixed_configuration 1)
    (measurableSet_singleton _)]
  have he : (fun marks : ℕ → ℕ => clusterConfiguration (1,marks)) ⁻¹' {Finsupp.single e 1}=
      (fun marks : ℕ → ℕ => marks 0) ⁻¹' {e+1} := by
    ext marks
    exact cluster_one_eq_single_iff marks e
  change (markSequenceMeasure geometricClusterMeasure).real _=_
  rw [he]
  exact ((hasLaw_mark_coordinate geometricClusterMeasure 0).measureReal_eq
    (measurableSet_singleton (e+1))).trans (geometricClusterMeasure_real_succ e)

theorem configuration_single_mass (rate : ℝ≥0) (hr : 0<rate) (e : ℕ) :
    (configurationMeasure rate).real {Finsupp.single e 1}=
      Real.exp (-(rate : ℝ))*(rate : ℝ)/(2 : ℝ)^(e+1) := by
  have hpos := configuration_size_probability_pos rate hr 1
  have hn : (poissonMeasure rate) {1}≠0 :=
    measure_ne_zero_of_real_pos _ (poissonMeasure_real_singleton_pos 1 (by exact_mod_cast hr))
  have h := congrArg (fun mu : Measure (ℕ →₀ ℕ) => mu.real {Finsupp.single e 1})
    (conditional_configuration_eq_thin rate 1 hn)
  rw [thin_one_singleton,cond_real_apply _ _ ((Set.to_countable _).measurableSet)] at h
  have he : {c : ℕ →₀ ℕ | configurationSize c=1}∩{Finsupp.single e 1}={Finsupp.single e 1} := by
    exact Set.inter_eq_right.mpr (by intro c hc;rcases hc with rfl;exact configurationSize_single e)
  rw [he] at h
  have hx := (div_eq_iff hpos.ne').mp h
  rw [configuration_size_probability] at hx
  simpa only [pow_one,Nat.factorial_one,Nat.cast_one,div_one] using hx.trans (by ring)

end
end PaperC.V282.CrossoverConfigurationAtoms
