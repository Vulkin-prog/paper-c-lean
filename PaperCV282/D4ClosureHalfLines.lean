import PaperCV282.D4ClosureIntegerLevels
import PaperCV282.GeometricConfigurationCounts
import PaperCV282.D4ClosureCovariance

/-! # Almost-sure finite upper tails of the two-sided target

The measurable inverse below merely gives a total definition on the null
set of non-finite tails; the actual coordinates agree almost surely.
-/
namespace PaperC.V282.D4ClosureHalfLines

open MeasureTheory ProbabilityTheory
open D4ClosureIntegerLevels D4ClosureThreshold D4ClosureCovariance
open GeometricMarkedConfiguration GeometricConfigurationCounts ThresholdPathEquivalence
open scoped BigOperators NNReal ENNReal

noncomputable section

theorem measurableEmbedding_configuration :
    MeasurableEmbedding (fun c : ℕ →₀ ℕ => (c : ℕ → ℕ)) :=
  ⟨(fun _ _ h => Finsupp.ext (congrFun h)), measurable_of_countable _, fun {_} _ =>
    (Set.to_countable _).image _ |>.measurableSet⟩

def recoverConfiguration (v : ℕ → ℕ) : ℕ →₀ ℕ :=
  measurableEmbedding_configuration.invFun v

theorem measurable_recoverConfiguration : Measurable recoverConfiguration :=
  measurableEmbedding_configuration.measurable_invFun

theorem recoverConfiguration_coe (c : ℕ →₀ ℕ) : recoverConfiguration c = c :=
  measurableEmbedding_configuration.leftInverse_invFun c

def halfLineConfiguration (m : ℤ) (counts : ℤ → ℕ) : ℕ →₀ ℕ :=
  recoverConfiguration (halfLineCounts m counts)

theorem measurable_halfLineConfiguration (m : ℤ) : Measurable (halfLineConfiguration m) :=
  measurable_recoverConfiguration.comp (measurable_halfLineCounts m)

theorem hasLaw_halfLineConfiguration (theta : ℝ) (m : ℤ) :
    HasLaw (halfLineConfiguration m) (configurationMeasure (integerHalfRate theta m))
      (integerCountMeasure theta) := by
  refine ⟨(measurable_halfLineConfiguration m).aemeasurable, ?_⟩
  rw [show halfLineConfiguration m = recoverConfiguration ∘ halfLineCounts m from rfl,
    ← Measure.map_map measurable_recoverConfiguration (measurable_halfLineCounts m),
    halfLineCounts_law, Measure.map_map measurable_recoverConfiguration
      measurableEmbedding_configuration.measurable]
  have he : recoverConfiguration ∘ (fun c : ℕ →₀ ℕ => (c : ℕ → ℕ)) = id :=
    funext recoverConfiguration_coe
  rw [he, Measure.map_id]

theorem ae_halfLineConfiguration_coordinates (theta : ℝ) (m : ℤ) :
    ∀ᵐ counts ∂integerCountMeasure theta,
      ∀ e : ℕ, halfLineConfiguration m counts e = counts (m + e) := by
  have hr : ∀ᵐ v ∂(configurationMeasure (integerHalfRate theta m)).map
      (fun c : ℕ →₀ ℕ => (c : ℕ → ℕ)),
      v ∈ Set.range (fun c : ℕ →₀ ℕ => (c : ℕ → ℕ)) := by
    apply (ae_map_iff (μ := configurationMeasure (integerHalfRate theta m))
      (p := fun v => v ∈ Set.range (fun c : ℕ →₀ ℕ => (c : ℕ → ℕ)))
      measurableEmbedding_configuration.measurable.aemeasurable
      measurableEmbedding_configuration.measurableSet_range).2
    exact Filter.Eventually.of_forall fun c => ⟨c, rfl⟩
  rw [← halfLineCounts_law theta m] at hr
  have hr' := (ae_map_iff (μ := integerCountMeasure theta)
    (p := fun v => v ∈ Set.range (fun c : ℕ →₀ ℕ => (c : ℕ → ℕ)))
    (measurable_halfLineCounts m).aemeasurable
    measurableEmbedding_configuration.measurableSet_range).1 hr
  filter_upwards [hr'] with counts hc
  obtain ⟨c, hc⟩ := hc
  have hrec : halfLineConfiguration m counts = c := by
    change recoverConfiguration (halfLineCounts m counts) = c
    rw [← hc, recoverConfiguration_coe]
  intro e
  rw [hrec]
  exact congrFun hc e

/-- Simultaneously for every integer starting level, only finitely many
upper exact-level counts are nonzero. -/
theorem ae_all_upper_tails_finite (theta : ℝ) :
    ∀ᵐ counts ∂integerCountMeasure theta,
      ∀ m : ℤ, (Function.support (halfLineCounts m counts)).Finite := by
  have hall := ae_all_iff.mpr (ae_halfLineConfiguration_coordinates theta)
  filter_upwards [hall] with counts hc
  intro m
  have he : halfLineCounts m counts = (halfLineConfiguration m counts : ℕ → ℕ) :=
    funext fun e => (hc m e).symm
  rw [he]
  exact (halfLineConfiguration m counts).hasFiniteSupport

def integerThreshold (m : ℤ) (counts : ℤ → ℕ) : ℕ :=
  configurationSize (halfLineConfiguration m counts)

theorem hasLaw_integerThreshold (theta : ℝ) (m : ℤ) :
    HasLaw (integerThreshold m) (poissonMeasure (integerHalfRate theta m))
      (integerCountMeasure theta) :=
  (hasLaw_configurationSize _).fun_comp (hasLaw_halfLineConfiguration theta m)

end
end PaperC.V282.D4ClosureHalfLines
