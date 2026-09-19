import PaperCPrel8.EmpiricalSupportTarget
import PaperCV282.UniformSpatialGrid

/-! # Finite-support obstruction for the actual uniform empirical measure

Testing E outside the empirical support yields nu(E)-N*b whenever each
target atom in E has mass at most b. This is deterministic and uniform in
the observed configurations, including repeated observations.
-/
namespace PaperC.Prel8.EmpiricalFiniteSupport
open MeasureTheory ProbabilityTheory
open PaperC.V282.SharpConditioning PaperC.V282.SharpConditioningDiscrete
open PaperC.V282.UniformSpatialGrid PaperC.V282.PoissonFieldMeasure
open PaperC.Prel8.EmpiricalSupportTarget
open scoped BigOperators NNReal
noncomputable section
local instance (α : Type*) : DecidableEq α := Classical.decEq α
local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- A finite set captures at most its cardinality times the maximal relevant atom. -/
theorem finite_event_mass_le {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (ν : Measure α) [IsFiniteMeasure ν] (S : Finset α) (E : Set α) (b : ℝ)
    (hb : 0 ≤ b) (hatom : ∀ x ∈ E, ν.real {x} ≤ b) :
    ν.real (E ∩ (S:Set α)) ≤ S.card*b := by
  classical
  have he : E ∩ (S:Set α) = (S.filter (fun x => x ∈ E):Set α) := by
    ext x
    simp [and_comm]
  rw [he,← sum_measureReal_singleton]
  calc
    _ ≤ ∑ _x ∈ S.filter (fun x => x ∈ E), b :=
      Finset.sum_le_sum (fun x hx => hatom x (Finset.mem_filter.mp hx).2)
    _ = ((S.filter (fun x => x ∈ E)).card:ℝ)*b := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_filter_le S (fun x => x ∈ E)) hb

/-- A normalized source supported on S misses all of E outside S. -/
theorem support_obstruction {α : Type*} [MeasurableSpace α] [Countable α]
    [MeasurableSingletonClass α] (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (S : Finset α) (hs : μ (S:Set α)ᶜ = 0) (E : Set α) (b : ℝ)
    (hb : 0 ≤ b) (hatom : ∀ x ∈ E, ν.real {x} ≤ b) :
    ν.real E-S.card*b ≤ measureTotalVariation μ ν := by
  have hz : μ.real (E \ (S:Set α)) = 0 := by
    have h : μ (E \ (S:Set α)) = 0 := measure_mono_null (by intro x hx; exact hx.2) hs
    simp only [Measure.real,h,ENNReal.toReal_zero]
  have ht := discrepancy_le μ ν (E \ (S:Set α)) (Set.to_countable _).measurableSet
  rw [hz,zero_sub,abs_neg,abs_of_nonneg measureReal_nonneg] at ht
  have hsplit := measureReal_sdiff_add_inter (μ := ν) (s := E) S.measurableSet
  have hm := finite_event_mass_le ν S E b hb hatom
  linarith

/-- The empirical law is the genuine pushforward of the uniform origin. -/
def empiricalMeasure {α : Type*} [MeasurableSpace α] (N : ℕ) (hN : 0 < N)
    (v : Fin N → α) : Measure α := (uniformGridMeasure N hN).map v

instance empiricalMeasure_probability {α : Type*} [MeasurableSpace α]
    (N : ℕ) (hN : 0 < N) (v : Fin N → α) : IsProbabilityMeasure (empiricalMeasure N hN v) := by
  unfold empiricalMeasure
  exact (Measure.isProbabilityMeasure_map_iff (measurable_of_countable v).aemeasurable).mpr inferInstance

/-- The pushforward has exactly the empirical frequency of every measurable event. -/
theorem empiricalMeasure_real_apply {α : Type*} [MeasurableSpace α]
    (N : ℕ) (hN : 0 < N) (v : Fin N → α) (E : Set α) (hE : MeasurableSet E) :
    (empiricalMeasure N hN v).real E =
      ((Finset.univ.filter (fun i => v i ∈ E)).card:ℝ)/(N:ℝ) := by
  classical
  let : NeZero N := ⟨hN.ne'⟩
  rw [Measure.real,empiricalMeasure,Measure.map_apply (measurable_of_countable _) hE]
  unfold uniformGridMeasure
  rw [PMF.toMeasure_uniformOfFintype_apply _ ((measurable_of_countable v) hE)]
  simp [ENNReal.toReal_div,Fintype.card_subtype]

/-- Repeated observations cannot increase the support beyond N points. -/
theorem empirical_support_null {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (N : ℕ) (hN : 0 < N) (v : Fin N → α) :
    (empiricalMeasure N hN v) (Finset.univ.image v : Set α)ᶜ = 0 := by
  classical
  rw [empiricalMeasure,Measure.map_apply (measurable_of_countable _) (Finset.measurableSet _).compl]
  have he : v ⁻¹' (Finset.univ.image v : Set α)ᶜ = ∅ := by ext i; simp
  rw [he,measure_empty]

/-- Uniform empirical laws obey the cardinality-N obstruction for every deterministic sample. -/
theorem empirical_obstruction {α : Type*} [MeasurableSpace α] [Countable α]
    [MeasurableSingletonClass α] (N : ℕ) (hN : 0 < N) (v : Fin N → α)
    (ν : Measure α) [IsProbabilityMeasure ν] (E : Set α) (b : ℝ)
    (hb : 0 ≤ b) (hatom : ∀ x ∈ E, ν.real {x} ≤ b) :
    ν.real E-N*b ≤ measureTotalVariation (empiricalMeasure N hN v) ν := by
  classical
  have h := support_obstruction (empiricalMeasure N hN v) ν (Finset.univ.image v)
    (empirical_support_null N hN v) E b hb hatom
  have hc : ((Finset.univ.image v).card:ℝ) ≤ N := by
    exact_mod_cast (Finset.card_image_le.trans (by simp : Finset.univ.card ≤ N))
  nlinarith

/-- The paper's finite bound, uniformly over every possible observed local vector. -/
theorem empirical_poisson_obstruction (N h : ℕ) (hN : 0 < N) (p : ℝ≥0) (hp : p ≤ 1)
    (v : Fin N → Fin h → ℕ) :
    1-Real.exp (-(h:ℝ)*(p:ℝ))*(1+(h:ℝ)*(p:ℝ))-(N:ℝ)*(p:ℝ)^2 ≤
      measureTotalVariation (empiricalMeasure N hN v) (fieldMeasure (fun _ : Fin h => p)) := by
  have ht := empirical_obstruction N hN v (fieldMeasure (fun _ : Fin h => p))
    {z | 2 ≤ ∑ i, z i} ((p:ℝ)^2) (sq_nonneg _) (fun z hz => multiple_point_mass_le p hp z hz)
  rw [field_multiple_probability] at ht
  simpa only [Fintype.card_fin] using ht

end
end PaperC.Prel8.EmpiricalFiniteSupport
