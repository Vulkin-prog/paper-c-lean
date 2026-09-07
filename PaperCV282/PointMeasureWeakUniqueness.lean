import PaperCV282.PointMeasureSpace
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-! # Uniqueness of the weak law of genuine finite point measures

Finite measures are embedded topologically into a probability measure and a
positive mass after adding one fixed Dirac mass. This proves the missing
metrizability instance from existing weak-topology and normalization facts.
-/
namespace PaperC.V282.PointMeasureWeakUniqueness

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace PointMeasureSpace
open scoped Topology NNReal BoundedContinuousFunction

noncomputable section

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]

theorem finite_integral_add (mu nu : FiniteMeasure X) (f : X →ᵇ ℝ) :
    (∫ x,f x ∂(mu+nu : FiniteMeasure X))=(∫ x,f x ∂mu)+(∫ x,f x ∂nu) := by
  rw [FiniteMeasure.toMeasure_add,integral_add_measure (f.integrable _) (f.integrable _)]

/-- Removing a fixed finite summand preserves weak convergence. -/
theorem tendsto_of_add_constant {α : Type*} {l : Filter α} (mu : α→FiniteMeasure X)
    (target extra : FiniteMeasure X)
    (h : Tendsto (fun i => mu i+extra) l (𝓝 (target+extra))) :
    Tendsto mu l (𝓝 target) := by
  apply FiniteMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  have hi := FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp h f
  simp_rw [finite_integral_add] at hi
  simpa only [add_sub_cancel_right] using hi.sub_const (∫ x,f x ∂extra)

omit [TopologicalSpace X] [BorelSpace X] in
theorem shifted_nonzero (x : X) (mu : FiniteMeasure X) :
    mu+(diracProba x).toFiniteMeasure≠0 := by
  intro he
  have hm := congrArg (fun v : FiniteMeasure X => v.mass) he
  change (mu+(diracProba x).toFiniteMeasure) Set.univ=0 at hm
  simp only [FiniteMeasure.coeFn_add,Pi.add_apply] at hm
  change mu.mass+(diracProba x).toFiniteMeasure.mass=0 at hm
  rw [ProbabilityMeasure.mass_toFiniteMeasure] at hm
  exact (by positivity : mu.mass+(1 : ℝ≥0)≠0) hm

def probabilityMassEncoding [Nonempty X] (x : X) (mu : FiniteMeasure X) :
    ProbabilityMeasure X × ℝ≥0 :=
  ((mu+(diracProba x).toFiniteMeasure).normalize,(mu+(diracProba x).toFiniteMeasure).mass)

theorem encoding_tendsto_iff [Nonempty X] (x : X) {α : Type*} {l : Filter α}
    (mu : α→FiniteMeasure X) (target : FiniteMeasure X) :
    Tendsto (fun i => probabilityMassEncoding x (mu i)) l (𝓝 (probabilityMassEncoding x target)) ↔
      Tendsto mu l (𝓝 target) := by
  rw [probabilityMassEncoding,Prod.tendsto_iff]
  change (Tendsto (fun i => (mu i+(diracProba x).toFiniteMeasure).normalize) l
    (𝓝 (target+(diracProba x).toFiniteMeasure).normalize) ∧
    Tendsto (fun i => (mu i+(diracProba x).toFiniteMeasure).mass) l
    (𝓝 (target+(diracProba x).toFiniteMeasure).mass)) ↔ _
  rw [FiniteMeasure.tendsto_normalize_iff_tendsto (shifted_nonzero x target)]
  exact ⟨tendsto_of_add_constant mu target _,fun h => h.add_const _⟩

theorem isInducing_encoding [Nonempty X] (x : X) :
    IsInducing (probabilityMassEncoding x) := by
  apply isInducing_iff_nhds.mpr
  intro mu
  apply le_antisymm
  · exact ((encoding_tendsto_iff x id mu).mpr tendsto_id).le_comap
  · have h : Tendsto id (Filter.comap (probabilityMassEncoding x)
        (𝓝 (probabilityMassEncoding x mu))) (𝓝 mu) :=
      (encoding_tendsto_iff x id mu).mp tendsto_comap
    simpa only [Filter.tendsto_id'] using h

/-- The actual weak topology of finite measures is pseudo-metrizable on a separable metrizable base. -/
instance instPseudoMetrizableFinite [Nonempty X] [PseudoMetrizableSpace X] [SeparableSpace X] :
    PseudoMetrizableSpace (FiniteMeasure X) :=
  (isInducing_encoding (Classical.choice (inferInstance : Nonempty X))).pseudoMetrizableSpace

instance instPseudoMetrizablePoint [Nonempty X] [PseudoMetrizableSpace X] [SeparableSpace X] :
    PseudoMetrizableSpace (PointMeasure X) :=
  inferInstanceAs (PseudoMetrizableSpace (FiniteMeasure X))

instance instT2PointLaws [Nonempty X] [PseudoMetrizableSpace X] [SeparableSpace X] :
    T2Space (ProbabilityMeasure (PointMeasure X)) := by infer_instance

/-- Weak convergence of point-configuration laws has a unique genuine probability limit. -/
theorem point_law_limit_unique [Nonempty X] [PseudoMetrizableSpace X] [SeparableSpace X]
    {α : Type*} {l : Filter α} [l.NeBot] (laws : α→ProbabilityMeasure (PointMeasure X))
    (mu nu : ProbabilityMeasure (PointMeasure X))
    (hmu : Tendsto laws l (𝓝 mu)) (hnu : Tendsto laws l (𝓝 nu)) : mu=nu :=
  tendsto_nhds_unique hmu hnu

end
end PaperC.V282.PointMeasureWeakUniqueness
