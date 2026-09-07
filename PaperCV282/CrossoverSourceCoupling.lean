import PaperCV282.CrossoverSourceGeometry

/-! # Almost-sure source couplings on actual rare conditioning events -/
namespace PaperC.V282.CrossoverSourceCoupling

open MeasureTheory ProbabilityTheory Set Filter InfiniteRademacher SharpConditioning ConditionedCountableLaw
open CrossoverSourceGeometry CrossoverMarkedModel CrossoverMarkedCandidate CrossoverBulkAtoms
open CrossoverPrimeClockStable BulkMarkedTypes BulkMarkedSource BulkMarkedGeometry
open RarePrefixGeometry RarePrefixEvents MicroscopicNonvacancy

noncomputable section
local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤
local instance instProbabilityInfiniteRademacher : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

/-- Coupling of arbitrary measurable observations, with an almost-sure exceptional-set inclusion. -/
theorem map_tv_le_of_ae_eq_off {Omega Alpha : Type*} [MeasurableSpace Omega] [MeasurableSpace Alpha]
    (mu : Measure Omega) [IsProbabilityMeasure mu] (E : Set Omega)
    {f g : Omega→Alpha} (hf : Measurable f) (hg : Measurable g)
    (h : ∀ᵐ omega ∂mu, omega∉E → f omega=g omega) :
    measureTotalVariation (mu.map f) (mu.map g) ≤ mu.real E := by
  letI instProbabilityMapF : IsProbabilityMeasure (mu.map f) := Measure.isProbabilityMeasure_map hf.aemeasurable
  letI instProbabilityMapG : IsProbabilityMeasure (mu.map g) := Measure.isProbabilityMeasure_map hg.aemeasurable
  apply (measureTotalVariation_le_iff _ _ _).mpr
  intro A hA
  simp only [Measure.real,Measure.map_apply hf hA,Measure.map_apply hg hA]
  apply (abs_measureReal_sub_le_measureReal_symmDiff (hf hA).nullMeasurableSet
    (hg hA).nullMeasurableSet).trans
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [h] with omega ho
  intro hs
  by_contra hn
  have he := ho hn
  change (f omega∈A ∧ g omega∉A) ∨ (g omega∈A ∧ f omega∉A) at hs
  rcases hs with hs | hs
  · exact hs.2 (he ▸ hs.1)
  · exact hs.2 (he.symm ▸ hs.1)

/-- The source map fed to the root's common candidate; marks and the actual clock are unchanged. -/
def candidateSource (M L K : ℕ) (delta : ℝ) (omega : InfiniteSample) : Record :=
  candidate (bulkStarts M L delta)
    (actualClockRecord L K omega,spatialMarkedSource (bulkStarts M L delta) L omega)

theorem measurable_candidateSource (M L K : ℕ) (delta : ℝ) : Measurable (candidateSource M L K delta) :=
  (measurable_of_countable _).comp ((measurable_actualClockRecord L K).prodMk
    (measurable_spatialMarkedSource _ _))

theorem measurable_capGamma (M L K : ℕ) (delta : ℝ) :
    Measurable (fun omega => capBorder K (gamma M L delta omega)) :=
  (measurable_of_countable (capBorder K)).comp (measurable_gamma M L delta)

/-- Conditioning is on any actual measurable source event with at most one bulk point.
In particular the root's sparse event satisfies this geometric condition. -/
theorem conditional_capGamma_candidate_le {M L K : ℕ} {delta : ℝ}
    (hM : 2≤M) (hL : 1≤L) (hLM : L≤M) (hdelta : 0<delta)
    (E : Set InfiniteSample) (hE : MeasurableSet E) (hEpos : 0 < infiniteRademacherMeasure.real E)
    (hsmall : ∀ omega∈E, totalSize (bulkStarts M L delta) (spatialMarkedSource _ L omega)≤1) :
    measureTotalVariation
      ((cond infiniteRademacherMeasure E).map (fun omega => capBorder K (gamma M L delta omega)))
      ((cond infiniteRademacherMeasure E).map (candidateSource M L K delta)) ≤
      (infiniteRademacherMeasure.real (interiorEvent L)+
        infiniteRademacherMeasure.real (middleEvent M L delta))/infiniteRademacherMeasure.real E := by
  letI instProbabilityConditional : IsProbabilityMeasure (cond infiniteRademacherMeasure E) :=
    cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ hEpos)
  have habs : cond infiniteRademacherMeasure E ≪ infiniteRademacherMeasure := cond_absolutelyContinuous
  have hc := habs.ae_le (ae_capGamma_eq_candidate (K := K) hM hL hLM hdelta)
  have hcouple : ∀ᵐ omega ∂cond infiniteRademacherMeasure E,
      omega∉interiorEvent L ∪ middleEvent M L delta →
      capBorder K (gamma M L delta omega)=candidateSource M L K delta omega := by
    filter_upwards [hc,ae_cond_mem hE] with omega ho he
    intro hn
    exact ho (fun h => hn (Or.inl h)) (fun h => hn (Or.inr h)) (hsmall omega he)
  apply (map_tv_le_of_ae_eq_off _ _ (measurable_capGamma M L K delta)
    (measurable_candidateSource M L K delta) hcouple).trans
  rw [cond_real_apply _ E hE]
  apply div_le_div_of_nonneg_right _ hEpos.le
  exact (measureReal_mono inter_subset_right).trans (measureReal_union_le _ _)

/-- The complete source rare event is contained in the true finite-prefix hit, without a null-set qualification. -/
theorem source_rare_subset_hit {M L K : ℕ} {delta : ℝ}
    (hM : 2≤M) (hL : 1≤L) (hLM : L≤M) (hdelta : 0<delta) :
    (fun omega => (actualClockRecord L K omega,spatialMarkedSource (bulkStarts M L delta) L omega)) ⁻¹'
      rareEvent (bulkStarts M L delta) ⊆ hitEvent M L :=
  rareEvent_source_subset_hit hM hL hLM hdelta

end
end PaperC.V282.CrossoverSourceCoupling
