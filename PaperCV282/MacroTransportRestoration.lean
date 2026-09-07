import PaperCV282.MacroTransportRestriction
import PaperCV282.SharpConditioningDiscrete
import PaperCV282.PoissonFillingCoupling

/-! # Restoring the discarded sites under the actual conditioning event

The probability of a removed source start is divided by the actual event
probability. The independent target pays only the sum of the removed rates.
-/
namespace PaperC.V282.MacroTransportRestoration

open MeasureTheory ProbabilityTheory BulkMarkedTypes BulkMarkedTarget BulkMarkedSource
open BulkMarkedAggregation MacroTransportRestriction FiniteStartMaskAverages
open InfiniteRademacher InfiniteStartProbabilityTransfer InfiniteMassCoupling
open FiniteFieldTotalVariation CountableLawTransfer SharpConditioning SharpConditioningDiscrete
open ConditionedCountableLaw
open scoped BigOperators NNReal ENNReal

noncomputable section
local instance instDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α
local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤
local instance instProbabilityInfinite : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

theorem siteCounts_eq_zero_iff (sites : Finset ℕ) (c : SpatialMarkedConfig sites) :
    siteCounts sites c=0 ↔ c=0 := by
  constructor
  · intro h
    ext j
    by_cases hj : c j=0
    · exact hj
    · have hl : c j ≤ siteCounts sites c j.1 := by
        change c j ≤ ∑ k∈c.support, if k.1=j.1 then c k else 0
        have hh := Finset.single_le_sum (s := c.support)
          (f := fun k => if k.1=j.1 then c k else 0)
          (fun k hk => Nat.zero_le _) (Finsupp.mem_support_iff.mpr hj)
        simpa only [if_true] using hh
      have hz := congrFun h j.1
      change siteCounts sites c j.1=0 at hz
      exact Nat.eq_zero_of_le_zero (hz ▸ hl)
  · intro h
    subst c
    funext x
    simp [siteCounts,Finsupp.sum]

/-- Any nonempty independent configuration costs at most its total target rate. -/
theorem target_nonzero_probability_le (sites : Finset ℕ) (L : ℕ) :
    (spatialTargetMeasure sites L).real {c | c≠0} ≤ (maskRate L sites : ℝ) := by
  have he : {c : SpatialMarkedConfig sites | c≠0}=
      (siteCounts sites) ⁻¹' {k : sites → ℕ | k≠0} := by
    ext c
    exact not_congr (siteCounts_eq_zero_iff sites c).symm
  rw [he]
  have hp := (hasLaw_siteCounts sites L).measureReal_eq
    (p := fun k : sites → ℕ => k≠0) (Set.to_countable _).measurableSet
  change (spatialTargetMeasure sites L).real ((siteCounts sites) ⁻¹' {k | k≠0}) = _ at hp
  rw [hp]
  apply (PoissonFillingCoupling.filling_nonzero_probability_le (startFieldRates sites L)).trans_eq
  simp only [startFieldRates,Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul]
  change (sites.card : ℝ)*(1/(2 : ℝ)^L)=(sites.card : ℝ)/(2 : ℝ)^L
  ring

theorem restrict_removed_zero_implies_agreement {s t : Finset ℕ} (h : s ⊆ t)
    (c : SpatialMarkedConfig t) (hz : restrictSites (Finset.sdiff_subset : t\s ⊆ t) c=0) :
    c=embedSites h (restrictSites h c) := by
  symm
  apply embed_restrict_eq_of_zero_outside
  intro j hj
  let i : SpatialMarkedIndex (t\s) := (⟨j.1.val,Finset.mem_sdiff.mpr ⟨j.1.property,hj⟩⟩,j.2)
  have he : siteEmbedding (Finset.sdiff_subset : t\s ⊆ t) i=j := by ext <;> rfl
  have hh := congrArg (fun k : SpatialMarkedConfig (t\s) => k i) hz
  simpa only [restrictSites_apply,he,Finsupp.zero_apply] using hh

theorem target_restoration_probability_le {s t : Finset ℕ} (h : s ⊆ t) (L : ℕ) :
    (spatialTargetMeasure t L).real {c | c≠embedSites h (restrictSites h c)} ≤
      (maskRate L (t\s) : ℝ) := by
  have hs : {c : SpatialMarkedConfig t | c≠embedSites h (restrictSites h c)} ⊆
      (restrictSites (Finset.sdiff_subset : t\s ⊆ t)) ⁻¹' {c | c≠0} := by
    intro c hc hz
    exact hc (restrict_removed_zero_implies_agreement h c hz)
  apply (measureReal_mono hs).trans
  have hp := (hasLaw_restrictSites (Finset.sdiff_subset : t\s ⊆ t) L).measureReal_eq
    (p := fun c : SpatialMarkedConfig (t\s) => c≠0) (Set.to_countable _).measurableSet
  change (spatialTargetMeasure t L).real ((restrictSites (Finset.sdiff_subset : t\s ⊆ t)) ⁻¹' {c | c≠0}) = _ at hp
  rw [hp]
  exact target_nonzero_probability_le _ _

theorem source_restoration_probability_le {s t : Finset ℕ} (h : s ⊆ t) (L : ℕ) :
    infiniteRademacherMeasure.real {omega | spatialMarkedSource t L omega≠
      embedSites h (spatialMarkedSource s L omega)} ≤
        ∑ x∈t\s, infiniteStartProbability x L := by
  have hs : {omega | spatialMarkedSource t L omega≠embedSites h (spatialMarkedSource s L omega)} ⊆
      ⋃ x∈t\s, infiniteStartEvent x L := by
    intro omega hw
    by_contra hn
    apply hw
    symm
    apply source_eq_embedded_off_removed_starts h L omega
    intro x hx he
    exact hn (Set.mem_iUnion.mpr ⟨x,Set.mem_iUnion.mpr ⟨hx,he⟩⟩)
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (measureReal_biUnion_finset_le _ _)

/-- Comparison of observable laws with different underlying probability spaces. -/
theorem map_distance_eq_mass {Ω α : Type*} [MeasurableSpace Ω]
    [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (μ : Measure Ω) (ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : Ω → α} (hf : Measurable f) :
    measureTotalVariation (μ.map f) ν=massTotalVariation (observableLaw μ f) (observableLaw ν id) := by
  letI instProbabilityMapped : IsProbabilityMeasure (μ.map f) := Measure.isProbabilityMeasure_map hf.aemeasurable
  rw [measureTotalVariation_eq_mass]
  congr 1
  funext a
  exact (observableLaw_eq_map μ hf a).symm

/-- The actual full event-conditioned field is restored with its true denominator. -/
theorem conditional_restoration_le {s t : Finset ℕ} (h : s ⊆ t) (L : ℕ)
    (A : Set InfiniteSample) (hA : MeasurableSet A) (hpos : 0 < infiniteRademacherMeasure.real A) :
    measureTotalVariation ((cond infiniteRademacherMeasure A).map (spatialMarkedSource t L))
      (spatialTargetMeasure t L) ≤
      (∑ x∈t\s, infiniteStartProbability x L)/infiniteRademacherMeasure.real A +
        measureTotalVariation ((cond infiniteRademacherMeasure A).map (spatialMarkedSource s L))
          (spatialTargetMeasure s L) + (maskRate L (t\s) : ℝ) := by
  letI instProbabilityConditional : IsProbabilityMeasure (cond infiniteRademacherMeasure A) :=
    cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ hpos)
  rw [map_distance_eq_mass _ _ (measurable_spatialMarkedSource t L),
    map_distance_eq_mass _ _ (measurable_spatialMarkedSource s L)]
  have hs := (conditional_event_le_div_probability infiniteRademacherMeasure A hA
    {omega | spatialMarkedSource t L omega≠embedSites h (spatialMarkedSource s L omega)}).trans
    (div_le_div_of_nonneg_right (source_restoration_probability_le h L) hpos.le)
  have he : observableLaw (spatialTargetMeasure t L) (restrictSites h)=
      observableLaw (spatialTargetMeasure s L) id :=
    observableLaw_of_hasLaw _ _ (hasLaw_restrictSites h L)
  apply truncation_tv_le_of_bounds (cond infiniteRademacherMeasure A) (spatialTargetMeasure t L)
    (measurable_spatialMarkedSource t L) measurable_id (measurable_spatialMarkedSource s L)
    (measurable_of_countable _) (embedSites h) hs
  · rw [he]
  · exact target_restoration_probability_le h L

end
end PaperC.V282.MacroTransportRestoration
