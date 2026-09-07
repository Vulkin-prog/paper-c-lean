import PaperCV282.MacroTransportModel
import PaperCV282.BulkMarkedAggregation

/-! # Exact restriction and extension of all signed marks between spatial masks -/
namespace PaperC.V282.MacroTransportRestriction

open MeasureTheory ProbabilityTheory BulkMarkedTypes BulkMarkedTarget BulkMarkedSource
open GeometricMarkedConfiguration InfiniteRademacher InfiniteCylinderTransfer InfiniteStartProbabilityTransfer
open scoped BigOperators NNReal ENNReal

noncomputable section

local instance instDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

/-- Positions keep their actual integer value, as do the excess and sign. -/
def siteEmbedding {s t : Finset ℕ} (h : s ⊆ t) : SpatialMarkedIndex s ↪ SpatialMarkedIndex t where
  toFun j := (⟨j.1.val,h j.1.property⟩,j.2)
  inj' := by
    intro i j he
    exact Prod.ext (Subtype.ext (congrArg (fun z : SpatialMarkedIndex t => z.1.val) he))
      (congrArg (fun z : SpatialMarkedIndex t => z.2) he)

def embedSites {s t : Finset ℕ} (h : s ⊆ t) (c : SpatialMarkedConfig s) : SpatialMarkedConfig t :=
  c.embDomain (siteEmbedding h)

def restrictSites {s t : Finset ℕ} (h : s ⊆ t) (c : SpatialMarkedConfig t) : SpatialMarkedConfig s :=
  c.comapDomain (siteEmbedding h) (siteEmbedding h).injective.injOn

theorem restrictSites_apply {s t : Finset ℕ} (h : s ⊆ t) (c : SpatialMarkedConfig t)
    (j : SpatialMarkedIndex s) : restrictSites h c j=c (siteEmbedding h j) := rfl

theorem embedSites_apply {s t : Finset ℕ} (h : s ⊆ t) (c : SpatialMarkedConfig s)
    (j : SpatialMarkedIndex s) : embedSites h c (siteEmbedding h j)=c j :=
  Finsupp.embDomain_apply_self _ _ _

theorem embedSites_apply_outside {s t : Finset ℕ} (h : s ⊆ t) (c : SpatialMarkedConfig s)
    (j : SpatialMarkedIndex t) (hj : j.1.val ∉ s) : embedSites h c j=0 := by
  apply Finsupp.embDomain_notin_range
  rintro ⟨i,hi⟩
  apply hj
  have hv := congrArg (fun z : SpatialMarkedIndex t => z.1.val) hi
  exact hv ▸ i.1.property

theorem restrict_embed_sites {s t : Finset ℕ} (h : s ⊆ t) (c : SpatialMarkedConfig s) :
    restrictSites h (embedSites h c)=c := by
  ext j
  exact embedSites_apply h c j

theorem embedSites_injective {s t : Finset ℕ} (h : s ⊆ t) : Function.Injective (embedSites h) := by
  intro c d he
  simpa only [restrict_embed_sites] using congrArg (restrictSites h) he

theorem embed_restrict_eq_of_zero_outside {s t : Finset ℕ} (h : s ⊆ t) (c : SpatialMarkedConfig t)
    (hc : ∀ j : SpatialMarkedIndex t, j.1.val ∉ s → c j=0) : embedSites h (restrictSites h c)=c := by
  ext j
  by_cases hj : j.1.val ∈ s
  · let i : SpatialMarkedIndex s := (⟨j.1.val,hj⟩,j.2)
    have he : siteEmbedding h i=j := by ext <;> rfl
    rw [← he,embedSites_apply,restrictSites_apply]
  · rw [embedSites_apply_outside h _ j hj,hc j hj]

theorem restrict_spatialMarkedSource {s t : Finset ℕ} (h : s ⊆ t) (L : ℕ) (omega : InfiniteSample) :
    restrictSites h (spatialMarkedSource t L omega)=spatialMarkedSource s L omega := by
  ext j
  rfl

/-- A discarded nonzero exact mark always implies a true base start. -/
theorem source_eq_embedded_off_removed_starts {s t : Finset ℕ} (h : s ⊆ t) (L : ℕ)
    (omega : InfiniteSample) (hzero : ∀ x ∈ t \ s, omega ∉ infiniteStartEvent x L) :
    embedSites h (spatialMarkedSource s L omega)=spatialMarkedSource t L omega := by
  rw [← restrict_spatialMarkedSource h L omega]
  apply embed_restrict_eq_of_zero_outside
  intro j hj
  by_contra hn
  have hm := (spatialMarkedValue_ne_zero_iff t L omega j).mp hn
  exact hzero j.1.val (Finset.mem_sdiff.mpr ⟨j.1.property,hj⟩)
    (ExactLengthDecomposition.exactLengthEvent_start hm.1)

def rowEmbedding {s t : Finset ℕ} (h : s ⊆ t) : (s × F₂) ↪ (t × F₂) where
  toFun i := (⟨i.1.val,h i.1.property⟩,i.2)
  inj' := by
    intro i j he
    exact Prod.ext (Subtype.ext (congrArg (fun z : t × F₂ => z.1.val) he)) (congrArg (fun z : t × F₂ => z.2) he)

def restrictRows {s t : Finset ℕ} (h : s ⊆ t) (rows : (t × F₂) → (ℕ →₀ ℕ)) :
    (s × F₂) → (ℕ →₀ ℕ) := fun i => rows (rowEmbedding h i)

theorem restrict_flattenRows {s t : Finset ℕ} (h : s ⊆ t) (rows : (t × F₂) → (ℕ →₀ ℕ)) :
    restrictSites h (flattenRows t rows)=flattenRows s (restrictRows h rows) := by
  ext j
  rfl

theorem hasLaw_restrictRows {s t : Finset ℕ} (h : s ⊆ t) (L : ℕ) :
    HasLaw (restrictRows h) (spatialRowsMeasure s L) (spatialRowsMeasure t L) := by
  exact iIndepFun.hasLaw_pi
    (fun i => hasLaw_spatial_row t L (rowEmbedding h i))
    ((independent_spatial_rows t L).precomp (rowEmbedding h).injective)

/-- The target restriction has exactly the independent target on the smaller set. -/
theorem hasLaw_restrictSites {s t : Finset ℕ} (h : s ⊆ t) (L : ℕ) :
    HasLaw (restrictSites h) (spatialTargetMeasure s L) (spatialTargetMeasure t L) := by
  refine ⟨(measurable_of_countable _).aemeasurable,?_⟩
  have hh := (hasLaw_flattenRows s L).fun_comp (hasLaw_restrictRows h L)
  rw [spatialTargetMeasure,Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  have he : (restrictSites h) ∘ (flattenRows t)=(flattenRows s) ∘ (restrictRows h) := by
    funext rows
    exact restrict_flattenRows h rows
  rw [he]
  exact hh.map_eq

end
end PaperC.V282.MacroTransportRestriction
