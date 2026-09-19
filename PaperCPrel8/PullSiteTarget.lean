import PaperCV282.MacroTransportRestriction

/-! # Exact target law under an arbitrary injective relabelling of sites -/
namespace PaperC.Prel8.PullSiteTarget
open MeasureTheory ProbabilityTheory V282.BulkMarkedTypes V282.BulkMarkedTarget
noncomputable section
variable {s t : Finset ℕ}

def labelEmbedding (e : t ↪ s) : SpatialMarkedIndex t ↪ SpatialMarkedIndex s :=
  Function.Embedding.prodMap e (Function.Embedding.refl _)

def pull (e : t ↪ s) (c : SpatialMarkedConfig s) : SpatialMarkedConfig t :=
  c.comapDomain (labelEmbedding e) (labelEmbedding e).injective.injOn

def rowEmbedding (e : t ↪ s) : t×F₂ ↪ s×F₂ :=
  Function.Embedding.prodMap e (Function.Embedding.refl _)

def pullRows (e : t ↪ s) (rows : s×F₂ → ℕ →₀ ℕ) : t×F₂ → ℕ →₀ ℕ :=
  fun r ↦ rows (rowEmbedding e r)

theorem pull_apply (e : t ↪ s) (c : SpatialMarkedConfig s) (a : SpatialMarkedIndex t) :
    pull e c a=c (labelEmbedding e a) := rfl

theorem pull_flatten (e : t ↪ s) (rows : s×F₂ → ℕ →₀ ℕ) :
    pull e (flattenRows s rows)=flattenRows t (pullRows e rows) := by ext a; rfl

theorem hasLaw_pullRows (e : t ↪ s) (L : ℕ) :
    HasLaw (pullRows e) (spatialRowsMeasure t L) (spatialRowsMeasure s L) :=
  iIndepFun.hasLaw_pi (fun i ↦ hasLaw_spatial_row s L (rowEmbedding e i))
    ((independent_spatial_rows s L).precomp (rowEmbedding e).injective)

/-- Positions may be translated and restricted simultaneously; the full marks remain unchanged. -/
theorem hasLaw_pull (e : t ↪ s) (L : ℕ) :
    HasLaw (pull e) (spatialTargetMeasure t L) (spatialTargetMeasure s L) := by
  refine ⟨(measurable_of_countable _).aemeasurable,?_⟩
  have hh := (hasLaw_flattenRows t L).fun_comp (hasLaw_pullRows e L)
  rw [spatialTargetMeasure,Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  have he : pull e ∘ flattenRows s=flattenRows t ∘ pullRows e := by funext rows; exact pull_flatten e rows
  rw [he]
  exact hh.map_eq

end
end PaperC.Prel8.PullSiteTarget
