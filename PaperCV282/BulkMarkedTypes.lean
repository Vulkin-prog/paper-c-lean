import PaperCV282.BulkMarkedInfinite
import Mathlib.Data.Finsupp.Basic

/-! # The exact-position carrier, retaining every excess and both signs -/
namespace PaperC.V282.BulkMarkedTypes

open ExactMarkedModel BulkSupportGraph ConditionalStartProbability MeasureTheory
open scoped BigOperators

noncomputable section

@[reducible]
def SpatialMarkedIndex (sites : Finset ℕ) := {x : ℕ // x ∈ sites} × (ℕ × F₂)

@[reducible]
def SpatialMarkedConfig (sites : Finset ℕ) := SpatialMarkedIndex sites →₀ ℕ

instance instMeasurableSpatialMarkedConfig (sites : Finset ℕ) : MeasurableSpace (SpatialMarkedConfig sites) := ⊤

instance instMeasurableSingletonSpatialMarkedConfig (sites : Finset ℕ) :
    MeasurableSingletonClass (SpatialMarkedConfig sites) := by infer_instance

/-- Include the finite signed carrier at unchanged integer positions into the complete spatial carrier. -/
def finiteMarkedEmbedding (sites : Finset ℕ) (E : ℕ) : LabelledIndex sites (Fin (E+1) × F₂) ↪ SpatialMarkedIndex sites where
  toFun i := (i.1,(i.2.1.val,i.2.2))
  inj' := by
    intro i j h
    have hsite := congrArg Prod.fst h
    have hex := congrArg (fun k : SpatialMarkedIndex sites => k.2.1) h
    have hsign := congrArg (fun k : SpatialMarkedIndex sites => k.2.2) h
    exact Prod.ext hsite (Prod.ext (Fin.ext hex) hsign)

def projectConfiguration (sites : Finset ℕ) (E : ℕ) (config : SpatialMarkedConfig sites) (i : LabelledIndex sites (Fin (E+1) × F₂)) : ℕ :=
  config (finiteMarkedEmbedding sites E i)

def embedConfiguration (sites : Finset ℕ) (E : ℕ) (k : LabelledIndex sites (Fin (E+1) × F₂) → ℕ) : SpatialMarkedConfig sites :=
  (Finsupp.equivFunOnFinite.symm k).embDomain (finiteMarkedEmbedding sites E)

def truncateConfiguration (sites : Finset ℕ) (E : ℕ) (config : SpatialMarkedConfig sites) : SpatialMarkedConfig sites :=
  config.filter (fun i => i.2.1 ≤ E)

theorem project_embed_configuration (sites : Finset ℕ) (E : ℕ) (k : LabelledIndex sites (Fin (E+1) × F₂) → ℕ) :
    projectConfiguration sites E (embedConfiguration sites E k)=k := by
  funext i
  exact Finsupp.embDomain_apply_self _ _ _

theorem finiteMarkedEmbedding_range (sites : Finset ℕ) (E : ℕ) (j : SpatialMarkedIndex sites) :
    j ∈ Set.range (finiteMarkedEmbedding sites E) ↔ j.2.1 ≤ E := by
  constructor
  · rintro ⟨i,rfl⟩
    exact Nat.le_of_lt_succ i.2.1.isLt
  · intro hj
    refine ⟨(j.1,(⟨j.2.1,by omega⟩,j.2.2)),?_⟩
    simp only [finiteMarkedEmbedding,Function.Embedding.coeFn_mk]

theorem truncate_configuration_apply (sites : Finset ℕ) (E : ℕ) (config : SpatialMarkedConfig sites)
    (j : SpatialMarkedIndex sites) :
    truncateConfiguration sites E config j = if j.2.1 ≤ E then config j else 0 := by
  classical
  exact Finsupp.filter_apply _ _ _

theorem embed_project_configuration (sites : Finset ℕ) (E : ℕ) (config : SpatialMarkedConfig sites) :
    embedConfiguration sites E (projectConfiguration sites E config)=truncateConfiguration sites E config := by
  classical
  ext j
  rw [truncate_configuration_apply]
  by_cases hj : j.2.1 ≤ E
  · obtain ⟨i,rfl⟩ := (finiteMarkedEmbedding_range sites E j).mpr hj
    rw [if_pos hj]
    exact Finsupp.embDomain_apply_self _ _ _
  · rw [if_neg hj]
    exact Finsupp.embDomain_notin_range _ _ _ (fun h => hj ((finiteMarkedEmbedding_range sites E j).mp h))

theorem embedConfiguration_injective (sites : Finset ℕ) (E : ℕ) : Function.Injective (embedConfiguration sites E) := by
  intro k l h
  simpa only [project_embed_configuration] using congrArg (projectConfiguration sites E) h

theorem truncate_configuration_eq_self_iff (sites : Finset ℕ) (E : ℕ) (config : SpatialMarkedConfig sites) :
    truncateConfiguration sites E config=config ↔ ∀ j, E<j.2.1 → config j=0 := by
  classical
  constructor
  · intro h j hj
    have hh := congrArg (fun c : SpatialMarkedConfig sites => c j) h
    simpa only [truncate_configuration_apply,if_neg (by omega : ¬j.2.1≤E)] using hh.symm
  · intro h
    ext j
    rw [truncate_configuration_apply]
    split_ifs with hj
    · rfl
    · exact (h j (by omega)).symm

end
end PaperC.V282.BulkMarkedTypes
