import PaperCV282.ExactMarkedModel
import Mathlib.Data.Finsupp.Basic

/-! # The common spatial carrier, retaining every excess and both signs -/
namespace PaperC.V282.SpatialMarkedTypes

open ExactMarkedModel ConditionalStartProbability MeasureTheory
open scoped BigOperators

noncomputable section

@[reducible]
def SpatialMarkedIndex (N : ℕ) := Fin N × (ℕ × F₂)

@[reducible]
def SpatialMarkedConfig (N : ℕ) := SpatialMarkedIndex N →₀ ℕ

instance instMeasurableSpatialMarkedConfig (N : ℕ) : MeasurableSpace (SpatialMarkedConfig N) := ⊤

instance instMeasurableSingletonSpatialMarkedConfig (N : ℕ) :
    MeasurableSingletonClass (SpatialMarkedConfig N) := by infer_instance

/-- The position of a finite spatial label is N+i, with no change of sites. -/
def dyadicSiteEquiv (N : ℕ) : Fin N ≃ {x : ℕ // x ∈ dyadicBlock N} where
  toFun i := ⟨N+i.val,Finset.mem_Ico.mpr ⟨by omega,by have h := i.isLt; omega⟩⟩
  invFun x := ⟨x.val-N,by have h := Finset.mem_Ico.mp x.property; omega⟩
  left_inv i := by apply Fin.ext; simp
  right_inv x := by apply Subtype.ext; have h := Finset.mem_Ico.mp x.property; dsimp; omega

theorem dyadicSiteEquiv_apply (N : ℕ) (i : Fin N) : (dyadicSiteEquiv N i).val=N+i.val := rfl

/-- Include the old finite signed carrier into the complete spatial carrier. -/
def finiteMarkedEmbedding (N E : ℕ) : SignedMarkIndex N E ↪ SpatialMarkedIndex N where
  toFun i := ((dyadicSiteEquiv N).symm i.1,(i.2.1.val,i.2.2))
  inj' := by
    intro i j h
    have hsite := congrArg Prod.fst h
    have hex := congrArg (fun k : SpatialMarkedIndex N => k.2.1) h
    have hsign := congrArg (fun k : SpatialMarkedIndex N => k.2.2) h
    exact Prod.ext ((dyadicSiteEquiv N).symm.injective hsite) (Prod.ext (Fin.ext hex) hsign)

def projectConfiguration (N E : ℕ) (config : SpatialMarkedConfig N) (i : SignedMarkIndex N E) : ℕ :=
  config (finiteMarkedEmbedding N E i)

def embedConfiguration (N E : ℕ) (k : SignedMarkIndex N E → ℕ) : SpatialMarkedConfig N :=
  (Finsupp.equivFunOnFinite.symm k).embDomain (finiteMarkedEmbedding N E)

def truncateConfiguration (N E : ℕ) (config : SpatialMarkedConfig N) : SpatialMarkedConfig N :=
  config.filter (fun i => i.2.1 ≤ E)

theorem project_embed_configuration (N E : ℕ) (k : SignedMarkIndex N E → ℕ) :
    projectConfiguration N E (embedConfiguration N E k)=k := by
  funext i
  exact Finsupp.embDomain_apply_self _ _ _

theorem finiteMarkedEmbedding_range (N E : ℕ) (j : SpatialMarkedIndex N) :
    j ∈ Set.range (finiteMarkedEmbedding N E) ↔ j.2.1 ≤ E := by
  constructor
  · rintro ⟨i,rfl⟩
    exact Nat.le_of_lt_succ i.2.1.isLt
  · intro hj
    refine ⟨(dyadicSiteEquiv N j.1,(⟨j.2.1,by omega⟩,j.2.2)),?_⟩
    change ((dyadicSiteEquiv N).symm (dyadicSiteEquiv N j.1), j.2) = j
    rw [Equiv.symm_apply_apply]

theorem truncate_configuration_apply (N E : ℕ) (config : SpatialMarkedConfig N)
    (j : SpatialMarkedIndex N) :
    truncateConfiguration N E config j = if j.2.1 ≤ E then config j else 0 := by
  classical
  exact Finsupp.filter_apply _ _ _

theorem embed_project_configuration (N E : ℕ) (config : SpatialMarkedConfig N) :
    embedConfiguration N E (projectConfiguration N E config)=truncateConfiguration N E config := by
  classical
  ext j
  rw [truncate_configuration_apply]
  by_cases hj : j.2.1 ≤ E
  · obtain ⟨i,rfl⟩ := (finiteMarkedEmbedding_range N E j).mpr hj
    rw [if_pos hj]
    exact Finsupp.embDomain_apply_self _ _ _
  · rw [if_neg hj]
    exact Finsupp.embDomain_notin_range _ _ _ (fun h => hj ((finiteMarkedEmbedding_range N E j).mp h))

theorem embedConfiguration_injective (N E : ℕ) : Function.Injective (embedConfiguration N E) := by
  intro k l h
  simpa only [project_embed_configuration] using congrArg (projectConfiguration N E) h

theorem truncate_configuration_eq_self_iff (N E : ℕ) (config : SpatialMarkedConfig N) :
    truncateConfiguration N E config=config ↔ ∀ j, E<j.2.1 → config j=0 := by
  classical
  constructor
  · intro h j hj
    have hh := congrArg (fun c : SpatialMarkedConfig N => c j) h
    simpa only [truncate_configuration_apply,if_neg (by omega : ¬j.2.1≤E)] using hh.symm
  · intro h
    ext j
    rw [truncate_configuration_apply]
    split_ifs with hj
    · rfl
    · exact (h j (by omega)).symm

end
end PaperC.V282.SpatialMarkedTypes
