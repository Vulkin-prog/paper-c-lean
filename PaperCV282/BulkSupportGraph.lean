import PaperCV282.DictionaryFieldDependency

/-!
# A maximal-support graph on an arbitrary finite population

The label set may describe marks of different lengths. Independence uses
only containment in the same maximal support and the complete outside
Boolean pattern. The cylinder cutoff is an independent parameter.
-/

namespace PaperC.V282.BulkSupportGraph

open ConditionalStartProbability ConditionalDependencyGraph ConditionalAGGInstantiation
open ConditionalAGGAverage ArratiaGoldsteinGordonInput LargePrimeDependencyGraph
open SectionThirteenFiniteBound

noncomputable section

local instance instDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

@[reducible]
def LabelledIndex (sites : Finset ℕ) (κ : Type*) := {x : ℕ // x ∈ sites} × κ

/-- Labels at a site and labels on adjacent maximal supports are neighbours. -/
def labelledGraph (sites : Finset ℕ) (Q Y : ℕ) (κ : Type*) : SimpleGraph (LabelledIndex sites κ) where
  Adj i j := i ≠ j ∧ (Nat.dist i.1.val j.1.val ≤ Q ∨ LargePrimeAdjacent Q Y i.1.val j.1.val)
  symm := ⟨fun _ _ h => ⟨Ne.symm h.1,h.2.elim
    (fun hd => Or.inl (by simpa only [Nat.dist_comm] using hd))
    (fun ha => Or.inr (largePrimeAdjacent_symm ha))⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem mem_closedNeighborhood_labelledGraph {κ : Type*} [Fintype κ] [DecidableEq κ]
    (sites : Finset ℕ) (Q Y : ℕ) (i j : LabelledIndex sites κ) :
    j ∈ closedNeighborhood (labelledGraph sites Q Y κ) i ↔
      Nat.dist i.1.val j.1.val ≤ Q ∨ LargePrimeAdjacent Q Y i.1.val j.1.val := by
  classical
  rw [mem_closedNeighborhood]
  constructor
  · rintro (h | h)
    · subst j
      exact Or.inl (by simp)
    · exact h.2
  · intro h
    by_cases hij : i = j
    · exact Or.inl hij.symm
    · exact Or.inr ⟨hij,h⟩

/-- Maximal-support locality alone gives full-pattern conditional independence. -/
theorem hasExactDependencyGraph_of_labelled_locality {κ : Type*} [Fintype κ] [DecidableEq κ]
    (C : ℕ) (sites : Finset ℕ) (Q Y : ℕ) (X : LabelledIndex sites κ → LargeSample C Y → Bool)
    (hlocal : ∀ i eta theta,
      (∀ q : LargePrimeCoordinate C Y,
        largeCoordinatePrime q ∈ largePrimeCoordinates i.1.val Q Y → eta q = theta q) →
      X i eta = X i theta) :
    HasExactDependencyGraph (largeUniformPMF C Y) X (labelledGraph sites Q Y κ) := by
  classical
  intro alpha value pattern
  rw [eventProbability_largeUniformPMF_eq,eventProbability_largeUniformPMF_eq,
    eventProbability_largeUniformPMF_eq]
  norm_cast
  let e := startCoordinateSplit C Y alpha.1.val Q
  let P : LargeSample C Y → Prop := fun eta => X alpha eta = value
  let R : LargeSample C Y → Prop := fun eta => HasOutsidePattern X
    (labelledGraph sites Q Y κ) alpha pattern eta
  let PA : StartSupportSample C Y alpha.1.val Q → Prop := fun a => P (e.symm (a,0))
  let RB : StartComplementSample C Y alpha.1.val Q → Prop := fun b => R (e.symm (0,b))
  apply finiteUniformProbability_and_eq_mul_of_product_support e P R PA RB
  · intro eta
    dsimp only [P,PA]
    have hi : X alpha eta = X alpha (e.symm ((e eta).1,0)) := by
      apply hlocal
      intro q hq
      change eta q = if largeCoordinatePrime q ∈ largePrimeCoordinates alpha.1.val Q Y then eta q else 0
      rw [if_pos hq]
    rw [hi]
  · intro eta
    dsimp only [R,RB]
    let theta := e.symm (0,(e eta).2)
    have hi (beta : OutsideIndex (labelledGraph sites Q Y κ) alpha) : X beta.val eta = X beta.val theta := by
      have hout := beta.property
      rw [mem_closedNeighborhood_labelledGraph] at hout
      have hne : alpha.1.val ≠ beta.val.1.val := by
        intro h
        exact hout (Or.inl (by simp [h]))
      have hnot : ¬LargePrimeAdjacent Q Y alpha.1.val beta.val.1.val := fun h => hout (Or.inr h)
      have hd := disjoint_largePrimeCoordinates_of_not_adjacent hne hnot
      apply hlocal
      intro q hq
      have hnotq : largeCoordinatePrime q ∉ largePrimeCoordinates alpha.1.val Q Y :=
        fun hqa => Finset.disjoint_left.mp hd hqa hq
      change eta q = if largeCoordinatePrime q ∈ largePrimeCoordinates alpha.1.val Q Y then 0 else eta q
      rw [if_neg hnotq]
    constructor
    · intro h beta
      rw [← hi beta]
      exact h beta
    · intro h beta
      rw [hi beta]
      exact h beta

/-- A deterministic site mask keeps the original labelled carrier. -/
def maskedLabelIndicator {κ S : Type*} (sites : Finset ℕ) (X : LabelledIndex sites κ → S → Bool)
    (mask : Finset ℕ) : LabelledIndex sites κ → S → Bool := by
  classical
  exact fun i omega => if i.1.val ∈ mask then X i omega else false

theorem maskedLabelIndicator_locality {κ : Type*} [Fintype κ] [DecidableEq κ]
    (C : ℕ) (sites : Finset ℕ) (Q Y : ℕ) (X : LabelledIndex sites κ → LargeSample C Y → Bool)
    (mask : Finset ℕ)
    (hlocal : ∀ i eta theta,
      (∀ q : LargePrimeCoordinate C Y,
        largeCoordinatePrime q ∈ largePrimeCoordinates i.1.val Q Y → eta q = theta q) →
      X i eta = X i theta) :
    ∀ i eta theta,
      (∀ q : LargePrimeCoordinate C Y,
        largeCoordinatePrime q ∈ largePrimeCoordinates i.1.val Q Y → eta q = theta q) →
      maskedLabelIndicator sites X mask i eta = maskedLabelIndicator sites X mask i theta := by
  intro i eta theta h
  unfold maskedLabelIndicator
  split_ifs
  · exact hlocal i eta theta h
  · rfl

end
end PaperC.V282.BulkSupportGraph
