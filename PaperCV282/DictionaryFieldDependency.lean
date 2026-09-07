import PaperCV282.DictionaryFieldModel

/-!
# Exact conditional dependency for the complete site-and-word field

All labels at one site, overlapping windows, and shared large-prime
supports are joined. Deterministic masking preserves the full-pattern
independence outside each closed neighbourhood.
-/

namespace PaperC.V282.DictionaryFieldDependency

open DictionaryFieldModel ConditionalStartProbability ConditionalDependencyGraph
open ConditionalAGGInstantiation ConditionalAGGAverage ArratiaGoldsteinGordonInput
open LargePrimeDependencyGraph SectionThirteenFiniteBound PrescribedValues WindowValues InfiniteWordTransfer

noncomputable section

def dictionaryGraph (N L Y : ℕ) (W : Finset (Fin (L + 1) → F₂)) :
    SimpleGraph (DictionaryIndex N L W) where
  Adj i j := i ≠ j ∧ (i.1.val = j.1.val ∨ Nat.dist i.1.val j.1.val ≤ L ∨
    LargePrimeAdjacent L Y i.1.val j.1.val)
  symm := ⟨fun i j h => ⟨Ne.symm h.1, h.2.elim (fun hs => Or.inl hs.symm)
    (fun hs => hs.elim (fun hd => Or.inr (Or.inl (by simpa only [Nat.dist_comm] using hd)))
      (fun hp => Or.inr (Or.inr (largePrimeAdjacent_symm hp))))⟩⟩
  loopless := ⟨fun i h => h.1 rfl⟩

/-- Closed adjacency has no artificial exclusion of different words at one site. -/
theorem mem_closedNeighborhood_dictionaryGraph (N L Y : ℕ) (W : Finset (Fin (L + 1) → F₂))
    (i j : DictionaryIndex N L W) :
    j ∈ closedNeighborhood (dictionaryGraph N L Y W) i ↔
      i.1.val = j.1.val ∨ Nat.dist i.1.val j.1.val ≤ L ∨ LargePrimeAdjacent L Y i.1.val j.1.val := by
  classical
  rw [mem_closedNeighborhood]
  constructor
  · rintro (h | h)
    · subst j
      exact Or.inl rfl
    · exact h.2
  · intro h
    by_cases hij : i = j
    · exact Or.inl hij.symm
    · exact Or.inr ⟨hij,h⟩

/-- Every prescribed bit depends only on the same complete large-prime support as its window. -/
theorem conditionedWordIndicator_eq_of_eqOn_largePrimeCoordinates {N L Y : ℕ}
    (W : Finset (Fin (L + 1) → F₂)) (hN : 2 ≤ N)
    (sigma : SmallSample (dyadicCutoff N L) Y) (i : DictionaryIndex N L W)
    (eta theta : LargeSample (dyadicCutoff N L) Y)
    (heq : ∀ q : LargePrimeCoordinate (dyadicCutoff N L) Y,
      largeCoordinatePrime q ∈ largePrimeCoordinates i.1.val L Y → eta q = theta q) :
    conditionedWordIndicator N L Y W sigma i eta = conditionedWordIndicator N L Y W sigma i theta := by
  classical
  unfold conditionedWordIndicator finiteWordIndicator
  apply Bool.decide_congr
  have hx : 1 ≤ i.1.val := by have h := two_le_of_mem_dyadicBlock hN i.1.property; omega
  have hb (j : Fin (L + 1)) :
      valueBit (assemble (dyadicCutoff N L) Y sigma eta) (vertex i.1.val (L + 1) j) =
      valueBit (assemble (dyadicCutoff N L) Y sigma theta) (vertex i.1.val (L + 1) j) := by
    have hlarge := valueBit_extendLarge_eq_of_eqOn_largePrimeCoordinates
      (vertex_mem_startTreeSupport hx j) eta theta heq
    unfold assemble
    simp only [← valueLinear_apply, map_add]
    simpa only [valueLinear_apply] using congrArg (fun z =>
      valueBit (extendSmall (dyadicCutoff N L) Y sigma) (vertex i.1.val (L + 1) j) + z) hlarge
  simp only [finiteWordEvent,Set.mem_setOf_eq]
  simp_rw [hb]

theorem maskedWordIndicator_eq_of_eqOn_largePrimeCoordinates {N L Y : ℕ}
    (W : Finset (Fin (L + 1) → F₂)) (mask : Finset ℕ) (hN : 2 ≤ N)
    (sigma : SmallSample (dyadicCutoff N L) Y) (i : DictionaryIndex N L W)
    (eta theta : LargeSample (dyadicCutoff N L) Y)
    (heq : ∀ q : LargePrimeCoordinate (dyadicCutoff N L) Y,
      largeCoordinatePrime q ∈ largePrimeCoordinates i.1.val L Y → eta q = theta q) :
    maskedWordIndicator N L Y W mask sigma i eta = maskedWordIndicator N L Y W mask sigma i theta := by
  unfold maskedWordIndicator
  split_ifs
  · exact conditionedWordIndicator_eq_of_eqOn_largePrimeCoordinates W hN sigma i eta theta heq
  · rfl

/-- Full Boolean-pattern independence, for arbitrary site and dictionary masks. -/
theorem hasExactDependencyGraph_maskedWordIndicator {N L Y : ℕ}
    (W : Finset (Fin (L + 1) → F₂)) (mask : Finset ℕ) (hN : 2 ≤ N)
    (sigma : SmallSample (dyadicCutoff N L) Y) :
    HasExactDependencyGraph (largeUniformPMF (dyadicCutoff N L) Y)
      (maskedWordIndicator N L Y W mask sigma) (dictionaryGraph N L Y W) := by
  classical
  intro alpha value pattern
  rw [eventProbability_largeUniformPMF_eq,eventProbability_largeUniformPMF_eq,eventProbability_largeUniformPMF_eq]
  norm_cast
  let e := startCoordinateSplit (dyadicCutoff N L) Y alpha.1.val L
  let P : LargeSample (dyadicCutoff N L) Y → Prop :=
    fun eta => maskedWordIndicator N L Y W mask sigma alpha eta = value
  let Q : LargeSample (dyadicCutoff N L) Y → Prop :=
    fun eta => HasOutsidePattern (maskedWordIndicator N L Y W mask sigma)
      (dictionaryGraph N L Y W) alpha pattern eta
  let PA : StartSupportSample (dyadicCutoff N L) Y alpha.1.val L → Prop :=
    fun a => P (e.symm (a,0))
  let QB : StartComplementSample (dyadicCutoff N L) Y alpha.1.val L → Prop :=
    fun b => Q (e.symm (0,b))
  apply finiteUniformProbability_and_eq_mul_of_product_support e P Q PA QB
  · intro eta
    dsimp only [P,PA]
    have hi : maskedWordIndicator N L Y W mask sigma alpha eta =
        maskedWordIndicator N L Y W mask sigma alpha (e.symm ((e eta).1,0)) := by
      apply maskedWordIndicator_eq_of_eqOn_largePrimeCoordinates W mask hN sigma alpha
      intro q hq
      dsimp only [e]
      change eta q = if largeCoordinatePrime q ∈ largePrimeCoordinates alpha.1.val L Y then eta q else 0
      rw [if_pos hq]
    rw [hi]
  · intro eta
    dsimp only [Q,QB]
    let theta := e.symm (0,(e eta).2)
    have hi : ∀ beta : OutsideIndex (dictionaryGraph N L Y W) alpha,
        maskedWordIndicator N L Y W mask sigma beta.val eta =
        maskedWordIndicator N L Y W mask sigma beta.val theta := by
      intro beta
      have houtside := beta.property
      rw [mem_closedNeighborhood_dictionaryGraph] at houtside
      have hne : alpha.1.val ≠ beta.val.1.val := fun h => houtside (Or.inl h)
      have hnot : ¬LargePrimeAdjacent L Y alpha.1.val beta.val.1.val :=
        fun h => houtside (Or.inr (Or.inr h))
      have hd := disjoint_largePrimeCoordinates_of_not_adjacent hne hnot
      apply maskedWordIndicator_eq_of_eqOn_largePrimeCoordinates W mask hN sigma beta.val
      intro q hq
      have hnotq : largeCoordinatePrime q ∉ largePrimeCoordinates alpha.1.val L Y := by
        intro hqa
        exact Finset.disjoint_left.mp hd hqa hq
      dsimp only [theta,e]
      change eta q = if largeCoordinatePrime q ∈ largePrimeCoordinates alpha.1.val L Y then 0 else eta q
      rw [if_neg hnotq]
    constructor
    · intro h beta
      rw [← hi beta]
      exact h beta
    · intro h beta
      rw [hi beta]
      exact h beta

end
end PaperC.V282.DictionaryFieldDependency
