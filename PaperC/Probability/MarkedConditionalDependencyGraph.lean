import PaperC.Probability.ExactLengthBadStartMass
import PaperC.Probability.ConditionalAGGInstantiation
import PaperC.Probability.MarkedLocalGeometry

set_option maxHeartbeats 1800000

/-!
# Conditional dependency graph for the truncated marked process

This file constructs the literal finite marked family used in §14.4.
For a fixed mark cutoff `E`, a vertex is a retained start together with an
excess `e ≤ E`.  The row count at that vertex is

`qₑ = L + e + 1`.

The common cutoff is `Q = L + E + 1`, and starts in `D(Q)` are removed.
After the coordinates at primes at most
`Y_Q = floor ((Q+1)^2 log (Q+1))` have been fixed, the indicator at `(x,e)`
depends only on the large-prime coordinates occurring in its own
length-`qₑ` support.

Two distinct marked vertices are joined if they have the same start or if
these coordinate supports intersect.  The resulting graph is proved to be
an exact dependency graph, in the full Boolean-pattern sense required by
Arratia--Goldstein--Gordon.  Moreover every retained marked marginal is
exactly `2^(-qₑ)`, independently of the fixed small-prime realization.

Everything in the module is finite and proved.  No asymptotic or
bibliographic input is introduced.
-/

namespace PaperC
namespace MarkedConditionalDependencyGraph

open scoped BigOperators

open Affine
open ArratiaGoldsteinGordonInput
open BadStartCount
open ConditionalAGGInstantiation
open ConditionalDependencyGraph
open ConditionalStartProbability
open ExactLengthBadStartMass
open ExactLengthConditionalRank
open LargeOddKernel
open LargePrimeDependencyGraph
open MixedLengthAffine
open TerminalPrimeCutoff

noncomputable section

/-! ## Parameters and the finite marked index type -/

/-- Common row count `Q = L + E + 1`. -/
abbrev markedCommonRowCount (L E : ℕ) : ℕ :=
  commonExactRowCount L E

/-- Conditioning cutoff `Y_Q = floor ((Q+1)^2 log (Q+1))`. -/
abbrev markedPrimeCutoff (L E : ℕ) : ℕ :=
  terminalPrimeCutoff (exactLengthBaseCutoff L E)

/-- Prime cylinder large enough for every exact-length support with `e ≤ E`. -/
abbrev markedCylinderCutoff (N L E : ℕ) : ℕ :=
  dyadicCutoff N (markedCommonRowCount L E)

/-- Starts surviving the removal of `D(Q)`. -/
def retainedMarkedStarts (N L E : ℕ) : Finset ℕ :=
  goodStarts N (markedCommonRowCount L E) (markedPrimeCutoff L E)

@[simp]
theorem mem_retainedMarkedStarts {N L E x : ℕ} :
    x ∈ retainedMarkedStarts N L E ↔
      x ∈ dyadicBlock N ∧ x ∉ removedExactLengthStarts N L E := by
  simp [retainedMarkedStarts, removedExactLengthStarts,
    markedCommonRowCount, markedPrimeCutoff]

/-- A retained start carrying an exact excess `0 ≤ e ≤ E`. -/
abbrev MarkedIndex (N L E : ℕ) :=
  {x : ℕ // x ∈ retainedMarkedStarts N L E} × Fin (E + 1)

/-- Row count `qₑ` attached to a marked index. -/
def markedRowCount {N L E : ℕ} (α : MarkedIndex N L E) : ℕ :=
  excessRowCount L α.2.1

theorem markedRowCount_le_common
    {N L E : ℕ} (α : MarkedIndex N L E) :
    markedRowCount α ≤ markedCommonRowCount L E := by
  unfold markedRowCount markedCommonRowCount commonExactRowCount
  simp only [excessRowCount]
  omega

theorem two_le_markedRowCount
    {N L E : ℕ} (hL : 1 ≤ L) (α : MarkedIndex N L E) :
    2 ≤ markedRowCount α := by
  simp [markedRowCount, excessRowCount]
  omega

/-- Large-prime coordinates on which the exact event at `α` depends. -/
def markedCoordinateSupport
    {N L E : ℕ} (α : MarkedIndex N L E) : Finset ℕ :=
  largePrimeCoordinates α.1.1 (markedRowCount α) (markedPrimeCutoff L E)

/-- Large-prime supports are monotone in the row/window length. -/
theorem largePrimeCoordinates_mono_length
    {x q Q Y : ℕ} (hqQ : q ≤ Q) :
    largePrimeCoordinates x q Y ⊆
      largePrimeCoordinates x Q Y := by
  intro p hp
  obtain ⟨n, hn, hpn⟩ := mem_largePrimeCoordinates.mp hp
  apply mem_largePrimeCoordinates.mpr
  refine ⟨n, ?_, hpn⟩
  rcases mem_startTreeSupport.mp hn with hroot | ⟨j, hj, rfl⟩
  · exact mem_startTreeSupport.mpr (Or.inl hroot)
  · exact mem_startTreeSupport.mpr
      (Or.inr ⟨j, lt_of_lt_of_le hj hqQ, rfl⟩)

/-- Every marked coordinate support lies in the common length-`Q` support. -/
theorem markedCoordinateSupport_subset_common
    {N L E : ℕ} (α : MarkedIndex N L E) :
    markedCoordinateSupport α ⊆
      largePrimeCoordinates α.1.1
        (markedCommonRowCount L E) (markedPrimeCutoff L E) :=
  largePrimeCoordinates_mono_length (markedRowCount_le_common α)

/-! ## The exact marked dependency graph -/

/--
Adjacency of two marked indices.  Same-start marks are included explicitly;
otherwise an edge records a shared unfixed prime coordinate.
-/
def MarkedAdjacent
    {N L E : ℕ} (α β : MarkedIndex N L E) : Prop :=
  α ≠ β ∧
    (α.1.1 = β.1.1 ∨
      (markedCoordinateSupport α ∩ markedCoordinateSupport β).Nonempty)

theorem markedAdjacent_symm
    {N L E : ℕ} {α β : MarkedIndex N L E} :
    MarkedAdjacent α β → MarkedAdjacent β α := by
  rintro ⟨hne, hsame | ⟨p, hp⟩⟩
  · exact ⟨hne.symm, Or.inl hsame.symm⟩
  · have hp' := Finset.mem_inter.mp hp
    exact ⟨hne.symm,
      Or.inr ⟨p, Finset.mem_inter.mpr ⟨hp'.2, hp'.1⟩⟩⟩

theorem not_markedAdjacent_self
    {N L E : ℕ} (α : MarkedIndex N L E) :
    ¬MarkedAdjacent α α := by
  intro h
  exact h.1 rfl

/-- Literal simple graph on retained marked starts. -/
def markedDependencyGraph (N L E : ℕ) :
    SimpleGraph (MarkedIndex N L E) where
  Adj α β := MarkedAdjacent α β
  symm := ⟨fun _ _ h ↦ markedAdjacent_symm h⟩
  loopless := ⟨fun α h ↦ not_markedAdjacent_self α h⟩

@[simp]
theorem markedDependencyGraph_adj
    {N L E : ℕ} {α β : MarkedIndex N L E} :
    (markedDependencyGraph N L E).Adj α β ↔
      MarkedAdjacent α β :=
  Iff.rfl

/-- Nonadjacent distinct marked indices have disjoint coordinate supports. -/
theorem disjoint_markedCoordinateSupport_of_not_adjacent
    {N L E : ℕ} {α β : MarkedIndex N L E}
    (hne : α ≠ β)
    (hnot :
      ¬(markedDependencyGraph N L E).Adj α β) :
    Disjoint (markedCoordinateSupport α)
      (markedCoordinateSupport β) := by
  rw [Finset.disjoint_left]
  intro p hpα hpβ
  apply hnot
  exact ⟨hne,
    Or.inr ⟨p, Finset.mem_inter.mpr ⟨hpα, hpβ⟩⟩⟩

/-! ## Conditioned marked indicators and their coordinate support -/

/-- Exact-length indicator after the small prime coordinates are fixed. -/
noncomputable def conditionedMarkedIndicator
    (N L E : ℕ)
    (σ : SmallSample (markedCylinderCutoff N L E) (markedPrimeCutoff L E))
    (α : MarkedIndex N L E)
    (η : LargeSample (markedCylinderCutoff N L E) (markedPrimeCutoff L E)) :
    Bool :=
  by
    classical
    exact decide
      (exactLengthAt
        (assemble (markedCylinderCutoff N L E) (markedPrimeCutoff L E) σ η)
        α.1.1 (markedRowCount α))

@[simp]
theorem conditionedMarkedIndicator_eq_true_iff
    {N L E : ℕ}
    {σ : SmallSample (markedCylinderCutoff N L E) (markedPrimeCutoff L E)}
    {α : MarkedIndex N L E}
    {η : LargeSample (markedCylinderCutoff N L E) (markedPrimeCutoff L E)} :
    conditionedMarkedIndicator N L E σ α η = true ↔
      exactLengthAt
        (assemble (markedCylinderCutoff N L E) (markedPrimeCutoff L E) σ η)
        α.1.1 (markedRowCount α) := by
  classical
  simp [conditionedMarkedIndicator]

@[simp]
theorem conditionedMarkedIndicator_eq_false_iff
    {N L E : ℕ}
    {σ : SmallSample (markedCylinderCutoff N L E) (markedPrimeCutoff L E)}
    {α : MarkedIndex N L E}
    {η : LargeSample (markedCylinderCutoff N L E) (markedPrimeCutoff L E)} :
    conditionedMarkedIndicator N L E σ α η = false ↔
      ¬exactLengthAt
        (assemble (markedCylinderCutoff N L E) (markedPrimeCutoff L E) σ η)
        α.1.1 (markedRowCount α) := by
  classical
  simp [conditionedMarkedIndicator]

/--
Changing coordinates outside the exact support does not change the
conditioned exact-length event.
-/
theorem conditionedExactLengthAt_iff_of_eqOn_markedCoordinateSupport
    {M Y x q : ℕ} (hq : 2 ≤ q)
    (σ : SmallSample M Y) (η θ : LargeSample M Y)
    (heq :
      ∀ p : LargePrimeCoordinate M Y,
        largeCoordinatePrime p ∈ largePrimeCoordinates x q Y →
          η p = θ p) :
    exactLengthAt (assemble M Y σ η) x q ↔
      exactLengthAt (assemble M Y σ θ) x q := by
  rw [assemble_exactLengthAt_iff M Y x q hq σ η,
    assemble_exactLengthAt_iff M Y x q hq σ θ]
  change
    largeStartSystem M Y x q η =
        conditionedExactLengthRhs M Y x q σ ↔
      largeStartSystem M Y x q θ =
        conditionedExactLengthRhs M Y x q σ
  rw [largeStartSystem_eq_of_eqOn_largePrimeCoordinates η θ heq]

theorem conditionedMarkedIndicator_eq_of_eqOn_support
    {N L E : ℕ} (hL : 1 ≤ L)
    (σ : SmallSample (markedCylinderCutoff N L E) (markedPrimeCutoff L E))
    (α : MarkedIndex N L E)
    (η θ : LargeSample (markedCylinderCutoff N L E) (markedPrimeCutoff L E))
    (heq :
      ∀ p :
          LargePrimeCoordinate
            (markedCylinderCutoff N L E) (markedPrimeCutoff L E),
        largeCoordinatePrime p ∈ markedCoordinateSupport α →
          η p = θ p) :
    conditionedMarkedIndicator N L E σ α η =
      conditionedMarkedIndicator N L E σ α θ := by
  classical
  unfold conditionedMarkedIndicator
  exact Bool.decide_congr
    (conditionedExactLengthAt_iff_of_eqOn_markedCoordinateSupport
      (two_le_markedRowCount hL α) σ η θ heq)

/-! ## Exact conditioned marginals -/

/-- Exact-length event as the corresponding conditioned affine fiber. -/
def conditionedExactLengthEventEquiv
    (M Y x q : ℕ) (hq : 2 ≤ q) (σ : SmallSample M Y) :
    {η : LargeSample M Y //
      exactLengthAt (assemble M Y σ η) x q} ≃
      Affine.Solution
        (largeExactLengthSystem M Y x q)
        (conditionedExactLengthRhs M Y x q σ) where
  toFun η :=
    ⟨η.1, (assemble_exactLengthAt_iff M Y x q hq σ η.1).mp η.2⟩
  invFun η :=
    ⟨η.1, (assemble_exactLengthAt_iff M Y x q hq σ η.1).mpr η.2⟩
  left_inv η := by
    apply Subtype.ext
    rfl
  right_inv η := by
    apply Subtype.ext
    rfl

/-- Rational event probability equals the conditioned affine probability. -/
theorem finiteUniformProbability_conditionedExactLength_eq
    (M Y x q : ℕ) (hq : 2 ≤ q) (σ : SmallSample M Y) :
    finiteUniformProbability
        (fun η : LargeSample M Y ↦
          exactLengthAt (assemble M Y σ η) x q) =
      conditionedExactLengthProbability M Y x q σ := by
  classical
  unfold finiteUniformProbability conditionedExactLengthProbability
    Affine.uniformSolutionProbability
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  rw [Fintype.card_congr
    (conditionedExactLengthEventEquiv M Y x q hq σ)]
  congr 1
  norm_cast
  simp only [← Nat.card_eq_fintype_card]

/--
The large exact-length system is surjective at every retained marked start.
-/
theorem largeExactLengthSystem_surjective_of_retained
    {N L E : ℕ} (hN : 2 ≤ N) (hL : 1 ≤ L)
    (α : MarkedIndex N L E) :
    Function.Surjective
      (largeExactLengthSystem
        (markedCylinderCutoff N L E) (markedPrimeCutoff L E)
        α.1.1 (markedRowCount α)) := by
  change Function.Surjective
    (largeStartSystem
      (markedCylinderCutoff N L E) (markedPrimeCutoff L E)
      α.1.1 (markedRowCount α))
  have hxData := mem_goodStarts.mp α.1.2
  apply largeStartSystem_surjective
    (two_le_of_mem_dyadicBlock hN hxData.1)
    (by have := two_le_markedRowCount hL α; omega)
    (by
      have hQ :
          markedCommonRowCount L E + 1 ≤ markedPrimeCutoff L E := by
        exact le_terminalPrimeCutoff
          (by simp [markedCommonRowCount, commonExactRowCount,
            exactLengthBaseCutoff, excessRowCount])
      exact (Nat.add_le_add_right (markedRowCount_le_common α) 1).trans hQ)
  · intro j
    exact startWindow_le_dyadicCutoff
      (L := markedCommonRowCount L E) hxData.1
      (lt_of_lt_of_le j.2 (markedRowCount_le_common α))
  · intro j hjDef
    exact hxData.2
      (mem_terminalBadStarts.mpr
        ⟨hxData.1, j.1,
          lt_of_lt_of_le j.2 (markedRowCount_le_common α),
          (largeOddKernel_eq_one_iff_hDefective
            (markedPrimeCutoff L E) (α.1.1 + j.1)).mpr hjDef⟩)

/--
Every retained conditioned marked indicator has exact marginal `2^(-qₑ)`.
-/
theorem marginal_conditionedMarkedIndicator_eq_baseline
    {N L E : ℕ} (hN : 2 ≤ N) (hL : 1 ≤ L)
    (σ : SmallSample (markedCylinderCutoff N L E) (markedPrimeCutoff L E))
    (α : MarkedIndex N L E) :
    marginal
        (largeUniformPMF
          (markedCylinderCutoff N L E) (markedPrimeCutoff L E))
        (conditionedMarkedIndicator N L E σ) α =
      (1 : ℝ) / (2 : ℝ) ^ markedRowCount α := by
  rw [marginal, eventProbability_largeUniformPMF_eq]
  have hevent :
      (fun η :
          LargeSample
            (markedCylinderCutoff N L E) (markedPrimeCutoff L E) ↦
        conditionedMarkedIndicator N L E σ α η = true) =
      (fun η ↦
        exactLengthAt
          (assemble
            (markedCylinderCutoff N L E) (markedPrimeCutoff L E) σ η)
          α.1.1 (markedRowCount α)) := by
    funext η
    apply propext
    exact conditionedMarkedIndicator_eq_true_iff
  rw [hevent]
  rw [finiteUniformProbability_conditionedExactLength_eq
    (markedCylinderCutoff N L E) (markedPrimeCutoff L E)
    α.1.1 (markedRowCount α) (two_le_markedRowCount hL α) σ]
  rw [conditionedExactLengthProbability_eq_baseline_of_surjective
    (largeExactLengthSystem_surjective_of_retained hN hL α)]
  norm_num

/-! ## Exact Boolean-pattern dependency -/

/--
The marked graph is an exact conditional dependency graph.  This is the
finite/conditional dependency assertion in §14.4, with no omitted `b₃`
term.
-/
theorem hasExactDependencyGraph_conditionedMarkedIndicator
    {N L E : ℕ} (hL : 1 ≤ L)
    (σ : SmallSample (markedCylinderCutoff N L E) (markedPrimeCutoff L E)) :
    HasExactDependencyGraph
      (largeUniformPMF
        (markedCylinderCutoff N L E) (markedPrimeCutoff L E))
      (conditionedMarkedIndicator N L E σ)
      (markedDependencyGraph N L E) := by
  classical
  intro α value pattern
  rw [eventProbability_largeUniformPMF_eq,
    eventProbability_largeUniformPMF_eq,
    eventProbability_largeUniformPMF_eq]
  norm_cast
  let split :=
    startCoordinateSplit
      (markedCylinderCutoff N L E) (markedPrimeCutoff L E)
      α.1.1 (markedRowCount α)
  let P :
      LargeSample
        (markedCylinderCutoff N L E) (markedPrimeCutoff L E) → Prop :=
    fun η ↦ conditionedMarkedIndicator N L E σ α η = value
  let R :
      LargeSample
        (markedCylinderCutoff N L E) (markedPrimeCutoff L E) → Prop :=
    fun η ↦
      HasOutsidePattern
        (conditionedMarkedIndicator N L E σ)
        (markedDependencyGraph N L E) α pattern η
  let PA :
      StartSupportSample
        (markedCylinderCutoff N L E) (markedPrimeCutoff L E)
        α.1.1 (markedRowCount α) → Prop :=
    fun a ↦ P (split.symm (a, 0))
  let RB :
      StartComplementSample
        (markedCylinderCutoff N L E) (markedPrimeCutoff L E)
        α.1.1 (markedRowCount α) → Prop :=
    fun b ↦ R (split.symm (0, b))
  apply finiteUniformProbability_and_eq_mul_of_product_support
    split P R PA RB
  · intro η
    dsimp only [P, PA]
    have hindicator :
        conditionedMarkedIndicator N L E σ α η =
          conditionedMarkedIndicator N L E σ α
            (split.symm ((split η).1, 0)) := by
      apply conditionedMarkedIndicator_eq_of_eqOn_support hL σ α
      intro p hp
      dsimp only [split]
      change
        η p =
          if largeCoordinatePrime p ∈ markedCoordinateSupport α then
            η p
          else 0
      rw [if_pos hp]
    rw [hindicator]
  · intro η
    dsimp only [R, RB]
    let θ := split.symm (0, (split η).2)
    have hindicator :
        ∀ β : OutsideIndex (markedDependencyGraph N L E) α,
          conditionedMarkedIndicator N L E σ β.1 η =
            conditionedMarkedIndicator N L E σ β.1 θ := by
      intro β
      have hnotMem :
          β.1 ∉ closedNeighborhood (markedDependencyGraph N L E) α :=
        β.2
      have hne : α ≠ β.1 := by
        intro h
        apply hnotMem
        rw [← h]
        exact self_mem_closedNeighborhood
          (markedDependencyGraph N L E) α
      have hnotAdj :
          ¬(markedDependencyGraph N L E).Adj α β.1 := by
        intro hadj
        exact hnotMem (mem_closedNeighborhood.mpr (Or.inr hadj))
      have hdisjoint :
          Disjoint (markedCoordinateSupport α)
            (markedCoordinateSupport β.1) :=
        disjoint_markedCoordinateSupport_of_not_adjacent hne hnotAdj
      apply conditionedMarkedIndicator_eq_of_eqOn_support hL σ β.1
      intro p hpβ
      have hnotα :
          largeCoordinatePrime p ∉ markedCoordinateSupport α := by
        intro hpα
        exact Finset.disjoint_left.mp hdisjoint hpα hpβ
      dsimp only [θ, split]
      change
        η p =
          if largeCoordinatePrime p ∈ markedCoordinateSupport α then
            0
          else η p
      rw [if_neg hnotα]
    constructor
    · intro h β
      rw [← hindicator β]
      exact h β
    · intro h β
      rw [hindicator β]
      exact h β

/-! ## Direct conditional AGG application -/

/--
For every fixed small-prime realization, the retained marked count satisfies
the AGG bound with the concrete marked `b₁` and `b₂`.
-/
theorem conditionalMarked_totalVariationToPoisson_le
    (hAGG : ArratiaGoldsteinGordonStatement)
    {N L E : ℕ} (hL : 1 ≤ L)
    (σ : SmallSample (markedCylinderCutoff N L E) (markedPrimeCutoff L E)) :
    totalVariationToPoisson
        (largeUniformPMF
          (markedCylinderCutoff N L E) (markedPrimeCutoff L E))
        (conditionedMarkedIndicator N L E σ) ≤
      2 *
        (bOne
            (largeUniformPMF
              (markedCylinderCutoff N L E) (markedPrimeCutoff L E))
            (conditionedMarkedIndicator N L E σ)
            (markedDependencyGraph N L E) +
          bTwo
            (largeUniformPMF
              (markedCylinderCutoff N L E) (markedPrimeCutoff L E))
            (conditionedMarkedIndicator N L E σ)
            (markedDependencyGraph N L E)) := by
  exact totalVariationToPoisson_le hAGG _ _ _
    (hasExactDependencyGraph_conditionedMarkedIndicator hL σ)

end

end MarkedConditionalDependencyGraph
end PaperC
