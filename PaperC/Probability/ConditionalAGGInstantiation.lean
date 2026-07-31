import PaperC.Probability.ArratiaGoldsteinGordonInput
import PaperC.Probability.ConditionalDependencyGraph
import PaperC.Probability.SteinChenTerms

set_option maxHeartbeats 1200000

/-!
# The conditioned cylinder as an Arratia--Goldstein--Gordon system

This module connects the exact conditional dependency graph of Lemma 13.5
to the finite external interface for Theorem 13.7.

For every fixed assignment of the prime signs at `p ≤ Y`, the remaining
large-prime cylinder is equipped with its uniform probability mass function.
The vertices are the good starts, the Boolean indicators are the conditioned
start events, and the graph is the literal large-prime dependency graph.

The main result proves the full `HasExactDependencyGraph` predicate required
by the Arratia--Goldstein--Gordon interface.  In particular it treats every
Boolean pattern outside a closed neighborhood, not only intersections of
positive start events.  Thus the passage from Lemma 13.5 to Theorem 13.7 is
now a checked finite theorem rather than an informal API identification.
-/

namespace PaperC
namespace ConditionalAGGInstantiation

open ArratiaGoldsteinGordonInput
open ConditionalDependencyGraph
open ConditionalStartProbability
open LargePrimeDependencyGraph

noncomputable section

/-! ## Uniform finite cylinders -/

/-- Uniform probability mass function on the unfixed large-prime cylinder. -/
noncomputable def largeUniformPMF (M Y : ℕ) :
    FinitePMF (LargeSample M Y) :=
  FinitePMF.uniform _

/--
`eventProbability` under the uniform finite PMF is the real cast of the
rational finite-uniform probability used by the conditional cylinder API.
-/
theorem eventProbability_largeUniformPMF_eq
    {M Y : ℕ} (event : LargeSample M Y → Prop) :
    eventProbability (largeUniformPMF M Y) event =
      ((finiteUniformProbability event : ℚ) : ℝ) := by
  classical
  unfold eventProbability largeUniformPMF
    FinitePMF.uniform finiteUniformProbability
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Fintype.card_subtype]
  simp only [div_eq_mul_inv, Rat.cast_mul, Rat.cast_natCast,
    Rat.cast_inv, Rat.cast_ofNat]
  rw [← Finset.sum_filter]
  simp

/-! ## The concrete conditioned indicators -/

/-- Boolean indicator of a good start after fixing the small-prime signs. -/
noncomputable def conditionedGoodIndicator
    (N L Y : ℕ)
    (σ : SmallSample (dyadicCutoff N L) Y) :
    {x : ℕ // x ∈ goodStarts N L Y} →
      LargeSample (dyadicCutoff N L) Y → Bool := by
  classical
  exact fun x η ↦
    decide
      (startAt
        (assemble (dyadicCutoff N L) Y σ η) x.1 L)

@[simp]
theorem conditionedGoodIndicator_eq_true_iff
    {N L Y : ℕ}
    {σ : SmallSample (dyadicCutoff N L) Y}
    {x : {x : ℕ // x ∈ goodStarts N L Y}}
    {η : LargeSample (dyadicCutoff N L) Y} :
    conditionedGoodIndicator N L Y σ x η = true ↔
      startAt
        (assemble (dyadicCutoff N L) Y σ η) x.1 L := by
  simp [conditionedGoodIndicator]

@[simp]
theorem conditionedGoodIndicator_eq_false_iff
    {N L Y : ℕ}
    {σ : SmallSample (dyadicCutoff N L) Y}
    {x : {x : ℕ // x ∈ goodStarts N L Y}}
    {η : LargeSample (dyadicCutoff N L) Y} :
    conditionedGoodIndicator N L Y σ x η = false ↔
      ¬startAt
        (assemble (dyadicCutoff N L) Y σ η) x.1 L := by
  simp [conditionedGoodIndicator]

theorem conditionedGoodIndicator_eq_of_eqOn_largePrimeCoordinates
    {N L Y : ℕ}
    (hL : 0 < L)
    (σ : SmallSample (dyadicCutoff N L) Y)
    (x : {x : ℕ // x ∈ goodStarts N L Y})
    (η θ : LargeSample (dyadicCutoff N L) Y)
    (heq :
      ∀ q : LargePrimeCoordinate (dyadicCutoff N L) Y,
        largeCoordinatePrime q ∈
            largePrimeCoordinates x.1 L Y →
          η q = θ q) :
    conditionedGoodIndicator N L Y σ x η =
      conditionedGoodIndicator N L Y σ x θ := by
  classical
  unfold conditionedGoodIndicator
  exact Bool.decide_congr
    (conditionedStartAt_iff_of_eqOn_largePrimeCoordinates
      hL σ η θ heq)

/-! ## Exact conditional marginals -/

/--
The event that a conditioned start occurs is canonically the affine fiber of
the translated large-prime start system.
-/
def conditionedStartEventEquiv
    (M Y x L : ℕ) (hL : 0 < L)
    (σ : SmallSample M Y) :
    {η : LargeSample M Y //
      startAt (assemble M Y σ η) x L} ≃
      Affine.Solution
        (largeStartSystem M Y x L)
        (conditionedStartRhs M Y x L σ) where
  toFun η :=
    ⟨η.1, (assemble_startAt_iff M Y x L hL σ η.1).mp η.2⟩
  invFun η :=
    ⟨η.1, (assemble_startAt_iff M Y x L hL σ η.1).mpr η.2⟩
  left_inv η := by
    apply Subtype.ext
    rfl
  right_inv η := by
    apply Subtype.ext
    rfl

/-- Rational uniform event probability equals the affine fiber probability. -/
theorem finiteUniformProbability_conditionedStart_eq
    (M Y x L : ℕ) (hL : 0 < L)
    (σ : SmallSample M Y) :
    finiteUniformProbability
        (fun η : LargeSample M Y ↦
          startAt (assemble M Y σ η) x L) =
      Affine.uniformSolutionProbability
        (largeStartSystem M Y x L)
        (conditionedStartRhs M Y x L σ) := by
  classical
  unfold finiteUniformProbability Affine.uniformSolutionProbability
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  rw [Fintype.card_congr
    (conditionedStartEventEquiv M Y x L hL σ)]
  congr 1
  norm_cast
  simp only [← Nat.card_eq_fintype_card]

/--
Every good conditioned indicator has the exact marginal `2⁻ᴸ`, independently
of the fixed small-prime assignment.
-/
theorem marginal_conditionedGoodIndicator_eq_baseline
    {N L Y : ℕ}
    (hN : 2 ≤ N) (hL : 0 < L) (hLY : L + 1 ≤ Y)
    (σ : SmallSample (dyadicCutoff N L) Y)
    (x : {x : ℕ // x ∈ goodStarts N L Y}) :
    marginal
        (largeUniformPMF (dyadicCutoff N L) Y)
        (conditionedGoodIndicator N L Y σ) x =
      (1 : ℝ) / (2 : ℝ) ^ L := by
  rw [marginal, eventProbability_largeUniformPMF_eq]
  have hevent :
      (fun η : LargeSample (dyadicCutoff N L) Y ↦
          conditionedGoodIndicator N L Y σ x η = true) =
        (fun η : LargeSample (dyadicCutoff N L) Y ↦
          startAt
            (assemble (dyadicCutoff N L) Y σ η) x.1 L) := by
    funext η
    apply propext
    exact conditionedGoodIndicator_eq_true_iff
  rw [hevent]
  rw [finiteUniformProbability_conditionedStart_eq
    (dyadicCutoff N L) Y x.1 L hL σ]
  rw [conditionedStartProbability_eq_baseline_of_not_terminalBad
    hN (mem_goodStarts.mp x.2).1 hL hLY
    (mem_goodStarts.mp x.2).2 σ]
  norm_num

/-! ## Full Boolean-pattern independence -/

/--
Lemma 13.5 in exactly the strength consumed by the finite AGG theorem:
after every fixed small-prime realization, the concrete graph on good starts
is an exact dependency graph for the complete Boolean indicator vector.
-/
theorem hasExactDependencyGraph_conditionedGoodIndicator
    {N L Y : ℕ}
    (hL : 0 < L)
    (σ : SmallSample (dyadicCutoff N L) Y) :
    HasExactDependencyGraph
      (largeUniformPMF (dyadicCutoff N L) Y)
      (conditionedGoodIndicator N L Y σ)
      (largePrimeDependencyGraph N L Y) := by
  classical
  intro α value pattern
  rw [eventProbability_largeUniformPMF_eq,
    eventProbability_largeUniformPMF_eq,
    eventProbability_largeUniformPMF_eq]
  norm_cast
  let e :=
    startCoordinateSplit (dyadicCutoff N L) Y α.1 L
  let P : LargeSample (dyadicCutoff N L) Y → Prop :=
    fun η ↦ conditionedGoodIndicator N L Y σ α η = value
  let Q : LargeSample (dyadicCutoff N L) Y → Prop :=
    fun η ↦
      HasOutsidePattern
        (conditionedGoodIndicator N L Y σ)
        (largePrimeDependencyGraph N L Y)
        α pattern η
  let PA :
      StartSupportSample (dyadicCutoff N L) Y α.1 L → Prop :=
    fun a ↦ P (e.symm (a, 0))
  let QB :
      StartComplementSample (dyadicCutoff N L) Y α.1 L → Prop :=
    fun b ↦ Q (e.symm (0, b))
  apply finiteUniformProbability_and_eq_mul_of_product_support
    e P Q PA QB
  · intro η
    dsimp only [P, PA]
    have hindicator :
        conditionedGoodIndicator N L Y σ α η =
          conditionedGoodIndicator N L Y σ α
            (e.symm ((e η).1, 0)) := by
      apply conditionedGoodIndicator_eq_of_eqOn_largePrimeCoordinates
        hL σ α
      intro q hq
      dsimp only [e]
      change
        η q =
          if largeCoordinatePrime q ∈
              largePrimeCoordinates α.1 L Y then
            η q
          else 0
      rw [if_pos hq]
    rw [hindicator]
  · intro η
    dsimp only [Q, QB]
    let θ := e.symm (0, (e η).2)
    have hindicator :
        ∀ β : OutsideIndex
            (largePrimeDependencyGraph N L Y) α,
          conditionedGoodIndicator N L Y σ β.1 η =
            conditionedGoodIndicator N L Y σ β.1 θ := by
      intro β
      have hnotMem :
          β.1 ∉
            closedNeighborhood
              (largePrimeDependencyGraph N L Y) α :=
        β.2
      have hne : α ≠ β.1 := by
        intro h
        apply hnotMem
        rw [← h]
        exact
          self_mem_closedNeighborhood
            (largePrimeDependencyGraph N L Y) α
      have hneNat : α.1 ≠ β.1.1 := by
        intro h
        apply hne
        apply Subtype.ext
        exact h
      have hnotAdj :
          ¬(largePrimeDependencyGraph N L Y).Adj α β.1 := by
        intro hadj
        exact hnotMem
          (mem_closedNeighborhood.mpr (Or.inr hadj))
      have hnotLarge :
          ¬LargePrimeAdjacent L Y α.1 β.1.1 := by
        simpa only [largePrimeDependencyGraph_adj] using hnotAdj
      have hdisjoint :
          Disjoint
            (largePrimeCoordinates α.1 L Y)
            (largePrimeCoordinates β.1.1 L Y) :=
        disjoint_largePrimeCoordinates_of_not_adjacent
          hneNat hnotLarge
      apply conditionedGoodIndicator_eq_of_eqOn_largePrimeCoordinates
        hL σ β.1
      intro q hqβ
      have hnotα :
          largeCoordinatePrime q ∉
            largePrimeCoordinates α.1 L Y := by
        intro hqα
        exact
          (Finset.disjoint_left.mp hdisjoint)
            hqα hqβ
      dsimp only [θ, e]
      change
        η q =
          if largeCoordinatePrime q ∈
              largePrimeCoordinates α.1 L Y then
            0
          else η q
      rw [if_neg hnotα]
    constructor
    · intro h β
      rw [← hindicator β]
      exact h β
    · intro h β
      rw [hindicator β]
      exact h β

/-! ## Direct application of Theorem 13.7 -/

/--
The conditional good-start count satisfies the Arratia--Goldstein--Gordon
bound for every fixed small-prime realization.

The only non-formal input is the explicitly supplied external theorem
`hAGG`; the exact dependency hypothesis is discharged above.
-/
theorem conditionalGood_totalVariationToPoisson_le
    (hAGG : ArratiaGoldsteinGordonStatement)
    {N L Y : ℕ}
    (hL : 0 < L)
    (σ : SmallSample (dyadicCutoff N L) Y) :
    totalVariationToPoisson
        (largeUniformPMF (dyadicCutoff N L) Y)
        (conditionedGoodIndicator N L Y σ) ≤
      2 *
        (bOne
            (largeUniformPMF (dyadicCutoff N L) Y)
            (conditionedGoodIndicator N L Y σ)
            (largePrimeDependencyGraph N L Y) +
          bTwo
            (largeUniformPMF (dyadicCutoff N L) Y)
            (conditionedGoodIndicator N L Y σ)
            (largePrimeDependencyGraph N L Y)) := by
  exact totalVariationToPoisson_le
    hAGG
    (largeUniformPMF (dyadicCutoff N L) Y)
    (conditionedGoodIndicator N L Y σ)
    (largePrimeDependencyGraph N L Y)
    (hasExactDependencyGraph_conditionedGoodIndicator hL σ)

end

end ConditionalAGGInstantiation
end PaperC
