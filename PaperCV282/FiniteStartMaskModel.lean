import PaperCV282.AllStartConditionalDependency

/-! # Actual start conditioning on an arbitrary finite population

The population is a literal finite set of integer starts. The represented
prime cylinder is independent of the population's lower endpoint. Exact
conditional independence follows from disjoint large-prime coordinates.
-/
namespace PaperC.V282.FiniteStartMaskModel

open Affine ArratiaGoldsteinGordonInput ConditionalDependencyGraph
open ConditionalAGGInstantiation ConditionalAGGAverage ConditionalStartProbability
open LargePrimeDependencyGraph SectionThirteenFiniteBound SectionThirteenCouplings
open scoped BigOperators

noncomputable section

local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

/-- Shared support graph on the actual finite population. -/
def startMaskGraph (L Y : ℕ) (mask : Finset ℕ) : SimpleGraph mask where
  Adj x y := LargePrimeAdjacent L Y x.val y.val
  symm := ⟨fun _ _ h => largePrimeAdjacent_symm h⟩
  loopless := ⟨fun x h => not_largePrimeAdjacent_self L Y x.val h⟩

@[simp]
theorem startMaskGraph_adj {L Y : ℕ} {mask : Finset ℕ} {x y : mask} :
    (startMaskGraph L Y mask).Adj x y ↔ LargePrimeAdjacent L Y x.val y.val := Iff.rfl

/-- The true start indicator on each small-prime fiber. -/
def conditionedIndicator (C L Y : ℕ) (mask : Finset ℕ) (sigma : SmallSample C Y) :
    mask → LargeSample C Y → Bool := fun x eta =>
  decide (startAt (assemble C Y sigma eta) x.val L)

@[simp]
theorem conditionedIndicator_eq_true {C L Y : ℕ} {mask : Finset ℕ}
    {sigma : SmallSample C Y} {x : mask} {eta : LargeSample C Y} :
    conditionedIndicator C L Y mask sigma x eta = true ↔
      startAt (assemble C Y sigma eta) x.val L := by
  classical
  simp [conditionedIndicator]

theorem conditionedIndicator_eq_of_eqOn {C L Y : ℕ} (mask : Finset ℕ)
    (hL : 0<L) (sigma : SmallSample C Y) (x : mask)
    (eta theta : LargeSample C Y)
    (heq : ∀ q : LargePrimeCoordinate C Y,
      largeCoordinatePrime q ∈ largePrimeCoordinates x.val L Y → eta q=theta q) :
    conditionedIndicator C L Y mask sigma x eta =
      conditionedIndicator C L Y mask sigma x theta := by
  classical
  exact Bool.decide_congr (conditionedStartAt_iff_of_eqOn_largePrimeCoordinates hL sigma eta theta heq)

/-- The literal full finite count, including every supplied site. -/
def finiteStartCount (C L : ℕ) (mask : Finset ℕ) (omega : SampleSpace C) : ℕ :=
  ∑ x ∈ mask, if startAt omega x L then 1 else 0

/-- Its true conditional pushforward mass. -/
def conditionalLaw (C L Y : ℕ) (mask : Finset ℕ) (sigma : SmallSample C Y) : ℕ → ℝ :=
  finiteNatLaw (largeUniformPMF C Y) (indicatorSum (conditionedIndicator C L Y mask sigma))

/-- Its true unconditional pushforward mass. -/
def finiteLaw (C L : ℕ) (mask : Finset ℕ) : ℕ → ℝ :=
  finiteNatLaw (fullUniformPMF C) (finiteStartCount C L mask)

theorem indicatorSum_eq_count (C L Y : ℕ) (mask : Finset ℕ)
    (sigma : SmallSample C Y) (eta : LargeSample C Y) :
    indicatorSum (conditionedIndicator C L Y mask sigma) eta =
      finiteStartCount C L mask (assemble C Y sigma eta) := by
  classical
  simp only [indicatorSum,Finset.card_filter,conditionedIndicator,finiteStartCount,decide_eq_true_eq]
  exact (Finset.sum_subtype mask (fun _ => Iff.rfl)
    (fun x => if startAt (assemble C Y sigma eta) x L then (1 : ℕ) else 0)).symm

theorem hasExactDependencyGraph_conditionedIndicator
    {C L Y : ℕ} (mask : Finset ℕ)
    (hL : 0 < L)
    (σ : SmallSample C Y) :
    HasExactDependencyGraph
      (largeUniformPMF C Y)
      (conditionedIndicator C L Y mask σ)
      (startMaskGraph L Y mask) := by
  classical
  intro α value pattern
  rw [eventProbability_largeUniformPMF_eq,
    eventProbability_largeUniformPMF_eq,
    eventProbability_largeUniformPMF_eq]
  norm_cast
  let e :=
    startCoordinateSplit C Y α.1 L
  let P : LargeSample C Y → Prop :=
    fun η ↦
      conditionedIndicator C L Y mask σ α η = value
  let Q : LargeSample C Y → Prop :=
    fun η ↦
      HasOutsidePattern
        (conditionedIndicator C L Y mask σ)
        (startMaskGraph L Y mask)
        α pattern η
  let PA :
      StartSupportSample C Y α.1 L → Prop :=
    fun a ↦ P (e.symm (a, 0))
  let QB :
      StartComplementSample C Y α.1 L → Prop :=
    fun b ↦ Q (e.symm (0, b))
  apply finiteUniformProbability_and_eq_mul_of_product_support
    e P Q PA QB
  · intro η
    dsimp only [P, PA]
    have hindicator :
        conditionedIndicator C L Y mask σ α η =
          conditionedIndicator C L Y mask σ α
            (e.symm ((e η).1, 0)) := by
      apply
        conditionedIndicator_eq_of_eqOn
          mask hL σ α
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
            (startMaskGraph L Y mask) α,
          conditionedIndicator C L Y mask σ β.1 η =
            conditionedIndicator C L Y mask σ β.1 θ := by
      intro β
      have hnotMem :
          β.1 ∉
            closedNeighborhood
              (startMaskGraph L Y mask) α :=
        β.2
      have hne : α ≠ β.1 := by
        intro h
        apply hnotMem
        rw [← h]
        exact
          self_mem_closedNeighborhood
            (startMaskGraph L Y mask) α
      have hneNat : α.1 ≠ β.1.1 := by
        intro h
        apply hne
        apply Subtype.ext
        exact h
      have hnotAdj :
          ¬(startMaskGraph L Y mask).Adj α β.1 := by
        intro hadj
        exact hnotMem
          (mem_closedNeighborhood.mpr (Or.inr hadj))
      have hnotLarge :
          ¬LargePrimeAdjacent L Y α.1 β.1.1 := by
        simpa only [startMaskGraph_adj] using hnotAdj
      have hdisjoint :
          Disjoint
            (largePrimeCoordinates α.1 L Y)
            (largePrimeCoordinates β.1.1 L Y) :=
        disjoint_largePrimeCoordinates_of_not_adjacent
          hneNat hnotLarge
      apply
        conditionedIndicator_eq_of_eqOn
          mask hL σ β.1
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



end
end PaperC.V282.FiniteStartMaskModel
