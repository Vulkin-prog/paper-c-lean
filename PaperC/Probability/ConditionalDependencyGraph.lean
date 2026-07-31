import PaperC.Probability.ConditionalStartProbability
import PaperC.Probability.LargePrimeDependencyGraph

set_option maxHeartbeats 1200000

/-!
# Conditional dependency graph in the finite prime cylinder

This file proves the finite conditional-independence statement behind
Lemma 13.5.

After fixing the prime signs at `p ≤ Y`, the remaining sample space is
`LargeSample M Y`.  For a start `x`, its translated affine start event
depends only on the coordinates in the finite set `Πₓ(Y)` defined by
`largePrimeCoordinates x L Y`.  We make this support statement extensionally
exact and package restriction to `Πₓ(Y)` as a linear coordinate mask.

For a finite family of good starts containing no edge of the large-prime
dependency graph, the sets `Πₓ(Y)` are pairwise disjoint.  Individual
surjectivity from `ConditionalStartProbability` can therefore be assembled
on disjoint coordinate masks into surjectivity of the joint start system.
Every joint affine fiber consequently has exact conditional probability

`2 ^ (-L · #family)`,

which is also the product of the individual conditional probabilities.

As in `ConditionalStartProbability`, conditioning is represented by the
uniform law on the remaining finite cylinder rather than by a
measure-theoretic conditional-expectation API.
-/

namespace PaperC
namespace ConditionalDependencyGraph

open scoped BigOperators

open Affine
open ConditionalStartProbability
open LargePrimeDependencyGraph
open BadStartCount
open DefectivePredicate
open LargeOddKernel

noncomputable section

/-! ## A finite product criterion for independence -/

/-- Uniform probability of a predicate on an arbitrary finite type. -/
def finiteUniformProbability
    {Ω : Type*} [Fintype Ω] (P : Ω → Prop) : ℚ := by
  exact (Nat.card {ω : Ω // P ω} : ℚ) /
    (Nat.card Ω : ℚ)

/--
Finite product criterion: if, under a product decomposition of the sample
space, `P` depends only on the first factor and `Q` only on the second, then
their uniform probabilities factor exactly.
-/
theorem finiteUniformProbability_and_eq_mul_of_product_support
    {Ω A B : Type*} [Fintype Ω] [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B]
    (e : Ω ≃ A × B)
    (P Q : Ω → Prop) (PA : A → Prop) (QB : B → Prop)
    (hP : ∀ ω, P ω ↔ PA (e ω).1)
    (hQ : ∀ ω, Q ω ↔ QB (e ω).2) :
    finiteUniformProbability (fun ω ↦ P ω ∧ Q ω) =
      finiteUniformProbability P * finiteUniformProbability Q := by
  classical
  let eP : {ω : Ω // P ω} ≃ ({a : A // PA a} × B) := {
    toFun ω := (⟨(e ω.1).1, (hP ω.1).mp ω.2⟩, (e ω.1).2)
    invFun z :=
      ⟨e.symm (z.1.1, z.2),
        (hP _).mpr (by simpa using z.1.2)⟩
    left_inv ω := by
      apply Subtype.ext
      simp
    right_inv z := by
      rcases z with ⟨a, b⟩
      ext <;> simp
  }
  let eQ : {ω : Ω // Q ω} ≃ (A × {b : B // QB b}) := {
    toFun ω := ((e ω.1).1, ⟨(e ω.1).2, (hQ ω.1).mp ω.2⟩)
    invFun z :=
      ⟨e.symm (z.1, z.2.1),
        (hQ _).mpr (by simpa using z.2.2)⟩
    left_inv ω := by
      apply Subtype.ext
      simp
    right_inv z := by
      rcases z with ⟨a, b⟩
      ext <;> simp
  }
  let ePQ :
      {ω : Ω // P ω ∧ Q ω} ≃
        ({a : A // PA a} × {b : B // QB b}) := {
    toFun ω :=
      (⟨(e ω.1).1, (hP ω.1).mp ω.2.1⟩,
        ⟨(e ω.1).2, (hQ ω.1).mp ω.2.2⟩)
    invFun z :=
      ⟨e.symm (z.1.1, z.2.1),
        ⟨(hP _).mpr (by simpa using z.1.2),
          (hQ _).mpr (by simpa using z.2.2)⟩⟩
    left_inv ω := by
      apply Subtype.ext
      simp
    right_inv z := by
      rcases z with ⟨a, b⟩
      ext <;> simp
  }
  have hcardΩ :
      Nat.card Ω = Nat.card A * Nat.card B := by
    calc
      Nat.card Ω = Nat.card (A × B) :=
        Nat.card_congr e
      _ = Nat.card A * Nat.card B :=
        Nat.card_prod A B
  have hcardP :
      Nat.card {ω : Ω // P ω} =
        Nat.card {a : A // PA a} * Nat.card B := by
    calc
      Nat.card {ω : Ω // P ω} =
          Nat.card ({a : A // PA a} × B) :=
        Nat.card_congr eP
      _ = Nat.card {a : A // PA a} * Nat.card B :=
        Nat.card_prod _ _
  have hcardQ :
      Nat.card {ω : Ω // Q ω} =
        Nat.card A * Nat.card {b : B // QB b} := by
    calc
      Nat.card {ω : Ω // Q ω} =
          Nat.card (A × {b : B // QB b}) :=
        Nat.card_congr eQ
      _ = Nat.card A * Nat.card {b : B // QB b} :=
        Nat.card_prod _ _
  have hcardPQ :
      Nat.card {ω : Ω // P ω ∧ Q ω} =
        Nat.card {a : A // PA a} *
          Nat.card {b : B // QB b} := by
    calc
      Nat.card {ω : Ω // P ω ∧ Q ω} =
          Nat.card
            ({a : A // PA a} × {b : B // QB b}) :=
        Nat.card_congr ePQ
      _ =
          Nat.card {a : A // PA a} *
            Nat.card {b : B // QB b} :=
        Nat.card_prod _ _
  unfold finiteUniformProbability
  rw [hcardPQ, hcardP, hcardQ, hcardΩ]
  push_cast
  have hA : (Nat.card A : ℚ) ≠ 0 := by
    exact_mod_cast
      (Nat.card_ne_zero.mpr
        ⟨inferInstance, inferInstance⟩ : Nat.card A ≠ 0)
  have hB : (Nat.card B : ℚ) ≠ 0 := by
    exact_mod_cast
      (Nat.card_ne_zero.mpr
        ⟨inferInstance, inferInstance⟩ : Nat.card B ≠ 0)
  field_simp [hA, hB]

/-! ## Extensional dependence on `Πₓ(Y)` -/

/-- The natural prime label carried by one represented large coordinate. -/
def largeCoordinatePrime
    {M Y : ℕ} (q : LargePrimeCoordinate M Y) : ℕ :=
  q.1.1.1

/--
Two large-coordinate assignments give the same truncated value at a vertex
of `Vₓ` if they agree on `Πₓ(Y)`.
-/
theorem valueBit_extendLarge_eq_of_eqOn_largePrimeCoordinates
    {M Y x L n : ℕ}
    (hn : n ∈ startTreeSupport x L)
    (η θ : LargeSample M Y)
    (heq :
      ∀ q : LargePrimeCoordinate M Y,
        largeCoordinatePrime q ∈ largePrimeCoordinates x L Y →
          η q = θ q) :
    valueBit (extendLarge M Y η) n =
      valueBit (extendLarge M Y θ) n := by
  classical
  rw [valueBit, valueBit]
  apply Finset.sum_congr rfl
  intro p _hp
  by_cases hpY : Y < p.1.1
  · let q : LargePrimeCoordinate M Y := ⟨p, hpY⟩
    by_cases hparity : parityVec n p.1.1 = 0
    · simp [extendLarge, hpY, hparity]
    · have hpSupport :
          p.1.1 ∈ largeOddPrimeSupport Y n :=
        mem_largeOddPrimeSupport_iff.mpr ⟨hpY, hparity⟩
      have hpCoordinates :
          largeCoordinatePrime q ∈
            largePrimeCoordinates x L Y := by
        rw [mem_largePrimeCoordinates]
        exact ⟨n, hn, hpSupport⟩
      have hq := heq q hpCoordinates
      simp [extendLarge, hpY, q, largeCoordinatePrime, hq]
  · simp [extendLarge, hpY]

/--
The conditioned linear start system depends only on the coordinates in
`Πₓ(Y)`.
-/
theorem largeStartSystem_eq_of_eqOn_largePrimeCoordinates
    {M Y x L : ℕ}
    (η θ : LargeSample M Y)
    (heq :
      ∀ q : LargePrimeCoordinate M Y,
        largeCoordinatePrime q ∈ largePrimeCoordinates x L Y →
          η q = θ q) :
    largeStartSystem M Y x L η =
      largeStartSystem M Y x L θ := by
  funext i
  have hL : 0 < L := Nat.zero_lt_of_lt i.2
  have hroot :
      valueBit (extendLarge M Y η) (x - 1) =
        valueBit (extendLarge M Y θ) (x - 1) :=
    valueBit_extendLarge_eq_of_eqOn_largePrimeCoordinates
      (mem_startTreeSupport.mpr (Or.inl rfl)) η θ heq
  have hcenter :
      valueBit (extendLarge M Y η) x =
        valueBit (extendLarge M Y θ) x :=
    valueBit_extendLarge_eq_of_eqOn_largePrimeCoordinates
      (mem_startTreeSupport.mpr
        (Or.inr ⟨0, hL, by simp⟩)) η θ heq
  have hleaf :
      valueBit (extendLarge M Y η) (x + i.1) =
        valueBit (extendLarge M Y θ) (x + i.1) :=
    valueBit_extendLarge_eq_of_eqOn_largePrimeCoordinates
      (mem_startTreeSupport.mpr
        (Or.inr ⟨i.1, i.2, rfl⟩)) η θ heq
  simp only [largeStartSystem, LinearMap.comp_apply,
    startSystem_apply]
  by_cases hi : i.1 = 0
  · simp only [if_pos hi]
    exact congrArg₂ (· + ·) hroot hcenter
  · simp only [if_neg hi]
    exact congrArg₂ (· + ·) hcenter hleaf

/--
Restriction to `Πₓ(Y)`, expressed as a linear endomorphism of the common
large-coordinate sample space.
-/
def maskToStartCoordinates
    (M Y x L : ℕ) :
    LargeSample M Y →ₗ[F₂] LargeSample M Y where
  toFun η q :=
    if largeCoordinatePrime q ∈ largePrimeCoordinates x L Y then
      η q
    else
      0
  map_add' η θ := by
    funext q
    change
      (if largeCoordinatePrime q ∈ largePrimeCoordinates x L Y then
          η q + θ q
        else 0) =
        (if largeCoordinatePrime q ∈ largePrimeCoordinates x L Y then
            η q
          else 0) +
          if largeCoordinatePrime q ∈ largePrimeCoordinates x L Y then
            θ q
          else 0
    by_cases hq :
        largeCoordinatePrime q ∈ largePrimeCoordinates x L Y
    · rw [if_pos hq, if_pos hq, if_pos hq]
    · rw [if_neg hq, if_neg hq, if_neg hq]
      simp
  map_smul' c η := by
    funext q
    simp only [Pi.smul_apply, RingHom.id_apply]
    by_cases hq :
        largeCoordinatePrime q ∈ largePrimeCoordinates x L Y
    · rw [if_pos hq, if_pos hq]
    · rw [if_neg hq, if_neg hq, smul_zero]

/-- Masking to `Πₓ(Y)` does not change the conditioned start system at `x`. -/
theorem largeStartSystem_maskToStartCoordinates
    (M Y x L : ℕ) (η : LargeSample M Y) :
    largeStartSystem M Y x L
        (maskToStartCoordinates M Y x L η) =
      largeStartSystem M Y x L η := by
  apply largeStartSystem_eq_of_eqOn_largePrimeCoordinates
  intro q hq
  change
    (if largeCoordinatePrime q ∈ largePrimeCoordinates x L Y then
        η q
      else 0) =
      η q
  rw [if_pos hq]

/--
If `Πₓ(Y)` and `Πᵧ(Y)` are disjoint, an assignment masked to the second set
contributes zero to the start system at `x`.
-/
theorem largeStartSystem_mask_eq_zero_of_disjoint
    {M Y x y L : ℕ}
    (hdisjoint :
      Disjoint (largePrimeCoordinates x L Y)
        (largePrimeCoordinates y L Y))
    (η : LargeSample M Y) :
    largeStartSystem M Y x L
        (maskToStartCoordinates M Y y L η) =
      0 := by
  have heq :
      largeStartSystem M Y x L
          (maskToStartCoordinates M Y y L η) =
        largeStartSystem M Y x L 0 := by
    apply largeStartSystem_eq_of_eqOn_largePrimeCoordinates
    intro q hqx
    have hnoty :
        largeCoordinatePrime q ∉
          largePrimeCoordinates y L Y := by
      exact Finset.disjoint_left.mp hdisjoint hqx
    change
      (if largeCoordinatePrime q ∈ largePrimeCoordinates y L Y then
          η q
        else 0) =
        0
    rw [if_neg hnoty]
  simpa using heq

/-- Nonadjacent distinct starts have disjoint large-prime coordinate sets. -/
theorem disjoint_largePrimeCoordinates_of_not_adjacent
    {L Y x y : ℕ}
    (hxy : x ≠ y)
    (hnot : ¬LargePrimeAdjacent L Y x y) :
    Disjoint (largePrimeCoordinates x L Y)
      (largePrimeCoordinates y L Y) := by
  rw [Finset.disjoint_left]
  intro p hpx hpy
  apply hnot
  exact ⟨hxy,
    ⟨p, Finset.mem_inter.mpr ⟨hpx, hpy⟩⟩⟩

/--
Event-level support statement: after the small coordinates are fixed,
changing large coordinates outside `Πₓ(Y)` cannot change `startAt x`.
-/
theorem conditionedStartAt_iff_of_eqOn_largePrimeCoordinates
    {M Y x L : ℕ}
    (hL : 0 < L)
    (σ : SmallSample M Y)
    (η θ : LargeSample M Y)
    (heq :
      ∀ q : LargePrimeCoordinate M Y,
        largeCoordinatePrime q ∈ largePrimeCoordinates x L Y →
          η q = θ q) :
    startAt (assemble M Y σ η) x L ↔
      startAt (assemble M Y σ θ) x L := by
  rw [assemble_startAt_iff M Y x L hL σ η,
    assemble_startAt_iff M Y x L hL σ θ,
    largeStartSystem_eq_of_eqOn_largePrimeCoordinates η θ heq]

/-! ## One start versus an arbitrary family of non-neighbors -/

/-- Represented large coordinates belonging to `Πₓ(Y)`. -/
def StartSupportCoordinate (M Y x L : ℕ) :=
  {q : LargePrimeCoordinate M Y //
    largeCoordinatePrime q ∈ largePrimeCoordinates x L Y}

/-- Represented large coordinates outside `Πₓ(Y)`. -/
def StartComplementCoordinate (M Y x L : ℕ) :=
  {q : LargePrimeCoordinate M Y //
    largeCoordinatePrime q ∉ largePrimeCoordinates x L Y}

instance (M Y x L : ℕ) :
    Fintype (StartSupportCoordinate M Y x L) :=
  Subtype.fintype _

instance (M Y x L : ℕ) :
    Fintype (StartComplementCoordinate M Y x L) :=
  Subtype.fintype _

noncomputable instance (M Y x L : ℕ) :
    DecidableEq (StartSupportCoordinate M Y x L) :=
  Classical.decEq _

noncomputable instance (M Y x L : ℕ) :
    DecidableEq (StartComplementCoordinate M Y x L) :=
  Classical.decEq _

/-- Assignments on the represented coordinates in `Πₓ(Y)`. -/
abbrev StartSupportSample (M Y x L : ℕ) :=
  StartSupportCoordinate M Y x L → F₂

/-- Assignments on the represented complement of `Πₓ(Y)`. -/
abbrev StartComplementSample (M Y x L : ℕ) :=
  StartComplementCoordinate M Y x L → F₂

/-- Exact product decomposition at the coordinate support `Πₓ(Y)`. -/
def startCoordinateSplit
    (M Y x L : ℕ) :
    LargeSample M Y ≃
      StartSupportSample M Y x L ×
        StartComplementSample M Y x L where
  toFun η :=
    (fun q ↦ η q.1, fun q ↦ η q.1)
  invFun z q :=
    if hq :
        largeCoordinatePrime q ∈ largePrimeCoordinates x L Y then
      z.1 ⟨q, hq⟩
    else
      z.2 ⟨q, hq⟩
  left_inv η := by
    funext q
    by_cases hq :
        largeCoordinatePrime q ∈ largePrimeCoordinates x L Y <;>
      simp [hq]
  right_inv z := by
    apply Prod.ext
    · funext q
      simp [q.2]
    · funext q
      simp [q.2]

/--
Finite conditional independence in the exact form used in Lemma 13.5:
one start is independent of the joint event for an arbitrary finite family
of its non-neighbors.  No pairwise-disjointness assumption is imposed inside
the family.
-/
theorem conditionedStart_independent_of_nonNeighbors
    {M Y x L : ℕ} (t : Finset ℕ)
    (hL : 0 < L)
    (hnonneighbors :
      ∀ y ∈ t, x ≠ y ∧
        ¬LargePrimeAdjacent L Y x y)
    (σ : SmallSample M Y) :
    finiteUniformProbability
        (fun η : LargeSample M Y ↦
          startAt (assemble M Y σ η) x L ∧
            ∀ y : ↥t,
              startAt (assemble M Y σ η) y.1 L) =
      finiteUniformProbability
          (fun η : LargeSample M Y ↦
            startAt (assemble M Y σ η) x L) *
        finiteUniformProbability
          (fun η : LargeSample M Y ↦
            ∀ y : ↥t,
              startAt (assemble M Y σ η) y.1 L) := by
  let e := startCoordinateSplit M Y x L
  let P : LargeSample M Y → Prop :=
    fun η ↦ startAt (assemble M Y σ η) x L
  let Q : LargeSample M Y → Prop :=
    fun η ↦ ∀ y : ↥t,
      startAt (assemble M Y σ η) y.1 L
  let PA : StartSupportSample M Y x L → Prop :=
    fun a ↦ P (e.symm (a, 0))
  let QB : StartComplementSample M Y x L → Prop :=
    fun b ↦ Q (e.symm (0, b))
  apply finiteUniformProbability_and_eq_mul_of_product_support
    e P Q PA QB
  · intro η
    dsimp only [P, PA]
    apply conditionedStartAt_iff_of_eqOn_largePrimeCoordinates
      hL σ η (e.symm ((e η).1, 0))
    intro q hqx
    dsimp only [e]
    change
      η q =
        if largeCoordinatePrime q ∈ largePrimeCoordinates x L Y then
          η q
        else 0
    rw [if_pos hqx]
  · intro η
    dsimp only [Q, QB]
    constructor
    · intro h y
      let θ := e.symm (0, (e η).2)
      have hyData := hnonneighbors y.1 y.2
      have hdisjoint :
          Disjoint (largePrimeCoordinates x L Y)
            (largePrimeCoordinates y.1 L Y) :=
        disjoint_largePrimeCoordinates_of_not_adjacent
          hyData.1 hyData.2
      apply
        (conditionedStartAt_iff_of_eqOn_largePrimeCoordinates
          hL σ η θ ?_).mp (h y)
      intro q hqy
      have hnotx :
          largeCoordinatePrime q ∉
            largePrimeCoordinates x L Y := by
        intro hqx
        exact Finset.disjoint_left.mp hdisjoint hqx hqy
      dsimp only [θ, e]
      change
        η q =
          if largeCoordinatePrime q ∈ largePrimeCoordinates x L Y then
            0
          else η q
      rw [if_neg hnotx]
    · intro h y
      let θ := e.symm (0, (e η).2)
      have hyData := hnonneighbors y.1 y.2
      have hdisjoint :
          Disjoint (largePrimeCoordinates x L Y)
            (largePrimeCoordinates y.1 L Y) :=
        disjoint_largePrimeCoordinates_of_not_adjacent
          hyData.1 hyData.2
      apply
        (conditionedStartAt_iff_of_eqOn_largePrimeCoordinates
          hL σ η θ ?_).mpr (h y)
      intro q hqy
      have hnotx :
          largeCoordinatePrime q ∉
            largePrimeCoordinates x L Y := by
        intro hqx
        exact Finset.disjoint_left.mp hdisjoint hqx hqy
      dsimp only [θ, e]
      change
        η q =
          if largeCoordinatePrime q ∈ largePrimeCoordinates x L Y then
            0
          else η q
      rw [if_neg hnotx]

/--
Literal graph specialization: conditionally on the small coordinates, a
good-start indicator is independent of the joint event generated by any
finite set of good vertices outside its graph neighborhood.
-/
theorem goodStart_independent_of_graph_nonNeighbors
    {N Y x L : ℕ} (t : Finset ℕ)
    (hL : 0 < L)
    (hxGood : x ∈ goodStarts N L Y)
    (htGood : ∀ y ∈ t, y ∈ goodStarts N L Y)
    (hxNotMem : x ∉ t)
    (hnonadj :
      ∀ y (hy : y ∈ t),
        ¬(largePrimeDependencyGraph N L Y).Adj
          ⟨x, hxGood⟩ ⟨y, htGood y hy⟩)
    (σ : SmallSample (dyadicCutoff N L) Y) :
    finiteUniformProbability
        (fun η : LargeSample (dyadicCutoff N L) Y ↦
          startAt
              (assemble (dyadicCutoff N L) Y σ η) x L ∧
            ∀ y : ↥t,
              startAt
                (assemble (dyadicCutoff N L) Y σ η) y.1 L) =
      finiteUniformProbability
          (fun η : LargeSample (dyadicCutoff N L) Y ↦
            startAt
              (assemble (dyadicCutoff N L) Y σ η) x L) *
        finiteUniformProbability
          (fun η : LargeSample (dyadicCutoff N L) Y ↦
            ∀ y : ↥t,
              startAt
                (assemble (dyadicCutoff N L) Y σ η) y.1 L) := by
  apply conditionedStart_independent_of_nonNeighbors t hL
  intro y hy
  constructor
  · intro hxy
    subst y
    exact hxNotMem hy
  · exact hnonadj y hy

/-! ## Joint conditioned systems for a finite family -/

/--
The joint linear system for a finite family of starts, all in the same
dyadic large-coordinate cylinder.
-/
def jointLargeStartSystem
    (N L Y : ℕ) (s : Finset ℕ) :
    LargeSample (dyadicCutoff N L) Y →ₗ[F₂]
      ((x : ↥s) → Fin L → F₂) :=
  LinearMap.pi fun x : ↥s ↦
    largeStartSystem (dyadicCutoff N L) Y x.1 L

/-- Joint translated right-hand side after fixing one small-prime assignment. -/
def jointConditionedStartRhs
    (N L Y : ℕ) (s : Finset ℕ)
    (σ : SmallSample (dyadicCutoff N L) Y) :
    (x : ↥s) → Fin L → F₂ :=
  fun x ↦
    conditionedStartRhs (dyadicCutoff N L) Y x.1 L σ

@[simp]
theorem jointLargeStartSystem_apply
    (N L Y : ℕ) (s : Finset ℕ)
    (η : LargeSample (dyadicCutoff N L) Y) (x : ↥s) :
    jointLargeStartSystem N L Y s η x =
      largeStartSystem (dyadicCutoff N L) Y x.1 L η :=
  rfl

/--
The joint affine fiber is exactly the conjunction of the conditioned
`startAt` events over the family.
-/
theorem jointConditionedSystem_eq_iff_forall_startAt
    (N L Y : ℕ) (s : Finset ℕ) (hL : 0 < L)
    (σ : SmallSample (dyadicCutoff N L) Y)
    (η : LargeSample (dyadicCutoff N L) Y) :
    jointLargeStartSystem N L Y s η =
        jointConditionedStartRhs N L Y s σ ↔
      ∀ x : ↥s, startAt (assemble (dyadicCutoff N L) Y σ η) x.1 L := by
  constructor
  · intro h x
    rw [assemble_startAt_iff
      (dyadicCutoff N L) Y x.1 L hL σ η]
    exact congrFun h x
  · intro h
    funext x
    exact (assemble_startAt_iff
      (dyadicCutoff N L) Y x.1 L hL σ η).mp (h x)

/-- Each good start has a surjective conditioned large-coordinate system. -/
theorem largeStartSystem_surjective_of_mem_goodStarts
    {N L Y x : ℕ}
    (hN : 2 ≤ N) (hL : 0 < L) (hLY : L + 1 ≤ Y)
    (hx : x ∈ goodStarts N L Y) :
    Function.Surjective
      (largeStartSystem (dyadicCutoff N L) Y x L) := by
  apply largeStartSystem_surjective
    (two_le_of_mem_dyadicBlock hN (mem_goodStarts.mp hx).1)
    hL hLY
  · intro j
    exact startWindow_le_dyadicCutoff
      (mem_goodStarts.mp hx).1 j.2
  · intro j hjDef
    exact (mem_goodStarts.mp hx).2
      (mem_terminalBadStarts.mpr
        ⟨(mem_goodStarts.mp hx).1, j.1, j.2,
          (largeOddKernel_eq_one_iff_hDefective
            Y (x + j.1)).mpr hjDef⟩)

/--
Surjectivity of the joint conditioned system on a family containing no
dependency edge.
-/
theorem jointLargeStartSystem_surjective
    {N L Y : ℕ} {s : Finset ℕ}
    (hN : 2 ≤ N) (hL : 0 < L) (hLY : L + 1 ≤ Y)
    (hsGood : ∀ x ∈ s, x ∈ goodStarts N L Y)
    (hsIndependent :
      ∀ x ∈ s, ∀ y ∈ s, x ≠ y →
        ¬LargePrimeAdjacent L Y x y) :
    Function.Surjective (jointLargeStartSystem N L Y s) := by
  classical
  intro b
  have hsurj :
      ∀ z : ↥s,
        Function.Surjective
          (largeStartSystem (dyadicCutoff N L) Y z.1 L) := by
    intro z
    exact largeStartSystem_surjective_of_mem_goodStarts
      hN hL hLY (hsGood z.1 z.2)
  let preimage :
      (z : ↥s) →
        LargeSample (dyadicCutoff N L) Y :=
    fun z ↦ Classical.choose (hsurj z (b z))
  have hpreimage :
      ∀ z : ↥s,
        largeStartSystem (dyadicCutoff N L) Y z.1 L
            (preimage z) =
          b z :=
    fun z ↦ Classical.choose_spec (hsurj z (b z))
  let η : LargeSample (dyadicCutoff N L) Y :=
    ∑ z : ↥s,
      maskToStartCoordinates
        (dyadicCutoff N L) Y z.1 L (preimage z)
  refine ⟨η, ?_⟩
  funext z
  change
    largeStartSystem (dyadicCutoff N L) Y z.1 L η = b z
  calc
    largeStartSystem (dyadicCutoff N L) Y z.1 L η =
        ∑ w : ↥s,
          largeStartSystem (dyadicCutoff N L) Y z.1 L
            (maskToStartCoordinates
              (dyadicCutoff N L) Y w.1 L (preimage w)) := by
          simp [η]
    _ = ∑ w : ↥s, if w = z then b z else 0 := by
      apply Finset.sum_congr rfl
      intro w _hw
      by_cases hwz : w = z
      · subst w
        simp [largeStartSystem_maskToStartCoordinates,
          hpreimage z]
      · have hvalues : w.1 ≠ z.1 := by
          intro h
          apply hwz
          exact Subtype.ext h
        have hdisjoint :
            Disjoint (largePrimeCoordinates z.1 L Y)
              (largePrimeCoordinates w.1 L Y) := by
          apply disjoint_largePrimeCoordinates_of_not_adjacent
            hvalues.symm
          exact hsIndependent z.1 z.2 w.1 w.2 hvalues.symm
        simp [hwz,
          largeStartSystem_mask_eq_zero_of_disjoint
            hdisjoint (preimage w)]
    _ = b z := by simp

/-! ## Exact factorization of conditioned probabilities -/

/-- Large assignments satisfying every translated start equation in `s`. -/
def jointConditionedStartSolutions
    (N L Y : ℕ) (s : Finset ℕ)
    (σ : SmallSample (dyadicCutoff N L) Y) :
    Finset (LargeSample (dyadicCutoff N L) Y) := by
  classical
  exact Finset.univ.filter fun η ↦
    jointLargeStartSystem N L Y s η =
      jointConditionedStartRhs N L Y s σ

/--
Division-free joint fiber count:

`#joint solutions · 2^(L · #s) = #large assignments`.
-/
theorem card_jointConditionedStartSolutions_mul_two_pow
    {N L Y : ℕ} {s : Finset ℕ}
    (hN : 2 ≤ N) (hL : 0 < L) (hLY : L + 1 ≤ Y)
    (hsGood : ∀ x ∈ s, x ∈ goodStarts N L Y)
    (hsIndependent :
      ∀ x ∈ s, ∀ y ∈ s, x ≠ y →
        ¬LargePrimeAdjacent L Y x y)
    (σ : SmallSample (dyadicCutoff N L) Y) :
    (jointConditionedStartSolutions N L Y s σ).card *
        2 ^ (s.card * L) =
      Fintype.card (LargeSample (dyadicCutoff N L) Y) := by
  classical
  let A := jointLargeStartSystem N L Y s
  let b := jointConditionedStartRhs N L Y s σ
  have hsurj : Function.Surjective A := by
    dsimp only [A]
    exact jointLargeStartSystem_surjective
      hN hL hLY hsGood hsIndependent
  have hcompat : Compatible A b :=
    LinearMap.mem_range.mpr (hsurj b)
  let η₀ : Solution A b :=
    Classical.choice ((compatible_iff_nonempty A b).mp hcompat)
  have hsolutionCard :
      Fintype.card (Solution A b) =
        (Finset.univ.filter fun η :
          LargeSample (dyadicCutoff N L) Y ↦ A η = b).card := by
    rw [Fintype.card_subtype]
    apply congrArg Finset.card
    ext η
    simp [solutionSet]
  have hfiber :
      (jointConditionedStartSolutions N L Y s σ).card =
        2 ^ Module.finrank F₂ (LinearMap.ker A) := by
    calc
      (jointConditionedStartSolutions N L Y s σ).card =
          (Finset.univ.filter fun η :
            LargeSample (dyadicCutoff N L) Y ↦ A η = b).card := by
              rfl
      _ = Fintype.card (Solution A b) :=
        hsolutionCard.symm
      _ = Fintype.card (LinearMap.ker A) :=
        Fintype.card_congr (solutionEquivKer A b η₀)
      _ = 2 ^ Module.finrank F₂ (LinearMap.ker A) := by
        calc
          Fintype.card (LinearMap.ker A) =
              Fintype.card F₂ ^
                Module.finrank F₂ (LinearMap.ker A) :=
            Module.card_eq_pow_finrank
              (K := F₂) (V := LinearMap.ker A)
          _ = 2 ^ Module.finrank F₂ (LinearMap.ker A) := by
            rw [ZMod.card]
  have hnullity :=
    LinearMap.finrank_range_add_finrank_ker A
  have hrange : LinearMap.range A = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  rw [hrange] at hnullity
  have hcodomain :
      Module.finrank F₂ ((x : ↥s) → Fin L → F₂) =
        s.card * L := by
    rw [Module.finrank_pi_fintype]
    simp [Module.finrank_fin_fun]
  rw [finrank_top, hcodomain] at hnullity
  have hdim :
      Module.finrank F₂
          (LargeSample (dyadicCutoff N L) Y) =
        Module.finrank F₂ (LinearMap.ker A) + s.card * L := by
    omega
  rw [hfiber, card_eq_two_pow_finrank, hdim, pow_add]

/--
The joint conditioned probability on an edge-free family of good starts is
the exact independent baseline `2^(-L · #s)`.
-/
theorem jointConditionedStartProbability_eq_baseline
    {N L Y : ℕ} {s : Finset ℕ}
    (hN : 2 ≤ N) (hL : 0 < L) (hLY : L + 1 ≤ Y)
    (hsGood : ∀ x ∈ s, x ∈ goodStarts N L Y)
    (hsIndependent :
      ∀ x ∈ s, ∀ y ∈ s, x ≠ y →
        ¬LargePrimeAdjacent L Y x y)
    (σ : SmallSample (dyadicCutoff N L) Y) :
    uniformSolutionProbability
        (jointLargeStartSystem N L Y s)
        (jointConditionedStartRhs N L Y s σ) =
      (1 : ℚ) / (2 : ℚ) ^ (s.card * L) := by
  let A := jointLargeStartSystem N L Y s
  let b := jointConditionedStartRhs N L Y s σ
  have hsurj : Function.Surjective A := by
    dsimp only [A]
    exact jointLargeStartSystem_surjective
      hN hL hLY hsGood hsIndependent
  have hcompat : Compatible A b :=
    LinearMap.mem_range.mpr (hsurj b)
  rw [uniformSolutionProbability_of_compatible A b hcompat]
  have hnullity :=
    LinearMap.finrank_range_add_finrank_ker A
  have hrange : LinearMap.range A = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  rw [hrange] at hnullity
  have hcodomain :
      Module.finrank F₂ ((x : ↥s) → Fin L → F₂) =
        s.card * L := by
    rw [Module.finrank_pi_fintype]
    simp [Module.finrank_fin_fun]
  rw [finrank_top, hcodomain] at hnullity
  have hdim :
      Module.finrank F₂
          (LargeSample (dyadicCutoff N L) Y) =
        Module.finrank F₂ (LinearMap.ker A) + s.card * L := by
    omega
  rw [hdim, pow_add]
  field_simp

/--
Exact product factorization: on every edge-free finite family of good starts,
the joint conditional probability equals the product of the individual
conditional probabilities.
-/
theorem jointConditionedStartProbability_eq_product
    {N L Y : ℕ} {s : Finset ℕ}
    (hN : 2 ≤ N) (hL : 0 < L) (hLY : L + 1 ≤ Y)
    (hsGood : ∀ x ∈ s, x ∈ goodStarts N L Y)
    (hsIndependent :
      ∀ x ∈ s, ∀ y ∈ s, x ≠ y →
        ¬LargePrimeAdjacent L Y x y)
    (σ : SmallSample (dyadicCutoff N L) Y) :
    uniformSolutionProbability
        (jointLargeStartSystem N L Y s)
        (jointConditionedStartRhs N L Y s σ) =
      ∏ x : ↥s,
        uniformSolutionProbability
          (largeStartSystem (dyadicCutoff N L) Y x.1 L)
          (conditionedStartRhs
            (dyadicCutoff N L) Y x.1 L σ) := by
  rw [jointConditionedStartProbability_eq_baseline
    hN hL hLY hsGood hsIndependent σ]
  have hindividual :
      ∀ x : ↥s,
        uniformSolutionProbability
            (largeStartSystem (dyadicCutoff N L) Y x.1 L)
            (conditionedStartRhs
              (dyadicCutoff N L) Y x.1 L σ) =
          (1 : ℚ) / (2 : ℚ) ^ L := by
    intro x
    exact conditionedStartProbability_eq_baseline_of_not_terminalBad
      hN (mem_goodStarts.mp (hsGood x.1 x.2)).1 hL hLY
      (mem_goodStarts.mp (hsGood x.1 x.2)).2 σ
  simp_rw [hindividual]
  rw [Finset.prod_const]
  simp only [Finset.card_univ, Fintype.card_coe]
  rw [div_pow, one_pow, ← pow_mul]
  rw [Nat.mul_comm L s.card]

end

end ConditionalDependencyGraph
end PaperC
