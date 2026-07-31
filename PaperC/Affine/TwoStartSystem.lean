import PaperC.Affine.Normalization
import PaperC.Affine.StartSystem
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Logic.Equiv.Fin.Basic

set_option maxHeartbeats 1200000

/-!
# Two arbitrary starts and their complete boundaries

This module packages two starts of common length `L`, based at arbitrary
positions `x` and `y`, into one affine system indexed by
`Sum (Fin L) (Fin L)`.

It also gives the complete vertex boundary of one start star.  Its
`L + 1` vertices are ordered as follows:

* vertex `0`: the root `x - 1`;
* vertex `1`: the centre `x`;
* vertex `i + 1`, for `0 < i < L`: the leaf `x + i`.

The complete boundary map is injective on edge coefficients.  For two starts,
the direct-sum boundary is therefore injective as well, so every nonzero row
relation selects at least one nonzero boundary occurrence.
-/

namespace PaperC
namespace Affine

open scoped BigOperators

noncomputable section

/-! ## The joint affine system -/

/-- A row of the joint system of starts based at `x` and `y`. -/
def twoStartRow (M x y L : ℕ) :
    Sum (Fin L) (Fin L) → SampleSpace M →ₗ[F₂] F₂
  | Sum.inl i => startRow M x L i
  | Sum.inr i => startRow M y L i

/-- The joint linear system of two arbitrary starts. -/
def twoStartSystem (M x y L : ℕ) :
    SampleSpace M →ₗ[F₂] (Sum (Fin L) (Fin L) → F₂) :=
  LinearMap.pi (twoStartRow M x y L)

/-- The right-hand side of the two-start system. -/
def twoStartRhs (L : ℕ) : Sum (Fin L) (Fin L) → F₂
  | Sum.inl i => startRhs L i
  | Sum.inr i => startRhs L i

@[simp]
theorem twoStartSystem_apply_inl
    (M x y L : ℕ) (ω : SampleSpace M) (i : Fin L) :
    twoStartSystem M x y L ω (Sum.inl i) =
      startSystem M x L ω i :=
  rfl

@[simp]
theorem twoStartSystem_apply_inr
    (M x y L : ℕ) (ω : SampleSpace M) (i : Fin L) :
    twoStartSystem M x y L ω (Sum.inr i) =
      startSystem M y L ω i :=
  rfl

@[simp]
theorem twoStartRhs_apply_inl (L : ℕ) (i : Fin L) :
    twoStartRhs L (Sum.inl i) = startRhs L i :=
  rfl

@[simp]
theorem twoStartRhs_apply_inr (L : ℕ) (i : Fin L) :
    twoStartRhs L (Sum.inr i) = startRhs L i :=
  rfl

/-- The joint system is exactly the intersection of the two start events. -/
theorem twoStartSystem_eq_twoStartRhs_iff
    {M x y L : ℕ} (ω : SampleSpace M) (hL : 0 < L) :
    twoStartSystem M x y L ω = twoStartRhs L ↔
      StartEvent (valueBit ω) x L ∧
        StartEvent (valueBit ω) y L := by
  rw [← startSystem_eq_startRhs_iff ω hL,
    ← startSystem_eq_startRhs_iff ω hL]
  constructor
  · intro h
    constructor
    · funext i
      exact congrFun h (Sum.inl i)
    · funext i
      exact congrFun h (Sum.inr i)
  · rintro ⟨hx, hy⟩
    funext i
    cases i with
    | inl i => exact congrFun hx i
    | inr i => exact congrFun hy i

/-! ## Complete boundary of one start star -/

/-- Root vertex of a start star. -/
def startRootVertex (L : ℕ) : Fin (L + 1) :=
  ⟨0, by omega⟩

/-- The vertex at the non-root endpoint of row `i`. -/
def startTipVertex {L : ℕ} (i : Fin L) : Fin (L + 1) :=
  ⟨i.1 + 1, by omega⟩

/--
The other endpoint of row `i`: the root for row zero and the centre for
all remaining rows.
-/
def startBaseVertex {L : ℕ} (i : Fin L) : Fin (L + 1) :=
  if i.1 = 0 then
    startRootVertex L
  else
    ⟨1, Nat.succ_lt_succ (Nat.zero_lt_of_lt i.2)⟩

/-- Binary incidence column of one start row on all `L+1` vertices. -/
def startIncidenceColumn {L : ℕ} (i : Fin L) : Fin (L + 1) → F₂ :=
  Pi.single (startBaseVertex i) 1 +
    Pi.single (startTipVertex i) 1

/--
The complete vertex boundary of a start edge-coefficient vector.
-/
def startCompleteBoundary (L : ℕ) :
    (Fin L → F₂) →ₗ[F₂] (Fin (L + 1) → F₂) :=
  Fintype.linearCombination F₂ (startIncidenceColumn (L := L))

@[simp]
theorem startCompleteBoundary_apply
    {L : ℕ} (u : Fin L → F₂) (v : Fin (L + 1)) :
    startCompleteBoundary L u v =
      ∑ i : Fin L, u i * startIncidenceColumn i v := by
  simp [startCompleteBoundary,
    Fintype.linearCombination_apply, smul_eq_mul]

/--
A private complete-boundary vertex for row `i`: the root for row zero and
its leaf otherwise.
-/
def startPrivateVertex {L : ℕ} (i : Fin L) : Fin (L + 1) :=
  if i.1 = 0 then startRootVertex L else startTipVertex i

private theorem startIncidenceColumn_apply_private
    {L : ℕ} (i j : Fin L) :
    startIncidenceColumn j (startPrivateVertex i) =
      if j = i then 1 else 0 := by
  classical
  by_cases hij : j = i
  · subst j
    by_cases hi0 : i.1 = 0
    · simp [startIncidenceColumn, startPrivateVertex,
        startBaseVertex, startRootVertex, startTipVertex,
        Pi.single_apply, hi0]
    · have htip_ne_center :
          startTipVertex i ≠ (⟨1, by omega⟩ : Fin (L + 1)) := by
        intro h
        apply hi0
        have hv := congrArg Fin.val h
        simp [startTipVertex] at hv
        omega
      simp [startIncidenceColumn, startPrivateVertex,
        startBaseVertex, Pi.single_apply, hi0,
        htip_ne_center, htip_ne_center.symm]
  · by_cases hi0 : i.1 = 0
    · have hiRoot : startPrivateVertex i = startRootVertex L := by
        simp [startPrivateVertex, hi0]
      have hj0 : j.1 ≠ 0 := by
        intro hj0
        apply hij
        apply Fin.ext
        omega
      have hroot_ne_base :
          startRootVertex L ≠ startBaseVertex j := by
        simp [startRootVertex, startBaseVertex, hj0]
      have hroot_ne_tip :
          startRootVertex L ≠ startTipVertex j := by
        intro h
        have hv := congrArg Fin.val h
        simp [startRootVertex, startTipVertex] at hv
      simp [startIncidenceColumn, hiRoot, Pi.single_apply,
        hroot_ne_base, hroot_ne_tip, hij]
    · have hj_tip_ne :
          startTipVertex j ≠ startTipVertex i := by
        intro h
        apply hij
        apply Fin.ext
        have hv := congrArg Fin.val h
        simp [startTipVertex] at hv
        omega
      by_cases hj0 : j.1 = 0
      · have htip_ne_root :
            startTipVertex i ≠ startRootVertex L := by
          intro h
          have hv := congrArg Fin.val h
          simp [startTipVertex, startRootVertex] at hv
        have htip_ne_center :
            startTipVertex i ≠ startTipVertex j := by
          exact Ne.symm hj_tip_ne
        simp [startIncidenceColumn, startPrivateVertex,
          startBaseVertex, Pi.single_apply, hi0, hj0,
          htip_ne_root, htip_ne_center, hij]
      · have htip_ne_center :
            startTipVertex i ≠ (⟨1, by omega⟩ : Fin (L + 1)) := by
          intro h
          apply hi0
          have hv := congrArg Fin.val h
          simp [startTipVertex] at hv
          omega
        have htip_ne_tip :
            startTipVertex i ≠ startTipVertex j :=
          Ne.symm hj_tip_ne
        simp [startIncidenceColumn, startPrivateVertex,
          startBaseVertex, Pi.single_apply, hi0, hj0,
          htip_ne_center, htip_ne_tip, hij]

/-- The complete boundary determines every start-row coefficient. -/
theorem startCompleteBoundary_injective
    (L : ℕ) :
    Function.Injective (startCompleteBoundary L) := by
  intro u v huv
  funext i
  have hi := congrFun huv (startPrivateVertex i)
  simp only [startCompleteBoundary_apply] at hi
  calc
    u i = ∑ j : Fin L, u j *
        startIncidenceColumn j (startPrivateVertex i) := by
      symm
      simp_rw [startIncidenceColumn_apply_private i]
      simp
    _ = ∑ j : Fin L, v j *
        startIncidenceColumn j (startPrivateVertex i) := hi
    _ = v i := by
      simp_rw [startIncidenceColumn_apply_private i]
      simp

/-- Integer label of a complete start vertex. -/
def startCompleteVertexLabel (x L : ℕ) (v : Fin (L + 1)) : ℕ :=
  if v.1 = 0 then x - 1 else x + (v.1 - 1)

/-- Parity-vector row corresponding to one edge of the start star. -/
def startEdgeParity (x p : ℕ) {L : ℕ} (i : Fin L) : F₂ :=
  if i.1 = 0 then
    parityVec (x - 1) p + parityVec x p
  else
    parityVec x p + parityVec (x + i.1) p

@[simp]
theorem startCompleteVertexLabel_root
    (x L : ℕ) :
    startCompleteVertexLabel x L (startRootVertex L) = x - 1 := by
  simp [startCompleteVertexLabel, startRootVertex]

@[simp]
theorem startCompleteVertexLabel_tip
    (x : ℕ) {L : ℕ} (i : Fin L) :
    startCompleteVertexLabel x L (startTipVertex i) = x + i.1 := by
  simp [startCompleteVertexLabel, startTipVertex]

theorem startCompleteVertexLabel_base
    (x : ℕ) {L : ℕ} (i : Fin L) :
    startCompleteVertexLabel x L (startBaseVertex i) =
      if i.1 = 0 then x - 1 else x := by
  by_cases hi : i.1 = 0
  · simp [startBaseVertex, hi]
  · simp [startBaseVertex, startCompleteVertexLabel, hi]

/-- A row parity vector is the sum of the parity vectors at its endpoints. -/
theorem startEdgeParity_eq_endpoint_sum
    (x p : ℕ) {L : ℕ} (i : Fin L) :
    startEdgeParity x p i =
      parityVec (startCompleteVertexLabel x L (startBaseVertex i)) p +
        parityVec (startCompleteVertexLabel x L (startTipVertex i)) p := by
  by_cases hi : i.1 = 0
  · simp [startEdgeParity, startCompleteVertexLabel_base, hi]
  · simp [startEdgeParity, startCompleteVertexLabel_base, hi]

/--
Incidence form of one parity row: sum the vertex parity coordinates against
the row's incidence column.
-/
theorem startEdgeParity_eq_sum_incidence
    (x p : ℕ) {L : ℕ} (i : Fin L) :
    startEdgeParity x p i =
      ∑ v : Fin (L + 1),
        startIncidenceColumn i v *
          parityVec (startCompleteVertexLabel x L v) p := by
  rw [startEdgeParity_eq_endpoint_sum]
  simp [startIncidenceColumn, Pi.single_apply,
    add_mul, Finset.sum_add_distrib]

/--
Line--boundary identity for a complete start star.

The linear combination of edge parity rows equals the linear combination of
vertex parity vectors selected by the complete boundary.
-/
theorem sum_startEdgeParity_eq_sum_completeBoundary
    (x p : ℕ) {L : ℕ} (u : Fin L → F₂) :
    (∑ i : Fin L, u i * startEdgeParity x p i) =
      ∑ v : Fin (L + 1),
        startCompleteBoundary L u v *
          parityVec (startCompleteVertexLabel x L v) p := by
  simp_rw [startEdgeParity_eq_sum_incidence]
  calc
    (∑ i : Fin L,
        u i *
          ∑ v : Fin (L + 1),
            startIncidenceColumn i v *
              parityVec (startCompleteVertexLabel x L v) p) =
        ∑ i : Fin L, ∑ v : Fin (L + 1),
          u i *
            (startIncidenceColumn i v *
              parityVec (startCompleteVertexLabel x L v) p) := by
          apply Finset.sum_congr rfl
          intro i _hi
          rw [Finset.mul_sum]
    _ = ∑ v : Fin (L + 1), ∑ i : Fin L,
          u i *
            (startIncidenceColumn i v *
              parityVec (startCompleteVertexLabel x L v) p) :=
      Finset.sum_comm
    _ = ∑ v : Fin (L + 1),
          (∑ i : Fin L, u i * startIncidenceColumn i v) *
            parityVec (startCompleteVertexLabel x L v) p := by
          apply Finset.sum_congr rfl
          intro v _hv
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _hi
          ring
    _ = ∑ v : Fin (L + 1),
          startCompleteBoundary L u v *
            parityVec (startCompleteVertexLabel x L v) p := by
          simp only [startCompleteBoundary_apply]

/-! ## Complete boundary of two starts -/

/--
Direct sum of the complete boundary maps of the left and right start blocks.
-/
def twoStartCompleteBoundary (L : ℕ) :
    (Sum (Fin L) (Fin L) → F₂) →ₗ[F₂]
      (Sum (Fin (L + 1)) (Fin (L + 1)) → F₂) where
  toFun u s :=
    match s with
    | Sum.inl v =>
        startCompleteBoundary L (fun i => u (Sum.inl i)) v
    | Sum.inr v =>
        startCompleteBoundary L (fun i => u (Sum.inr i)) v
  map_add' u v := by
    funext s
    cases s with
    | inl s =>
        change
          startCompleteBoundary L
              ((fun i => u (Sum.inl i)) +
                (fun i => v (Sum.inl i))) s =
            startCompleteBoundary L (fun i => u (Sum.inl i)) s +
              startCompleteBoundary L (fun i => v (Sum.inl i)) s
        rw [LinearMap.map_add]
        rfl
    | inr s =>
        change
          startCompleteBoundary L
              ((fun i => u (Sum.inr i)) +
                (fun i => v (Sum.inr i))) s =
            startCompleteBoundary L (fun i => u (Sum.inr i)) s +
              startCompleteBoundary L (fun i => v (Sum.inr i)) s
        rw [LinearMap.map_add]
        rfl
  map_smul' c u := by
    funext s
    cases s with
    | inl s =>
        change
          startCompleteBoundary L
              (c • (fun i => u (Sum.inl i))) s =
            c • startCompleteBoundary L (fun i => u (Sum.inl i)) s
        rw [LinearMap.map_smul]
        rfl
    | inr s =>
        change
          startCompleteBoundary L
              (c • (fun i => u (Sum.inr i))) s =
            c • startCompleteBoundary L (fun i => u (Sum.inr i)) s
        rw [LinearMap.map_smul]
        rfl

@[simp]
theorem twoStartCompleteBoundary_apply_inl
    {L : ℕ} (u : Sum (Fin L) (Fin L) → F₂)
    (v : Fin (L + 1)) :
    twoStartCompleteBoundary L u (Sum.inl v) =
      startCompleteBoundary L (fun i => u (Sum.inl i)) v :=
  rfl

@[simp]
theorem twoStartCompleteBoundary_apply_inr
    {L : ℕ} (u : Sum (Fin L) (Fin L) → F₂)
    (v : Fin (L + 1)) :
    twoStartCompleteBoundary L u (Sum.inr v) =
      startCompleteBoundary L (fun i => u (Sum.inr i)) v :=
  rfl

/-- The two-block complete boundary is injective. -/
theorem twoStartCompleteBoundary_injective
    (L : ℕ) :
    Function.Injective (twoStartCompleteBoundary L) := by
  intro u v huv
  funext s
  cases s with
  | inl i =>
      have hleft :
          startCompleteBoundary L (fun j => u (Sum.inl j)) =
            startCompleteBoundary L (fun j => v (Sum.inl j)) := by
        funext w
        exact congrFun huv (Sum.inl w)
      exact congrFun (startCompleteBoundary_injective L hleft) i
  | inr i =>
      have hright :
          startCompleteBoundary L (fun j => u (Sum.inr j)) =
            startCompleteBoundary L (fun j => v (Sum.inr j)) := by
        funext w
        exact congrFun huv (Sum.inr w)
      exact congrFun (startCompleteBoundary_injective L hright) i

/-- Parity row of either block of a two-start system. -/
def twoStartEdgeParity (x y p : ℕ) {L : ℕ} :
    Sum (Fin L) (Fin L) → F₂
  | Sum.inl i => startEdgeParity x p i
  | Sum.inr i => startEdgeParity y p i

/-- Integer label of an occurrence in the two complete start boundaries. -/
def twoStartCompleteVertexLabel (x y L : ℕ) :
    Sum (Fin (L + 1)) (Fin (L + 1)) → ℕ
  | Sum.inl v => startCompleteVertexLabel x L v
  | Sum.inr v => startCompleteVertexLabel y L v

/-- Joint line--boundary identity for two arbitrary starts. -/
theorem sum_twoStartEdgeParity_eq_sum_completeBoundary
    (x y p : ℕ) {L : ℕ}
    (u : Sum (Fin L) (Fin L) → F₂) :
    (∑ s : Sum (Fin L) (Fin L),
        u s * twoStartEdgeParity x y p s) =
      ∑ v : Sum (Fin (L + 1)) (Fin (L + 1)),
        twoStartCompleteBoundary L u v *
          parityVec (twoStartCompleteVertexLabel x y L v) p := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  change
    (∑ i : Fin L, u (Sum.inl i) * startEdgeParity x p i) +
        (∑ i : Fin L, u (Sum.inr i) * startEdgeParity y p i) =
      (∑ v : Fin (L + 1),
          startCompleteBoundary L (fun i => u (Sum.inl i)) v *
            parityVec (startCompleteVertexLabel x L v) p) +
        ∑ v : Fin (L + 1),
          startCompleteBoundary L (fun i => u (Sum.inr i)) v *
            parityVec (startCompleteVertexLabel y L v) p
  rw [sum_startEdgeParity_eq_sum_completeBoundary,
    sum_startEdgeParity_eq_sum_completeBoundary]

/-! ## Nonzero and canonical selected occurrences -/

/-- A nonzero coefficient vector has a nonzero complete-boundary occurrence. -/
theorem exists_twoStartCompleteBoundary_ne_zero
    {L : ℕ} {u : Sum (Fin L) (Fin L) → F₂}
    (hu : u ≠ 0) :
    ∃ v : Sum (Fin (L + 1)) (Fin (L + 1)),
      twoStartCompleteBoundary L u v ≠ 0 := by
  have hb :
      twoStartCompleteBoundary L u ≠ 0 := by
    intro hzero
    apply hu
    apply twoStartCompleteBoundary_injective L
    simpa using hzero
  by_contra h
  push Not at h
  apply hb
  funext v
  exact h v

/--
Relation-specific occurrence theorem: every nonzero relation of the two-start
system selects at least one complete-boundary vertex.
-/
theorem relation_exists_selectedOccurrence
    {M x y L : ℕ}
    (u : RelationSpace (twoStartSystem M x y L))
    (hu : u ≠ 0) :
    ∃ v : Sum (Fin (L + 1)) (Fin (L + 1)),
      twoStartCompleteBoundary L
        (u : Sum (Fin L) (Fin L) → F₂) v ≠ 0 := by
  apply exists_twoStartCompleteBoundary_ne_zero
  intro hcoe
  apply hu
  apply Subtype.ext
  exact hcoe

/--
Support of the two-start boundary, encoded in `Fin ((L+1)+(L+1))`.
Via `finSumFinEquiv`, this orders every left-block occurrence before every
right-block occurrence and uses increasing vertex offsets within each block.
-/
noncomputable def twoStartBoundarySupport
    (L : ℕ) (u : Sum (Fin L) (Fin L) → F₂) :
    Finset (Fin ((L + 1) + (L + 1))) := by
  classical
  exact Finset.univ.filter
    (fun k =>
      twoStartCompleteBoundary L u
        (finSumFinEquiv.symm k) ≠ 0)

@[simp]
theorem mem_twoStartBoundarySupport
    {L : ℕ} {u : Sum (Fin L) (Fin L) → F₂}
    {k : Fin ((L + 1) + (L + 1))} :
    k ∈ twoStartBoundarySupport L u ↔
      twoStartCompleteBoundary L u
        (finSumFinEquiv.symm k) ≠ 0 := by
  simp [twoStartBoundarySupport]

/-- The ordered boundary support of a nonzero relation is nonempty. -/
theorem relation_twoStartBoundarySupport_nonempty
    {M x y L : ℕ}
    (u : RelationSpace (twoStartSystem M x y L))
    (hu : u ≠ 0) :
    (twoStartBoundarySupport L
      (u : Sum (Fin L) (Fin L) → F₂)).Nonempty := by
  obtain ⟨v, hv⟩ := relation_exists_selectedOccurrence u hu
  let k : Fin ((L + 1) + (L + 1)) := finSumFinEquiv v
  refine ⟨k, ?_⟩
  rw [mem_twoStartBoundarySupport]
  simpa [k] using hv

/-- Canonical first selected index, in left-block-then-right-block order. -/
noncomputable def canonicalTwoStartBoundaryIndex
    {L : ℕ} (u : Sum (Fin L) (Fin L) → F₂)
    (h : (twoStartBoundarySupport L u).Nonempty) :
    Fin ((L + 1) + (L + 1)) :=
  (twoStartBoundarySupport L u).min' h

/-- Canonical first selected occurrence in the original sum-index type. -/
noncomputable def canonicalTwoStartBoundaryOccurrence
    {L : ℕ} (u : Sum (Fin L) (Fin L) → F₂)
    (h : (twoStartBoundarySupport L u).Nonempty) :
    Sum (Fin (L + 1)) (Fin (L + 1)) :=
  finSumFinEquiv.symm (canonicalTwoStartBoundaryIndex u h)

theorem canonicalTwoStartBoundaryIndex_mem
    {L : ℕ} (u : Sum (Fin L) (Fin L) → F₂)
    (h : (twoStartBoundarySupport L u).Nonempty) :
    canonicalTwoStartBoundaryIndex u h ∈
      twoStartBoundarySupport L u :=
  Finset.min'_mem _ _

/-- The canonical occurrence is genuinely selected. -/
theorem canonicalTwoStartBoundaryOccurrence_ne_zero
    {L : ℕ} (u : Sum (Fin L) (Fin L) → F₂)
    (h : (twoStartBoundarySupport L u).Nonempty) :
    twoStartCompleteBoundary L u
      (canonicalTwoStartBoundaryOccurrence u h) ≠ 0 := by
  change
    twoStartCompleteBoundary L u
      (finSumFinEquiv.symm
        (canonicalTwoStartBoundaryIndex u h)) ≠ 0
  exact mem_twoStartBoundarySupport.mp
    (canonicalTwoStartBoundaryIndex_mem u h)

/-- Minimality of the canonical index among all selected occurrences. -/
theorem canonicalTwoStartBoundaryIndex_le
    {L : ℕ} (u : Sum (Fin L) (Fin L) → F₂)
    (h : (twoStartBoundarySupport L u).Nonempty)
    {k : Fin ((L + 1) + (L + 1))}
    (hk : k ∈ twoStartBoundarySupport L u) :
    canonicalTwoStartBoundaryIndex u h ≤ k := by
  exact Finset.min'_le _ _ hk

/-- Canonical selected occurrence attached directly to a nonzero relation. -/
noncomputable def relationCanonicalSelectedOccurrence
    {M x y L : ℕ}
    (u : RelationSpace (twoStartSystem M x y L))
    (hu : u ≠ 0) :
    Sum (Fin (L + 1)) (Fin (L + 1)) :=
  canonicalTwoStartBoundaryOccurrence
    (u : Sum (Fin L) (Fin L) → F₂)
    (relation_twoStartBoundarySupport_nonempty u hu)

/-- The canonical occurrence of a nonzero relation has nonzero boundary bit. -/
theorem relationCanonicalSelectedOccurrence_ne_zero
    {M x y L : ℕ}
    (u : RelationSpace (twoStartSystem M x y L))
    (hu : u ≠ 0) :
    twoStartCompleteBoundary L
        (u : Sum (Fin L) (Fin L) → F₂)
        (relationCanonicalSelectedOccurrence u hu) ≠
      0 := by
  exact canonicalTwoStartBoundaryOccurrence_ne_zero
    (u : Sum (Fin L) (Fin L) → F₂)
    (relation_twoStartBoundarySupport_nonempty u hu)

/--
The canonical relation occurrence is first in left-block-then-right-block,
increasing-offset order.
-/
theorem relationCanonicalSelectedOccurrence_minimal
    {M x y L : ℕ}
    (u : RelationSpace (twoStartSystem M x y L))
    (hu : u ≠ 0)
    (v : Sum (Fin (L + 1)) (Fin (L + 1)))
    (hv :
      twoStartCompleteBoundary L
        (u : Sum (Fin L) (Fin L) → F₂) v ≠ 0) :
    finSumFinEquiv (relationCanonicalSelectedOccurrence u hu) ≤
      finSumFinEquiv v := by
  have hvMem :
      finSumFinEquiv v ∈
        twoStartBoundarySupport L
          (u : Sum (Fin L) (Fin L) → F₂) := by
    rw [mem_twoStartBoundarySupport]
    simpa using hv
  simpa [relationCanonicalSelectedOccurrence,
    canonicalTwoStartBoundaryOccurrence] using
      (canonicalTwoStartBoundaryIndex_le
        (u : Sum (Fin L) (Fin L) → F₂)
        (relation_twoStartBoundarySupport_nonempty u hu) hvMem)

end

end Affine
end PaperC
