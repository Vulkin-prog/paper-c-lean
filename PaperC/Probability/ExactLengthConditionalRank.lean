import PaperC.Probability.MixedLengthAffine
import PaperC.Probability.ConditionalStartProbability
import PaperC.Combinatorics.CycleSpaceDimension

set_option maxHeartbeats 1800000

/-!
# Conditional rank bounds for exact-length events

This file isolates the finite probabilistic core used in Lemma 14.8 and in
the local part of the marked-process argument following it.

After the coordinates at primes at most `Y` have been fixed, the remaining
large-prime coordinates form the finite vector space `LargeSample M Y`.
The exact-length equations are therefore an affine system on that space.
We define the one-start and mixed two-start conditioned systems, prove their
exact `η 2^ρ / 2^m` formulas, and turn any relation-defect bound into a
probability bound.

The graph-theoretic part is stated through a literal row-realization
condition: on every coordinate basis vector, each row is the sum of the
vectors attached to its two displayed endpoints.  The private-pivot theorem
and the proved dimension formula for the binary cycle space then bound the
relation defect.  For a local two-start union with cyclomatic number at most
one this gives

`P(K(x,q) ∩ K(y,r) | small coordinates) ≤ 2 / 2^(q+r)`,

which is the finite meaning of `2^(1-q-r)` in the manuscript.

The construction is entirely finite.  Instantiating the row-realization and
graph-connectivity hypotheses with a particular arithmetic support remains
separate from this probabilistic rank argument; no bridge or placeholder is
introduced here.
-/

namespace PaperC
namespace ExactLengthConditionalRank

open Affine
open MixedLengthAffine
open ConditionalStartProbability
open GraphCycleRank

noncomputable section

/-! ## Generic rank-to-probability implications -/

/--
Any upper bound on the relation defect gives the corresponding upper bound
on the probability of an affine fiber.
-/
theorem uniformSolutionProbability_le_two_pow_relation_bound
    {V β : Type*}
    [AddCommGroup V] [Module F₂ V] [Fintype V] [DecidableEq V]
    [Fintype β] [DecidableEq β]
    (A : V →ₗ[F₂] (β → F₂)) (b : β → F₂) {d : ℕ}
    (hrho : relationRho A ≤ d) :
    uniformSolutionProbability A b ≤
      (2 : ℚ) ^ d / (2 : ℚ) ^ Fintype.card β := by
  rw [SectionTwelveMoments.uniformSolutionProbability_eq_eta_mul_two_pow_rho_div]
  rcases relationEta_eq_zero_or_one A b with heta | heta
  · have hnonneg :
        (0 : ℚ) ≤
          (2 : ℚ) ^ d / (2 : ℚ) ^ Fintype.card β := by
      positivity
    simpa [heta] using hnonneg
  · rw [heta]
    simp only [Nat.cast_one, one_mul]
    exact div_le_div_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num) hrho)
      (by positivity)

/--
A surjective binary affine system has the uniform fiber probability
`2^(-m)`, independently of its translated right-hand side.
-/
theorem uniformSolutionProbability_eq_inv_two_pow_of_surjective
    {V β : Type*}
    [AddCommGroup V] [Module F₂ V] [Fintype V] [DecidableEq V]
    [Fintype β] [DecidableEq β]
    (A : V →ₗ[F₂] (β → F₂)) (b : β → F₂)
    (hsurj : Function.Surjective A) :
    uniformSolutionProbability A b =
      (1 : ℚ) / (2 : ℚ) ^ Fintype.card β := by
  have hcompat : Compatible A b :=
    LinearMap.mem_range.mpr (hsurj b)
  rw [uniformSolutionProbability_of_compatible A b hcompat]
  have hnullity :=
    LinearMap.finrank_range_add_finrank_ker A
  have hrange : LinearMap.range A = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  rw [hrange, finrank_top, Module.finrank_pi] at hnullity
  have hdim :
      Module.finrank F₂ V =
        Module.finrank F₂ (LinearMap.ker A) +
          Fintype.card β := by
    omega
  rw [hdim, pow_add]
  field_simp

/--
Equivalently, vanishing relation defect already forces every right-hand side
to be compatible and gives the independent baseline.
-/
theorem uniformSolutionProbability_eq_inv_two_pow_of_relationRho_eq_zero
    {V β : Type*}
    [AddCommGroup V] [Module F₂ V] [Fintype V] [DecidableEq V]
    [Fintype β] [DecidableEq β]
    (A : V →ₗ[F₂] (β → F₂)) (b : β → F₂)
    (hrho : relationRho A = 0) :
    uniformSolutionProbability A b =
      (1 : ℚ) / (2 : ℚ) ^ Fintype.card β := by
  have hcharacter : relationCharacter A b = 0 := by
    by_contra hne
    have hpos := relationRho_pos_of_character_ne_zero A b hne
    omega
  have heta : relationEta A b = 1 :=
    (relationEta_eq_one_iff A b).mpr hcharacter
  rw [SectionTwelveMoments.uniformSolutionProbability_eq_eta_mul_two_pow_rho_div,
    heta, hrho]
  simp

/-! ## One conditioned exact-length event -/

/-- Linear part of one exact-length system on the unfixed coordinates. -/
def largeExactLengthSystem (M Y x q : ℕ) :
    LargeSample M Y →ₗ[F₂] (Fin q → F₂) :=
  (startSystem M x q).comp (extendLarge M Y)

/-- Translated exact-length right-hand side after fixing small coordinates. -/
def conditionedExactLengthRhs
    (M Y x q : ℕ) (σ : SmallSample M Y) :
    Fin q → F₂ :=
  exactLengthRhs q -
    startSystem M x q (extendSmall M Y σ)

/--
Reassembling the two coordinate blocks solves the exact-length system
exactly when the large block solves the translated system.
-/
theorem assemble_solves_exactLength_iff
    (M Y x q : ℕ) (σ : SmallSample M Y) (η : LargeSample M Y) :
    startSystem M x q (assemble M Y σ η) = exactLengthRhs q ↔
      largeExactLengthSystem M Y x q η =
        conditionedExactLengthRhs M Y x q σ := by
  simp only [assemble, map_add, largeExactLengthSystem,
    LinearMap.comp_apply, conditionedExactLengthRhs]
  constructor <;> intro h
  · rw [← h]
    simp
  · rw [h]
    simp

/-- Event-level form of `assemble_solves_exactLength_iff`. -/
theorem assemble_exactLengthAt_iff
    (M Y x q : ℕ) (hq : 2 ≤ q)
    (σ : SmallSample M Y) (η : LargeSample M Y) :
    exactLengthAt (assemble M Y σ η) x q ↔
      largeExactLengthSystem M Y x q η =
        conditionedExactLengthRhs M Y x q σ := by
  rw [← startSystem_eq_exactLengthRhs_iff
    (assemble M Y σ η) hq]
  exact assemble_solves_exactLength_iff M Y x q σ η

/-- Conditional finite probability of one exact-length event. -/
def conditionedExactLengthProbability
    (M Y x q : ℕ) (σ : SmallSample M Y) : ℚ :=
  uniformSolutionProbability
    (largeExactLengthSystem M Y x q)
    (conditionedExactLengthRhs M Y x q σ)

/-- Exact affine normalization of one conditioned exact-length event. -/
theorem conditionedExactLengthProbability_eq_eta_mul_two_pow_rho_div
    (M Y x q : ℕ) (σ : SmallSample M Y) :
    conditionedExactLengthProbability M Y x q σ =
      ((relationEta
          (largeExactLengthSystem M Y x q)
          (conditionedExactLengthRhs M Y x q σ) : ℚ) *
        (2 : ℚ) ^
          relationRho (largeExactLengthSystem M Y x q)) /
        (2 : ℚ) ^ q := by
  unfold conditionedExactLengthProbability
  rw [SectionTwelveMoments.uniformSolutionProbability_eq_eta_mul_two_pow_rho_div]
  congr 1
  simp

/--
Pointwise rank bound used in the first case of Lemma 14.8.
-/
theorem conditionedExactLengthProbability_le_of_relationRho
    {M Y x q d : ℕ} {σ : SmallSample M Y}
    (hrho : relationRho (largeExactLengthSystem M Y x q) ≤ d) :
    conditionedExactLengthProbability M Y x q σ ≤
      (2 : ℚ) ^ d / (2 : ℚ) ^ q := by
  unfold conditionedExactLengthProbability
  simpa using
    uniformSolutionProbability_le_two_pow_relation_bound
      (largeExactLengthSystem M Y x q)
      (conditionedExactLengthRhs M Y x q σ) hrho

/--
Full row rank gives the exact conditional baseline `2^(-q)`, as used for a
retained exact-length start whose support has private pivots.
-/
theorem conditionedExactLengthProbability_eq_baseline_of_surjective
    {M Y x q : ℕ} {σ : SmallSample M Y}
    (hsurj : Function.Surjective
      (largeExactLengthSystem M Y x q)) :
    conditionedExactLengthProbability M Y x q σ =
      (1 : ℚ) / (2 : ℚ) ^ q := by
  unfold conditionedExactLengthProbability
  simpa using
    uniformSolutionProbability_eq_inv_two_pow_of_surjective
      (largeExactLengthSystem M Y x q)
      (conditionedExactLengthRhs M Y x q σ) hsurj

/-! ## Two conditioned exact-length events -/

/-- Linear part of the mixed system on the unfixed large coordinates. -/
def largeMixedLengthSystem
    (M Y x y q r : ℕ) :
    LargeSample M Y →ₗ[F₂] (Sum (Fin q) (Fin r) → F₂) :=
  (mixedLengthSystem M x y q r).comp (extendLarge M Y)

/-- Translated mixed right-hand side after fixing the small coordinates. -/
def conditionedMixedLengthRhs
    (M Y x y q r : ℕ) (σ : SmallSample M Y) :
    Sum (Fin q) (Fin r) → F₂ :=
  mixedLengthRhs q r -
    mixedLengthSystem M x y q r (extendSmall M Y σ)

/-- Exact splitting identity for the mixed system. -/
theorem assemble_solves_mixedLength_iff
    (M Y x y q r : ℕ)
    (σ : SmallSample M Y) (η : LargeSample M Y) :
    mixedLengthSystem M x y q r (assemble M Y σ η) =
        mixedLengthRhs q r ↔
      largeMixedLengthSystem M Y x y q r η =
        conditionedMixedLengthRhs M Y x y q r σ := by
  simp only [assemble, map_add, largeMixedLengthSystem,
    LinearMap.comp_apply, conditionedMixedLengthRhs]
  constructor <;> intro h
  · rw [← h]
    simp
  · rw [h]
    simp

/-- Event-level form of the conditioned mixed-system identity. -/
theorem assemble_mixedExactLengthAt_iff
    (M Y x y q r : ℕ) (hq : 2 ≤ q) (hr : 2 ≤ r)
    (σ : SmallSample M Y) (η : LargeSample M Y) :
    (exactLengthAt (assemble M Y σ η) x q ∧
        exactLengthAt (assemble M Y σ η) y r) ↔
      largeMixedLengthSystem M Y x y q r η =
        conditionedMixedLengthRhs M Y x y q r σ := by
  rw [← mixedLengthSystem_eq_rhs_iff
    (assemble M Y σ η) hq hr]
  exact assemble_solves_mixedLength_iff M Y x y q r σ η

/-- Conditional finite probability of two mixed exact-length events. -/
def conditionedMixedLengthProbability
    (M Y x y q r : ℕ) (σ : SmallSample M Y) : ℚ :=
  uniformSolutionProbability
    (largeMixedLengthSystem M Y x y q r)
    (conditionedMixedLengthRhs M Y x y q r σ)

/-- Exact conditional affine identity at mixed lengths. -/
theorem conditionedMixedLengthProbability_eq_eta_mul_two_pow_rho_div
    (M Y x y q r : ℕ) (σ : SmallSample M Y) :
    conditionedMixedLengthProbability M Y x y q r σ =
      ((relationEta
          (largeMixedLengthSystem M Y x y q r)
          (conditionedMixedLengthRhs M Y x y q r σ) : ℚ) *
        (2 : ℚ) ^
          relationRho (largeMixedLengthSystem M Y x y q r)) /
        (2 : ℚ) ^ (q + r) := by
  unfold conditionedMixedLengthProbability
  rw [SectionTwelveMoments.uniformSolutionProbability_eq_eta_mul_two_pow_rho_div]
  congr 1
  simp [Fintype.card_sum]

/-- Conditional mixed probability under an arbitrary relation-defect bound. -/
theorem conditionedMixedLengthProbability_le_of_relationRho
    {M Y x y q r d : ℕ} {σ : SmallSample M Y}
    (hrho :
      relationRho (largeMixedLengthSystem M Y x y q r) ≤ d) :
    conditionedMixedLengthProbability M Y x y q r σ ≤
      (2 : ℚ) ^ d / (2 : ℚ) ^ (q + r) := by
  unfold conditionedMixedLengthProbability
  simpa [Fintype.card_sum] using
    uniformSolutionProbability_le_two_pow_relation_bound
      (largeMixedLengthSystem M Y x y q r)
      (conditionedMixedLengthRhs M Y x y q r σ) hrho

/--
The direct rank-one local estimate, before providing its graph-theoretic
proof.
-/
theorem conditionedMixedLengthProbability_le_local_of_relationRho_le_one
    {M Y x y q r : ℕ} {σ : SmallSample M Y}
    (hrho :
      relationRho (largeMixedLengthSystem M Y x y q r) ≤ 1) :
    conditionedMixedLengthProbability M Y x y q r σ ≤
      (2 : ℚ) / (2 : ℚ) ^ (q + r) := by
  simpa using
    conditionedMixedLengthProbability_le_of_relationRho
      (σ := σ) hrho

/-! ## Graph realization and the private-pivot rank bound -/

/--
Every row of `A`, read on a coordinate basis vector, is the vector attached
to the displayed graph edge.  This is the exact finite structural condition
needed to transfer a row relation to a represented-edge relation.
-/
def RowsRepresentedByGraph
    {V E P : Type*}
    [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    [Fintype P] [DecidableEq P]
    (A : (P → F₂) →ₗ[F₂] (E → F₂))
    (vertexVector : V → P → F₂)
    (left right : E → V) : Prop :=
  ∀ e p,
    A (Pi.single p 1) e =
      representedEdgeVector vertexVector left right e p

/--
Under literal row realization, every relation among the affine-system rows
is a relation among the graph's represented edge vectors.
-/
theorem relationSpace_le_ker_representedEdgeMap
    {V E P : Type*}
    [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    [Fintype P] [DecidableEq P]
    (A : (P → F₂) →ₗ[F₂] (E → F₂))
    (vertexVector : V → P → F₂)
    (left right : E → V)
    (hrows : RowsRepresentedByGraph A vertexVector left right) :
    RelationSpace A ≤
      LinearMap.ker
        (representedEdgeMap vertexVector left right) := by
  intro u hu
  rw [LinearMap.mem_ker]
  funext p
  have hrel :
      relationMap A (u : E → F₂) = 0 :=
    LinearMap.mem_ker.mp hu
  have hrelp := DFunLike.congr_fun hrel (Pi.single p 1)
  rw [relationMap_apply, relationFunctional_apply] at hrelp
  have hrowp :
      ∀ e : E,
        A (Pi.single p 1) e =
          representedEdgeVector vertexVector left right e p :=
    fun e => hrows e p
  simp only [dotProduct] at hrelp
  simp_rw [hrowp] at hrelp
  simpa only [representedEdgeMap,
    Fintype.linearCombination_apply, representedEdgeVector,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    LinearMap.zero_apply, Pi.zero_apply] using hrelp

/--
Graph-theoretic relation-defect bound.  It combines the exact row
realization, Lemma 14.7's private-pivot inclusion, and the proved dimension
bound for the binary cycle space.
-/
theorem relationRho_le_cyclomaticNumber_of_privatePivots
    {V E C P : Type*}
    [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    [Fintype C] [DecidableEq C]
    [Fintype P] [DecidableEq P]
    (A : (P → F₂) →ₗ[F₂] (E → F₂))
    (vertexVector : V → P → F₂)
    (left right : E → V)
    (component : V → C) (root : C → V)
    (hrows : RowsRepresentedByGraph A vertexVector left right)
    (hroot : ∀ c : C, component (root c) = c)
    (hedge : ∀ e : E, component (left e) = component (right e))
    (hconnected :
      ∀ v : V,
        CycleSpaceDimension.PresentedReachable
          left right (root (component v)) v)
    (hprivate :
      HasPrivatePivots vertexVector component root) :
    relationRho A ≤
      Fintype.card E - Fintype.card V + Fintype.card C := by
  unfold relationRho
  exact
    (Submodule.finrank_mono
      (relationSpace_le_ker_representedEdgeMap
        A vertexVector left right hrows)).trans
      (CycleSpaceDimension.finrank_ker_representedEdgeMap_le_cyclomaticNumber
        vertexVector left right component root hroot hedge hconnected hprivate)

/--
Truncation-safe form of the preceding bound.  This is the form used by the
probabilistic specializations below: unlike `|E| - |V| + |C|` in `ℕ`, the
expression `|E| - (|V| - |C|)` does not truncate before the component count
is restored.
-/
theorem relationRho_le_card_edges_sub_nonRoot_of_privatePivots
    {V E C P : Type*}
    [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    [Fintype C] [DecidableEq C]
    [Fintype P] [DecidableEq P]
    (A : (P → F₂) →ₗ[F₂] (E → F₂))
    (vertexVector : V → P → F₂)
    (left right : E → V)
    (component : V → C) (root : C → V)
    (hrows : RowsRepresentedByGraph A vertexVector left right)
    (hroot : ∀ c : C, component (root c) = c)
    (hedge : ∀ e : E, component (left e) = component (right e))
    (hconnected :
      ∀ v : V,
        CycleSpaceDimension.PresentedReachable
          left right (root (component v)) v)
    (hprivate :
      HasPrivatePivots vertexVector component root) :
    relationRho A ≤
      Fintype.card E - (Fintype.card V - Fintype.card C) := by
  unfold relationRho
  exact
    (Submodule.finrank_mono
      (relationSpace_le_ker_representedEdgeMap
        A vertexVector left right hrows)).trans
      (CycleSpaceDimension.finrank_ker_representedEdgeMap_le_card_edges_sub_nonRoot
        vertexVector left right component root
        hroot hedge hconnected hprivate)

/--
Abstract conditional local bound for two exact-length events.

The structural hypotheses say precisely that the conditioned rows are the
edge vectors of a finite graph, that all but one chosen root per component
have private coordinates, and that the graph has cyclomatic number at most
one.  These are the finite facts verified in the local geometry discussion
after Lemma 14.8.
-/
theorem conditionedMixedLengthProbability_le_local_of_privatePivots
    {M Y x y q r : ℕ} {σ : SmallSample M Y}
    {V C : Type*}
    [Fintype V] [DecidableEq V]
    [Fintype C] [DecidableEq C]
    (vertexVector :
      V → LargePrimeCoordinate M Y → F₂)
    (left right : Sum (Fin q) (Fin r) → V)
    (component : V → C) (root : C → V)
    (hrows :
      RowsRepresentedByGraph
        (largeMixedLengthSystem M Y x y q r)
        vertexVector left right)
    (hroot : ∀ c : C, component (root c) = c)
    (hedge :
      ∀ e : Sum (Fin q) (Fin r),
        component (left e) = component (right e))
    (hconnected :
      ∀ v : V,
        CycleSpaceDimension.PresentedReachable
          left right (root (component v)) v)
    (hprivate :
      HasPrivatePivots vertexVector component root)
    (hcycle :
      Fintype.card (Sum (Fin q) (Fin r)) -
          (Fintype.card V - Fintype.card C) ≤ 1) :
    conditionedMixedLengthProbability M Y x y q r σ ≤
      (2 : ℚ) / (2 : ℚ) ^ (q + r) := by
  apply conditionedMixedLengthProbability_le_local_of_relationRho_le_one
  exact
    (relationRho_le_card_edges_sub_nonRoot_of_privatePivots
      (largeMixedLengthSystem M Y x y q r)
      vertexVector left right component root
      hrows hroot hedge hconnected hprivate).trans hcycle

/--
Tree/forest specialization for a single exact-length event.

If its conditioned rows are the represented edges of a graph satisfying the
private-pivot hypotheses and having cyclomatic number zero, then the row
relation space is trivial and the conditional probability is exactly
`2^(-q)`.  This is the finite rank argument in the second case of Lemma 14.8.
-/
theorem conditionedExactLengthProbability_eq_baseline_of_privatePivots
    {M Y x q : ℕ} {σ : SmallSample M Y}
    {V C : Type*}
    [Fintype V] [DecidableEq V]
    [Fintype C] [DecidableEq C]
    (vertexVector :
      V → LargePrimeCoordinate M Y → F₂)
    (left right : Fin q → V)
    (component : V → C) (root : C → V)
    (hrows :
      RowsRepresentedByGraph
        (largeExactLengthSystem M Y x q)
        vertexVector left right)
    (hroot : ∀ c : C, component (root c) = c)
    (hedge :
      ∀ e : Fin q,
        component (left e) = component (right e))
    (hconnected :
      ∀ v : V,
        CycleSpaceDimension.PresentedReachable
          left right (root (component v)) v)
    (hprivate :
      HasPrivatePivots vertexVector component root)
    (hforest :
      Fintype.card (Fin q) -
          (Fintype.card V - Fintype.card C) = 0) :
    conditionedExactLengthProbability M Y x q σ =
      (1 : ℚ) / (2 : ℚ) ^ q := by
  have hrhoLe :
      relationRho (largeExactLengthSystem M Y x q) ≤ 0 := by
    have hbound :=
      relationRho_le_card_edges_sub_nonRoot_of_privatePivots
        (largeExactLengthSystem M Y x q)
        vertexVector left right component root
        hrows hroot hedge hconnected hprivate
    simp only [Fintype.card_fin] at hbound hforest
    omega
  have hrho :
      relationRho (largeExactLengthSystem M Y x q) = 0 :=
    Nat.eq_zero_of_le_zero hrhoLe
  unfold conditionedExactLengthProbability
  simpa using
    uniformSolutionProbability_eq_inv_two_pow_of_relationRho_eq_zero
      (largeExactLengthSystem M Y x q)
      (conditionedExactLengthRhs M Y x q σ) hrho

end

end ExactLengthConditionalRank
end PaperC
