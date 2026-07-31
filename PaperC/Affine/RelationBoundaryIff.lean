import PaperC.Affine.RelationalPrimeAssignment

set_option maxHeartbeats 1200000

/-!
# Exact boundary characterization of two-start relations

The prime-coordinate equations on the complete boundary are not merely
necessary for a row relation: taken over every prime represented by the
finite cylinder, they are sufficient.  This module records that exact
equivalence for arbitrary coefficient vectors.
-/

namespace PaperC
namespace Affine

open scoped BigOperators

noncomputable section

/-- One finite-cylinder start row is the incidence sum of its endpoint values. -/
private theorem startSystem_apply_eq_sum_incidence'
    (M x L : ℕ) (ω : SampleSpace M) (i : Fin L) :
    startSystem M x L ω i =
      ∑ v : Fin (L + 1),
        startIncidenceColumn i v *
          valueBit ω (startCompleteVertexLabel x L v) := by
  rw [startSystem_apply]
  by_cases hi : i.1 = 0
  · simp [startIncidenceColumn, startBaseVertex, startTipVertex,
      startRootVertex, startCompleteVertexLabel, Pi.single_apply, hi,
      add_mul, Finset.sum_add_distrib]
  · simp [startIncidenceColumn, startBaseVertex, startTipVertex,
      startRootVertex, startCompleteVertexLabel, Pi.single_apply, hi,
      add_mul, Finset.sum_add_distrib]

/--
Line-boundary identity for the actual finite-cylinder rows of one start.
-/
private theorem sum_startSystem_eq_sum_completeBoundary'
    (M x L : ℕ) (ω : SampleSpace M) (u : Fin L → F₂) :
    (∑ i : Fin L, u i * startSystem M x L ω i) =
      ∑ v : Fin (L + 1),
        startCompleteBoundary L u v *
          valueBit ω (startCompleteVertexLabel x L v) := by
  simp_rw [startSystem_apply_eq_sum_incidence']
  calc
    (∑ i : Fin L,
        u i *
          ∑ v : Fin (L + 1),
            startIncidenceColumn i v *
              valueBit ω (startCompleteVertexLabel x L v)) =
        ∑ i : Fin L, ∑ v : Fin (L + 1),
          u i *
            (startIncidenceColumn i v *
              valueBit ω (startCompleteVertexLabel x L v)) := by
          apply Finset.sum_congr rfl
          intro i _hi
          rw [Finset.mul_sum]
    _ = ∑ v : Fin (L + 1), ∑ i : Fin L,
          u i *
            (startIncidenceColumn i v *
              valueBit ω (startCompleteVertexLabel x L v)) :=
      Finset.sum_comm
    _ = ∑ v : Fin (L + 1),
          (∑ i : Fin L, u i * startIncidenceColumn i v) *
            valueBit ω (startCompleteVertexLabel x L v) := by
          apply Finset.sum_congr rfl
          intro v _hv
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _hi
          ring
    _ = ∑ v : Fin (L + 1),
          startCompleteBoundary L u v *
            valueBit ω (startCompleteVertexLabel x L v) := by
          simp only [startCompleteBoundary_apply]

/--
The value of the two-start system against an arbitrary row vector can be
computed on the complete vertex boundary.
-/
private theorem dotProduct_twoStartSystem_eq_sum_completeBoundary'
    (M x y L : ℕ) (ω : SampleSpace M)
    (u : Sum (Fin L) (Fin L) → F₂) :
    dotProduct u (twoStartSystem M x y L ω) =
      ∑ v : Sum (Fin (L + 1)) (Fin (L + 1)),
        twoStartCompleteBoundary L u v *
          valueBit ω (twoStartCompleteVertexLabel x y L v) := by
  rw [dotProduct, Fintype.sum_sum_type, Fintype.sum_sum_type]
  change
    (∑ i : Fin L, u (Sum.inl i) * startSystem M x L ω i) +
        (∑ i : Fin L, u (Sum.inr i) * startSystem M y L ω i) =
      (∑ v : Fin (L + 1),
          startCompleteBoundary L (fun i => u (Sum.inl i)) v *
            valueBit ω (startCompleteVertexLabel x L v)) +
        ∑ v : Fin (L + 1),
          startCompleteBoundary L (fun i => u (Sum.inr i)) v *
            valueBit ω (startCompleteVertexLabel y L v)
  rw [sum_startSystem_eq_sum_completeBoundary',
    sum_startSystem_eq_sum_completeBoundary']

/--
After expanding `valueBit`, the pairing with a two-start system is the sum of
its complete-boundary prime equations, weighted by the prime assignment.
-/
private theorem dotProduct_twoStartSystem_eq_sum_primeBoundary
    (M x y L : ℕ) (ω : SampleSpace M)
    (u : Sum (Fin L) (Fin L) → F₂) :
    dotProduct u (twoStartSystem M x y L ω) =
      ∑ p : PrimeUpTo M, ω p *
        (∑ v : Sum (Fin (L + 1)) (Fin (L + 1)),
          twoStartCompleteBoundary L u v *
            parityVec (twoStartCompleteVertexLabel x y L v) p.1) := by
  rw [dotProduct_twoStartSystem_eq_sum_completeBoundary']
  simp only [valueBit]
  calc
    (∑ v : Sum (Fin (L + 1)) (Fin (L + 1)),
        twoStartCompleteBoundary L u v *
          ∑ p : PrimeUpTo M,
            ω p * parityVec (twoStartCompleteVertexLabel x y L v) p.1) =
      ∑ v : Sum (Fin (L + 1)) (Fin (L + 1)),
        ∑ p : PrimeUpTo M,
          twoStartCompleteBoundary L u v *
            (ω p * parityVec
              (twoStartCompleteVertexLabel x y L v) p.1) := by
        apply Finset.sum_congr rfl
        intro v _hv
        rw [Finset.mul_sum]
    _ = ∑ p : PrimeUpTo M,
        ∑ v : Sum (Fin (L + 1)) (Fin (L + 1)),
          twoStartCompleteBoundary L u v *
            (ω p * parityVec
              (twoStartCompleteVertexLabel x y L v) p.1) :=
      Finset.sum_comm
    _ = ∑ p : PrimeUpTo M, ω p *
        (∑ v : Sum (Fin (L + 1)) (Fin (L + 1)),
          twoStartCompleteBoundary L u v *
            parityVec (twoStartCompleteVertexLabel x y L v) p.1) := by
        apply Finset.sum_congr rfl
        intro p _hp
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro v _hv
        ring

/--
Exact converse to `relation_boundary_prime_equation`: an ambient row vector
is a relation precisely when every represented prime coordinate annihilates
its complete boundary.
-/
theorem mem_relationSpace_twoStartSystem_iff_boundary_prime_equations
    {M x y L : ℕ} (u : Sum (Fin L) (Fin L) → F₂) :
    u ∈ RelationSpace (twoStartSystem M x y L) ↔
      ∀ p : PrimeUpTo M,
        ∑ v : Sum (Fin (L + 1)) (Fin (L + 1)),
          twoStartCompleteBoundary L u v *
            parityVec (twoStartCompleteVertexLabel x y L v) p.1 =
          0 := by
  constructor
  · intro hu p
    exact
      RelationalPrimeAssignment.relation_boundary_prime_equation
        (⟨u, hu⟩ : RelationSpace (twoStartSystem M x y L))
        p.2 (Nat.le_of_lt_succ p.1.2)
  · intro h
    rw [LinearMap.mem_ker]
    apply LinearMap.ext
    intro ω
    rw [relationMap_apply, relationFunctional_apply,
      dotProduct_twoStartSystem_eq_sum_primeBoundary]
    simp_rw [h]
    simp

end

end Affine
end PaperC
