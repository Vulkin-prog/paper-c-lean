import PaperC.Affine.TwoStartSystem
import PaperC.Arithmetic.LargeOddKernel
import PaperC.LinearAlgebra.PrivatePivots

set_option maxHeartbeats 1200000

/-!
# Prime assignments forced by a two-start relation

This module isolates the local combinatorial mechanism in Lemma 4.2 of
Paper C.  If a nonzero relation selects one occurrence in one start block,
then every sufficiently large odd prime occurring at that integer forces a
unique selected occurrence in the opposite block.

The statement is deliberately finite and exact.  It is the input used later
to encode a relational host by a start, a selected offset, and at most one
opposite offset for each prime of the large odd kernel.
-/

namespace PaperC
namespace Affine
namespace RelationalPrimeAssignment

open scoped BigOperators

noncomputable section

private theorem valueBit_single
    {M n p : ℕ} (hp : p.Prime) (hpM : p ≤ M) :
    valueBit
        (M := M)
        (Pi.single
          (⟨⟨p, Nat.lt_succ_of_le hpM⟩, hp⟩ : PrimeUpTo M) 1)
        n =
      parityVec n p := by
  classical
  let q : PrimeUpTo M :=
    ⟨⟨p, Nat.lt_succ_of_le hpM⟩, hp⟩
  rw [valueBit]
  rw [Fintype.sum_eq_single q]
  · simp [q]
  · intro r hrq
    have hrq' :
        r ≠ (⟨⟨p, Nat.lt_succ_of_le hpM⟩, hp⟩ : PrimeUpTo M) := by
      simpa only [q] using hrq
    simp [Pi.single_apply, hrq']

/--
Every relation between the two start systems gives the corresponding parity
equation at each represented prime coordinate.
-/
theorem relation_prime_equation
    {M x y L p : ℕ}
    (u : RelationSpace (twoStartSystem M x y L))
    (hp : p.Prime) (hpM : p ≤ M) :
    ∑ s : Sum (Fin L) (Fin L),
        (u : Sum (Fin L) (Fin L) → F₂) s *
          twoStartEdgeParity x y p s =
      0 := by
  classical
  let q : PrimeUpTo M :=
    ⟨⟨p, Nat.lt_succ_of_le hpM⟩, hp⟩
  let ω : SampleSpace M := Pi.single q 1
  have hrel :
      relationFunctional (twoStartSystem M x y L)
          (u : Sum (Fin L) (Fin L) → F₂) ω =
        0 := by
    have hu :
        relationMap (twoStartSystem M x y L)
            (u : Sum (Fin L) (Fin L) → F₂) =
          0 :=
      LinearMap.mem_ker.mp u.2
    have huω := DFunLike.congr_fun hu ω
    change
      relationFunctional (twoStartSystem M x y L)
          (u : Sum (Fin L) (Fin L) → F₂) ω =
        0 at huω
    exact huω
  rw [relationFunctional_apply] at hrel
  dsimp only [ω, q] at hrel
  simp only [dotProduct, Fintype.sum_sum_type,
    twoStartSystem_apply_inl, twoStartSystem_apply_inr,
    startSystem_apply, twoStartEdgeParity] at hrel ⊢
  simp_rw [valueBit_single hp hpM] at hrel
  exact hrel

/-- Boundary form of `relation_prime_equation`. -/
theorem relation_boundary_prime_equation
    {M x y L p : ℕ}
    (u : RelationSpace (twoStartSystem M x y L))
    (hp : p.Prime) (hpM : p ≤ M) :
    ∑ v : Sum (Fin (L + 1)) (Fin (L + 1)),
        twoStartCompleteBoundary L
            (u : Sum (Fin L) (Fin L) → F₂) v *
          parityVec (twoStartCompleteVertexLabel x y L v) p =
      0 := by
  rw [← sum_twoStartEdgeParity_eq_sum_completeBoundary]
  exact relation_prime_equation u hp hpM

/-- Complete labels in one start block are pairwise distinct away from zero. -/
theorem startCompleteVertexLabel_injective
    {x L : ℕ} (hx : 1 ≤ x) :
    Function.Injective (startCompleteVertexLabel x L) := by
  intro v w hvw
  apply Fin.ext
  by_cases hv0 : v.1 = 0
  · have hw0 : w.1 = 0 := by
      by_contra hw0
      simp [startCompleteVertexLabel, hv0, hw0] at hvw
      omega
    omega
  · have hw0 : w.1 ≠ 0 := by
      intro hw0
      simp [startCompleteVertexLabel, hv0, hw0] at hvw
      omega
    simp [startCompleteVertexLabel, hv0, hw0] at hvw
    omega

/--
Any two complete labels in one start block are at distance strictly less
than `L + 1`.
-/
theorem startCompleteVertexLabel_dist_lt
    {x L : ℕ} (hx : 1 ≤ x)
    (v w : Fin (L + 1)) :
    Nat.dist (startCompleteVertexLabel x L v)
        (startCompleteVertexLabel x L w) <
      L + 1 := by
  simp only [startCompleteVertexLabel]
  by_cases hv0 : v.1 = 0
  · rw [if_pos hv0]
    by_cases hw0 : w.1 = 0
    · rw [if_pos hw0, Nat.dist_self]
      omega
    · rw [if_neg hw0]
      simp only [Nat.dist]
      have hvlt := v.2
      have hwlt := w.2
      omega
  · rw [if_neg hv0]
    by_cases hw0 : w.1 = 0
    · rw [if_pos hw0]
      simp only [Nat.dist]
      have hvlt := v.2
      have hwlt := w.2
      omega
    · rw [if_neg hw0]
      rw [Nat.dist_add_add_left]
      simp only [Nat.dist]
      have hvlt := v.2
      have hwlt := w.2
      omega

/-- A nonzero parity coordinate forces divisibility by its prime index. -/
theorem dvd_of_parityVec_ne_zero
    {n p : ℕ} (h : parityVec n p ≠ 0) :
    p ∣ n := by
  by_contra hpdvd
  apply h
  rw [parityVec_apply, Nat.factorization_eq_zero_of_not_dvd hpdvd]
  rfl

/--
A prime above `L+1` can have a nonzero parity coordinate at at most one
complete vertex of a start block.
-/
theorem parityVec_ne_zero_unique_in_start
    {x L p : ℕ} (hx : 1 ≤ x) (hpL : L + 1 < p)
    {v w : Fin (L + 1)}
    (hv : parityVec (startCompleteVertexLabel x L v) p ≠ 0)
    (hw : parityVec (startCompleteVertexLabel x L w) p ≠ 0) :
    v = w := by
  by_contra hvw
  have hlabelNe :
      startCompleteVertexLabel x L v ≠
        startCompleteVertexLabel x L w :=
    fun h ↦ hvw (startCompleteVertexLabel_injective hx h)
  have hvDvd :
      p ∣ startCompleteVertexLabel x L v :=
    dvd_of_parityVec_ne_zero hv
  have hwNotDvd :
      ¬p ∣ startCompleteVertexLabel x L w :=
    PrivatePivots.not_dvd_of_dvd_and_dist_lt
      hvDvd hlabelNe hpL
      (startCompleteVertexLabel_dist_lt hx v w)
  exact hwNotDvd (dvd_of_parityVec_ne_zero hw)

private theorem sum_eq_selected
    {x L p : ℕ} (hx : 1 ≤ x) (hpL : L + 1 < p)
    (c : Fin (L + 1) → F₂) (v : Fin (L + 1))
    (hv : parityVec (startCompleteVertexLabel x L v) p ≠ 0) :
    (∑ w : Fin (L + 1),
        c w * parityVec (startCompleteVertexLabel x L w) p) =
      c v * parityVec (startCompleteVertexLabel x L v) p := by
  classical
  apply Finset.sum_eq_single v
  · intro w _hw hwv
    have hzero :
        parityVec (startCompleteVertexLabel x L w) p = 0 := by
      by_contra hw
      exact hwv (parityVec_ne_zero_unique_in_start hx hpL hw hv)
    simp [hzero]
  · simp

/--
If a relation-selected occurrence in the left block has a nonzero coordinate
at a prime above `L+1`, there is a unique selected occurrence with nonzero
coordinate at that prime in the right block.
-/
theorem existsUnique_opposite_of_left
    {M x y L p : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hp : p.Prime) (hpM : p ≤ M) (hpL : L + 1 < p)
    (u : RelationSpace (twoStartSystem M x y L))
    (v : Fin (L + 1))
    (hvSelected :
      twoStartCompleteBoundary L
          (u : Sum (Fin L) (Fin L) → F₂) (Sum.inl v) ≠
        0)
    (hvParity :
      parityVec (startCompleteVertexLabel x L v) p ≠ 0) :
    ∃! w : Fin (L + 1),
      twoStartCompleteBoundary L
          (u : Sum (Fin L) (Fin L) → F₂) (Sum.inr w) ≠
        0 ∧
      parityVec (startCompleteVertexLabel y L w) p ≠ 0 := by
  classical
  let cLeft : Fin (L + 1) → F₂ :=
    fun w ↦ twoStartCompleteBoundary L
      (u : Sum (Fin L) (Fin L) → F₂) (Sum.inl w)
  let cRight : Fin (L + 1) → F₂ :=
    fun w ↦ twoStartCompleteBoundary L
      (u : Sum (Fin L) (Fin L) → F₂) (Sum.inr w)
  have heq := relation_boundary_prime_equation u hp hpM
  rw [Fintype.sum_sum_type] at heq
  change
    (∑ w : Fin (L + 1),
        cLeft w * parityVec (startCompleteVertexLabel x L w) p) +
      (∑ w : Fin (L + 1),
        cRight w * parityVec (startCompleteVertexLabel y L w) p) =
      0 at heq
  have hleftEq :
      (∑ w : Fin (L + 1),
          cLeft w * parityVec (startCompleteVertexLabel x L w) p) =
        cLeft v * parityVec (startCompleteVertexLabel x L v) p :=
    sum_eq_selected hx hpL cLeft v hvParity
  have hleftNe :
      (∑ w : Fin (L + 1),
          cLeft w * parityVec (startCompleteVertexLabel x L w) p) ≠
        0 := by
    rw [hleftEq]
    exact mul_ne_zero hvSelected hvParity
  have hrightNe :
      (∑ w : Fin (L + 1),
          cRight w * parityVec (startCompleteVertexLabel y L w) p) ≠
        0 := by
    intro hzero
    rw [hzero, add_zero] at heq
    exact hleftNe heq
  obtain ⟨w, _hw, hwTerm⟩ :=
    Finset.exists_ne_zero_of_sum_ne_zero hrightNe
  refine ⟨w, ⟨?_, ?_⟩, ?_⟩
  · exact left_ne_zero_of_mul hwTerm
  · exact right_ne_zero_of_mul hwTerm
  · intro w' hw'
    exact parityVec_ne_zero_unique_in_start hy hpL hw'.2
      (right_ne_zero_of_mul hwTerm)

/-- Symmetric right-to-left version. -/
theorem existsUnique_opposite_of_right
    {M x y L p : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hp : p.Prime) (hpM : p ≤ M) (hpL : L + 1 < p)
    (u : RelationSpace (twoStartSystem M x y L))
    (v : Fin (L + 1))
    (hvSelected :
      twoStartCompleteBoundary L
          (u : Sum (Fin L) (Fin L) → F₂) (Sum.inr v) ≠
        0)
    (hvParity :
      parityVec (startCompleteVertexLabel y L v) p ≠ 0) :
    ∃! w : Fin (L + 1),
      twoStartCompleteBoundary L
          (u : Sum (Fin L) (Fin L) → F₂) (Sum.inl w) ≠
        0 ∧
      parityVec (startCompleteVertexLabel x L w) p ≠ 0 := by
  classical
  let cLeft : Fin (L + 1) → F₂ :=
    fun w ↦ twoStartCompleteBoundary L
      (u : Sum (Fin L) (Fin L) → F₂) (Sum.inl w)
  let cRight : Fin (L + 1) → F₂ :=
    fun w ↦ twoStartCompleteBoundary L
      (u : Sum (Fin L) (Fin L) → F₂) (Sum.inr w)
  have heq := relation_boundary_prime_equation u hp hpM
  rw [Fintype.sum_sum_type] at heq
  change
    (∑ w : Fin (L + 1),
        cLeft w * parityVec (startCompleteVertexLabel x L w) p) +
      (∑ w : Fin (L + 1),
        cRight w * parityVec (startCompleteVertexLabel y L w) p) =
      0 at heq
  have hrightEq :
      (∑ w : Fin (L + 1),
          cRight w * parityVec (startCompleteVertexLabel y L w) p) =
        cRight v * parityVec (startCompleteVertexLabel y L v) p :=
    sum_eq_selected hy hpL cRight v hvParity
  have hrightNe :
      (∑ w : Fin (L + 1),
          cRight w * parityVec (startCompleteVertexLabel y L w) p) ≠
        0 := by
    rw [hrightEq]
    exact mul_ne_zero hvSelected hvParity
  have hleftNe :
      (∑ w : Fin (L + 1),
          cLeft w * parityVec (startCompleteVertexLabel x L w) p) ≠
        0 := by
    intro hzero
    rw [hzero, zero_add] at heq
    exact hrightNe heq
  obtain ⟨w, _hw, hwTerm⟩ :=
    Finset.exists_ne_zero_of_sum_ne_zero hleftNe
  refine ⟨w, ⟨?_, ?_⟩, ?_⟩
  · exact left_ne_zero_of_mul hwTerm
  · exact right_ne_zero_of_mul hwTerm
  · intro w' hw'
    exact parityVec_ne_zero_unique_in_start hx hpL hw'.2
      (right_ne_zero_of_mul hwTerm)

/--
Large-kernel specialization of the left-to-right assignment theorem.

For every prime in the large odd support of the selected left label, the
opposite selected occurrence exists uniquely.  The hypothesis `hnM` merely
says that the finite sample space contains every prime dividing that label.
-/
theorem existsUnique_opposite_for_largeKernel_of_left
    {M x y L : ℕ}
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (u : RelationSpace (twoStartSystem M x y L))
    (v : Fin (L + 1))
    (hvSelected :
      twoStartCompleteBoundary L
          (u : Sum (Fin L) (Fin L) → F₂) (Sum.inl v) ≠
        0)
    (hnM : startCompleteVertexLabel x L v ≤ M)
    {p : ℕ}
    (hpSupport :
      p ∈ LargeOddKernel.largeOddPrimeSupport (L + 1)
        (startCompleteVertexLabel x L v)) :
    ∃! w : Fin (L + 1),
      twoStartCompleteBoundary L
          (u : Sum (Fin L) (Fin L) → F₂) (Sum.inr w) ≠
        0 ∧
      parityVec (startCompleteVertexLabel y L w) p ≠ 0 := by
  have hpData :=
    LargeOddKernel.prime_and_large_of_mem_largeOddPrimeSupport hpSupport
  have hpParity :
      parityVec (startCompleteVertexLabel x L v) p ≠ 0 :=
    (LargeOddKernel.mem_largeOddPrimeSupport_iff.mp hpSupport).2
  have hnPos : 0 < startCompleteVertexLabel x L v := by
    simp only [startCompleteVertexLabel]
    split_ifs <;> omega
  have hpLeN :
      p ≤ startCompleteVertexLabel x L v :=
    Nat.le_of_dvd hnPos (dvd_of_parityVec_ne_zero hpParity)
  exact existsUnique_opposite_of_left (one_le_two.trans hx) (one_le_two.trans hy)
    hpData.1 (hpLeN.trans hnM) hpData.2 u v hvSelected hpParity

/-- Symmetric large-kernel specialization. -/
theorem existsUnique_opposite_for_largeKernel_of_right
    {M x y L : ℕ}
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (u : RelationSpace (twoStartSystem M x y L))
    (v : Fin (L + 1))
    (hvSelected :
      twoStartCompleteBoundary L
          (u : Sum (Fin L) (Fin L) → F₂) (Sum.inr v) ≠
        0)
    (hnM : startCompleteVertexLabel y L v ≤ M)
    {p : ℕ}
    (hpSupport :
      p ∈ LargeOddKernel.largeOddPrimeSupport (L + 1)
        (startCompleteVertexLabel y L v)) :
    ∃! w : Fin (L + 1),
      twoStartCompleteBoundary L
          (u : Sum (Fin L) (Fin L) → F₂) (Sum.inl w) ≠
        0 ∧
      parityVec (startCompleteVertexLabel x L w) p ≠ 0 := by
  have hpData :=
    LargeOddKernel.prime_and_large_of_mem_largeOddPrimeSupport hpSupport
  have hpParity :
      parityVec (startCompleteVertexLabel y L v) p ≠ 0 :=
    (LargeOddKernel.mem_largeOddPrimeSupport_iff.mp hpSupport).2
  have hnPos : 0 < startCompleteVertexLabel y L v := by
    simp only [startCompleteVertexLabel]
    split_ifs <;> omega
  have hpLeN :
      p ≤ startCompleteVertexLabel y L v :=
    Nat.le_of_dvd hnPos (dvd_of_parityVec_ne_zero hpParity)
  exact existsUnique_opposite_of_right (one_le_two.trans hx) (one_le_two.trans hy)
    hpData.1 (hpLeN.trans hnM) hpData.2 u v hvSelected hpParity

end

end RelationalPrimeAssignment
end Affine
end PaperC
