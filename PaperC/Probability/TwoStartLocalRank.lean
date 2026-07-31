import PaperC.Probability.ExactLengthConditionalRank
import PaperC.Probability.LargePrimeDependencyGraph
import PaperC.Analysis.TerminalPrimeCutoff

set_option maxHeartbeats 1800000

/-!
# The concrete two-star rank estimate

This file instantiates the graph/private-pivot interface of Lemma 14.6 for
two equal-length start systems whose bases are at distance `d ≤ Q`.

For oriented starts `x < x+d`, the union of the two displayed stars has

* `2Q` edges,
* `d+Q+1` vertices, and
* one connected component.

Thus its cyclomatic number is `Q-d`.  If both starts survive the terminal
bad-start deletion and the large-prime cutoff exceeds the diameter of this
union, every non-root vertex has a private prime coordinate.  Consequently
the common two-start relation defect is at most `Q-d`.

The construction below is literal: vertices are `Fin (d+Q+1)`, labelled by
`x-1+v`, and the two summands of `Sum (Fin Q) (Fin Q)` are the two star edge
sets.  No graph-realization hypothesis is left as a premise.
-/

namespace PaperC
namespace TwoStartLocalRank

open Affine
open BadStartCount
open ConditionalStartProbability
open CycleSpaceDimension
open ExactLengthConditionalRank
open GraphCycleRank
open LargeOddKernel
open LargePrimeDependencyGraph
open SectionTwelveMoments
open TerminalPrimeCutoff

noncomputable section

/-! ## The explicit union of two stars -/

/-- Vertex labels for the oriented union, starting with the left root. -/
def localVertexLabel (x : ℕ) {Q d : ℕ}
    (v : Fin (d + Q + 1)) : ℕ :=
  x - 1 + v.1

/-- Left endpoint of each displayed star edge. -/
def localTwoStarLeft
    (Q d : ℕ) (hQ : 0 < Q) :
    Sum (Fin Q) (Fin Q) → Fin (d + Q + 1)
  | Sum.inl i =>
      if hi : i.1 = 0 then
        ⟨0, by omega⟩
      else
        ⟨1, by omega⟩
  | Sum.inr i =>
      if hi : i.1 = 0 then
        ⟨d, by omega⟩
      else
        ⟨d + 1, by omega⟩

/-- Right endpoint of each displayed star edge. -/
def localTwoStarRight
    (Q d : ℕ) :
    Sum (Fin Q) (Fin Q) → Fin (d + Q + 1)
  | Sum.inl i => ⟨i.1 + 1, by omega⟩
  | Sum.inr i => ⟨d + i.1 + 1, by omega⟩

/-- The prime-parity vector attached to an actual integer vertex. -/
def localVertexVector
    (M x : ℕ) {Q d : ℕ} :
    Fin (d + Q + 1) → PrimeUpTo M → F₂ :=
  fun v p ↦ parityVec (localVertexLabel x v) p.1.1

/-- Reachability is transitive. -/
theorem presentedReachable_trans
    {V E : Type*} {left right : E → V} {u v w : V}
    (huv : PresentedReachable left right u v)
    (hvw : PresentedReachable left right v w) :
    PresentedReachable left right u w := by
  induction hvw with
  | refl => exact huv
  | tail _ hadj ih =>
      exact PresentedReachable.tail ih hadj

/-- Every vertex in the first star is reachable from the left root. -/
theorem localTwoStar_reachable_of_le_Q
    {Q d : ℕ} (hQ : 0 < Q)
    (v : Fin (d + Q + 1)) (hvQ : v.1 ≤ Q) :
    PresentedReachable
      (localTwoStarLeft Q d hQ) (localTwoStarRight Q d)
      ⟨0, by omega⟩ v := by
  by_cases hv0 : v.1 = 0
  · have hv : v = ⟨0, by omega⟩ := Fin.ext hv0
    rw [hv]
    exact PresentedReachable.refl _
  by_cases hv1 : v.1 = 1
  · have hi : (0 : ℕ) < Q := hQ
    let e : Sum (Fin Q) (Fin Q) := Sum.inl ⟨0, hi⟩
    apply PresentedReachable.tail (PresentedReachable.refl _)
    refine ⟨e, Or.inl ⟨?_, ?_⟩⟩
    · apply Fin.ext
      simp [e, localTwoStarLeft]
    · apply Fin.ext
      simp [e, localTwoStarRight, hv1]
  · have hiv : v.1 - 1 < Q := by omega
    let e0 : Sum (Fin Q) (Fin Q) := Sum.inl ⟨0, hQ⟩
    let ev : Sum (Fin Q) (Fin Q) :=
      Sum.inl ⟨v.1 - 1, hiv⟩
    have h01 :
        PresentedReachable
          (localTwoStarLeft Q d hQ) (localTwoStarRight Q d)
          (⟨0, by omega⟩ : Fin (d + Q + 1))
          ⟨1, by omega⟩ := by
      apply PresentedReachable.tail (PresentedReachable.refl _)
      refine ⟨e0, Or.inl ⟨?_, ?_⟩⟩
      · apply Fin.ext
        simp [e0, localTwoStarLeft]
      · apply Fin.ext
        simp [e0, localTwoStarRight]
    apply PresentedReachable.tail h01
    refine ⟨ev, Or.inl ⟨?_, ?_⟩⟩
    · apply Fin.ext
      have hev0 : v.1 - 1 ≠ 0 := by omega
      simp [ev, localTwoStarLeft, hev0]
    · apply Fin.ext
      simp [ev, localTwoStarRight]
      omega

/-- Every vertex in the second star is reachable from its left root. -/
theorem localTwoStar_reachable_from_secondRoot
    {Q d : ℕ} (hQ : 0 < Q)
    (v : Fin (d + Q + 1))
    (hdv : d ≤ v.1) (hv : v.1 ≤ d + Q) :
    PresentedReachable
      (localTwoStarLeft Q d hQ) (localTwoStarRight Q d)
      ⟨d, by omega⟩ v := by
  by_cases hvRoot : v.1 = d
  · have hvEq : v = ⟨d, by omega⟩ := Fin.ext hvRoot
    rw [hvEq]
    exact PresentedReachable.refl _
  by_cases hvCenter : v.1 = d + 1
  · let e : Sum (Fin Q) (Fin Q) := Sum.inr ⟨0, hQ⟩
    apply PresentedReachable.tail (PresentedReachable.refl _)
    refine ⟨e, Or.inl ⟨?_, ?_⟩⟩
    · apply Fin.ext
      simp [e, localTwoStarLeft]
    · apply Fin.ext
      simp [e, localTwoStarRight, hvCenter]
  · have hi : v.1 - d - 1 < Q := by omega
    let e0 : Sum (Fin Q) (Fin Q) := Sum.inr ⟨0, hQ⟩
    let ev : Sum (Fin Q) (Fin Q) :=
      Sum.inr ⟨v.1 - d - 1, hi⟩
    have hdCenter :
        PresentedReachable
          (localTwoStarLeft Q d hQ) (localTwoStarRight Q d)
          (⟨d, by omega⟩ : Fin (d + Q + 1))
          ⟨d + 1, by omega⟩ := by
      apply PresentedReachable.tail (PresentedReachable.refl _)
      refine ⟨e0, Or.inl ⟨?_, ?_⟩⟩
      · apply Fin.ext
        simp [e0, localTwoStarLeft]
      · apply Fin.ext
        simp [e0, localTwoStarRight]
    apply PresentedReachable.tail hdCenter
    refine ⟨ev, Or.inl ⟨?_, ?_⟩⟩
    · apply Fin.ext
      have hev0 : v.1 - d - 1 ≠ 0 := by omega
      simp [ev, localTwoStarLeft, hev0]
    · apply Fin.ext
      simp [ev, localTwoStarRight]
      omega

/-- When `0<d≤Q`, the displayed union of stars is connected. -/
theorem localTwoStar_connected
    {Q d : ℕ} (hQ : 0 < Q) (hd : 0 < d) (hdQ : d ≤ Q) :
    ∀ v : Fin (d + Q + 1),
      PresentedReachable
        (localTwoStarLeft Q d hQ) (localTwoStarRight Q d)
        ⟨0, by omega⟩ v := by
  intro v
  by_cases hvQ : v.1 ≤ Q
  · exact localTwoStar_reachable_of_le_Q hQ v hvQ
  · have hroot :
        PresentedReachable
          (localTwoStarLeft Q d hQ) (localTwoStarRight Q d)
          (⟨0, by omega⟩ : Fin (d + Q + 1))
          ⟨d, by omega⟩ :=
      localTwoStar_reachable_of_le_Q hQ ⟨d, by omega⟩ hdQ
    have hsecond :=
      localTwoStar_reachable_from_secondRoot hQ v
        (by omega) (by omega)
    exact presentedReachable_trans hroot hsecond

/-! ## Literal realization by the two-start affine system -/

/-- A prime-coordinate basis vector evaluates `valueBit` to `parityVec`. -/
theorem valueBit_primeSingle
    {M n : ℕ} (p : PrimeUpTo M) :
    valueBit (Pi.single p 1) n = parityVec n p.1.1 := by
  classical
  rw [valueBit]
  rw [Fintype.sum_eq_single p]
  · simp
  · intro r hr
    simp [Pi.single_apply, hr]

/--
Every row of the common two-start system is the represented edge of the
explicit union of stars.
-/
theorem twoStartSystem_rowsRepresented
    {M x Q d : ℕ} (hx : 1 ≤ x) (hQ : 0 < Q) (hd : 0 < d) :
    RowsRepresentedByGraph
      (twoStartSystem M x (x + d) Q)
      (localVertexVector M x)
      (localTwoStarLeft Q d hQ)
      (localTwoStarRight Q d) := by
  intro e p
  cases e with
  | inl i =>
      by_cases hi : i.1 = 0
      · simp [RowsRepresentedByGraph, representedEdgeVector,
          localVertexVector, localVertexLabel, localTwoStarLeft,
          localTwoStarRight, valueBit_primeSingle, hi]
        rw [show x - 1 + 1 = x by omega]
      · simp [RowsRepresentedByGraph, representedEdgeVector,
          localVertexVector, localVertexLabel, localTwoStarLeft,
          localTwoStarRight, valueBit_primeSingle, hi]
        rw [show x - 1 + 1 = x by omega,
          show x - 1 + (i.1 + 1) = x + i.1 by omega]
  | inr i =>
      by_cases hi : i.1 = 0
      · simp [RowsRepresentedByGraph, representedEdgeVector,
          localVertexVector, localVertexLabel, localTwoStarLeft,
          localTwoStarRight, valueBit_primeSingle, hi]
        rw [show x - 1 + d = x + d - 1 by omega,
          show x - 1 + (d + 1) = x + d by omega]
      · simp [RowsRepresentedByGraph, representedEdgeVector,
          localVertexVector, localVertexLabel, localTwoStarLeft,
          localTwoStarRight, valueBit_primeSingle, hi]
        rw [show x - 1 + (d + 1) = x + d by omega,
          show x - 1 + (d + i.1 + 1) = x + d + i.1 by omega]

/-! ## Private coordinates on the union interval -/

/--
Every non-root vertex of the union belongs to the run support of one of the
two starts.
-/
theorem localVertex_mem_one_runSupport
    {x Q d : ℕ} (hx : 1 ≤ x) (hQ : 0 < Q)
    (hd : 0 < d) (hdQ : d ≤ Q)
    (v : Fin (d + Q + 1))
    (hv : v ≠ (⟨0, by omega⟩ : Fin (d + Q + 1))) :
    localVertexLabel x v ∈ startRunSupport x Q ∨
      localVertexLabel x v ∈ startRunSupport (x + d) Q := by
  have hv0 : v.1 ≠ 0 := by
    intro h
    apply hv
    apply Fin.ext
    exact h
  by_cases hvQ : v.1 ≤ Q
  · apply Or.inl
    apply mem_startRunSupport.mpr
    refine ⟨v.1 - 1, by omega, ?_⟩
    simp [localVertexLabel]
    omega
  · apply Or.inr
    apply mem_startRunSupport.mpr
    refine ⟨v.1 - d - 1, by omega, ?_⟩
    simp [localVertexLabel]
    omega

/--
Private large-prime pivots for all non-root vertices of the concrete union.
-/
theorem localTwoStar_privatePivots
    {N Q Y x d : ℕ}
    (hN : 2 ≤ N) (hQ : 0 < Q)
    (hd : 0 < d) (hdQ : d ≤ Q)
    (hdiam : 2 * Q < Y)
    (hx : x ∈ goodStarts N Q Y)
    (hy : x + d ∈ goodStarts N Q Y) :
    HasPrivatePivots
      (localVertexVector (dyadicCutoff N Q) x)
      (fun _ : Fin (d + Q + 1) ↦ ())
      (fun _ : Unit ↦ (⟨0, by omega⟩ : Fin (d + Q + 1))) := by
  intro v hv
  have hxNat : 2 ≤ x :=
    two_le_of_mem_dyadicBlock hN (mem_goodStarts.mp hx).1
  have hmem :=
    localVertex_mem_one_runSupport
      (show 1 ≤ x by omega) hQ hd hdQ v hv
  obtain ⟨p, hpSupport⟩ :
      ∃ p, p ∈ largeOddPrimeSupport Y (localVertexLabel x v) :=
    hmem.elim
      (fun hvx ↦ by
        obtain ⟨p, hp, _⟩ :=
          exists_largePrime_of_mem_runSupport_of_good
            (N := N) (L := Q) (Y := Y) (x := x)
            (n := localVertexLabel x v) hx hvx
        exact ⟨p, hp⟩)
      (fun hvy ↦ by
        obtain ⟨p, hp, _⟩ :=
          exists_largePrime_of_mem_runSupport_of_good
            (N := N) (L := Q) (Y := Y) (x := x + d)
            (n := localVertexLabel x v) hy hvy
        exact ⟨p, hp⟩)
  have hpData :=
    prime_and_large_of_mem_largeOddPrimeSupport hpSupport
  have hpParity :
      parityVec (localVertexLabel x v) p ≠ 0 :=
    (mem_largeOddPrimeSupport_iff.mp hpSupport).2
  have hpDvd : p ∣ localVertexLabel x v := by
    have hpFactor :
        (localVertexLabel x v).factorization p ≠ 0 := by
      intro hz
      apply hpParity
      rw [parityVec_apply, hz]
      rfl
    by_contra hnot
    exact hpFactor
      (Nat.factorization_eq_zero_of_not_dvd
        (show ¬p ∣ localVertexLabel x v from hnot))
  have hvLabelLe :
      localVertexLabel x v ≤ dyadicCutoff N Q := by
    rcases hmem with hvx | hvy
    · obtain ⟨j, hj, hjEq⟩ := mem_startRunSupport.mp hvx
      rw [← hjEq]
      exact startWindow_le_dyadicCutoff
        (mem_goodStarts.mp hx).1 hj
    · obtain ⟨j, hj, hjEq⟩ := mem_startRunSupport.mp hvy
      rw [← hjEq]
      exact startWindow_le_dyadicCutoff
        (mem_goodStarts.mp hy).1 hj
  have hpM : p ≤ dyadicCutoff N Q :=
    (Nat.le_of_dvd (by
      have hv0 : v.1 ≠ 0 := by
        intro hvzero
        apply hv
        apply Fin.ext
        simpa using hvzero
      have : 2 ≤ localVertexLabel x v := by
        unfold localVertexLabel
        omega
      omega) hpDvd).trans hvLabelLe
  let pCoord : PrimeUpTo (dyadicCutoff N Q) :=
    ⟨⟨p, Nat.lt_succ_of_le hpM⟩, hpData.1⟩
  refine ⟨pCoord, ?_⟩
  intro w
  by_cases hwv : w = v
  · subst w
    rw [if_pos rfl]
    change parityVec (localVertexLabel x v) p = 1
    exact Fin.eq_one_of_ne_zero _ hpParity
  · rw [if_neg hwv]
    have hlabels :
        localVertexLabel x v ≠ localVertexLabel x w := by
      intro h
      apply hwv
      apply Fin.ext
      unfold localVertexLabel at h
      omega
    have hdist :
        Nat.dist (localVertexLabel x v) (localVertexLabel x w) < Y := by
      unfold localVertexLabel
      rw [Nat.dist_add_add_left]
      have hvBound := v.2
      have hwBound := w.2
      simp only [Nat.dist]
      omega
    have hpNot : ¬p ∣ localVertexLabel x w :=
      PrivatePivots.not_dvd_of_dvd_and_dist_lt
        hpDvd hlabels hpData.2 hdist
    change parityVec (localVertexLabel x w) p = 0
    rw [parityVec_apply,
      Nat.factorization_eq_zero_of_not_dvd hpNot]
    rfl

/-! ## The concrete relation-defect bound -/

/--
For two retained oriented starts at distance `d≤Q`, the common relation
defect is bounded by the overlap cyclomatic number `Q-d`.
-/
theorem jointRho_le_sub_distance_oriented
    {N Q Y x d : ℕ}
    (hN : 2 ≤ N) (hQ : 0 < Q)
    (hd : 0 < d) (hdQ : d ≤ Q)
    (hdiam : 2 * Q < Y)
    (hx : x ∈ goodStarts N Q Y)
    (hy : x + d ∈ goodStarts N Q Y) :
    jointRho N Q (x, x + d) ≤ Q - d := by
  have hbound :=
    relationRho_le_card_edges_sub_nonRoot_of_privatePivots
      (twoStartSystem (dyadicCutoff N Q) x (x + d) Q)
      (localVertexVector (dyadicCutoff N Q) x)
      (localTwoStarLeft Q d hQ)
      (localTwoStarRight Q d)
      (fun _ : Fin (d + Q + 1) ↦ ())
      (fun _ : Unit ↦ (⟨0, by omega⟩ : Fin (d + Q + 1)))
      (twoStartSystem_rowsRepresented
        (show 1 ≤ x by
          have := two_le_of_mem_dyadicBlock hN (mem_goodStarts.mp hx).1
          omega)
        hQ hd)
      (by intro c; cases c; rfl)
      (by intro e; rfl)
      (by
        intro v
        simpa using localTwoStar_connected hQ hd hdQ v)
      (localTwoStar_privatePivots hN hQ hd hdQ hdiam hx hy)
  have harith : Q + Q - (d + Q) = Q - d := by omega
  simpa [jointRho, Fintype.card_sum, harith] using hbound

/--
The terminal cutoff at base `Q+1` is strictly larger than the diameter
`2Q` once `Q≥2`.
-/
theorem two_mul_lt_terminalPrimeCutoff_succ
    {Q : ℕ} (hQ : 2 ≤ Q) :
    2 * Q < terminalPrimeCutoff (Q + 1) := by
  have hB : (2 : ℝ) ≤ (Q + 1 : ℕ) := by
    exact_mod_cast (show 2 ≤ Q + 1 by omega)
  have hlogMono :
      Real.log (2 : ℝ) ≤ Real.log ((Q + 1 : ℕ) : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hB)
  have hlog :
      (2 / 3 : ℝ) ≤ Real.log ((Q + 1 : ℕ) : ℝ) := by
    have hnum : (2 / 3 : ℝ) < Real.log 2 := by
      nlinarith [Real.log_two_gt_d9]
    exact hnum.le.trans hlogMono
  have hquad :
      ((2 * Q + 1 : ℕ) : ℝ) ≤
        ((Q : ℝ) + 1) ^ 2 * (2 / 3 : ℝ) := by
    have hQr : (2 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
    have hprod :
        0 ≤ ((Q : ℝ) - 2) * (2 * (Q : ℝ) + 1) :=
      mul_nonneg (sub_nonneg.mpr hQr) (by positivity)
    norm_num
    nlinarith
  have hscale :
      ((2 * Q + 1 : ℕ) : ℝ) ≤ terminalPrimeScale (Q + 1) := by
    simp only [terminalPrimeScale, Nat.cast_add, Nat.cast_one]
    norm_num at hquad ⊢
    have hlog' :
        (2 / 3 : ℝ) ≤ Real.log ((Q : ℝ) + 1) := by
      norm_num at hlog ⊢
      exact hlog
    exact hquad.trans
      (mul_le_mul_of_nonneg_left hlog' (sq_nonneg _))
  have hfloor :
      2 * Q + 1 ≤ terminalPrimeCutoff (Q + 1) := by
    rw [terminalPrimeCutoff,
      Nat.le_floor_iff (terminalPrimeScale_nonneg (Q + 1))]
    exact hscale
  omega

end

end TwoStartLocalRank
end PaperC
