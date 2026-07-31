import PaperC.Affine.Normalization
import PaperC.Affine.TouchingSystem
import PaperC.Combinatorics.TouchingPairs
import Mathlib.Algebra.Order.Ring.Finset

/-!
# Finite mass of touching pairs

This module packages the finite weighted sum occurring in Lemma 3.4(ii).
It deliberately makes no claim yet about the arithmetic size of the relation
defect: the future rank argument only has to provide a bound for
`touchingRho`.
-/

namespace PaperC
namespace TouchingMass

open scoped BigOperators
open Affine

noncomputable section

/-- The smaller start in an ordered pair. -/
def touchingLower (pair : ℕ × ℕ) : ℕ :=
  min pair.1 pair.2

/--
Relation defect of the joint affine system attached to the two touching
starts.  The cylinder cutoff covers the full union of their windows.
-/
def touchingRho (N L : ℕ) (pair : ℕ × ℕ) : ℕ :=
  relationRho
    (touchingSystem
      (dyadicCutoff N (2 * L)) (touchingLower pair) L)

/-- The natural weight `2^ρ - 1` from Lemma 3.4(ii). -/
def touchingWeight (N L : ℕ) (pair : ℕ × ℕ) : ℕ :=
  2 ^ touchingRho N L pair - 1

/-- Total ordered touching-pair mass in the dyadic block. -/
def touchingMass (N L : ℕ) : ℕ :=
  ∑ pair ∈ TouchingPairs.touchingPairs N L,
    touchingWeight N L pair

/-- Largest joint relation defect among the touching pairs. -/
def maxTouchingRho (N L : ℕ) : ℕ :=
  (TouchingPairs.touchingPairs N L).sup (touchingRho N L)

/-- The lower endpoint of every touching pair remains in the dyadic block. -/
theorem touchingLower_mem_dyadicBlock
    {N L : ℕ} {pair : ℕ × ℕ}
    (hpair : pair ∈ TouchingPairs.touchingPairs N L) :
    touchingLower pair ∈ dyadicBlock N := by
  obtain ⟨hleft, hright, _hdist⟩ :=
    TouchingPairs.mem_touchingPairs.mp hpair
  unfold touchingLower
  by_cases hle : pair.1 ≤ pair.2
  · simpa [min_eq_left hle] using hleft
  · have hge : pair.2 ≤ pair.1 := Nat.le_of_not_ge hle
    simpa [min_eq_right hge] using hright

/-- Every member's defect is bounded by the finite supremum. -/
theorem touchingRho_le_maxTouchingRho
    {N L : ℕ} {pair : ℕ × ℕ}
    (hpair : pair ∈ TouchingPairs.touchingPairs N L) :
    touchingRho N L pair ≤ maxTouchingRho N L := by
  exact Finset.le_sup hpair

/-- Pointwise weight bound supplied by the maximal touching defect. -/
theorem touchingWeight_le_two_pow_maxTouchingRho
    {N L : ℕ} {pair : ℕ × ℕ}
    (hpair : pair ∈ TouchingPairs.touchingPairs N L) :
    touchingWeight N L pair ≤ 2 ^ maxTouchingRho N L := by
  calc
    touchingWeight N L pair ≤ 2 ^ touchingRho N L pair := by
      exact Nat.sub_le _ _
    _ ≤ 2 ^ maxTouchingRho N L :=
      Nat.pow_le_pow_right (by norm_num)
        (touchingRho_le_maxTouchingRho hpair)

/-- Natural-valued mass bound using at most `2N` ordered touching pairs. -/
theorem touchingMass_le_two_mul_two_pow_maxTouchingRho
    (N L : ℕ) :
    touchingMass N L ≤
      (2 * N) * 2 ^ maxTouchingRho N L := by
  exact TouchingPairs.sum_nat_le_two_mul
    N L (2 ^ maxTouchingRho N L) (touchingWeight N L)
    (fun _pair hpair ↦
      touchingWeight_le_two_pow_maxTouchingRho hpair)

/-- Real-cast form of the same finite mass bound. -/
theorem touchingMass_cast_le_two_mul_two_pow_maxTouchingRho
    (N L : ℕ) :
    (touchingMass N L : ℝ) ≤
      (2 * N : ℝ) * (2 : ℝ) ^ maxTouchingRho N L := by
  exact_mod_cast touchingMass_le_two_mul_two_pow_maxTouchingRho N L

/--
Convenient passage from a pointwise real bound for all touching defects to a
bound for their finite maximum.  The nonnegativity hypothesis handles the
empty touching-pair set, whose natural supremum is zero.
-/
theorem maxTouchingRho_cast_le
    {N L : ℕ} {R : ℝ}
    (hR : 0 ≤ R)
    (hrho : ∀ pair ∈ TouchingPairs.touchingPairs N L,
      (touchingRho N L pair : ℝ) ≤ R) :
    (maxTouchingRho N L : ℝ) ≤ R := by
  classical
  have aux :
      ∀ s : Finset (ℕ × ℕ),
        (∀ pair ∈ s, (touchingRho N L pair : ℝ) ≤ R) →
          ((s.sup (touchingRho N L) : ℕ) : ℝ) ≤ R := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro _h
        simpa using hR
    | @insert pair s hpairNotMem ih =>
        intro hs
        rw [Finset.sup_insert, Nat.cast_max]
        apply max_le
        · exact hs pair (Finset.mem_insert_self pair s)
        · apply ih
          intro other hother
          exact hs other (Finset.mem_insert_of_mem hother)
  exact aux (TouchingPairs.touchingPairs N L) hrho

end

end TouchingMass
end PaperC
