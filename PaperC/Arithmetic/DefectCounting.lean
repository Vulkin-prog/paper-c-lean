import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.Sqrt
import Mathlib.Order.Interval.Finset.Nat
import Lean.Elab.Tactic.Omega

/-!
# Finite counting of square-defect representations

This file isolates the elementary finite-counting part of Proposition 3.2.
An integer with defect supported on a finite set `P` is represented as

`n = s * a^2`,  where  `s = ∏ p ∈ S, p`  for some `S ⊆ P`.

The represented values up to `X` are covered by one finite family for every
subset `S`.  Taking cardinalities first gives a sum over all subsets and then
the robust coarse estimate

`(# represented values) ≤ (Nat.sqrt X + 1) * 2 ^ P.card`.

The last section proves the independent interval-overlap fact used when the
global count is converted into an average of local counts: a fixed value lies
in at most `H + 1` integer intervals `[u, u + H]`.
-/

namespace PaperC
namespace DefectCounting

open scoped BigOperators

/-- The finite set of primes at most `H`. -/
def smallPrimesUpTo (H : ℕ) : Finset ℕ :=
  (Finset.range (H + 1)).filter Nat.Prime

@[simp]
theorem mem_smallPrimesUpTo {H p : ℕ} :
    p ∈ smallPrimesUpTo H ↔ p.Prime ∧ p ≤ H := by
  simp [smallPrimesUpTo, Nat.lt_succ_iff, and_comm]

/--
A representation of `n` by a square part and a defect supported on `P`.

The finset `support` records the subset of small primes, while
`support.prod id` is the defect part `s`.
-/
structure DefectRepresentation (P : Finset ℕ) (n : ℕ) where
  support : Finset ℕ
  support_subset : support ⊆ P
  squarePart : ℕ
  value_eq : n = support.prod id * squarePart ^ 2

/-- The defect part `s` occurring in a defect representation. -/
def DefectRepresentation.defectPart {P : Finset ℕ} {n : ℕ}
    (rep : DefectRepresentation P n) : ℕ :=
  rep.support.prod id

@[simp]
theorem DefectRepresentation.value_eq_defectPart_mul_sq
    {P : Finset ℕ} {n : ℕ} (rep : DefectRepresentation P n) :
    n = rep.defectPart * rep.squarePart ^ 2 :=
  rep.value_eq

/-- `H`-defect representations use only primes at most `H`. -/
abbrev HDefectRepresentation (H n : ℕ) :=
  DefectRepresentation (smallPrimesUpTo H) n

/--
Candidate values associated with one fixed prime support.  The filter retains
only values at most `X`; the range contains every possible square part because
`a^2 ≤ X` implies `a ≤ Nat.sqrt X`.
-/
def valuesForSupport (support : Finset ℕ) (X : ℕ) : Finset ℕ :=
  ((Finset.range (Nat.sqrt X + 1)).image
      (fun a ↦ support.prod id * a ^ 2)).filter (· ≤ X)

/-- All values up to `X` represented by a subset of the finite prime set `P`. -/
def defectValues (P : Finset ℕ) (X : ℕ) : Finset ℕ :=
  P.powerset.biUnion (fun support ↦ valuesForSupport support X)

theorem mem_valuesForSupport_iff
    {support : Finset ℕ} {X n : ℕ} :
    n ∈ valuesForSupport support X ↔
      n ≤ X ∧ ∃ a ≤ Nat.sqrt X, n = support.prod id * a ^ 2 := by
  simp [valuesForSupport, Nat.lt_succ_iff, eq_comm, and_comm,
    and_left_comm, and_assoc]

theorem mem_defectValues_iff {P : Finset ℕ} {X n : ℕ} :
    n ∈ defectValues P X ↔
      n ≤ X ∧
        ∃ support ⊆ P, ∃ a ≤ Nat.sqrt X,
          n = support.prod id * a ^ 2 := by
  simp only [defectValues, Finset.mem_biUnion, Finset.mem_powerset,
    mem_valuesForSupport_iff]
  constructor
  · rintro ⟨support, hsP, hnX, a, ha, rfl⟩
    exact ⟨hnX, support, hsP, a, ha, rfl⟩
  · rintro ⟨hnX, support, hsP, a, ha, hvalue⟩
    exact ⟨support, hsP, hnX, a, ha, hvalue⟩

/--
The square part of a bounded representation is at most `Nat.sqrt X`, provided
the allowed factors are positive.  For a set of primes this positivity is
automatic.
-/
theorem squarePart_le_sqrt
    {P : Finset ℕ} {X n : ℕ}
    (hP : ∀ p ∈ P, 1 ≤ p)
    (rep : DefectRepresentation P n)
    (hnX : n ≤ X) :
    rep.squarePart ≤ Nat.sqrt X := by
  rw [Nat.le_sqrt']
  calc
    rep.squarePart ^ 2 = 1 * rep.squarePart ^ 2 := by simp
    _ ≤ rep.support.prod id * rep.squarePart ^ 2 := by
      apply Nat.mul_le_mul_right
      apply Nat.one_le_iff_ne_zero.mpr
      rw [Finset.prod_ne_zero_iff]
      intro p hp
      exact Nat.ne_of_gt
        (Nat.zero_lt_one.trans_le (hP p (rep.support_subset hp)))
    _ = n := rep.value_eq.symm
    _ ≤ X := hnX

/-- Every bounded explicit representation occurs in `defectValues`. -/
theorem mem_defectValues_of_representation
    {P : Finset ℕ} {X n : ℕ}
    (hP : ∀ p ∈ P, 1 ≤ p)
    (rep : DefectRepresentation P n)
    (hnX : n ≤ X) :
    n ∈ defectValues P X := by
  rw [mem_defectValues_iff]
  exact ⟨hnX, rep.support, rep.support_subset, rep.squarePart,
    squarePart_le_sqrt hP rep hnX, rep.value_eq⟩

/-- Specialization to defect parts supported on primes at most `H`. -/
theorem mem_defectValues_of_HDefectRepresentation
    {H X n : ℕ}
    (rep : HDefectRepresentation H n)
    (hnX : n ≤ X) :
    n ∈ defectValues (smallPrimesUpTo H) X := by
  apply mem_defectValues_of_representation _ rep hnX
  intro p hp
  exact (mem_smallPrimesUpTo.mp hp).1.one_lt.le

/-- Each fixed support contributes at most `Nat.sqrt X + 1` values. -/
theorem card_valuesForSupport_le (support : Finset ℕ) (X : ℕ) :
    (valuesForSupport support X).card ≤ Nat.sqrt X + 1 := by
  unfold valuesForSupport
  exact (Finset.card_filter_le _ _).trans
    (Finset.card_image_le.trans_eq (Finset.card_range _))

/--
First form of the global defect count: a sum of the contributions of all
subsets of the allowed small primes.
-/
theorem card_defectValues_le_sum (P : Finset ℕ) (X : ℕ) :
    (defectValues P X).card ≤
      ∑ support ∈ P.powerset, (valuesForSupport support X).card := by
  unfold defectValues
  exact Finset.card_biUnion_le

/--
Coarse finite bound for the global defect mass.  The `+ 1` makes the estimate
valid at `X = 0` and allows the square part `a = 0`.
-/
theorem card_defectValues_le (P : Finset ℕ) (X : ℕ) :
    (defectValues P X).card ≤
      (Nat.sqrt X + 1) * 2 ^ P.card := by
  calc
    (defectValues P X).card
        ≤ ∑ support ∈ P.powerset,
            (valuesForSupport support X).card :=
      card_defectValues_le_sum P X
    _ ≤ ∑ _support ∈ P.powerset, (Nat.sqrt X + 1) := by
      exact Finset.sum_le_sum fun support _ ↦
        card_valuesForSupport_le support X
    _ = (Nat.sqrt X + 1) * 2 ^ P.card := by
      simp [Finset.card_powerset, Nat.mul_comm]

/-- The same bound for the actual set of primes at most `H`. -/
theorem card_HDefectValues_le (H X : ℕ) :
    (defectValues (smallPrimesUpTo H) X).card ≤
      (Nat.sqrt X + 1) * 2 ^ (smallPrimesUpTo H).card :=
  card_defectValues_le _ _

/-! ## Multiplicity of sliding integer intervals -/

/--
The starting points `u` in `starts` whose integer interval `[u, u + H]`
contains `n`.
-/
def intervalStartsContaining (starts : Finset ℕ) (H n : ℕ) : Finset ℕ :=
  starts.filter (fun u ↦ u ≤ n ∧ n ≤ u + H)

theorem intervalStartsContaining_subset_Icc
    (starts : Finset ℕ) (H n : ℕ) :
    intervalStartsContaining starts H n ⊆ Finset.Icc (n - H) n := by
  intro u hu
  rw [intervalStartsContaining, Finset.mem_filter] at hu
  rw [Finset.mem_Icc]
  exact ⟨by
    rw [Nat.sub_le_iff_le_add]
    simpa [Nat.add_comm] using hu.2.2, hu.2.1⟩

/--
A fixed integer belongs to at most `H + 1` intervals `[u, u + H]`, even when
the possible starting points are restricted to an arbitrary finset.
-/
theorem card_intervalStartsContaining_le
    (starts : Finset ℕ) (H n : ℕ) :
    (intervalStartsContaining starts H n).card ≤ H + 1 := by
  calc
    (intervalStartsContaining starts H n).card
        ≤ (Finset.Icc (n - H) n).card :=
      Finset.card_le_card
        (intervalStartsContaining_subset_Icc starts H n)
    _ = n + 1 - (n - H) := Nat.card_Icc (n - H) n
    _ ≤ H + 1 := by omega

end DefectCounting
end PaperC
