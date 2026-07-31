import PaperC.Arithmetic.BalasubramanianShoreyInput
import PaperC.Arithmetic.DefectCounting
import Mathlib.Data.Nat.Squarefree

/-!
# Squarefree smooth kernels in Lemma 15.3

The manuscript uses Rankin's method to count squarefree `B`-smooth kernels.
For squarefree integers there is a simpler exact finite injection: the
integer is uniquely determined by the subset of primes at most `B` that
divides it.  Hence there are at most `2^π(B)` such kernels, independently of
the ambient height cutoff.
-/

namespace PaperC
namespace SquarefreeSmoothCount

open DefectCounting
open BalasubramanianShoreyInput

/-- Positive squarefree `B`-smooth integers at most `X`. -/
noncomputable def squarefreeSmoothUpTo (B X : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 X).filter fun s ↦
    Squarefree s ∧ IsSmoothAt B s

@[simp]
theorem mem_squarefreeSmoothUpTo {B X s : ℕ} :
    s ∈ squarefreeSmoothUpTo B X ↔
      1 ≤ s ∧ s ≤ X ∧ Squarefree s ∧ IsSmoothAt B s := by
  classical
  simp [squarefreeSmoothUpTo, and_assoc]

/-- The prime support of every member is a subset of the small-prime set. -/
theorem primeFactors_subset_smallPrimesUpTo
    {B X s : ℕ} (hs : s ∈ squarefreeSmoothUpTo B X) :
    s.primeFactors ⊆ smallPrimesUpTo B := by
  intro p hp
  rw [mem_smallPrimesUpTo]
  exact ⟨Nat.prime_of_mem_primeFactors hp,
    (mem_squarefreeSmoothUpTo.mp hs).2.2.2 p hp⟩

/-- Prime support is injective on positive squarefree integers. -/
theorem primeFactors_injective_on_squarefreeSmoothUpTo
    (B X : ℕ) :
    Set.InjOn (fun s : ℕ ↦ s.primeFactors)
      (squarefreeSmoothUpTo B X : Set ℕ) := by
  intro a ha b hb hab
  have haSquarefree :=
    (mem_squarefreeSmoothUpTo.mp ha).2.2.1
  have hbSquarefree :=
    (mem_squarefreeSmoothUpTo.mp hb).2.2.1
  change a.primeFactors = b.primeFactors at hab
  calc
    a = ∏ p ∈ a.primeFactors, p :=
      (Nat.prod_primeFactors_of_squarefree haSquarefree).symm
    _ = ∏ p ∈ b.primeFactors, p := by rw [hab]
    _ = b :=
      Nat.prod_primeFactors_of_squarefree hbSquarefree

/--
Exact finite smooth-kernel bound:

`#{s ≤ X : s squarefree and B-smooth} ≤ 2 ^ π(B)`.
-/
theorem card_squarefreeSmoothUpTo_le_two_pow
    (B X : ℕ) :
    (squarefreeSmoothUpTo B X).card ≤
      2 ^ (smallPrimesUpTo B).card := by
  classical
  let supports :=
    (squarefreeSmoothUpTo B X).image
      (fun s : ℕ ↦ s.primeFactors)
  have hsupports :
      supports ⊆ (smallPrimesUpTo B).powerset := by
    intro support hsupport
    obtain ⟨s, hs, rfl⟩ :=
      Finset.mem_image.mp hsupport
    exact Finset.mem_powerset.mpr
      (primeFactors_subset_smallPrimesUpTo hs)
  calc
    (squarefreeSmoothUpTo B X).card =
        supports.card := by
      symm
      exact Finset.card_image_of_injOn
        (primeFactors_injective_on_squarefreeSmoothUpTo B X)
    _ ≤ ((smallPrimesUpTo B).powerset).card :=
      Finset.card_le_card hsupports
    _ = 2 ^ (smallPrimesUpTo B).card := by simp

end SquarefreeSmoothCount
end PaperC
