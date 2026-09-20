import PaperCV282.BadStartRankinFreeCutoff
import Mathlib.Data.Finset.Lattice.Fold

/-! # Largest odd prime and its actual counting function

The pivot is the largest prime with odd valuation, with value 1 for a square.
Its distribution is identified with the already proved defective-integer
count, so the free-cutoff Rankin theorem applies without a new analytic input.
This module does not yet sum reciprocal pivots or prove the directed footprint.
-/
namespace PaperC.Prel8.OddPrimePivot
open PaperC.DefectivePredicate PaperC.DefectCounting
open PaperC.V282.DefectiveRankinCount PaperC.V282.BadStartRankinFreeCutoff
open PaperC.V282.PrimeEulerPNT PaperC.V282.SaddleBranch PaperC.V282.SaddleParameters
noncomputable section

/-- `κ_odd` in companion F: the maximum of the actual odd valuation support. -/
def largestOddPrime (n : ℕ) : ℕ := max 1 ((oddPrimeSupport n).sup id)

theorem largestOddPrime_pos (n : ℕ) : 0 < largestOddPrime n := by
  exact lt_of_lt_of_le (by decide : 0<1) (le_max_left _ _)

/-- The cutoff predicate agrees exactly with parity-defect counting. -/
theorem largestOddPrime_le_iff {Y n : ℕ} (hY : 1 ≤ Y) :
    largestOddPrime n ≤ Y ↔ HDefective Y n := by
  rw [largestOddPrime, max_le_iff]
  constructor
  · rintro ⟨_, hsup⟩
    rw [hDefective_iff_even_factorization]
    intro p hp hpY
    by_contra hodd
    have hmem : p ∈ oddPrimeSupport n := by
      simp only [oddPrimeSupport, Finsupp.mem_support_iff, oddFactorization, Finsupp.mapRange_apply]
      exact fun h => hodd (Nat.dvd_of_mod_eq_zero h)
    have hle : p ≤ Y := (Finset.le_sup (f := id) hmem).trans hsup
    omega
  · intro h
    refine ⟨hY, Finset.sup_le ?_⟩
    intro p hp
    exact (mem_smallPrimesUpTo.mp (oddPrimeSupport_subset_smallPrimesUpTo h hp)).2

/-- Positive integers only; zero is never included in the pivot population. -/
def pivotValues (X Y : ℕ) : Finset ℕ := (Finset.Icc 1 X).filter (fun n => largestOddPrime n ≤ Y)

theorem pivotValues_eq_defectiveValues {X Y : ℕ} (hY : 1 ≤ Y) :
    pivotValues X Y = defectiveValues X Y := by
  classical
  ext n
  simp [pivotValues, defectiveValues, largestOddPrime_le_iff hY]

/-- Finite Rankin bound for this exact pivot population. -/
theorem pivot_count_rankin {X Y : ℕ} (hY : 1 ≤ Y) {zeta : ℝ} (hzeta : zeta ≤ 1/2) :
    ((pivotValues X Y).card : ℝ) ≤ (X : ℝ)^(1-zeta)*rankinEulerProduct Y zeta := by
  rw [pivotValues_eq_defectiveValues hY]
  exact card_defectiveValues_le_rankin X Y hzeta

/-- Uniform free-cutoff bound, with its threshold before the varying cutoff. -/
theorem pivot_count_free_cutoff (hPNT : PrimeNumberTheoremRemainder)
    (c C epsilon : ℝ) (hc : 0<c) (hC : 0<C) (hepsilon : 0<epsilon) :
    ∃ Xzero : ℕ, ∀ X ≥ Xzero, ∀ w : ℝ,
      c*Real.sqrt (Real.log X*Real.log (Real.log X)) ≤ w →
      w ≤ C*Real.sqrt (Real.log X*Real.log (Real.log X)) →
      ((pivotValues X ⌊Real.exp w⌋₊).card : ℝ)/X ≤
        Real.exp (-saddleCost (Real.log X/w)+epsilon*(Real.log X/w)) := by
  obtain ⟨Xzero,h⟩ := normalized_defectiveValues_free_cutoff_le_eventually hPNT c C epsilon hc hC hepsilon
  refine ⟨Xzero, ?_⟩
  intro X hX w hlo hhi
  have hw0 : 0 ≤ w := (mul_nonneg hc.le (Real.sqrt_nonneg _)).trans hlo
  have hw : 1 ≤ ⌊Real.exp w⌋₊ := (Nat.one_le_floor_iff _).mpr (Real.one_le_exp hw0)
  rw [pivotValues_eq_defectiveValues hw]
  exact h X hX w hlo hhi

end
end PaperC.Prel8.OddPrimePivot
