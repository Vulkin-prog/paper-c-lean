import PaperCV282.PrecisePellCount
import PaperCV282.PrecisePellDivisors
import PaperCV282.PositiveSquareclassPairs

/-!
# Precise counts for both branches of the squareclass reduction

The equal-squareclass case uses the injective divisor parametrization of
positive roots. The distinct case uses the actual bounded-height Pell count.
Both constants and both thresholds are independent of the squareclasses.
-/

namespace PaperC.V282.PrecisePellSquareclasses

open PellInput PositiveSquareclassPairs PrecisePellCount PrecisePellDivisors

noncomputable section

/-- A uniform precise count, including equal squareclasses and both signs of the difference. -/
theorem positiveSquareclassBox_atMost_expLogLog_eventually
    (hNR : NicolasRobinDivisorLogBoundStatement) (K : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∃ Mzero : ℕ, ∀ M ≥ Mzero,
      ∀ A C H : ℕ, ∀ e : ℤ,
      0 < A → 0 < C → Squarefree A → Squarefree C → e ≠ 0 →
      A ≤ M ^ K → C ≤ M ^ K → H ≤ M ^ K → e.natAbs ≤ M ^ K →
      HasAtMostSolutionsReal (positiveSquareclassBox A C H e) (expLogLogBound c M) := by
  obtain ⟨cp, hcp, Mp, hp⟩ := pellBox_atMost_expLogLog_eventually hNR K
  obtain ⟨cd, hcd, Md, hd⟩ := card_divisors_le_expLogLog_eventually hNR K
  refine ⟨cp + cd, add_nonneg hcp hcd, max Mp (max Md 64), ?_⟩
  intro M hM A C H e hA hC hAsq hCsq he hAM hCM hHM heM
  have htail : max Md 64 ≤ M := (le_max_right _ _).trans hM
  have h64 : 64 ≤ M := (le_max_right _ _).trans htail
  rw [expLogLogBound_add]
  by_cases hAC : A = C
  · subst C
    intro s hs
    calc
      (s.card : ℝ) ≤ e.natAbs.divisors.card := equal_squareclass_atMost_divisors hA he s hs
      _ ≤ expLogLogBound cd M := hd M ((le_max_left _ _).trans htail) e.natAbs heM
      _ ≤ expLogLogBound cp M * expLogLogBound cd M :=
        le_mul_of_one_le_left (expLogLogBound_pos cd M).le (one_le_expLogLogBound hcp h64)
  · have hcount := positiveSquareclassBox_atMost_of_pell
      (hp M ((le_max_left _ _).trans hM) A C H e hA hC hAsq hCsq
        (TerminalPartnerPell.not_isSquare_ratio_of_squarefree_of_ne hA hC hAsq hCsq hAC)
        he hAM hCM hHM heM)
    intro s hs
    exact (hcount s hs).trans
      (le_mul_of_one_le_right (expLogLogBound_pos cp M).le (one_le_expLogLogBound hcd h64))

end
end PaperC.V282.PrecisePellSquareclasses
