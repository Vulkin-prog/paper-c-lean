import PaperCV282.PreciseSplitProducts
import PaperCV282.PolynomialSplitSolutions

/-!
# Article 3.14 at its precise rate and with its real height

All integer pairs `(X,Y)` are counted. There is no imposed height bound on
`Y`: for every fixed `X` the existing exact fibre count is at most two.
The coefficient need only be positive; squarefreeness is unnecessary.
-/

namespace PaperC.V282.PreciseSplitSolutions

open PellInput PrecisePellDivisors PreciseSplitProducts PolynomialSplitSolutions
open scoped BigOperators

noncomputable section

/-- The at-most-two ordinates per start cost another fixed logarithmic exponential. -/
theorem splitProductSolution_atMost_expLogLog_eventually
    (hNR : NicolasRobinDivisorLogBoundStatement) (K d : ℕ) (hd : 2 ≤ d) :
    ∃ c : ℝ, 0 ≤ c ∧ ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ h : Fin d → ℤ, ∀ e : ℕ,
      Function.Injective h → 0 < e → e ≤ M ^ K →
      (∀ i, (h i).natAbs ≤ M ^ K) →
      HasAtMostSolutionsReal (splitProductSolution h e (M ^ K)) (expLogLogBound c M) := by
  obtain ⟨cp, hcp, Mp, hp⟩ := splitProductStart_atMost_expLogLog_eventually hNR K d hd
  obtain ⟨cd, hcd, Md, hdv⟩ := card_divisors_le_expLogLog_eventually hNR 1
  refine ⟨cp + cd, add_nonneg hcp hcd, max Mp (max Md 2), ?_⟩
  intro M hM h e hh he heM hshift
  have htail : max Md 2 ≤ M := (le_max_right _ _).trans hM
  have htwo : 2 ≤ M := (le_max_right _ _).trans htail
  have htwoBound : (2 : ℝ) ≤ expLogLogBound cd M := by
    simpa [Nat.prime_two.divisors] using
      hdv M ((le_max_left _ _).trans htail) 2 (by simpa using htwo)
  have hcount := splitProductSolution_atMost_of_start he
    (hp M ((le_max_left _ _).trans hM) h e hh he heM hshift)
  intro s hs
  calc
    (s.card : ℝ) ≤ 2 * expLogLogBound cp M := hcount s hs
    _ ≤ expLogLogBound cd M * expLogLogBound cp M :=
      mul_le_mul_of_nonneg_right htwoBound (expLogLogBound_pos cp M).le
    _ = expLogLogBound (cp + cd) M := by rw [expLogLogBound_add, mul_comm]

/-- The literal real-height predicate in 3.14; the ordinate is unrestricted. -/
def splitProductRealSolution {d : ℕ} (h : Fin d → ℤ) (e M : ℕ) (K : ℝ)
    (p : ℤ × ℤ) : Prop :=
  (p.1.natAbs : ℝ) ≤ (M : ℝ) ^ K ∧ (∀ i, 0 < p.1 + h i) ∧
    ∏ i, (p.1 + h i) = (e : ℤ) * p.2 ^ 2

/-- Ceiling the fixed exponent enlarges every real polynomial bound uniformly. -/
theorem realPolynomialBound_le_natCeilPow {K : ℝ} {M n : ℕ} (hM : 1 ≤ M)
    (hn : (n : ℝ) ≤ (M : ℝ) ^ K) : n ≤ M ^ ⌈K⌉₊ := by
  have hbase : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hpow := Real.rpow_le_rpow_of_exponent_le hbase (Nat.le_ceil K)
  have hcast : (n : ℝ) ≤ ((M : ℝ) ^ ⌈K⌉₊) := by
    exact hn.trans (by simpa only [Real.rpow_natCast] using hpow)
  exact_mod_cast hcast

/-- Article 3.14, with fixed real exponent, arbitrary distinct shifts and all ordinates.
The same proof permits a nonsquarefree positive coefficient. -/
theorem lemma_three_fourteen
    (hNR : NicolasRobinDivisorLogBoundStatement)
    (d : ℕ) (hd : 2 ≤ d) (K : ℝ) (_hK : 0 < K) :
    ∃ c : ℝ, 0 ≤ c ∧ ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ h : Fin d → ℤ, ∀ e : ℕ,
      Function.Injective h → 0 < e → (e : ℝ) ≤ (M : ℝ) ^ K →
      (∀ i, ((h i).natAbs : ℝ) ≤ (M : ℝ) ^ K) →
      HasAtMostSolutionsReal (splitProductRealSolution h e M K) (expLogLogBound c M) := by
  obtain ⟨c, hc, Mzero, hcount⟩ :=
    splitProductSolution_atMost_expLogLog_eventually hNR ⌈K⌉₊ d hd
  refine ⟨c, hc, max Mzero 1, ?_⟩
  intro M hM h e hh he heM hshift
  have hone : 1 ≤ M := (le_max_right _ _).trans hM
  have h := hcount M ((le_max_left _ _).trans hM) h e hh he
    (realPolynomialBound_le_natCeilPow hone heM)
    (fun i => realPolynomialBound_le_natCeilPow hone (hshift i))
  intro s hs
  apply h s
  intro p hp
  obtain ⟨hX, hpos, heq⟩ := hs p hp
  exact ⟨realPolynomialBound_le_natCeilPow hone hX, hpos, heq⟩

end
end PaperC.V282.PreciseSplitSolutions
