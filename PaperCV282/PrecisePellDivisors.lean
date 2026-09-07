import PaperC.Diophantine.PellDivisorEnvelope

/-!
# Divisor counts at the precise logarithmic exponential scale

The existing Nicolas--Robin envelope contains the polynomial substitution
and its small-integer case. Its elementary specialization at zero height
also bounds a single divisor count uniformly, including the integer zero.
-/

namespace PaperC.V282.PrecisePellDivisors

open PellInput

noncomputable section

/-- Products add constants at the precise scale, without an asymptotic loss. -/
theorem expLogLogBound_add (a b : ℝ) (M : ℕ) :
    expLogLogBound (a + b) M = expLogLogBound a M * expLogLogBound b M := by
  simp only [expLogLogBound, add_mul, add_div, Real.exp_add]

/-- The envelope is positive, also below its eventual threshold. -/
theorem expLogLogBound_pos (a : ℝ) (M : ℕ) : 0 < expLogLogBound a M :=
  Real.exp_pos _

/-- Nonnegative constants give an envelope at least one above a fixed threshold. -/
theorem one_le_expLogLogBound {a : ℝ} (ha : 0 ≤ a) {M : ℕ} (hM : 64 ≤ M) :
    1 ≤ expLogLogBound a M := by
  have hexp : (1 : ℝ) < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
  have hlog : 1 < Real.log (M : ℝ) :=
    hexp.trans_le (exp_one_le_log_nat_of_sixtyFour_le hM)
  have hloglog : 0 < Real.log (Real.log (M : ℝ)) := Real.log_pos hlog
  apply Real.one_le_exp_iff.mpr
  exact div_nonneg (mul_nonneg ha (by linarith)) hloglog.le

/-- Uniform divisor bound for every integer of a fixed polynomial height. -/
theorem card_divisors_le_expLogLog_eventually
    (hNR : NicolasRobinDivisorLogBoundStatement) (K : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ n : ℕ,
      n ≤ M ^ K → (n.divisors.card : ℝ) ≤ expLogLogBound c M := by
  obtain ⟨c, hc, Mzero, hcount⟩ :=
    nicolasRobinPellEnvelope_of_divisorLogBound hNR (K + 1) (by omega)
  refine ⟨c, hc, max Mzero 1, ?_⟩
  intro M hM n hn
  by_cases hzero : n = 0
  · subst n
    simpa using (expLogLogBound_pos c M).le
  have hone : 1 ≤ M := (le_max_right _ _).trans hM
  have hpow : M ^ K ≤ M ^ (K + 1) := Nat.pow_le_pow_right hone (by omega)
  have h := hcount M ((le_max_left _ _).trans hM) (n : ℤ) 0
    (by exact_mod_cast hzero) (by simpa using hn.trans hpow) (Nat.zero_le _)
  have hsmall : n.divisors.card ≤ (4 * n.divisors.card ^ 2) * pellUnitOrbitEnvelope 0 := by
    simp only [pellUnitOrbitEnvelope]
    norm_num
    nlinarith [sq_nonneg (n.divisors.card : ℤ)]
  exact (by exact_mod_cast hsmall : (n.divisors.card : ℝ) ≤
    (((4 * n.divisors.card ^ 2) * pellUnitOrbitEnvelope 0 : ℕ) : ℝ)).trans
      (by simpa only [Int.natAbs_natCast] using h)

end
end PaperC.V282.PrecisePellDivisors
