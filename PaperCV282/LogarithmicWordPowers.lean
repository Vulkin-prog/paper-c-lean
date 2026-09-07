import PaperC.Asymptotics.ExpSqrtLog
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Word-space powers and uniform logarithmic factors

These bounds keep the word-space size `2^(L+1)` explicit. They do not
replace it with the ambient scale or impose a bounded critical offset.
Only polynomial factors in the logarithmic length are subpolynomial.
-/

namespace PaperC.V282.LogarithmicWordPowers

noncomputable section

/-- The integer quotient exponent is bounded by the corresponding root
of the actual word-space size. -/
theorem two_pow_div_le_word_rpow (L d : ℕ) (hd : 0 < d) :
    (2 : ℝ) ^ (L / d) ≤ ((2 : ℝ) ^ (L + 1)) ^ (1 / (d : ℝ)) := by
  rw [one_div]
  apply (Real.le_rpow_inv_iff_of_pos (by positivity) (by positivity)
    (by exact_mod_cast hd : (0 : ℝ) < d)).mpr
  rw [Real.rpow_natCast, ← pow_mul]
  exact pow_le_pow_right₀ (by norm_num) ((Nat.div_mul_le_self L d).trans (Nat.le_succ L))

/-- Every fixed power of `L+1` is uniformly subpolynomial under the
upper logarithmic ceiling alone. -/
theorem length_pow_uniformSubpolynomial (C : ℝ) (hC : 0 ≤ C) (d : ℕ) :
    UniformSubpolynomialOn
      (fun M L => ((L + 1 : ℕ) : ℝ) ≤ C * Real.log M)
      (fun _ L => (L + 1 : ℝ) ^ d) := by
  have hbase : UniformSubpolynomialOn
      (fun M L => ((L + 1 : ℕ) : ℝ) ≤ C * Real.log M)
      (fun _ L => (L + 1 : ℝ)) := by
    apply ExpSqrtLog.uniformSubpolynomialOn_linear_log_add_one
      _ (fun _ L => L) C hC
    intro M L hL
    have hcast : (L : ℝ) ≤ ((L + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ L
    exact hcast.trans hL
  by_cases hd : d = 0
  · subst d
    simpa only [pow_zero] using ExpSqrtLog.uniformSubpolynomialOn_const
      (fun M L => ((L + 1 : ℕ) : ℝ) ≤ C * Real.log M) (1 : ℝ)
  · intro k hk
    obtain ⟨M₀, hM₀⟩ := hbase (d * k) (Nat.mul_pos (Nat.pos_of_ne_zero hd) hk)
    refine ⟨M₀, ?_⟩
    intro M hM L hL
    simpa only [abs_pow, ← pow_mul] using hM₀ M hM L hL

/-- A fixed coefficient does not change the preceding uniform growth rate. -/
theorem polynomial_factor_uniformSubpolynomial
    (C : ℝ) (hC : 0 ≤ C) (a : ℝ) (d : ℕ) :
    UniformSubpolynomialOn
      (fun M L => ((L + 1 : ℕ) : ℝ) ≤ C * Real.log M)
      (fun _ L => a * (L + 1 : ℝ) ^ d) :=
  ExpSqrtLog.uniformSubpolynomialOn_const_mul a (length_pow_uniformSubpolynomial C hC d)

/-- The reciprocal-power convention gives the literal real-exponent
bound used in the paper, for every fixed positive error exponent. -/
theorem polynomial_factor_le_rpow_eventually
    (C : ℝ) (hC : 0 ≤ C) (a : ℝ) (d : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ M₀ : ℕ, ∀ M ≥ M₀, ∀ L : ℕ,
      ((L + 1 : ℕ) : ℝ) ≤ C * Real.log M →
      |a * (L + 1 : ℝ) ^ d| ≤ (M : ℝ) ^ ε := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  obtain ⟨Mcore, hcore⟩ := polynomial_factor_uniformSubpolynomial C hC a d
    (n + 1) (by omega)
  refine ⟨max Mcore 1, ?_⟩
  intro M hM L hL
  have hMcore : Mcore ≤ M := (le_max_left _ _).trans hM
  have hMone : (1 : ℝ) ≤ M := by
    exact_mod_cast (le_max_right Mcore 1).trans hM
  have hroot : |a * (L + 1 : ℝ) ^ d| ≤
      (M : ℝ) ^ (1 / (n + 1 : ℝ)) := by
    rw [one_div]
    apply (Real.le_rpow_inv_iff_of_pos (abs_nonneg _) (by positivity)
      (by positivity : (0 : ℝ) < n + 1)).mpr
    have hpower := hcore M hMcore L hL
    rw [show (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) by norm_cast, Real.rpow_natCast]
    exact hpower
  exact hroot.trans (Real.rpow_le_rpow_of_exponent_le hMone hn.le)

end
end PaperC.V282.LogarithmicWordPowers
