import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Analysis.SpecialFunctions.Log.Base
import PaperCV282.LogarithmicWordPowers
import PaperCV282.HostRealPowers

/-!
# An elementary divisor estimate at every positive power scale

Small primes contribute a fixed power of the logarithm; for primes at
least `2^k`, the kth power of the local divisor factor is at most the
corresponding prime power. This proves a subpolynomial divisor bound
without the external explicit Nicolas--Robin estimate.
-/

namespace PaperC.V282.DivisorSubpolynomial

open scoped BigOperators

noncomputable section

/-- Every prime exponent of a positive integer is at most its binary logarithm. -/
theorem factorization_le_binary_log {n p : ℕ} (hn : 0 < n) (hp : p.Prime) :
    n.factorization p ≤ Nat.log 2 n := by
  apply Nat.le_log_of_pow_le (by omega)
  calc
    2 ^ n.factorization p ≤ p ^ n.factorization p := Nat.pow_le_pow_left hp.two_le _
    _ ≤ n := Nat.le_of_dvd hn (Nat.ordProj_dvd n p)

/-- Large prime factors pay for the kth power of their entire divisor factor. -/
theorem local_divisor_pow_le_prime_pow {a p k : ℕ} (hp : 2 ^ k ≤ p) :
    (a + 1) ^ k ≤ p ^ a := by
  have hlocal : a + 1 ≤ 2 ^ a := by
    induction a with
    | zero => norm_num
    | succ a ih =>
      rw [pow_succ]
      have htwo : 1 ≤ 2 ^ a := Nat.one_le_pow _ _ (by omega)
      omega
  calc
    _ ≤ (2 ^ a) ^ k := Nat.pow_le_pow_left hlocal _
    _ = (2 ^ k) ^ a := by rw [← pow_mul, ← pow_mul, Nat.mul_comm a k]
    _ ≤ _ := Nat.pow_le_pow_left hp _

/-- The small-prime subset has at most `2^k` members, independently of the integer. -/
theorem card_small_primeFactors_le (n k : ℕ) :
    (n.primeFactors.filter fun p => p < 2 ^ k).card ≤ 2 ^ k := by
  calc
    _ ≤ (Finset.range (2 ^ k)).card := Finset.card_le_card (by
      intro p hp
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2)
    _ = _ := Finset.card_range _

/-- Explicit finite divisor estimate, using only unique factorization. -/
theorem card_divisors_pow_le_log_power_mul_self {n : ℕ} (hn : 0 < n) (k : ℕ) :
    n.divisors.card ^ k ≤ (Nat.log 2 n + 1) ^ (k * 2 ^ k) * n := by
  classical
  rw [Nat.card_divisors (by omega), ← Finset.prod_pow]
  have hlocal : ∀ p ∈ n.primeFactors,
      (n.factorization p + 1) ^ k ≤
        (if p < 2 ^ k then (Nat.log 2 n + 1) ^ k else 1) * p ^ n.factorization p := by
    intro p hp
    by_cases hsmall : p < 2 ^ k
    · rw [if_pos hsmall]
      have ha := factorization_le_binary_log hn (Nat.prime_of_mem_primeFactors hp)
      calc
        _ ≤ (Nat.log 2 n + 1) ^ k := Nat.pow_le_pow_left (by omega) _
        _ ≤ (Nat.log 2 n + 1) ^ k * p ^ n.factorization p := by
          exact Nat.le_mul_of_pos_right _ (Nat.pow_pos (Nat.prime_of_mem_primeFactors hp).pos)
    · rw [if_neg hsmall, one_mul]
      exact local_divisor_pow_le_prime_pow (by omega)
  calc
    _ ≤ ∏ p ∈ n.primeFactors,
        ((if p < 2 ^ k then (Nat.log 2 n + 1) ^ k else 1) * p ^ n.factorization p) :=
      Finset.prod_le_prod (fun _ _ => Nat.zero_le _) hlocal
    _ = (∏ p ∈ n.primeFactors, if p < 2 ^ k then (Nat.log 2 n + 1) ^ k else 1) * n := by
      rw [Finset.prod_mul_distrib, ← Nat.prod_primeFactors_pow_factorization (by omega)]
    _ = ((Nat.log 2 n + 1) ^ k) ^ (n.primeFactors.filter fun p => p < 2 ^ k).card * n := by
      rw [← Finset.prod_filter]
      simp
    _ ≤ ((Nat.log 2 n + 1) ^ k) ^ (2 ^ k) * n := by
      apply Nat.mul_le_mul_right
      exact Nat.pow_le_pow_right (Nat.one_le_pow _ _ (by omega)) (card_small_primeFactors_le n k)
    _ = _ := by rw [← pow_mul]

/-- The binary logarithm of every polynomial-height integer has a common ceiling. -/
theorem binary_log_le_polynomial_log {M n K : ℕ}
    (hn : 0 < n) (hnM : n ≤ M ^ K) :
    (Nat.log 2 n : ℝ) ≤ ((K : ℝ) / Real.log 2) * Real.log M := by
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log (n : ℝ) ≤ (K : ℝ) * Real.log M := by
    calc
      _ ≤ Real.log ((M : ℝ) ^ K) := Real.log_le_log (by exact_mod_cast hn) (by exact_mod_cast hnM)
      _ = _ := Real.log_pow _ _
  calc
    _ ≤ Real.logb 2 n := Real.natLog_le_logb _ _
    _ = Real.log n / Real.log 2 := rfl
    _ ≤ ((K : ℝ) * Real.log M) / Real.log 2 := div_le_div_of_nonneg_right hlog hlogTwo.le
    _ = _ := by ring

/-- A fixed logarithmic polynomial pays for all small-prime factors uniformly in the integer. -/
theorem divisor_log_factor_le_scale_eventually (K k : ℕ) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ n : ℕ, 0 < n → n ≤ M ^ K →
      ((Nat.log 2 n + 1 : ℕ) : ℝ) ^ (k * 2 ^ k) ≤ (M : ℝ) := by
  let C : ℝ := (K : ℝ) / Real.log 2 + 1
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  obtain ⟨Mpoly, hpoly⟩ := LogarithmicWordPowers.polynomial_factor_le_rpow_eventually
    C hC 1 (k * 2 ^ k) 1 (by norm_num)
  refine ⟨max Mpoly (⌈Real.exp 1⌉₊ + 1), ?_⟩
  intro M hM n hn hnM
  have hMlarge : ⌈Real.exp 1⌉₊ + 1 ≤ M := (le_max_right _ _).trans hM
  have hexp : Real.exp 1 ≤ (M : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈Real.exp 1⌉₊ ≤ M by omega))
  have hlogOne : 1 ≤ Real.log M := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hexp
  have hlog := binary_log_le_polynomial_log hn hnM
  have hceiling : ((Nat.log 2 n + 1 : ℕ) : ℝ) ≤ C * Real.log M := by
    dsimp [C]
    push_cast
    nlinarith
  have h := hpoly M ((le_max_left _ _).trans hM) (Nat.log 2 n) hceiling
  simpa only [one_mul, abs_of_nonneg (by positivity :
    (0 : ℝ) ≤ (Nat.log 2 n + 1 : ℝ) ^ (k * 2 ^ k)), Real.rpow_one, Nat.cast_add, Nat.cast_one] using h

/-- Uniform natural-power formulation throughout an arbitrary fixed polynomial-height box. -/
theorem card_divisors_pow_le_polynomial_eventually (K k : ℕ) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ n : ℕ, n ≤ M ^ K →
      (n.divisors.card : ℝ) ^ k ≤ (M : ℝ) ^ (K + 1) := by
  obtain ⟨Mfactor, hfactor⟩ := divisor_log_factor_le_scale_eventually K k
  refine ⟨max Mfactor 1, ?_⟩
  intro M hM n hnM
  have hMone : 1 ≤ M := (le_max_right _ _).trans hM
  by_cases hn : n = 0
  · subst n
    simp only [Nat.divisors_zero, Finset.card_empty, Nat.cast_zero]
    by_cases hk : k = 0
    · subst k
      exact_mod_cast Nat.one_le_pow (K + 1) M hMone
    · simp [zero_pow hk]
  · have hnpos : 0 < n := by omega
    have hfinite : (n.divisors.card : ℝ) ^ k ≤
        ((Nat.log 2 n + 1 : ℕ) : ℝ) ^ (k * 2 ^ k) * (n : ℝ) := by
      exact_mod_cast card_divisors_pow_le_log_power_mul_self hnpos k
    have hlog := hfactor M ((le_max_left _ _).trans hM) n hnpos hnM
    calc
      _ ≤ _ := hfinite
      _ ≤ (M : ℝ) * (M : ℝ) ^ K := mul_le_mul hlog (by exact_mod_cast hnM) (by positivity) (by positivity)
      _ = _ := (pow_succ' _ _).symm

/-- Unconditional divisor subpolynomiality, with the threshold before every coefficient in the box. -/
theorem card_divisors_le_rpow_eventually (K : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ n : ℕ, n ≤ M ^ K →
      (n.divisors.card : ℝ) ≤ (M : ℝ) ^ epsilon := by
  obtain ⟨k : ℕ, hk⟩ := exists_nat_gt (((K + 1 : ℕ) : ℝ) / epsilon)
  have hkpos : 0 < k := by
    have : (0 : ℝ) < k := (by positivity : (0 : ℝ) < ((K + 1 : ℕ) : ℝ) / epsilon).trans hk
    exact_mod_cast this
  obtain ⟨Mpower, hpower⟩ := card_divisors_pow_le_polynomial_eventually K k
  refine ⟨max Mpower 1, ?_⟩
  intro M hM n hnM
  have hMone : (1 : ℝ) ≤ M := by exact_mod_cast (le_max_right Mpower 1).trans hM
  have hroot := HostRealPowers.le_rpow_div_of_pow_le
    (by positivity : (0 : ℝ) ≤ (n.divisors.card : ℝ)) (by positivity : (0 : ℝ) ≤ M)
    hkpos (hpower M ((le_max_left _ _).trans hM) n hnM)
  have hfrac : (((K + 1 : ℕ) : ℝ) / k) ≤ epsilon := by
    apply (div_le_iff₀ (by exact_mod_cast hkpos : (0 : ℝ) < k)).mpr
    have h := (div_lt_iff₀ hepsilon).mp hk
    linarith
  exact hroot.trans (Real.rpow_le_rpow_of_exponent_le hMone hfrac)

end
end PaperC.V282.DivisorSubpolynomial
