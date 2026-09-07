import PaperCV282.PrimeEulerRankin
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.PrimeCounting

/-!
# Partial summation for the actual weighted prime sum

The counting function is the standard number of primes at most floor(t).
Abel summation is applied to its prime indicator, not to an abstract
sequence assumed to have the desired weighted asymptotic.
-/

namespace PaperC.V282.PrimeEulerAbel

open DefectCounting PrimeEulerRankin MeasureTheory

noncomputable section

/-- The ordinary prime-counting step function at a real argument. -/
def primeCountingReal (t : ℝ) : ℝ := (Nat.primeCounting ⌊t⌋₊ : ℝ)

/-- The old small-prime support is exactly mathlib's standard primesLE. -/
theorem smallPrimesUpTo_eq_primesLE (X : ℕ) : smallPrimesUpTo X = Nat.primesLE X := by
  ext p
  simp only [mem_smallPrimesUpTo, Nat.mem_primesLE, and_comm]

/-- Counting the actual prime indicator gives pi(X), exactly. -/
theorem sum_prime_indicator_eq (X : ℕ) :
    (∑ k ∈ Finset.Icc 0 X, if k.Prime then (1 : ℝ) else 0) = (Nat.primeCounting X : ℝ) := by
  rw [← Nat.primesLE_card_eq_primeCounting, Nat.primesLE_eq_filter_Icc_zero, Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> norm_num

/-- The weighted sum uses exactly that same indicator. -/
theorem rankinPrimeSum_eq_indicator_sum (X : ℕ) (zeta : ℝ) :
    rankinPrimeSum X zeta = ∑ k ∈ Finset.Icc 0 X,
      (k : ℝ) ^ (-1 + zeta) * (if k.Prime then (1 : ℝ) else 0) := by
  unfold rankinPrimeSum
  rw [smallPrimesUpTo_eq_primesLE, Nat.primesLE_eq_filter_Icc_zero, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> simp

/-- A difference of the two literal prime sums is the sum over the intervening interval. -/
theorem rankinPrimeSum_sub_eq_tail {a b : ℝ} (hab : a ≤ b) (zeta : ℝ) :
    rankinPrimeSum ⌊b⌋₊ zeta - rankinPrimeSum ⌊a⌋₊ zeta =
      ∑ k ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, (k : ℝ) ^ (-1 + zeta) * (if k.Prime then (1 : ℝ) else 0) := by
  have hfloor := Nat.floor_mono hab
  have hunion : Finset.Icc 0 ⌊a⌋₊ ∪ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊ = Finset.Icc 0 ⌊b⌋₊ := by
    ext k
    simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hdisj : Disjoint (Finset.Icc 0 ⌊a⌋₊) (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊) := by
    apply Finset.disjoint_left.mpr
    intro k hk hk'
    have := Finset.mem_Icc.mp hk
    have := Finset.mem_Ioc.mp hk'
    omega
  rw [rankinPrimeSum_eq_indicator_sum, rankinPrimeSum_eq_indicator_sum, ← hunion, Finset.sum_union hdisj]
  ring

/-- The power weight has its actual derivative on every positive interval. -/
theorem hasDerivAt_rankinWeight {t : ℝ} (ht : 0 < t) (zeta : ℝ) :
    HasDerivAt (fun t : ℝ => t ^ (-1 + zeta))
      ((-1 + zeta) * t ^ (-2 + zeta)) t := by
  simpa only [show (-1 + zeta) - 1 = -2 + zeta by ring] using
    (Real.hasDerivAt_rpow_const (x := t) (p := -1 + zeta) (Or.inl ht.ne'))

/-- Abel's exact identity on an arbitrary positive real interval, retaining both boundary terms. -/
theorem rankinPrimeSum_partial_summation {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (zeta : ℝ) :
    rankinPrimeSum ⌊b⌋₊ zeta - rankinPrimeSum ⌊a⌋₊ zeta =
      b ^ (-1 + zeta) * primeCountingReal b - a ^ (-1 + zeta) * primeCountingReal a -
        ∫ t in Set.Ioc a b, ((-1 + zeta) * t ^ (-2 + zeta)) * primeCountingReal t := by
  have hderiv (t : ℝ) (ht : t ∈ Set.Icc a b) :
      deriv (fun t : ℝ => t ^ (-1 + zeta)) t = (-1 + zeta) * t ^ (-2 + zeta) :=
    (hasDerivAt_rankinWeight (ha.trans_le ht.1) zeta).deriv
  have hcont : ContinuousOn (fun t : ℝ => (-1 + zeta) * t ^ (-2 + zeta)) (Set.Icc a b) := by
    apply continuousOn_const.mul (continuousOn_id.rpow_const ?_)
    intro t ht
    exact Or.inl (ha.trans_le ht.1).ne'
  have hdcont : ContinuousOn (deriv (fun t : ℝ => t ^ (-1 + zeta))) (Set.Icc a b) := by
    apply hcont.congr
    intro t ht
    exact hderiv t ht
  have habel := sum_mul_eq_sub_sub_integral_mul (fun k : ℕ => if k.Prime then (1 : ℝ) else 0)
    ha.le hab (fun t ht => (hasDerivAt_rankinWeight (ha.trans_le ht.1) zeta).differentiableAt)
    hdcont.integrableOn_Icc
  rw [rankinPrimeSum_sub_eq_tail hab]
  simp_rw [sum_prime_indicator_eq] at habel
  calc
    _ = _ := habel
    _ = _ := by
      congr 1
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
      intro t ht
      change deriv (fun t : ℝ => t ^ (-1 + zeta)) t * primeCountingReal t =
        ((-1 + zeta) * t ^ (-2 + zeta)) * primeCountingReal t
      rw [hderiv t ⟨ht.1.le, ht.2⟩]

end
end PaperC.V282.PrimeEulerAbel
