import PaperC.Arithmetic.DefectCounting
import PaperC.Arithmetic.ChebyshevPrimeCount
import PaperC.Coding.CanonicalDefectCode

/-!
# Pointwise defect bound on a concrete integer interval

This file instantiates the canonical defect code with the actual finite set of
represented values in `[U, U + H]`.  It performs the finite enumeration,
chooses one square-defect representation for each value, and handles the two
small-cardinality cases omitted by the Hamming-bound branch.
-/

namespace PaperC
namespace IntervalDefectBound

open scoped BigOperators

/--
The represented `H`-defect values in the inclusive interval `[U, U + H]`.
-/
noncomputable def defectsInInterval (H U : ℕ) : Finset ℕ :=
  DefectCounting.defectValues
      (DefectCounting.smallPrimesUpTo H) (U + H) ∩
    Finset.Icc U (U + H)

@[simp]
theorem mem_defectsInInterval {H U n : ℕ} :
    n ∈ defectsInInterval H U ↔
      n ∈ DefectCounting.defectValues
          (DefectCounting.smallPrimesUpTo H) (U + H) ∧
        U ≤ n ∧ n ≤ U + H := by
  simp [defectsInInterval]

/--
The concrete finite pointwise conclusion of the Runge--code--Hamming
argument.  The `max` incorporates the independent-columns case and the case
where fewer than `2*t` values are present.

The remaining asymptotic step of Proposition 3.2 consists of choosing `t`
and bounding `PrimesUpTo.count H`.
-/
theorem card_defectsInInterval_lt_of_log
    {H U t : ℕ}
    (hH : 2 ≤ H)
    (hU : 2 * H ≤ U)
    (ht : 1 ≤ t)
    (hlog :
      (4 * t : ℝ) *
          Real.log (128 * (2 * t) * H) <
        Real.log U) :
    (defectsInInterval H U).card <
      max (PrimesUpTo.count H + 1)
        (2 * t *
          2 ^ ((PrimesUpTo.count H + 1) / t + 1)) := by
  classical
  let D := defectsInInterval H U
  let m := D.card
  let enum : Fin m ≃ D := by
    simpa only [m] using D.equivFin.symm
  let f : Fin m → ℕ := fun i ↦ (enum i).1
  have hfmem : ∀ i, f i ∈ D := fun i ↦ (enum i).2
  have hfdefect :
      ∀ i, f i ∈
        DefectCounting.defectValues
          (DefectCounting.smallPrimesUpTo H) (U + H) := by
    intro i
    exact (mem_defectsInInterval.mp (by simpa only [D] using hfmem i)).1
  have hexists :
      ∀ i, ∃ support ⊆ DefectCounting.smallPrimesUpTo H,
        ∃ squarePart ≤ Nat.sqrt (U + H),
          f i = support.prod id * squarePart ^ 2 := by
    intro i
    exact
      (DefectCounting.mem_defectValues_iff.mp (hfdefect i)).2
  choose support hsupport squarePart hsquarePart hvalue using hexists
  let s : Fin m → ℕ := fun i ↦ (support i).prod id
  let a : Fin m → ℕ := squarePart
  have hrep : ∀ i, f i = s i * (a i) ^ 2 := by
    intro i
    simpa only [s, a] using hvalue i
  have hs : ∀ i, s i ≠ 0 := by
    intro i
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    have hpSmall := hsupport i hp
    exact (DefectCounting.mem_smallPrimesUpTo.mp hpSmall).1.ne_zero
  have hlower : ∀ i, U ≤ f i := by
    intro i
    exact
      (mem_defectsInInterval.mp (by simpa only [D] using hfmem i)).2.1
  have hupper : ∀ i, f i ≤ U + H := by
    intro i
    exact
      (mem_defectsInInterval.mp (by simpa only [D] using hfmem i)).2.2
  have ha : ∀ i, a i ≠ 0 := by
    intro i hai
    have hfiPos : 0 < f i := by
      have hUPos : 0 < U := by omega
      exact hUPos.trans_le (hlower i)
    have hz : f i = 0 := by
      rw [hrep i, hai]
      norm_num
    omega
  have hbounded :
      ∀ i p, Nat.Prime p → p ∣ s i → p ≤ H := by
    intro i p hp hps
    obtain ⟨q, hqSupport, hpq⟩ :=
      (hp.prime.dvd_finset_prod_iff id).mp (by simpa only [s] using hps)
    have hqSmall := hsupport i hqSupport
    have hqPrime := (DefectCounting.mem_smallPrimesUpTo.mp hqSmall).1
    have hpqEq : p = q :=
      (Nat.prime_dvd_prime_iff_eq hp hqPrime).mp hpq
    subst q
    exact (DefectCounting.mem_smallPrimesUpTo.mp hqSmall).2
  have hinjective : Function.Injective f := by
    intro i j hij
    apply enum.injective
    apply Subtype.ext
    exact hij
  by_cases hrows : PrimesUpTo.count H + 1 ≤ m
  · by_cases htm : 2 * t ≤ m
    · have hmain :
          m <
            2 * t *
              2 ^ ((PrimesUpTo.count H + 1) / t + 1) := by
        apply CanonicalDefectCode.length_lt_of_log
          f s a hrep hs ha hbounded hinjective hlower hupper
        · omega
        · exact hU
        · exact ht
        · exact hlog
        · exact htm
        · exact hrows
      simpa only [m] using
        hmain.trans_le (le_max_right _ _)
    · have hsmall : m < 2 * t := Nat.lt_of_not_ge htm
      have hfactor :
          2 * t ≤
            2 * t *
              2 ^ ((PrimesUpTo.count H + 1) / t + 1) := by
        have hone :
            1 ≤ 2 ^ ((PrimesUpTo.count H + 1) / t + 1) := by
          have hpos :
              0 < 2 ^ ((PrimesUpTo.count H + 1) / t + 1) :=
            pow_pos (by norm_num) _
          omega
        simpa using Nat.mul_le_mul_left (2 * t) hone
      simpa only [m] using
        hsmall.trans_le (hfactor.trans (le_max_right _ _))
  · have hsmall : m < PrimesUpTo.count H + 1 :=
      Nat.lt_of_not_ge hrows
    simpa only [m] using
      hsmall.trans_le (le_max_left _ _)

/--
Constant-ratio form of the pointwise estimate.  If the number of prime rows
is at most `A * t`, the exponential factor in the Hamming conclusion is a
constant depending only on `A`.
-/
theorem card_defectsInInterval_lt_of_log_of_count_ratio
    {H U t A : ℕ}
    (hH : 2 ≤ H)
    (hU : 2 * H ≤ U)
    (ht : 1 ≤ t)
    (hlog :
      (4 * t : ℝ) *
          Real.log (128 * (2 * t) * H) <
        Real.log U)
    (hratio : PrimesUpTo.count H + 1 ≤ A * t) :
    (defectsInInterval H U).card <
      2 * t * 2 ^ (A + 1) := by
  have hbase :=
    card_defectsInInterval_lt_of_log hH hU ht hlog
  apply hbase.trans_le
  apply max_le
  · have hpowAux : ∀ n : ℕ, n ≤ 2 ^ (n + 1) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
          calc
            n + 1 ≤ 2 ^ (n + 1) + 1 :=
              Nat.add_le_add_right ih 1
            _ ≤ 2 ^ (n + 1) + 2 ^ (n + 1) := by
              exact Nat.add_le_add_left
                (by
                  have hpos : 0 < 2 ^ (n + 1) :=
                    pow_pos (by norm_num) _
                  omega)
                _
            _ = 2 ^ (n + 1 + 1) := by
              rw [pow_succ]
              ring
    have hpow : A ≤ 2 ^ (A + 1) := hpowAux A
    calc
      PrimesUpTo.count H + 1 ≤ A * t := hratio
      _ ≤ 2 ^ (A + 1) * t :=
        Nat.mul_le_mul_right t hpow
      _ ≤ 2 * t * 2 ^ (A + 1) := by
        have htTwo : t ≤ 2 * t := by omega
        simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
          Nat.mul_le_mul_right (2 ^ (A + 1)) htTwo
  · have hdiv :
        (PrimesUpTo.count H + 1) / t ≤ A := by
      apply Nat.div_le_of_le_mul'
      simpa [Nat.mul_comm] using hratio
    have hexponent :
        (PrimesUpTo.count H + 1) / t + 1 ≤ A + 1 :=
      Nat.add_le_add_right hdiv 1
    exact Nat.mul_le_mul_left (2 * t)
      (Nat.pow_le_pow_right (by omega) hexponent)

/--
Chebyshev-specialized constant-ratio form.  The explicit budget is stated
only in terms of `H`, `t`, and the base-two logarithm; the prime count itself
has disappeared.
-/
theorem card_defectsInInterval_lt_of_log_of_chebyshev_budget
    {H U t A : ℕ}
    (hH : 4 ≤ H)
    (hU : 2 * H ≤ U)
    (ht : 1 ≤ t)
    (hlog :
      (4 * t : ℝ) *
          Real.log (128 * (2 * t) * H) <
        Real.log U)
    (hbudget :
      (7 * H) / Nat.log 2 H + 1 ≤ A * t) :
    (defectsInInterval H U).card <
      2 * t * 2 ^ (A + 1) := by
  apply card_defectsInInterval_lt_of_log_of_count_ratio
    (by omega) hU ht hlog
  have hcount :=
    ChebyshevPrimeCount.count_le_seven_mul_div_log hH
  omega

/--
Completely explicit integer-radius form.  The coding radius is the floor
`RungeLogarithmicGrowth.cappedRadius U H T`; only its nontriviality, advertised
cap, and the elementary Chebyshev budget remain as finite side conditions.
-/
theorem card_defectsInInterval_lt_of_cappedRadius
    {H U T A : ℕ}
    (hH : 4 ≤ H)
    (hU : 2 * H ≤ U)
    (hT : 1 ≤ T)
    (hpositive :
      1 ≤ RungeLogarithmicGrowth.cappedRadius U H T)
    (hbelow :
      RungeLogarithmicGrowth.cappedRadius U H T ≤ T)
    (hbudget :
      (7 * H) / Nat.log 2 H + 1 ≤
        A * RungeLogarithmicGrowth.cappedRadius U H T) :
    (defectsInInterval H U).card <
      2 * RungeLogarithmicGrowth.cappedRadius U H T *
        2 ^ (A + 1) := by
  apply card_defectsInInterval_lt_of_log_of_chebyshev_budget
    hH hU hpositive
  · apply RungeLogarithmicGrowth.cappedRadius_log_endpoint
    · omega
    · omega
    · exact hT
    · exact hpositive
    · exact hbelow
  · exact hbudget

end IntervalDefectBound
end PaperC
