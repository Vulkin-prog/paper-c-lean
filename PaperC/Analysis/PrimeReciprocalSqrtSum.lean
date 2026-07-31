import PaperC.Analysis.SmoothEulerProduct
import PaperC.Arithmetic.DyadicPrimeReciprocalSums
import PaperC.Probability.BadStartCount
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Positivity

/-!
# A prime-sensitive reciprocal-square-root sum

The all-integer estimate

`∑_{n≤H} n⁻¹/² ≤ 2 √H`

is too coarse at the terminal cutoff of Section 13.  This file combines that
estimate with the elementary Chebyshev bound already proved in
`ChebyshevPrimeCount` to obtain a genuinely prime-sensitive finite bound.

For `B ≥ 4`, every dyadic shell `(Y,2Y]`, `B ≤ Y`, contributes at most

`14 √Y / log₂ B`.

The geometric growth of the square roots is retained rather than replaced by
the number of shells.  This gives the explicit estimate

`∑_{B<p≤B2^K} p⁻¹/² ≤ 56 √(B2^K) / log₂ B`.

Taking

`B = 2^(⌊log₂ H⌋/2)`

and covering `H` by the next power of two yields, for `H ≥ 16`,

`∑_{p≤H} p⁻¹/²
  ≤ 2 √B + 56 √(2^(⌊log₂ H⌋+1)) / (⌊log₂ H⌋/2)`.

Thus the two visible terms have respectively the expected sizes
`O(H^(1/4))` and `O(√H / log H)`.  Exponentiating gives the corresponding
finite Euler-product envelope used in Lemma 13.3.

No prime number theorem, asymptotic assumption, or external bridge is used.
-/

namespace PaperC
namespace PrimeReciprocalSqrtSum

open Finset
open scoped BigOperators

open DyadicPrimeReciprocalSums

private theorem two_le_log_two {B : ℕ} (hB : 4 ≤ B) :
    2 ≤ Nat.log 2 B := by
  apply Nat.le_log_of_pow_le (by norm_num)
  norm_num
  exact hB

private theorem primesBetween_subset_smallPrimesUpTo (B X : ℕ) :
    primesBetween B X ⊆ DefectCounting.smallPrimesUpTo X :=
  Finset.filter_subset _ _

private theorem card_primesBetween_le_count (B X : ℕ) :
    (primesBetween B X).card ≤ PrimesUpTo.count X := by
  calc
    (primesBetween B X).card ≤
        (DefectCounting.smallPrimesUpTo X).card :=
      Finset.card_le_card (primesBetween_subset_smallPrimesUpTo B X)
    _ = PrimesUpTo.count X :=
      (PrimeCountBridge.count_eq_card_smallPrimesUpTo X).symm

/--
The Chebyshev cardinality estimate for one shell `(Y,2Y]`, with the
logarithm frozen at the lower reference scale `B`.
-/
theorem log_mul_card_primesBetween_le
    {B Y : ℕ} (hB : 4 ≤ B) (hBY : B ≤ Y) :
    Nat.log 2 B * (primesBetween Y (2 * Y)).card ≤ 14 * Y := by
  have hlog :
      Nat.log 2 B ≤ Nat.log 2 (2 * Y) :=
    Nat.log_mono_right (hBY.trans (by omega))
  have hcard :
      (primesBetween Y (2 * Y)).card ≤
        PrimesUpTo.count (2 * Y) :=
    card_primesBetween_le_count Y (2 * Y)
  calc
    Nat.log 2 B * (primesBetween Y (2 * Y)).card
        ≤ Nat.log 2 (2 * Y) * PrimesUpTo.count (2 * Y) :=
      Nat.mul_le_mul hlog hcard
    _ ≤ 7 * (2 * Y) :=
      ChebyshevPrimeCount.log_mul_count_le_seven_mul
        (H := 2 * Y) (by omega)
    _ = 14 * Y := by omega

/--
Prime-sensitive reciprocal-square-root estimate on one dyadic shell.
-/
theorem sum_inv_sqrt_primesBetween_le
    {B Y : ℕ} (hB : 4 ≤ B) (hBY : B ≤ Y) :
    (∑ p ∈ primesBetween Y (2 * Y), (Real.sqrt p)⁻¹) ≤
      14 * Real.sqrt Y / (Nat.log 2 B : ℝ) := by
  have hYposNat : 0 < Y := by omega
  have hYpos : (0 : ℝ) < Real.sqrt Y :=
    Real.sqrt_pos.2 (Nat.cast_pos.mpr hYposNat)
  have hlogPosNat : 0 < Nat.log 2 B := by
    have := two_le_log_two hB
    omega
  have hlogPos : (0 : ℝ) < (Nat.log 2 B : ℝ) :=
    Nat.cast_pos.mpr hlogPosNat
  have hterm :
      ∀ p ∈ primesBetween Y (2 * Y),
        (Real.sqrt p)⁻¹ ≤ (Real.sqrt Y)⁻¹ := by
    intro p hp
    have hpPos : (0 : ℝ) < Real.sqrt p := by
      exact Real.sqrt_pos.2
        (Nat.cast_pos.mpr (mem_primesBetween.mp hp).1.pos)
    exact (inv_le_inv₀ hpPos hYpos).2
      (Real.sqrt_le_sqrt
        (Nat.cast_le.mpr (mem_primesBetween.mp hp).2.1.le))
  have hsum :
      (∑ p ∈ primesBetween Y (2 * Y), (Real.sqrt p)⁻¹) ≤
        ((primesBetween Y (2 * Y)).card : ℝ) /
          Real.sqrt Y := by
    calc
      (∑ p ∈ primesBetween Y (2 * Y), (Real.sqrt p)⁻¹)
          ≤ ∑ _p ∈ primesBetween Y (2 * Y),
              (Real.sqrt Y)⁻¹ :=
        Finset.sum_le_sum hterm
      _ = ((primesBetween Y (2 * Y)).card : ℝ) /
          Real.sqrt Y := by
        simp [div_eq_mul_inv]
  have hcardR :
      (Nat.log 2 B : ℝ) *
          ((primesBetween Y (2 * Y)).card : ℝ) ≤
        14 * (Y : ℝ) := by
    exact_mod_cast log_mul_card_primesBetween_le hB hBY
  calc
    (∑ p ∈ primesBetween Y (2 * Y), (Real.sqrt p)⁻¹)
        ≤ ((primesBetween Y (2 * Y)).card : ℝ) /
            Real.sqrt Y :=
      hsum
    _ ≤ 14 * Real.sqrt Y / (Nat.log 2 B : ℝ) := by
      rw [div_le_div_iff₀ hYpos hlogPos]
      calc
        ((primesBetween Y (2 * Y)).card : ℝ) *
              (Nat.log 2 B : ℝ)
            = (Nat.log 2 B : ℝ) *
                ((primesBetween Y (2 * Y)).card : ℝ) := by ring
        _ ≤ 14 * (Y : ℝ) := hcardR
        _ = 14 * Real.sqrt Y * Real.sqrt Y := by
          calc
            14 * (Y : ℝ) =
                14 * (Real.sqrt Y * Real.sqrt Y) := by
              rw [Real.mul_self_sqrt (Nat.cast_nonneg Y)]
            _ = 14 * Real.sqrt Y * Real.sqrt Y := by ring

private theorem primesBetween_double_eq_union
    {B Y : ℕ} (hBY : B ≤ Y) :
    primesBetween B (2 * Y) =
      primesBetween B Y ∪ primesBetween Y (2 * Y) := by
  ext p
  simp only [mem_primesBetween, Finset.mem_union]
  constructor
  · rintro ⟨hp, hBp, hp2Y⟩
    by_cases hpY : p ≤ Y
    · exact Or.inl ⟨hp, hBp, hpY⟩
    · exact Or.inr ⟨hp, lt_of_not_ge hpY, hp2Y⟩
  · rintro (hp | hp)
    · exact ⟨hp.1, hp.2.1, hp.2.2.trans (by omega)⟩
    · exact ⟨hp.1, hBY.trans_lt hp.2.1, hp.2.2⟩

private theorem disjoint_primesBetween_adjacent (B Y : ℕ) :
    Disjoint (primesBetween B Y) (primesBetween Y (2 * Y)) := by
  rw [Finset.disjoint_left]
  intro p hp₁ hp₂
  have hpY := (mem_primesBetween.mp hp₁).2.2
  have hYp := (mem_primesBetween.mp hp₂).2.1
  omega

private theorem dyadicPrimes_succ_eq_union (B K : ℕ) :
    dyadicPrimes B (K + 1) =
      dyadicPrimes B K ∪
        primesBetween (B * 2 ^ K) (2 * (B * 2 ^ K)) := by
  have hscale : B ≤ B * 2 ^ K :=
    Nat.le_mul_of_pos_right B (by positivity)
  unfold dyadicPrimes
  rw [show B * 2 ^ (K + 1) = 2 * (B * 2 ^ K) by
    rw [pow_succ]
    ring]
  exact primesBetween_double_eq_union hscale

private theorem disjoint_dyadicPrimes_shell (B K : ℕ) :
    Disjoint (dyadicPrimes B K)
      (primesBetween (B * 2 ^ K) (2 * (B * 2 ^ K))) := by
  unfold dyadicPrimes
  exact disjoint_primesBetween_adjacent B (B * 2 ^ K)

private theorem five_le_four_mul_sqrt_two :
    (5 : ℝ) ≤ 4 * Real.sqrt 2 := by
  have hsqrt : 0 ≤ Real.sqrt (2 : ℝ) := Real.sqrt_nonneg _
  have hsq : (Real.sqrt (2 : ℝ)) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  nlinarith

private theorem seventy_mul_sqrt_le_fifty_six_mul_sqrt_double
    (Y : ℕ) :
    70 * Real.sqrt Y ≤
      56 * Real.sqrt ((2 * Y : ℕ) : ℝ) := by
  have hsqrtY : 0 ≤ Real.sqrt (Y : ℝ) := Real.sqrt_nonneg _
  have hscaled :
      5 * Real.sqrt Y ≤
        (4 * Real.sqrt 2) * Real.sqrt Y :=
    mul_le_mul_of_nonneg_right five_le_four_mul_sqrt_two hsqrtY
  have hsqrtDouble :
      Real.sqrt (2 * (Y : ℝ)) =
        Real.sqrt 2 * Real.sqrt Y := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  norm_cast at hsqrtDouble
  rw [hsqrtDouble]
  nlinarith

/--
Explicit reciprocal-square-root estimate on the dyadic interval
`(B, B*2^K]`.

The constant `56` comes from the shell constant `14` and the elementary
geometric inequality `5 ≤ 4√2`.
-/
theorem sum_inv_sqrt_dyadicPrimes_le
    (B K : ℕ) (hB : 4 ≤ B) :
    (∑ p ∈ dyadicPrimes B K, (Real.sqrt p)⁻¹) ≤
      56 * Real.sqrt ((B * 2 ^ K : ℕ) : ℝ) /
        (Nat.log 2 B : ℝ) := by
  have hlogPosNat : 0 < Nat.log 2 B := by
    have := two_le_log_two hB
    omega
  have hlogPos : (0 : ℝ) < (Nat.log 2 B : ℝ) :=
    Nat.cast_pos.mpr hlogPosNat
  induction K with
  | zero =>
      simp [dyadicPrimes]
      positivity
  | succ K ih =>
      have hscale : B ≤ B * 2 ^ K :=
        Nat.le_mul_of_pos_right B (by positivity)
      have hshell :=
        sum_inv_sqrt_primesBetween_le hB hscale
      rw [show K + 1 = Nat.succ K by omega,
        dyadicPrimes_succ_eq_union,
        Finset.sum_union (disjoint_dyadicPrimes_shell B K)]
      calc
        (∑ p ∈ dyadicPrimes B K, (Real.sqrt p)⁻¹) +
              ∑ p ∈ primesBetween (B * 2 ^ K)
                (2 * (B * 2 ^ K)), (Real.sqrt p)⁻¹
            ≤ 56 * Real.sqrt ((B * 2 ^ K : ℕ) : ℝ) /
                  (Nat.log 2 B : ℝ) +
                14 * Real.sqrt ((B * 2 ^ K : ℕ) : ℝ) /
                  (Nat.log 2 B : ℝ) :=
          add_le_add ih hshell
        _ = 70 * Real.sqrt ((B * 2 ^ K : ℕ) : ℝ) /
            (Nat.log 2 B : ℝ) := by ring
        _ ≤ 56 * Real.sqrt (((2 * (B * 2 ^ K) : ℕ)) : ℝ) /
            (Nat.log 2 B : ℝ) := by
          exact (div_le_div_iff_of_pos_right hlogPos).2
            (seventy_mul_sqrt_le_fifty_six_mul_sqrt_double
              (B * 2 ^ K))
        _ = 56 * Real.sqrt ((B * 2 ^ (Nat.succ K) : ℕ) : ℝ) /
            (Nat.log 2 B : ℝ) := by
          congr 3
          norm_num [pow_succ]
          ring

/-! ## The square-root cutoff and a global prime sum -/

/-- Lower cutoff used to split the primes at the square-root scale. -/
def rootCutoff (H : ℕ) : ℕ :=
  2 ^ (Nat.log 2 H / 2)

/-- Number of dyadic shells from `rootCutoff H` to the next power of two. -/
def coverExponent (H : ℕ) : ℕ :=
  Nat.log 2 H + 1 - Nat.log 2 H / 2

/-- The power-of-two endpoint of the dyadic cover. -/
def dyadicCover (H : ℕ) : ℕ :=
  rootCutoff H * 2 ^ coverExponent H

theorem rootCutoff_eq (H : ℕ) :
    rootCutoff H = 2 ^ (Nat.log 2 H / 2) :=
  rfl

theorem dyadicCover_eq_two_pow (H : ℕ) :
    dyadicCover H = 2 ^ (Nat.log 2 H + 1) := by
  unfold dyadicCover rootCutoff coverExponent
  rw [← pow_add]
  congr 1
  omega

theorem le_dyadicCover (H : ℕ) :
    H ≤ dyadicCover H := by
  rw [dyadicCover_eq_two_pow]
  exact (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) H).le

theorem dyadicCover_le_two_mul {H : ℕ} (hH : 1 ≤ H) :
    dyadicCover H ≤ 2 * H := by
  rw [dyadicCover_eq_two_pow, pow_succ]
  simpa [Nat.mul_comm] using
    Nat.mul_le_mul_left 2
      (Nat.pow_log_le_self 2 (ne_of_gt hH))

/--
The lower cutoff really is at most the square-root scale:
`(rootCutoff H)² ≤ H`.
-/
theorem rootCutoff_sq_le {H : ℕ} (hH : 1 ≤ H) :
    rootCutoff H ^ 2 ≤ H := by
  unfold rootCutoff
  calc
    (2 ^ (Nat.log 2 H / 2)) ^ 2 =
        2 ^ ((Nat.log 2 H / 2) * 2) := by
      rw [pow_mul]
    _ ≤ 2 ^ (Nat.log 2 H) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    _ ≤ H :=
      Nat.pow_log_le_self 2 (ne_of_gt hH)

theorem four_le_rootCutoff {H : ℕ} (hH : 16 ≤ H) :
    4 ≤ rootCutoff H := by
  have hlog : 4 ≤ Nat.log 2 H := by
    apply Nat.le_log_of_pow_le (by norm_num)
    norm_num
    exact hH
  change 2 ^ 2 ≤ 2 ^ (Nat.log 2 H / 2)
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem log_rootCutoff (H : ℕ) :
    Nat.log 2 (rootCutoff H) = Nat.log 2 H / 2 := by
  simp [rootCutoff, Nat.log_pow (by norm_num : 1 < 2)]

private def lowPrimes (H : ℕ) : Finset ℕ :=
  (DefectCounting.smallPrimesUpTo H).filter fun p ↦ p ≤ rootCutoff H

private def highPrimes (H : ℕ) : Finset ℕ :=
  (DefectCounting.smallPrimesUpTo H).filter fun p ↦ ¬ p ≤ rootCutoff H

private theorem sum_lowPrimes_le (H : ℕ) :
    (∑ p ∈ lowPrimes H, (Real.sqrt p)⁻¹) ≤
      2 * Real.sqrt (rootCutoff H) := by
  calc
    (∑ p ∈ lowPrimes H, (Real.sqrt p)⁻¹) ≤
        ∑ n ∈ Finset.Icc 1 (rootCutoff H),
          (Real.sqrt n)⁻¹ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        have hp' := Finset.mem_filter.mp hp
        have hprime :=
          DefectCounting.mem_smallPrimesUpTo.mp hp'.1
        exact Finset.mem_Icc.mpr ⟨hprime.1.pos, hp'.2⟩
      · intro n _ _
        exact inv_nonneg.mpr (Real.sqrt_nonneg n)
    _ ≤ 2 * Real.sqrt (rootCutoff H) :=
      sum_Icc_inv_sqrt_le (rootCutoff H)

private theorem highPrimes_subset_dyadicPrimes (H : ℕ) :
    highPrimes H ⊆
      dyadicPrimes (rootCutoff H) (coverExponent H) := by
  intro p hp
  have hp' := Finset.mem_filter.mp hp
  have hprime :=
    DefectCounting.mem_smallPrimesUpTo.mp hp'.1
  rw [mem_dyadicPrimes]
  exact ⟨hprime.1, lt_of_not_ge hp'.2,
    hprime.2.trans (le_dyadicCover H)⟩

private theorem sum_highPrimes_le {H : ℕ} (hH : 16 ≤ H) :
    (∑ p ∈ highPrimes H, (Real.sqrt p)⁻¹) ≤
      56 * Real.sqrt (dyadicCover H) /
        ((Nat.log 2 H / 2 : ℕ) : ℝ) := by
  calc
    (∑ p ∈ highPrimes H, (Real.sqrt p)⁻¹) ≤
        ∑ p ∈ dyadicPrimes (rootCutoff H) (coverExponent H),
          (Real.sqrt p)⁻¹ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact highPrimes_subset_dyadicPrimes H
      · intro p _ _
        exact inv_nonneg.mpr (Real.sqrt_nonneg p)
    _ ≤ 56 *
          Real.sqrt
            ((rootCutoff H * 2 ^ coverExponent H : ℕ) : ℝ) /
            (Nat.log 2 (rootCutoff H) : ℝ) :=
      sum_inv_sqrt_dyadicPrimes_le
        (rootCutoff H) (coverExponent H) (four_le_rootCutoff hH)
    _ = 56 * Real.sqrt (dyadicCover H) /
          ((Nat.log 2 H / 2 : ℕ) : ℝ) := by
      rw [log_rootCutoff]
      simp [dyadicCover]

private theorem low_add_high_sum (H : ℕ) :
    (∑ p ∈ lowPrimes H, (Real.sqrt p)⁻¹) +
        (∑ p ∈ highPrimes H, (Real.sqrt p)⁻¹) =
      ∑ p ∈ DefectCounting.smallPrimesUpTo H,
        (Real.sqrt p)⁻¹ := by
  simpa [lowPrimes, highPrimes] using
    (Finset.sum_filter_add_sum_filter_not
      (DefectCounting.smallPrimesUpTo H)
      (fun p ↦ p ≤ rootCutoff H)
      (fun p ↦ (Real.sqrt p)⁻¹))

/--
Global explicit prime-sensitive estimate.  The first summand is the
`O(H^(1/4))` low-prime contribution; the second is the
`O(√H / log H)` dyadic contribution.
-/
theorem sum_smallPrimesUpTo_inv_sqrt_le
    {H : ℕ} (hH : 16 ≤ H) :
    (∑ p ∈ DefectCounting.smallPrimesUpTo H,
        (Real.sqrt p)⁻¹) ≤
      2 * Real.sqrt (rootCutoff H) +
        56 * Real.sqrt (dyadicCover H) /
          ((Nat.log 2 H / 2 : ℕ) : ℝ) := by
  rw [← low_add_high_sum H]
  exact add_le_add (sum_lowPrimes_le H) (sum_highPrimes_le hH)

/--
Slightly coarser form with the dyadic endpoint replaced by `2H`.  Together
with `rootCutoff_sq_le`, this displays directly the finite
`O(H^(1/4)) + O(√H / log H)` shape.
-/
theorem sum_smallPrimesUpTo_inv_sqrt_le_two_mul
    {H : ℕ} (hH : 16 ≤ H) :
    (∑ p ∈ DefectCounting.smallPrimesUpTo H,
        (Real.sqrt p)⁻¹) ≤
      2 * Real.sqrt (rootCutoff H) +
        56 * Real.sqrt (2 * H) /
          ((Nat.log 2 H / 2 : ℕ) : ℝ) := by
  have hqPosNat : 0 < Nat.log 2 H / 2 := by
    have hlog : 4 ≤ Nat.log 2 H := by
      apply Nat.le_log_of_pow_le (by norm_num)
      norm_num
      exact hH
    omega
  have hqNonneg :
      (0 : ℝ) ≤ ((Nat.log 2 H / 2 : ℕ) : ℝ) :=
    (Nat.cast_pos.mpr hqPosNat).le
  have hcoverCast :
      (dyadicCover H : ℝ) ≤ 2 * (H : ℝ) := by
    exact_mod_cast
      dyadicCover_le_two_mul (show 1 ≤ H by omega)
  have hcover :
      Real.sqrt (dyadicCover H) ≤ Real.sqrt (2 * H) :=
    Real.sqrt_le_sqrt hcoverCast
  have hsecond :
      56 * Real.sqrt (dyadicCover H) /
          ((Nat.log 2 H / 2 : ℕ) : ℝ) ≤
        56 * Real.sqrt (2 * H) /
          ((Nat.log 2 H / 2 : ℕ) : ℝ) := by
    apply div_le_div_of_nonneg_right _ hqNonneg
    exact mul_le_mul_of_nonneg_left hcover (by norm_num)
  exact (sum_smallPrimesUpTo_inv_sqrt_le hH).trans
    (add_le_add_right hsecond _)

/--
The corresponding Euler-product envelope, in reciprocal-square-root
notation.
-/
theorem prod_smallPrimesUpTo_one_add_inv_sqrt_le_primeSensitive
    {H : ℕ} (hH : 16 ≤ H) :
    (∏ p ∈ DefectCounting.smallPrimesUpTo H,
        (1 + (Real.sqrt p)⁻¹)) ≤
      Real.exp
        (2 * Real.sqrt (rootCutoff H) +
          56 * Real.sqrt (dyadicCover H) /
            ((Nat.log 2 H / 2 : ℕ) : ℝ)) := by
  calc
    (∏ p ∈ DefectCounting.smallPrimesUpTo H,
        (1 + (Real.sqrt p)⁻¹))
        ≤ Real.exp
            (∑ p ∈ DefectCounting.smallPrimesUpTo H,
              (Real.sqrt p)⁻¹) :=
      prod_one_add_inv_sqrt_le_exp_sum
        (DefectCounting.smallPrimesUpTo H)
    _ ≤ Real.exp
        (2 * Real.sqrt (rootCutoff H) +
          56 * Real.sqrt (dyadicCover H) /
            ((Nat.log 2 H / 2 : ℕ) : ℝ)) :=
      Real.exp_le_exp.mpr (sum_smallPrimesUpTo_inv_sqrt_le hH)

/--
Euler-product envelope with the simpler endpoint `2H`.
-/
theorem prod_smallPrimesUpTo_one_add_inv_sqrt_le_primeSensitive_two_mul
    {H : ℕ} (hH : 16 ≤ H) :
    (∏ p ∈ DefectCounting.smallPrimesUpTo H,
        (1 + (Real.sqrt p)⁻¹)) ≤
      Real.exp
        (2 * Real.sqrt (rootCutoff H) +
          56 * Real.sqrt (2 * H) /
            ((Nat.log 2 H / 2 : ℕ) : ℝ)) := by
  calc
    (∏ p ∈ DefectCounting.smallPrimesUpTo H,
        (1 + (Real.sqrt p)⁻¹))
        ≤ Real.exp
            (∑ p ∈ DefectCounting.smallPrimesUpTo H,
              (Real.sqrt p)⁻¹) :=
      prod_one_add_inv_sqrt_le_exp_sum
        (DefectCounting.smallPrimesUpTo H)
    _ ≤ Real.exp
        (2 * Real.sqrt (rootCutoff H) +
          56 * Real.sqrt (2 * H) /
            ((Nat.log 2 H / 2 : ℕ) : ℝ)) :=
      Real.exp_le_exp.mpr (sum_smallPrimesUpTo_inv_sqrt_le_two_mul hH)

/-- The same prime-sensitive product bound in negative-half-power notation. -/
theorem prod_smallPrimesUpTo_one_add_rpow_neg_one_half_le_primeSensitive
    {H : ℕ} (hH : 16 ≤ H) :
    (∏ p ∈ DefectCounting.smallPrimesUpTo H,
        (1 + (p : ℝ) ^ (-(1 / 2 : ℝ)))) ≤
      Real.exp
        (2 * Real.sqrt (rootCutoff H) +
          56 * Real.sqrt (dyadicCover H) /
            ((Nat.log 2 H / 2 : ℕ) : ℝ)) := by
  simpa only [rpow_neg_one_half_eq_inv_sqrt _ (Nat.cast_nonneg _)] using
    prod_smallPrimesUpTo_one_add_inv_sqrt_le_primeSensitive hH

/--
Multiplicative interface for finite counting bounds: any nonnegative
prefactor can be carried across the prime-sensitive Euler-product estimate.
In particular the prefactor
`2 L √(dyadicCutoff N L)` from `BadStartCount` can be inserted directly.
-/
theorem mul_prod_smallPrimesUpTo_one_add_inv_sqrt_le_primeSensitive
    (A : ℝ) (hA : 0 ≤ A) {H : ℕ} (hH : 16 ≤ H) :
    A * (∏ p ∈ DefectCounting.smallPrimesUpTo H,
        (1 + (Real.sqrt p)⁻¹)) ≤
      A * Real.exp
        (2 * Real.sqrt (rootCutoff H) +
          56 * Real.sqrt (dyadicCover H) /
            ((Nat.log 2 H / 2 : ℕ) : ℝ)) :=
  mul_le_mul_of_nonneg_left
    (prod_smallPrimesUpTo_one_add_inv_sqrt_le_primeSensitive hH) hA

end PrimeReciprocalSqrtSum

namespace BadStartCount

open PrimeReciprocalSqrtSum

/--
Prime-sensitive finite completion of the counting estimate in Lemma 13.3.
It is obtained by composing `card_terminalBadStarts_cast_le_eulerProduct`
with the Euler-product theorem above.
-/
theorem card_terminalBadStarts_cast_le_primeSensitive
    {N L B : ℕ} (hN : 1 ≤ N) (hB : 16 ≤ B) :
    ((terminalBadStarts N L B).card : ℝ) ≤
      2 * L * Real.sqrt (dyadicCutoff N L) *
        Real.exp
          (2 * Real.sqrt (rootCutoff B) +
            56 * Real.sqrt (dyadicCover B) /
              ((Nat.log 2 B / 2 : ℕ) : ℝ)) := by
  calc
    ((terminalBadStarts N L B).card : ℝ) ≤
        2 * L * Real.sqrt (dyadicCutoff N L) *
          ∏ p ∈ DefectCounting.smallPrimesUpTo B,
            (1 + (Real.sqrt p)⁻¹) :=
      card_terminalBadStarts_cast_le_eulerProduct hN
    _ ≤ 2 * L * Real.sqrt (dyadicCutoff N L) *
        Real.exp
          (2 * Real.sqrt (rootCutoff B) +
            56 * Real.sqrt (dyadicCover B) /
              ((Nat.log 2 B / 2 : ℕ) : ℝ)) := by
      exact
        mul_prod_smallPrimesUpTo_one_add_inv_sqrt_le_primeSensitive
          (2 * L * Real.sqrt (dyadicCutoff N L)) (by positivity) hB

/--
The same bad-start bound with the dyadic cover simplified to `2B`.
-/
theorem card_terminalBadStarts_cast_le_primeSensitive_two_mul
    {N L B : ℕ} (hN : 1 ≤ N) (hB : 16 ≤ B) :
    ((terminalBadStarts N L B).card : ℝ) ≤
      2 * L * Real.sqrt (dyadicCutoff N L) *
        Real.exp
          (2 * Real.sqrt (rootCutoff B) +
            56 * Real.sqrt (2 * B) /
              ((Nat.log 2 B / 2 : ℕ) : ℝ)) := by
  calc
    ((terminalBadStarts N L B).card : ℝ) ≤
        2 * L * Real.sqrt (dyadicCutoff N L) *
          ∏ p ∈ DefectCounting.smallPrimesUpTo B,
            (1 + (Real.sqrt p)⁻¹) :=
      card_terminalBadStarts_cast_le_eulerProduct hN
    _ ≤ 2 * L * Real.sqrt (dyadicCutoff N L) *
        Real.exp
          (2 * Real.sqrt (rootCutoff B) +
            56 * Real.sqrt (2 * B) /
              ((Nat.log 2 B / 2 : ℕ) : ℝ)) := by
      apply mul_le_mul_of_nonneg_left
        (prod_smallPrimesUpTo_one_add_inv_sqrt_le_primeSensitive_two_mul hB)
      positivity

end BadStartCount
end PaperC
