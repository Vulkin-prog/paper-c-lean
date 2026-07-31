import PaperC.Combinatorics.AlignedCoreExclusion
import PaperC.Arithmetic.ChebyshevPrimeCount

set_option maxHeartbeats 800000

/-!
# A fixed-constant extraction for the aligned deep core

This module discharges one concrete numerical specialization of the
small-component extraction used in Paper C, Section 8.  At density
`3B < 16 c#`, the fixed cutoff `K = 43` leaves at least `B / 16`
exact-free residual components once `B ≥ 32`.

The constants are deliberately integral.  The abstract extraction pays two
components for exact units and at most `2B / 44` components for the support
tail.  The elementary lemma below checks that these costs fit below the
density margin.
-/

namespace PaperC
namespace AlignedDeepCoreExtraction

open Affine.CanonicalRationalCode
open AlignedCoreExclusion
open CanonicalResidualComponents

noncomputable section

/--
The arithmetic budget behind the fixed choice `K = 43`.

The conclusion is exactly the counting premise required by
`target_le_card_smallExactFreeResidualComponents`, with
`target = B / 16`.
-/
theorem fixed_cutoff_counting_budget
    {B residualCount : ℕ}
    (hB : 32 ≤ B)
    (hdensity : 3 * B < 16 * residualCount) :
    B / 16 + 2 + (2 * B) / (43 + 1) ≤ residualCount := by
  have htail :
      (2 * B) / (43 + 1) ≤ B / 16 := by
    calc
      (2 * B) / (43 + 1) = B / 22 := by
        simpa using
          (Nat.mul_div_mul_left B 22
            (by norm_num : 0 < (2 : ℕ)))
      _ ≤ B / 16 :=
        Nat.div_le_div_left (by norm_num : 16 ≤ 22)
          (by norm_num : 0 < 16)
  have hquotient :
      (B / 16) * 16 ≤ B :=
    Nat.div_mul_le_self B 16
  have hscaled :
      16 * (B / 16 + 2 + (2 * B) / (43 + 1)) ≤ 3 * B := by
    omega
  omega

/--
At the explicit binary-logarithm threshold `256`, Chebyshev's certified
prime-counting estimate leaves room for the two block-parity rows inside the
same `B/16` column budget.
-/
theorem prime_rows_le_one_sixteenth
    {B : ℕ}
    (hB : 64 ≤ B)
    (hlog : 256 ≤ Nat.log 2 B) :
    PrimesUpTo.count B + 2 ≤ B / 16 := by
  have hcount :
      PrimesUpTo.count B ≤ (7 * B) / Nat.log 2 B :=
    ChebyshevPrimeCount.count_le_seven_mul_div_log (by omega)
  have hdenominator :
      (7 * B) / Nat.log 2 B ≤ (7 * B) / 256 :=
    Nat.div_le_div_left hlog (by norm_num)
  have hbudget :
      (7 * B) / 256 + 2 ≤ B / 16 := by
    omega
  omega

/--
Fixed-constant extraction for an explicit primitive aligned channel.

If `B = L + 1 ≥ 32` and `c# > 3B/16`, then at least `B/16` residual
components are exact-free and supported on at most `43` vertices.
-/
theorem one_sixteenth_le_card_smallExactFreeResidualComponents
    {x y L a b : ℕ} {h : ℤ}
    (ha : 0 < a) (hb : 0 < b)
    (hab : a.Coprime b)
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hheight : h = (b : ℤ) * y - (a : ℤ) * x)
    (hB : 32 ≤ L + 1)
    (hdensity :
      3 * (L + 1) <
        16 * (residualComponents x y L a b h).card) :
    (L + 1) / 16 ≤
      (smallExactFreeResidualComponents
        x y L a b h 43).card := by
  apply
    target_le_card_smallExactFreeResidualComponents
      ha hb hab hx hy hheight
  exact fixed_cutoff_counting_budget hB hdensity

/--
Candidate-specialized version of the fixed-constant extraction.  The
primitive-channel hypotheses and height identity are read from `c`.
-/
theorem one_sixteenth_le_card_smallExactFreeResidualComponents_of_candidate
    {x y L H : ℕ}
    (c : ReducedCandidate x y (L + 1) H)
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hB : 32 ≤ L + 1)
    (hdensity :
      3 * (L + 1) <
        16 *
          (residualComponents x y L c.1.1 c.1.2
            (pairChannelError x y c.1.1 c.1.2)).card) :
    (L + 1) / 16 ≤
      (smallExactFreeResidualComponents
        x y L c.1.1 c.1.2
          (pairChannelError x y c.1.1 c.1.2) 43).card := by
  apply
    target_le_card_smallExactFreeResidualComponents_of_candidate
      c hx hy
  exact fixed_cutoff_counting_budget hB hdensity

/--
The aligned deep-core contradiction with every combinatorial hypothesis
eliminated.

For the density `3B < 16c#`, the only remaining inputs are numerical
inequalities in `B=L+1`, the Hamming radius `t`, the candidate height and the
base point.  In particular no family of components, matrix, code word,
square-product witness or root enumeration appears in the statement.
-/
theorem no_dense_candidate_aligned_core_of_numerical_conditions
    {x y L H t : ℕ}
    (c : ReducedCandidate x y (L + 1) H)
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hB : 32 ≤ L + 1)
    (hdensity :
      3 * (L + 1) <
        16 *
          (residualComponents x y L c.1.1 c.1.2
            (pairChannelError x y c.1.1 c.1.2)).card)
    (ht : 1 ≤ t)
    (htwo : 2 * t ≤ (L + 1) / 16)
    (hrows :
      PrimesUpTo.count (L + 1) + 2 ≤ (L + 1) / 16)
    (hHamming :
      2 * t *
          2 ^ ((PrimesUpTo.count (L + 1) + 2) / t + 1) ≤
        (L + 1) / 16)
    (hbase :
      2 * (3 * H * (L + 1)) ≤ c.1.1 * x)
    (hRungeRange :
      ∀ k : ℕ, 1 ≤ k → k ≤ 43 * t →
        (128 * (2 * k) * (3 * H * (L + 1))) ^ (4 * k) <
          c.1.1 * x) :
    False := by
  have hfamily :=
    one_sixteenth_le_card_smallExactFreeResidualComponents_of_candidate
      c hx hy hB hdensity
  exact
    no_candidate_aligned_core_of_finite_conditions
      (K := 43) c hx hy ht
      (htwo.trans hfamily)
      (hrows.trans hfamily)
      (hHamming.trans hfamily)
      hbase hRungeRange

/--
Variant of the preceding exclusion in which the small-prime row budget is
discharged by the explicit Chebyshev threshold.
-/
theorem no_dense_candidate_aligned_core_of_hamming_runge_conditions
    {x y L H t : ℕ}
    (c : ReducedCandidate x y (L + 1) H)
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hB : 64 ≤ L + 1)
    (hlog : 256 ≤ Nat.log 2 (L + 1))
    (hdensity :
      3 * (L + 1) <
        16 *
          (residualComponents x y L c.1.1 c.1.2
            (pairChannelError x y c.1.1 c.1.2)).card)
    (ht : 1 ≤ t)
    (htwo : 2 * t ≤ (L + 1) / 16)
    (hHamming :
      2 * t *
          2 ^ ((PrimesUpTo.count (L + 1) + 2) / t + 1) ≤
        (L + 1) / 16)
    (hbase :
      2 * (3 * H * (L + 1)) ≤ c.1.1 * x)
    (hRungeRange :
      ∀ k : ℕ, 1 ≤ k → k ≤ 43 * t →
        (128 * (2 * k) * (3 * H * (L + 1))) ^ (4 * k) <
          c.1.1 * x) :
    False := by
  exact
    no_dense_candidate_aligned_core_of_numerical_conditions
      c hx hy (by omega) hdensity ht htwo
      (prime_rows_le_one_sixteenth hB hlog)
      hHamming hbase hRungeRange

end

end AlignedDeepCoreExtraction
end PaperC
