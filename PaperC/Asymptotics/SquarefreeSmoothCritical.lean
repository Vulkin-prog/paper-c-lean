import PaperC.Arithmetic.SquarefreeSmoothCount
import PaperC.Arithmetic.PrimeNumberTheoremInput

/-!
# Critical bound for squarefree smooth kernels

This is the first counting factor in Lemma 15.3.  The exact injection into
subsets of primes gives `2^π(B)` possibilities.  PNT turns this into the
manuscript scale `exp(O(B / log B))`.
-/

namespace PaperC
namespace SquarefreeSmoothCritical

open Filter
open DefectCounting
open PrimeNumberTheoremInput
open SquarefreeSmoothCount

/--
Under PNT, uniformly in the height cutoff `X`, the number of squarefree
`B`-smooth kernels is at most

`exp(2 log(2) B / log B)`

for all sufficiently large `B`.
-/
theorem primeNumberTheorem_implies_squarefreeSmooth_bound
    (hpnt : PrimeNumberTheoremStatement) :
    ∃ B₀ : ℕ, ∀ B ≥ B₀, ∀ X,
      ((squarefreeSmoothUpTo B X).card : ℝ) ≤
        Real.exp
          ((2 * Real.log 2) *
            ((B : ℝ) / Real.log (B : ℝ))) := by
  have hpntUpper :
      ∀ᶠ B : ℕ in atTop,
        (PrimesUpTo.count B : ℝ) *
            Real.log (B : ℝ) / (B : ℝ) <
          (2 : ℝ) :=
    hpnt.eventually (Iio_mem_nhds (by norm_num))
  have heventually :
      ∀ᶠ B : ℕ in atTop,
        ∀ X,
          ((squarefreeSmoothUpTo B X).card : ℝ) ≤
            Real.exp
              ((2 * Real.log 2) *
                ((B : ℝ) / Real.log (B : ℝ))) := by
    filter_upwards
      [hpntUpper, eventually_ge_atTop 2] with
        B hpntB hB
    intro X
    have hBpos : (0 : ℝ) < (B : ℝ) := by
      positivity
    have hlogPos : 0 < Real.log (B : ℝ) :=
      Real.log_pos (by exact_mod_cast hB)
    have hprimeCount :
        (PrimesUpTo.count B : ℝ) ≤
          2 * (B : ℝ) / Real.log (B : ℝ) := by
      rw [div_lt_iff₀ hBpos] at hpntB
      rw [le_div_iff₀ hlogPos]
      nlinarith
    have hcardNat :=
      card_squarefreeSmoothUpTo_le_two_pow B X
    have hcardReal :
        ((squarefreeSmoothUpTo B X).card : ℝ) ≤
          (2 : ℝ) ^ (smallPrimesUpTo B).card := by
      exact_mod_cast hcardNat
    have hcountIdentity :
        (smallPrimesUpTo B).card =
          PrimesUpTo.count B :=
      (PrimeCountBridge.count_eq_card_smallPrimesUpTo B).symm
    calc
      ((squarefreeSmoothUpTo B X).card : ℝ) ≤
          (2 : ℝ) ^ (smallPrimesUpTo B).card :=
        hcardReal
      _ =
          Real.exp
            (((smallPrimesUpTo B).card : ℝ) *
              Real.log 2) := by
        calc
          (2 : ℝ) ^ (smallPrimesUpTo B).card =
              (Real.exp (Real.log 2)) ^
                (smallPrimesUpTo B).card := by
            rw [Real.exp_log]
            norm_num
          _ =
              Real.exp
                (((smallPrimesUpTo B).card : ℝ) *
                  Real.log 2) :=
            (Real.exp_nat_mul
              (Real.log 2)
              (smallPrimesUpTo B).card).symm
      _ ≤
          Real.exp
            ((2 * Real.log 2) *
              ((B : ℝ) / Real.log (B : ℝ))) := by
        apply Real.exp_le_exp.mpr
        rw [hcountIdentity]
        have hlogTwoNonneg :
            0 ≤ Real.log 2 :=
          (Real.log_pos one_lt_two).le
        have hscaled :=
          mul_le_mul_of_nonneg_right hprimeCount
            hlogTwoNonneg
        calc
          (PrimesUpTo.count B : ℝ) * Real.log 2 ≤
              (2 * (B : ℝ) / Real.log (B : ℝ)) *
                Real.log 2 :=
            hscaled
          _ =
              (2 * Real.log 2) *
                ((B : ℝ) / Real.log (B : ℝ)) := by
            ring
  exact eventually_atTop.mp heventually

end SquarefreeSmoothCritical
end PaperC
