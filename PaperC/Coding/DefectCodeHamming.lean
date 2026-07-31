import PaperC.Coding.DefectCodeRank
import PaperC.Coding.HammingDefectBound

/-!
# From the defect matrix to the finite Hamming estimate

This file assembles the exact linear-algebraic and sphere-packing steps in
equation (3.5) of Paper C.

The kernel of the augmented parity matrix has codimension at most `r + 1`.
Consequently, a lower bound on the weight of its nonzero words gives the
binomial-volume estimate

`∑ j ≤ t, m.choose j ≤ 2 ^ (r + 1)`.

The elementary numerical argument of `HammingDefectBound` then turns this
into an explicit upper bound for `m`.  The missing input for Proposition 3.2
is now isolated cleanly: the Runge argument must supply the minimum-weight
hypothesis.
-/

namespace PaperC
namespace DefectCodeHamming

open Finset

/--
The exact second inequality of (3.5) for the kernel of the augmented defect
matrix.  The `r` supplied small-prime coordinates and the appended constant
coordinate give `r + 1` rows.
-/
theorem defectCode_volume_le_two_pow
    {m r t : ℕ}
    (smallPrime : Fin r → ℕ) (f : Fin m → ℕ)
    (hweight :
      HammingBound.MinWeightAbove
        (LinearMap.ker
          (DefectCodeRank.augmentedParityMap smallPrime f))
        (2 * t))
    (hrows : r + 1 ≤ m) :
    (∑ j ∈ Finset.range (t + 1), m.choose j) ≤ 2 ^ (r + 1) := by
  apply HammingBound.sum_choose_le_pow_of_finrank_ge
    (C := LinearMap.ker
      (DefectCodeRank.augmentedParityMap smallPrime f))
    hweight
  · exact DefectCodeRank.defectCode_finrank_ge smallPrime f
  · exact hrows

/--
Finite quantitative consequence of the defect-code Hamming bound.  This is
the fully assembled algebraic/combinatorial conclusion after Runge has
excluded nonzero kernel words of weight at most `2 * t`.
-/
theorem defectCode_length_lt
    {m r t : ℕ}
    (smallPrime : Fin r → ℕ) (f : Fin m → ℕ)
    (ht : 1 ≤ t)
    (htm : 2 * t ≤ m)
    (hrows : r + 1 ≤ m)
    (hweight :
      HammingBound.MinWeightAbove
        (LinearMap.ker
          (DefectCodeRank.augmentedParityMap smallPrime f))
        (2 * t)) :
    m < 2 * t * 2 ^ ((r + 1) / t + 1) := by
  apply HammingDefectBound.length_lt_of_sum_choose_le_two_pow
    ht htm
  exact defectCode_volume_le_two_pow smallPrime f hweight
    hrows

end DefectCodeHamming
end PaperC
