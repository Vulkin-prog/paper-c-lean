import PaperC.Analysis.RungeLogarithmicGrowth
import PaperC.Arithmetic.PrimesUpTo

/-!
# The defect code with the canonical small-prime coordinates

The abstract coding files accept an arbitrary finite list of coordinates.
For Proposition 3.2 that list is canonical: all primes `p ≤ H`.  The
theorems below instantiate the abstract list and discharge its coverage
hypothesis, leaving only the representation of the selected interval values.
-/

namespace PaperC
namespace CanonicalDefectCode

open Finset

/--
Equation (3.5) for represented values in `[U, U + H]`, using the canonical
enumeration of every prime at most `H`.
-/
theorem volume_le_two_pow_of_log
    {m U H t : ℕ}
    (f s a : Fin m → ℕ)
    (hrep : ∀ i, f i = s i * (a i) ^ 2)
    (hs : ∀ i, s i ≠ 0)
    (ha : ∀ i, a i ≠ 0)
    (hbounded :
      ∀ i p, Nat.Prime p → p ∣ s i → p ≤ H)
    (hinjective : Function.Injective f)
    (hlower : ∀ i, U ≤ f i)
    (hupper : ∀ i, f i ≤ U + H)
    (hH : 1 ≤ H)
    (hU : 2 * H ≤ U)
    (ht : 1 ≤ t)
    (hlog :
      (4 * t : ℝ) * Real.log (128 * (2 * t) * H) <
        Real.log U)
    (hrows : PrimesUpTo.count H + 1 ≤ m) :
    (∑ j ∈ Finset.range (t + 1), m.choose j) ≤
      2 ^ (PrimesUpTo.count H + 1) := by
  apply
    RungeDefectApplication.defectCode_volume_le_two_pow_of_endpoint_growth
      (PrimesUpTo.smallPrime H) f s a hrep hs ha
  · intro i
    exact PrimesUpTo.covers_primeDivisors (hbounded i)
  · exact hinjective
  · exact hlower
  · exact hupper
  · exact hH
  · exact hU
  · exact RungeLogarithmicGrowth.endpoint_growth_of_log
      ht hH (by omega) hlog
  · exact hrows

/--
Finite pointwise length estimate for represented values in `[U, U + H]`.
This is the exact output of the Runge--code--Hamming chain before the
asymptotic choices of `t` and the estimate for `π(H)`.
-/
theorem length_lt_of_log
    {m U H t : ℕ}
    (f s a : Fin m → ℕ)
    (hrep : ∀ i, f i = s i * (a i) ^ 2)
    (hs : ∀ i, s i ≠ 0)
    (ha : ∀ i, a i ≠ 0)
    (hbounded :
      ∀ i p, Nat.Prime p → p ∣ s i → p ≤ H)
    (hinjective : Function.Injective f)
    (hlower : ∀ i, U ≤ f i)
    (hupper : ∀ i, f i ≤ U + H)
    (hH : 1 ≤ H)
    (hU : 2 * H ≤ U)
    (ht : 1 ≤ t)
    (hlog :
      (4 * t : ℝ) * Real.log (128 * (2 * t) * H) <
        Real.log U)
    (htm : 2 * t ≤ m)
    (hrows : PrimesUpTo.count H + 1 ≤ m) :
    m <
      2 * t *
        2 ^ ((PrimesUpTo.count H + 1) / t + 1) := by
  apply
    RungeDefectApplication.defectCode_length_lt_of_endpoint_growth
      (PrimesUpTo.smallPrime H) f s a hrep hs ha
  · intro i
    exact PrimesUpTo.covers_primeDivisors (hbounded i)
  · exact hinjective
  · exact hlower
  · exact hupper
  · exact hH
  · exact hU
  · exact RungeLogarithmicGrowth.endpoint_growth_of_log
      ht hH (by omega) hlog
  · exact ht
  · exact htm
  · exact hrows

end CanonicalDefectCode
end PaperC
