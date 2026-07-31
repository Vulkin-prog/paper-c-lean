import PaperC.Coding.DefectCodeDistance
import PaperC.Coding.DefectCodeHamming

/-!
# The assembled finite defect-code proposition

This file combines the arithmetic representation of the selected integers,
the finite Runge obstruction, and the exact binary Hamming bound.

The two conclusions are the precise volume inequality in equation (3.5) and
its elementary finite consequence for the number `m` of selected integers.
-/

namespace PaperC
namespace DefectCodeProposition

open Finset

/--
The exact Hamming-volume inequality obtained directly from the represented
integers and the absence of short Runge square products.
-/
theorem defectCode_volume_le_two_pow_of_representations
    {m r U R t : ℕ}
    (smallPrime : Fin r → ℕ)
    (f s a : Fin m → ℕ)
    (hrep : ∀ i, f i = s i * (a i) ^ 2)
    (hs : ∀ i, s i ≠ 0)
    (ha : ∀ i, a i ≠ 0)
    (hsmall : ∀ i p, Nat.Prime p → p ∣ s i →
      ∃ j : Fin r, smallPrime j = p)
    (hinjective : Function.Injective f)
    (hlower : ∀ i, U ≤ f i)
    (hupper : ∀ i, f i ≤ U + R)
    (hRunge : DefectCodeDistance.NoShortRungeSquare U R t)
    (hrows : r + 1 ≤ m) :
    (∑ j ∈ Finset.range (t + 1), m.choose j) ≤ 2 ^ (r + 1) := by
  have hweight :=
    DefectCodeDistance.minWeightAbove_augmentedParityMap_of_noShortRungeSquare
        smallPrime f s a hrep hs ha hsmall hinjective hlower hupper hRunge
  exact DefectCodeHamming.defectCode_volume_le_two_pow
    smallPrime f hweight hrows

/--
The fully assembled finite length estimate:

`m < 2 * t * 2 ^ ((r + 1) / t + 1)`.

All arithmetic, coding, and Runge hypotheses are exposed explicitly; no
minimum-distance or volume premise remains.
-/
theorem defectCode_length_lt_of_representations
    {m r U R t : ℕ}
    (smallPrime : Fin r → ℕ)
    (f s a : Fin m → ℕ)
    (hrep : ∀ i, f i = s i * (a i) ^ 2)
    (hs : ∀ i, s i ≠ 0)
    (ha : ∀ i, a i ≠ 0)
    (hsmall : ∀ i p, Nat.Prime p → p ∣ s i →
      ∃ j : Fin r, smallPrime j = p)
    (hinjective : Function.Injective f)
    (hlower : ∀ i, U ≤ f i)
    (hupper : ∀ i, f i ≤ U + R)
    (hRunge : DefectCodeDistance.NoShortRungeSquare U R t)
    (ht : 1 ≤ t)
    (htm : 2 * t ≤ m)
    (hrows : r + 1 ≤ m) :
    m < 2 * t * 2 ^ ((r + 1) / t + 1) := by
  have hweight :=
    DefectCodeDistance.minWeightAbove_augmentedParityMap_of_noShortRungeSquare
        smallPrime f s a hrep hs ha hsmall hinjective hlower hupper hRunge
  exact DefectCodeHamming.defectCode_length_lt
    smallPrime f ht htm hrows hweight

end DefectCodeProposition
end PaperC
