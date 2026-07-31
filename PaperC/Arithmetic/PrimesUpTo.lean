import PaperC.Model.FiniteRademacher
import Mathlib.Data.Finset.Sort

/-!
# Canonical enumeration of the primes below a cutoff

The finite-cylinder model represents a prime `p ≤ H` by an element of
`PrimeUpTo H`.  This file orders that finite type increasingly and exposes the
result as the function `smallPrime H` expected by the defect-code
formalization.

The resulting enumeration has no repetitions and contains every prime at most
`H`.  In particular, a defect part all of whose prime divisors are at most
`H` has all its prime divisors among the enumerated coordinates.
-/

namespace PaperC
namespace PrimesUpTo

/-- The order inherited from the underlying bounded natural number. -/
instance primeUpToLinearOrder (H : ℕ) : LinearOrder (PrimeUpTo H) := by
  unfold PrimeUpTo
  infer_instance

/-- The number of primes at most `H`. -/
abbrev count (H : ℕ) : ℕ :=
  Fintype.card (PrimeUpTo H)

/--
The increasing order isomorphism from the coordinate type to the subtype of
primes at most `H`.
-/
noncomputable def primeOrderIso (H : ℕ) :
    Fin (count H) ≃o PrimeUpTo H :=
  Fintype.orderIsoFinOfCardEq (PrimeUpTo H) rfl

/--
The canonical increasing enumeration of the prime numbers at most `H`.
-/
noncomputable def smallPrime (H : ℕ) : Fin (count H) → ℕ :=
  fun i ↦ (primeOrderIso H i).1

/-- Every enumerated coordinate is prime. -/
theorem smallPrime_prime (H : ℕ) (i : Fin (count H)) :
    Nat.Prime (smallPrime H i) :=
  (primeOrderIso H i).2

/-- Every enumerated prime lies below the inclusive cutoff. -/
theorem smallPrime_le (H : ℕ) (i : Fin (count H)) :
    smallPrime H i ≤ H := by
  exact Nat.le_of_lt_succ (primeOrderIso H i).1.2

/-- The canonical prime enumeration contains no repetitions. -/
theorem smallPrime_injective (H : ℕ) :
    Function.Injective (smallPrime H) := by
  intro i j hij
  apply (primeOrderIso H).injective
  apply Subtype.ext
  exact Fin.ext hij

/--
Every prime below the inclusive cutoff occurs in the canonical enumeration.
-/
theorem exists_smallPrime_eq_of_prime_le
    {H p : ℕ} (hp : Nat.Prime p) (hpH : p ≤ H) :
    ∃ i : Fin (count H), smallPrime H i = p := by
  let q : PrimeUpTo H :=
    ⟨⟨p, Nat.lt_succ_iff.mpr hpH⟩, hp⟩
  refine ⟨(primeOrderIso H).symm q, ?_⟩
  change ((primeOrderIso H ((primeOrderIso H).symm q)).1 : ℕ) = p
  rw [(primeOrderIso H).apply_symm_apply]

/--
Equivalently, the range of `smallPrime H` consists exactly of the primes at
most `H`.
-/
theorem mem_range_smallPrime_iff {H p : ℕ} :
    p ∈ Set.range (smallPrime H) ↔ Nat.Prime p ∧ p ≤ H := by
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨smallPrime_prime H i, smallPrime_le H i⟩
  · rintro ⟨hp, hpH⟩
    exact exists_smallPrime_eq_of_prime_le hp hpH

/--
If every prime divisor of `s` is at most `H`, then every prime divisor of
`s` occurs among the canonical small-prime coordinates.

This is the divisor-coverage statement consumed by the defect-code
representation argument.
-/
theorem covers_primeDivisors
    {H s : ℕ}
    (hbounded : ∀ p, Nat.Prime p → p ∣ s → p ≤ H) :
    ∀ p, Nat.Prime p → p ∣ s →
      ∃ i : Fin (count H), smallPrime H i = p := by
  intro p hp hps
  exact exists_smallPrime_eq_of_prime_le hp (hbounded p hp hps)

end PrimesUpTo
end PaperC
