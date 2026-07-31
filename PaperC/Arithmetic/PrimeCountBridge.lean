import PaperC.Arithmetic.DefectCounting
import PaperC.Arithmetic.PrimesUpTo

/-!
# Identifying the two finite models of primes at most a cutoff

The probability model uses the finite type `PrimeUpTo H`, while the counting
argument uses the finset `DefectCounting.smallPrimesUpTo H`.  They represent
the same inclusive prime interval; this file records the exact equivalence.
-/

namespace PaperC
namespace PrimeCountBridge

/-- `PrimeUpTo H` is equivalent to membership in the small-prime finset. -/
noncomputable def primeUpToEquivSmallPrimes (H : ℕ) :
    PrimeUpTo H ≃
      {p : ℕ // p ∈ DefectCounting.smallPrimesUpTo H} where
  toFun p :=
    ⟨p.1.1, DefectCounting.mem_smallPrimesUpTo.mpr
      ⟨p.2, Nat.le_of_lt_succ p.1.2⟩⟩
  invFun p :=
    ⟨⟨p.1, Nat.lt_succ_iff.mpr
      (DefectCounting.mem_smallPrimesUpTo.mp p.2).2⟩,
      (DefectCounting.mem_smallPrimesUpTo.mp p.2).1⟩
  left_inv p := by
    apply Subtype.ext
    apply Fin.ext
    rfl
  right_inv p := by
    apply Subtype.ext
    rfl

/-- The canonical coordinate count equals the cardinality of the prime finset. -/
theorem count_eq_card_smallPrimesUpTo (H : ℕ) :
    PrimesUpTo.count H =
      (DefectCounting.smallPrimesUpTo H).card := by
  change Fintype.card (PrimeUpTo H) =
    (DefectCounting.smallPrimesUpTo H).card
  rw [Fintype.card_congr (primeUpToEquivSmallPrimes H)]
  exact Fintype.card_coe _

end PrimeCountBridge
end PaperC
