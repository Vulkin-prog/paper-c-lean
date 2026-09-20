import PaperCPrel8.OddPrimePivot
import PaperCV282.PrescribedValues

/-! # Actual odd-prime pivots in finite cylinders

No upper quadratic size bound and no exponent-one hypothesis is needed.
The selected largest odd-valuation prime is private as soon as it is larger
than the window diameter. All displayed primes are actual cylinder coordinates.
-/
namespace PaperC.Prel8.PivotGeometry
open PaperC.DefectivePredicate PaperC.V282.PrescribedValues
open PaperC.Prel8.OddPrimePivot
noncomputable section

/-- A nontrivial maximum belongs to the actual odd-valuation support. -/
theorem pivot_mem_support {n : ℕ} (h : 1 < largestOddPrime n) :
    largestOddPrime n ∈ oddPrimeSupport n := by
  have hs : (oddPrimeSupport n).Nonempty := by
    by_contra he
    have he := Finset.not_nonempty_iff_eq_empty.mp he
    simp [largestOddPrime, he] at h
  have hm := Finset.sup_mem_of_nonempty (f := id) hs
  have he : largestOddPrime n = (oddPrimeSupport n).sup id := by
    unfold largestOddPrime at *
    omega
  rw [he]
  simpa using hm

/-- The selected pivot is prime, divides its vertex, and has parity exactly one. -/
theorem pivot_spec {n : ℕ} (h : 1 < largestOddPrime n) :
    (largestOddPrime n).Prime ∧ largestOddPrime n ∣ n ∧
      parityVec n (largestOddPrime n) = 1 := by
  have hm := pivot_mem_support h
  have hf : largestOddPrime n ∈ n.factorization.support :=
    Finsupp.support_mapRange hm
  have hp := Nat.prime_of_mem_primeFactors hf
  refine ⟨hp, Nat.dvd_of_mem_primeFactors hf, ?_⟩
  have ho := oddFactorization_apply_eq_one_of_mem hm
  change n.factorization (largestOddPrime n) % 2 = 1 at ho
  rw [parityVec_apply, ← ZMod.natCast_mod (n.factorization (largestOddPrime n)) 2, ho]
  rfl

/-- Divisibility at two offsets would force those offsets to coincide. -/
theorem private_divisor {j B p : ℕ} (hp : B ≤ p) (a b : Fin B)
    (ha : p ∣ j+a.val) (hb : p ∣ j+b.val) : a=b := by
  apply Fin.ext
  have he := ha.modEq_zero_nat.trans hb.modEq_zero_nat.symm
  have he := (Nat.ModEq.refl j).add_left_cancel he
  exact he.eq_of_lt_of_lt (a.isLt.trans_le hp) (b.isLt.trans_le hp)

/-- Off-diagonal valuations vanish, even before reduction modulo two. -/
theorem pivot_off_diagonal {j B : ℕ} (a b : Fin B)
    (h1 : 1 < largestOddPrime (j+a.val))
    (hB : B ≤ largestOddPrime (j+a.val)) (hne : b ≠ a) :
    parityVec (j+b.val) (largestOddPrime (j+a.val)) = 0 := by
  have hd := (pivot_spec h1).2.1
  have hn : ¬largestOddPrime (j+a.val) ∣ j+b.val := by
    intro hb
    exact hne (private_divisor hB b a hb hd)
  simp [parityVec_apply, Nat.factorization_eq_zero_of_not_dvd hn]

/-- Distinct vertices select distinct prime coordinates. -/
theorem pivot_injective {j B : ℕ}
    (h1 : ∀ a : Fin B, 1 < largestOddPrime (j+a.val))
    (hB : ∀ a : Fin B, B ≤ largestOddPrime (j+a.val)) :
    Function.Injective (fun a : Fin B => largestOddPrime (j+a.val)) := by
  intro a b he
  apply private_divisor (hB a) a b (pivot_spec (h1 a)).2.1
  change largestOddPrime (j+a.val) = largestOddPrime (j+b.val) at he
  rw [he]
  exact (pivot_spec (h1 b)).2.1

/-- The actual pivot, placed in the same finite cylinder as the existing model. -/
def cylinderPivot {M j B : ℕ} (hj : 0 < j) (hM : j+B ≤ M+1)
    (h1 : ∀ a : Fin B, 1 < largestOddPrime (j+a.val)) (a : Fin B) : PrimeUpTo M :=
  ⟨⟨largestOddPrime (j+a.val), by
    have hp := Nat.le_of_dvd (by omega : 0 < j+a.val) (pivot_spec (h1 a)).2.1
    have ha := a.isLt
    omega⟩, (pivot_spec (h1 a)).1⟩

/-- Every selected prime basis vector is sent to the corresponding word basis vector. -/
theorem cylinderPivot_basis {M j B : ℕ} (hj : 0 < j) (hM : j+B ≤ M+1)
    (h1 : ∀ a : Fin B, 1 < largestOddPrime (j+a.val))
    (hB : ∀ a : Fin B, B ≤ largestOddPrime (j+a.val)) (a : Fin B) :
    valueSystem M (fun a : Fin B => j+a.val)
      (Pi.single (cylinderPivot hj hM h1 a) 1) = Pi.single a 1 := by
  apply valueSystem_prime_basis
  · exact (pivot_spec (h1 a)).2.2
  · intro b hb
    exact pivot_off_diagonal a b (h1 a) (hB a) hb

end
end PaperC.Prel8.PivotGeometry
