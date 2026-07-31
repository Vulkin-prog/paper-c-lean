import PaperC.Arithmetic.DefectCounting
import PaperC.Arithmetic.DefectParitySupport
import Mathlib.Algebra.BigOperators.Associated

/-!
# The small-prime defect predicate

The condition denoted `K_H(n) = 1` in Proposition 3.2 says that every prime
whose exponent in `n` is odd is at most `H`.  We formulate it through the
already established parity vector: all coordinates indexed by primes greater
than `H` vanish.

The main theorem below checks that the finite representation used by the
counting argument,

`n = (∏ p ∈ support, p) * a^2`, with `support ⊆ {p prime | p ≤ H}`,

indeed implies this intrinsic predicate.
-/

namespace PaperC
namespace DefectivePredicate

open DefectCounting

/--
`n` has no odd prime valuation above `H`.

The primality hypothesis is kept in the definition to mirror the paper.
Coordinates of `parityVec` at non-primes vanish automatically.
-/
def HDefective (H n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → H < p → parityVec n p = 0

/-- The parity-vector formulation is exactly evenness of every valuation above `H`. -/
theorem hDefective_iff_even_factorization (H n : ℕ) :
    HDefective H n ↔
      ∀ p : ℕ, p.Prime → H < p → 2 ∣ n.factorization p := by
  simp only [HDefective, parityVec_apply,
    ZMod.natCast_eq_zero_iff]

/--
Equivalent support formulation: every nonzero prime coordinate of the parity
vector is indexed by a prime at most `H`.
-/
theorem hDefective_iff_parity_support_le (H n : ℕ) :
    HDefective H n ↔
      ∀ p : ℕ, p.Prime → parityVec n p ≠ 0 → p ≤ H := by
  constructor
  · intro h p hp hparity
    by_contra hpH
    exact hparity (h p hp (Nat.lt_of_not_ge hpH))
  · intro h p hp hpH
    by_contra hparity
    exact (Nat.not_le_of_gt hpH) (h p hp hparity)

/-- The defect part of an `H`-defect representation is nonzero. -/
theorem defectPart_ne_zero_of_HDefectRepresentation
    {H n : ℕ} (rep : HDefectRepresentation H n) :
    rep.defectPart ≠ 0 := by
  rw [DefectRepresentation.defectPart, Finset.prod_ne_zero_iff]
  intro p hp
  exact (mem_smallPrimesUpTo.mp (rep.support_subset hp)).1.ne_zero

/--
An explicit square-times-small-prime representation satisfies the intrinsic
`K_H(n) = 1` predicate.

This statement also covers the degenerate representation of `0` (necessarily
with square part `0`): `Nat.factorization 0`, hence its parity vector, is zero.
-/
theorem hDefective_of_HDefectRepresentation
    {H n : ℕ} (rep : HDefectRepresentation H n) :
    HDefective H n := by
  intro p hp hpH
  by_cases ha : rep.squarePart = 0
  · have hn : n = 0 := by
      rw [rep.value_eq, ha]
      simp
    subst n
    simp [parityVec_apply]
  · by_contra hparity
    have hp_dvd : p ∣ rep.defectPart :=
      DefectParitySupport.dvd_defectPart_of_eq_mul_sq_of_parityVec_ne_zero
        (defectPart_ne_zero_of_HDefectRepresentation rep) ha
        rep.value_eq hparity
    rw [DefectRepresentation.defectPart] at hp_dvd
    obtain ⟨q, hq, hpq⟩ :=
      (hp.prime.dvd_finsetProd_iff id).mp hp_dvd
    have hq_small := mem_smallPrimesUpTo.mp (rep.support_subset hq)
    have hp_eq_q : p = q :=
      (Nat.prime_dvd_prime_iff_eq hp hq_small.1).mp hpq
    exact (Nat.not_le_of_gt hpH) (hp_eq_q ▸ hq_small.2)

/-- Valuation-only consequence of an explicit `H`-defect representation. -/
theorem even_factorization_of_HDefectRepresentation
    {H n p : ℕ} (rep : HDefectRepresentation H n)
    (hp : p.Prime) (hpH : H < p) :
    2 ∣ n.factorization p :=
  (hDefective_iff_even_factorization H n).mp
    (hDefective_of_HDefectRepresentation rep) p hp hpH

/-! ## Canonical reconstruction from the intrinsic predicate -/

/--
The factorization retaining only the parity (remainder modulo two) of every
prime exponent.
-/
noncomputable def oddFactorization (n : ℕ) : ℕ →₀ ℕ :=
  n.factorization.mapRange (fun e : ℕ ↦ e % 2) (by simp)

/-- The canonical set of primes occurring to odd order in `n`. -/
noncomputable def oddPrimeSupport (n : ℕ) : Finset ℕ :=
  (oddFactorization n).support

/-- The factorization obtained by halving every prime exponent of `n`. -/
noncomputable def halfFactorization (n : ℕ) : ℕ →₀ ℕ :=
  n.factorization.mapRange (fun e : ℕ ↦ e / 2) (by simp)

/-- The square part obtained by multiplying the halved prime powers. -/
noncomputable def canonicalSquarePart (n : ℕ) : ℕ :=
  (halfFactorization n).prod (· ^ ·)

theorem factorization_eq_odd_add_two_half (n : ℕ) :
    n.factorization =
      oddFactorization n + 2 • halfFactorization n := by
  ext p
  simp only [oddFactorization, halfFactorization, Finsupp.add_apply,
    Finsupp.mapRange_apply, Finsupp.smul_apply, nsmul_eq_mul]
  exact (Nat.mod_add_div (n.factorization p) 2).symm

/-- Every exponent occurring in `oddFactorization` is exactly one. -/
theorem oddFactorization_apply_eq_one_of_mem
    {n p : ℕ} (hp : p ∈ oddPrimeSupport n) :
    oddFactorization n p = 1 := by
  have hp_ne : oddFactorization n p ≠ 0 :=
    Finsupp.mem_support_iff.mp hp
  simp only [oddFactorization, Finsupp.mapRange_apply] at hp_ne ⊢
  exact Nat.mod_two_ne_zero.mp hp_ne

/--
The product encoded by `oddFactorization` is the ordinary product of its
support, since every retained exponent is one.
-/
theorem prod_oddPrimeSupport_eq_prod_oddFactorization (n : ℕ) :
    (oddPrimeSupport n).prod id =
      (oddFactorization n).prod (· ^ ·) := by
  classical
  simp only [oddPrimeSupport, Finsupp.prod]
  apply Finset.prod_congr rfl
  intro p hp
  rw [oddFactorization_apply_eq_one_of_mem hp, pow_one]
  rfl

/-- The canonical odd-support/half-exponent decomposition of a nonzero integer. -/
theorem canonical_odd_mul_sq_decomposition
    {n : ℕ} (hn : n ≠ 0) :
    n = (oddPrimeSupport n).prod id * canonicalSquarePart n ^ 2 := by
  let powIndex : ℕ → ℕ → ℕ := fun p e ↦ p ^ e
  have hprod_add (f g : ℕ →₀ ℕ) :
      (f + g).prod powIndex = f.prod powIndex * g.prod powIndex :=
    Finsupp.prod_add_index' (fun p ↦ pow_zero p)
      (fun p e₁ e₂ ↦ pow_add p e₁ e₂)
  calc
    n = n.factorization.prod powIndex :=
      (Nat.prod_factorization_pow_eq_self hn).symm
    _ = (oddFactorization n + 2 • halfFactorization n).prod powIndex := by
      rw [factorization_eq_odd_add_two_half]
    _ = (oddFactorization n).prod powIndex *
        (2 • halfFactorization n).prod powIndex :=
      hprod_add _ _
    _ = (oddFactorization n).prod powIndex *
        ((halfFactorization n).prod powIndex *
          (halfFactorization n).prod powIndex) := by
      rw [two_nsmul, hprod_add]
    _ = (oddPrimeSupport n).prod id * canonicalSquarePart n ^ 2 := by
      rw [prod_oddPrimeSupport_eq_prod_oddFactorization]
      simp only [canonicalSquarePart, powIndex, pow_two]

/--
If the intrinsic predicate holds, every prime in the canonical odd support is
one of the primes at most `H`.
-/
theorem oddPrimeSupport_subset_smallPrimesUpTo
    {H n : ℕ} (h : HDefective H n) :
    oddPrimeSupport n ⊆ smallPrimesUpTo H := by
  intro p hp
  have hp_factorization : p ∈ n.factorization.support := by
    exact Finsupp.support_mapRange hp
  have hp_prime : p.Prime :=
    Nat.prime_of_mem_primeFactors hp_factorization
  rw [mem_smallPrimesUpTo]
  refine ⟨hp_prime, ?_⟩
  by_contra hp_not_le
  have hpH : H < p := Nat.lt_of_not_ge hp_not_le
  have hp_even : 2 ∣ n.factorization p :=
    (hDefective_iff_even_factorization H n).mp h p hp_prime hpH
  have hp_mod_zero : n.factorization p % 2 = 0 :=
    Nat.mod_eq_zero_of_dvd hp_even
  have hp_ne : oddFactorization n p ≠ 0 :=
    Finsupp.mem_support_iff.mp hp
  exact hp_ne (by
    simp only [oddFactorization, Finsupp.mapRange_apply]
    exact hp_mod_zero)

/--
Conversely, every nonzero integer satisfying the intrinsic `K_H(n) = 1`
condition has the finite representation used by the counting argument.
-/
noncomputable def representationOfHDefective
    {H n : ℕ} (h : HDefective H n) (hn : n ≠ 0) :
    HDefectRepresentation H n where
  support := oddPrimeSupport n
  support_subset := oddPrimeSupport_subset_smallPrimesUpTo h
  squarePart := canonicalSquarePart n
  value_eq := canonical_odd_mul_sq_decomposition hn

/-- For nonzero integers, the predicate and finite representation are equivalent. -/
theorem hDefective_iff_exists_HDefectRepresentation
    {H n : ℕ} (hn : n ≠ 0) :
    HDefective H n ↔ Nonempty (HDefectRepresentation H n) := by
  constructor
  · intro h
    exact ⟨representationOfHDefective h hn⟩
  · rintro ⟨rep⟩
    exact hDefective_of_HDefectRepresentation rep

end DefectivePredicate
end PaperC
