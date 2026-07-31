import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.ZMod.Basic

/-!
# Parity vectors of natural numbers

The parity vector of `n` records every prime exponent in the factorization of
`n`, reduced modulo two.  We index the vector by all natural numbers (rather
than by a subtype of primes); the non-prime coordinates are automatically
zero.
-/

namespace PaperC

/-- The two-element field used for parity vectors. -/
abbrev F₂ := ZMod 2

/-- The vector of prime-factorization exponents of `n`, reduced modulo two. -/
noncomputable def parityVec (n : ℕ) : ℕ →₀ F₂ :=
  n.factorization.mapRange (fun e : ℕ => (e : F₂)) (by simp)

/-- Evaluation of the parity vector at a coordinate. -/
@[simp]
theorem parityVec_apply (n p : ℕ) :
    parityVec n p = (n.factorization p : F₂) :=
  rfl

/-- The parity vector of one is zero. -/
@[simp]
theorem parityVec_one : parityVec 1 = 0 := by
  simp [parityVec]

/-- On nonzero naturals, multiplication becomes addition of parity vectors. -/
theorem parityVec_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    parityVec (a * b) = parityVec a + parityVec b := by
  ext p
  simp [parityVec, Nat.factorization_mul ha hb]

/-- Every square has zero parity vector. -/
@[simp]
theorem parityVec_pow_two (n : ℕ) : parityVec (n ^ 2) = 0 := by
  ext p
  simp only [parityVec_apply, Nat.factorization_pow, Finsupp.smul_apply, Finsupp.zero_apply]
  rw [nsmul_eq_mul, Nat.cast_mul]
  change ((2 : ℕ) : F₂) * (n.factorization p : F₂) = 0
  rw [show ((2 : ℕ) : F₂) = 0 by decide, zero_mul]

/-- The product notation for a square also has zero parity vector. -/
@[simp]
theorem parityVec_mul_self (n : ℕ) : parityVec (n * n) = 0 := by
  simpa [pow_two] using parityVec_pow_two n

/-- A positive natural identified with a square has zero parity vector. -/
theorem parityVec_eq_zero_of_eq_sq {n r : ℕ} (_hn : 0 < n) (h : n = r ^ 2) :
    parityVec n = 0 := by
  rw [h, parityVec_pow_two]

/--
A nonzero natural number has zero parity vector exactly when it is a square.

The reverse implication reconstructs a square root from the prime
factorization by halving every (even) exponent.
-/
theorem parityVec_eq_zero_iff_exists_sq {n : ℕ} (hn : n ≠ 0) :
    parityVec n = 0 ↔ ∃ r : ℕ, n = r ^ 2 := by
  constructor
  · intro hparity
    have heven : ∀ p : ℕ, 2 ∣ n.factorization p := by
      intro p
      rw [← ZMod.natCast_eq_zero_iff]
      have hp := DFunLike.congr_fun hparity p
      simpa only [parityVec_apply, Finsupp.zero_apply] using hp
    let halfFactorization : ℕ →₀ ℕ :=
      n.factorization.mapRange (fun e : ℕ => e / 2) (by simp)
    let r : ℕ := halfFactorization.prod (· ^ ·)
    have hprime : ∀ p : ℕ, p ∈ halfFactorization.support → p.Prime := by
      intro p hp
      exact Nat.prime_of_mem_primeFactors
        (Finsupp.support_mapRange hp)
    have hrpos : 0 < r := by
      exact Nat.prod_pow_pos_of_zero_notMem_support fun hzero =>
        Nat.not_prime_zero (hprime 0 hzero)
    have hrfactorization : r.factorization = halfFactorization :=
      Nat.prod_pow_factorization_eq_self hprime
    have hsquareFactorization : (r ^ 2).factorization = n.factorization := by
      rw [Nat.factorization_pow, hrfactorization]
      ext p
      simp only [Finsupp.smul_apply, halfFactorization, Finsupp.mapRange_apply]
      simpa [nsmul_eq_mul] using Nat.mul_div_cancel_left' (heven p)
    refine ⟨r, ?_⟩
    exact Nat.eq_of_factorization_eq hn (pow_ne_zero 2 hrpos.ne') fun p =>
      congrArg (fun f : ℕ →₀ ℕ => f p) hsquareFactorization.symm
  · rintro ⟨r, rfl⟩
    exact parityVec_pow_two r

/-- `IsSquare` formulation of `parityVec_eq_zero_iff_exists_sq`. -/
theorem parityVec_eq_zero_iff_isSquare {n : ℕ} (hn : n ≠ 0) :
    parityVec n = 0 ↔ IsSquare n := by
  simpa only [isSquare_iff_exists_sq] using parityVec_eq_zero_iff_exists_sq hn

/--
The parity vector of a finite product of nonzero naturals is the sum of their
parity vectors.
-/
theorem parityVec_prod {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (hf : ∀ i ∈ s, f i ≠ 0) :
    parityVec (∏ i ∈ s, f i) = ∑ i ∈ s, parityVec (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert i s hi ih =>
      have hfi : f i ≠ 0 := hf i (Finset.mem_insert_self i s)
      have hfs : ∀ j ∈ s, f j ≠ 0 := by
        intro j hj
        exact hf j (Finset.mem_insert_of_mem hj)
      have hprod : ∏ j ∈ s, f j ≠ 0 := Finset.prod_ne_zero_iff.mpr hfs
      rw [Finset.prod_insert hi, Finset.sum_insert hi,
        parityVec_mul hfi hprod, ih hfs]

/--
The implication needed in the multiplicative translation of Lemma 2.2:
if a finite product is a square, the sum of the selected parity vectors is
zero.
-/
theorem sum_parityVec_eq_zero_of_prod_eq_sq {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (hf : ∀ i ∈ s, f i ≠ 0) {r : ℕ}
    (hsq : ∏ i ∈ s, f i = r ^ 2) :
    ∑ i ∈ s, parityVec (f i) = 0 := by
  rw [← parityVec_prod s f hf, hsq, parityVec_pow_two]

/--
The full multiplicative translation of Lemma 2.2: a finite sum of parity
vectors vanishes exactly when the corresponding product is a square.
-/
theorem sum_parityVec_eq_zero_iff_prod_eq_sq {ι : Type*}
    (s : Finset ι) (f : ι → ℕ) (hf : ∀ i ∈ s, f i ≠ 0) :
    (∑ i ∈ s, parityVec (f i) = 0) ↔
      ∃ r : ℕ, ∏ i ∈ s, f i = r ^ 2 := by
  classical
  have hprod : ∏ i ∈ s, f i ≠ 0 := Finset.prod_ne_zero_iff.mpr hf
  rw [← parityVec_prod s f hf]
  exact parityVec_eq_zero_iff_exists_sq hprod

/-- Binary specialization of `sum_parityVec_eq_zero_of_prod_eq_sq`. -/
theorem add_parityVec_eq_zero_of_mul_eq_sq {a b r : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hsq : a * b = r ^ 2) :
    parityVec a + parityVec b = 0 := by
  rw [← parityVec_mul ha hb, hsq, parityVec_pow_two]

/-- Binary specialization of `sum_parityVec_eq_zero_iff_prod_eq_sq`. -/
theorem add_parityVec_eq_zero_iff_mul_eq_sq {a b : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    parityVec a + parityVec b = 0 ↔ ∃ r : ℕ, a * b = r ^ 2 := by
  rw [← parityVec_mul ha hb]
  exact parityVec_eq_zero_iff_exists_sq (mul_ne_zero ha hb)

end PaperC
