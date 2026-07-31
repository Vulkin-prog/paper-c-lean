import PaperC.Combinatorics.CanonicalResidualComponents

set_option maxHeartbeats 1800000

/-!
# The canonical residual prime product

This file packages the product denoted by `P#` in Section 7.  Its factors
are exactly the distinct primes selected by the canonical residual
certificates of Lemma 6.5.  Besides the finite-set definition, we record the
equivalent product indexed by residual components, positivity, the exact
number of factors, and the two branches `P# ≤ N` and `N < P#`.
-/

namespace PaperC
namespace CanonicalResidualComponents

open LargePrimeGraph
open ResidualComponentCounts

noncomputable section

/--
The canonical residual prime product `P#`: the product of the distinct
primes selected by the canonical residual certificates.
-/
noncomputable def canonicalResidualPrimeProduct
    {A x y L : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y) : ℕ :=
  ∏ p ∈ canonicalResidualCertificatePrimes
      (A := A) (L := L) hx hy, p

/--
The finite-set product is the product indexed directly by the canonical
residual components.  Injectivity of the selected-prime map is precisely
what prevents repeated factors when passing to its image.
-/
theorem canonicalResidualPrimeProduct_eq_product_certificates
    {A x y L : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y) :
    canonicalResidualPrimeProduct
        (A := A) (L := L) hx hy =
      ∏ C :
          {C : (largePrimeGraph x y L).ConnectedComponent //
            C ∈ canonicalResidualComponents A x y L},
        (canonicalResidualCertificates hx hy C).prime := by
  classical
  unfold canonicalResidualPrimeProduct
  unfold canonicalResidualCertificatePrimes
  unfold ResidualCertificates.canonicalCertificatePrimes
  rw [Finset.prod_image]
  · rw [Finset.attach_eq_univ]
    rfl
  · intro C₁ _hC₁ C₂ _hC₂ hprime
    exact
      canonicalResidualCertificates_prime_injective hx hy hprime

/-- Every factor of `P#` is a genuine prime strictly above `L + 1`. -/
theorem prime_large_of_mem_canonicalResidualCertificatePrimes
    {A x y L p : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hp :
      p ∈ canonicalResidualCertificatePrimes
        (A := A) (L := L) hx hy) :
    IsLargePrime L p := by
  classical
  unfold canonicalResidualCertificatePrimes at hp
  unfold ResidualCertificates.canonicalCertificatePrimes at hp
  rw [Finset.mem_image] at hp
  obtain ⟨C, _hC, rfl⟩ := hp
  exact (canonicalResidualCertificates hx hy C).prime_large

/-- The canonical residual prime product is positive. -/
theorem canonicalResidualPrimeProduct_pos
    {A x y L : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y) :
    0 < canonicalResidualPrimeProduct
      (A := A) (L := L) hx hy := by
  unfold canonicalResidualPrimeProduct
  apply Finset.prod_pos
  intro p hp
  exact
    (prime_large_of_mem_canonicalResidualCertificatePrimes
      hx hy hp).1.pos

/-- In particular, the empty-product convention included, `1 ≤ P#`. -/
theorem one_le_canonicalResidualPrimeProduct
    {A x y L : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y) :
    1 ≤ canonicalResidualPrimeProduct
      (A := A) (L := L) hx hy := by
  exact canonicalResidualPrimeProduct_pos hx hy

/--
The number of factors of `P#` is exactly the canonical residual component
count `c#`.
-/
theorem canonicalResidualPrimeProduct_factorCount
    {A x y L : ℕ}
    (hx : 2 ≤ x) (hy : 2 ≤ y) :
    (canonicalResidualCertificatePrimes
        (A := A) (L := L)
        (show 1 ≤ x by omega) (show 1 ≤ y by omega)).card =
      canonicalResidualComponentCount A x y L :=
  card_canonicalResidualCertificatePrimes hx hy

/-! ## The two `P#` branches -/

/-- The small-product branch of Section 7: `P# ≤ N`. -/
def CanonicalResidualPrimeProductAtMost
    {A x y L : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y) (N : ℕ) : Prop :=
  canonicalResidualPrimeProduct
    (A := A) (L := L) hx hy ≤ N

/-- The complementary large-product branch of Section 7: `N < P#`. -/
def CanonicalResidualPrimeProductExceeds
    {A x y L : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y) (N : ℕ) : Prop :=
  N < canonicalResidualPrimeProduct
    (A := A) (L := L) hx hy

@[simp]
theorem canonicalResidualPrimeProductAtMost_iff
    {A x y L N : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y) :
    CanonicalResidualPrimeProductAtMost
        (A := A) (L := L) hx hy N ↔
      canonicalResidualPrimeProduct
        (A := A) (L := L) hx hy ≤ N :=
  Iff.rfl

@[simp]
theorem canonicalResidualPrimeProductExceeds_iff
    {A x y L N : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y) :
    CanonicalResidualPrimeProductExceeds
        (A := A) (L := L) hx hy N ↔
      N < canonicalResidualPrimeProduct
        (A := A) (L := L) hx hy :=
  Iff.rfl

/-- Every cutoff lies in exactly one of the small- or large-product cases. -/
theorem canonicalResidualPrimeProduct_dichotomy
    {A x y L : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y) (N : ℕ) :
    CanonicalResidualPrimeProductAtMost
        (A := A) (L := L) hx hy N ∨
      CanonicalResidualPrimeProductExceeds
        (A := A) (L := L) hx hy N := by
  unfold CanonicalResidualPrimeProductAtMost
  unfold CanonicalResidualPrimeProductExceeds
  exact le_or_gt _ _

/-- The two branches are disjoint. -/
theorem canonicalResidualPrimeProduct_branches_disjoint
    {A x y L : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y) (N : ℕ) :
    ¬(CanonicalResidualPrimeProductAtMost
          (A := A) (L := L) hx hy N ∧
        CanonicalResidualPrimeProductExceeds
          (A := A) (L := L) hx hy N) := by
  intro h
  exact (Nat.not_lt_of_ge h.1) h.2

@[simp]
theorem canonicalResidualPrimeProductAtMost_iff_not_exceeds
    {A x y L : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y) (N : ℕ) :
    CanonicalResidualPrimeProductAtMost
        (A := A) (L := L) hx hy N ↔
      ¬CanonicalResidualPrimeProductExceeds
        (A := A) (L := L) hx hy N := by
  simp [CanonicalResidualPrimeProductAtMost,
    CanonicalResidualPrimeProductExceeds]

@[simp]
theorem canonicalResidualPrimeProductExceeds_iff_not_atMost
    {A x y L : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y) (N : ℕ) :
    CanonicalResidualPrimeProductExceeds
        (A := A) (L := L) hx hy N ↔
      ¬CanonicalResidualPrimeProductAtMost
        (A := A) (L := L) hx hy N := by
  simp [CanonicalResidualPrimeProductAtMost,
    CanonicalResidualPrimeProductExceeds]

end

end CanonicalResidualComponents
end PaperC
