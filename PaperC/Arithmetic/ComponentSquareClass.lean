import PaperC.Arithmetic.LargeOddKernel

/-!
# Square classes of finite components

This file isolates the exact arithmetic core of Lemma 6.2.  If the parity
vectors of the positive integers in a finite component cancel at every prime
above a cutoff `B`, then their product is a square times a squarefree integer
supported on primes at most `B`.

The squarefree factor is chosen canonically: it is the small odd part of the
component product.  We also prove that any positive squarefree factor with the
same support restriction occurring in such a decomposition is equal to this
canonical factor; the accompanying positive square root is then unique as
well.
-/

namespace PaperC
namespace ComponentSquareClass

open scoped BigOperators

open LargeOddKernel

/-- The product of the (distinct) positive integers in a finite component. -/
def componentProduct (C : Finset ℕ) : ℕ :=
  ∏ n ∈ C, n

/--
The canonical square-class representative of a component product at cutoff
`B`: the product of precisely the primes at most `B` which occur to odd order.
-/
noncomputable def componentSquareClass (B : ℕ) (C : Finset ℕ) : ℕ :=
  smallOddPart B (componentProduct C)

/-- The canonical square part of the component product. -/
noncomputable def componentSquareRoot (C : Finset ℕ) : ℕ :=
  DefectivePredicate.canonicalSquarePart (componentProduct C)

/-- A component of positive integers has nonzero (indeed positive) product. -/
theorem componentProduct_pos
    {C : Finset ℕ}
    (hpos : ∀ n ∈ C, 0 < n) :
    0 < componentProduct C := by
  rw [componentProduct]
  exact Finset.prod_pos fun n hn ↦ hpos n hn

/--
Coordinatewise cancellation above `B` says exactly that the large odd kernel
of the component product is trivial.
-/
theorem largeOddKernel_componentProduct_eq_one
    {B : ℕ} {C : Finset ℕ}
    (hpos : ∀ n ∈ C, 0 < n)
    (hlarge :
      ∀ p : ℕ, p.Prime → B < p →
        (∑ n ∈ C, parityVec n p) = 0) :
    largeOddKernel B (componentProduct C) = 1 := by
  have hnonzero : ∀ n ∈ C, n ≠ 0 := by
    intro n hn
    exact (hpos n hn).ne'
  have hproductParity :
      ∀ p : ℕ, p.Prime → B < p →
        parityVec (componentProduct C) p = 0 := by
    intro p hpPrime hpB
    rw [componentProduct,
      parityVec_prod C (fun n : ℕ ↦ n) hnonzero]
    simpa using hlarge p hpPrime hpB
  rw [largeOddKernel_eq_one_iff_support_eq_empty]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  have hpData := prime_and_large_of_mem_largeOddPrimeSupport hp
  exact (mem_largeOddPrimeSupport_iff.mp hp).2
    (hproductParity p hpData.1 hpData.2)

/--
Canonical square-class decomposition of a finite component.

The four conclusions give positivity and squarefreeness of the canonical
factor, its precise support restriction, positivity of the square root, and
the exact product identity.
-/
theorem canonical_decomposition
    {B : ℕ} {C : Finset ℕ}
    (hpos : ∀ n ∈ C, 0 < n)
    (hlarge :
      ∀ p : ℕ, p.Prime → B < p →
        (∑ n ∈ C, parityVec n p) = 0) :
    0 < componentSquareClass B C ∧
      Squarefree (componentSquareClass B C) ∧
      (∀ p : ℕ, p.Prime → p ∣ componentSquareClass B C → p ≤ B) ∧
      0 < componentSquareRoot C ∧
      componentProduct C =
        componentSquareClass B C * componentSquareRoot C ^ 2 := by
  have hP : componentProduct C ≠ 0 :=
    (componentProduct_pos hpos).ne'
  have hkernel :
      largeOddKernel B (componentProduct C) = 1 :=
    largeOddKernel_componentProduct_eq_one hpos hlarge
  have hdecomp :=
    canonical_largeOddKernel_decomposition (B := B) hP
  have heq :
      componentProduct C =
        componentSquareClass B C * componentSquareRoot C ^ 2 := by
    rw [hkernel, mul_one] at hdecomp
    simpa [componentSquareClass, componentSquareRoot, mul_comm] using hdecomp
  refine ⟨Nat.pos_of_ne_zero (smallOddPart_ne_zero B (componentProduct C)),
    smallOddPart_squarefree B (componentProduct C), ?_, ?_, heq⟩
  · intro p hpPrime hpDvd
    exact
      ((prime_dvd_smallOddPart_iff_small_odd hpPrime).mp hpDvd).1
  · exact Nat.pos_of_ne_zero (canonicalSquarePart_ne_zero hP)

/--
Existential form of the component square-class statement.  This is the direct
arithmetic conclusion used in Lemma 6.2.
-/
theorem exists_squarefree_mul_sq
    {B : ℕ} {C : Finset ℕ}
    (hpos : ∀ n ∈ C, 0 < n)
    (hlarge :
      ∀ p : ℕ, p.Prime → B < p →
        (∑ n ∈ C, parityVec n p) = 0) :
    ∃ d z : ℕ,
      0 < d ∧ Squarefree d ∧
      (∀ p : ℕ, p.Prime → p ∣ d → p ≤ B) ∧
      0 < z ∧ componentProduct C = d * z ^ 2 := by
  refine ⟨componentSquareClass B C, componentSquareRoot C, ?_⟩
  exact canonical_decomposition hpos hlarge

/--
A positive squarefree factor supported at primes at most `B` is forced to be
the canonical component square class.
-/
theorem componentSquareClass_unique
    {B : ℕ} {C : Finset ℕ}
    {d z : ℕ}
    (hdPos : 0 < d)
    (hzPos : 0 < z)
    (hdSquarefree : Squarefree d)
    (hdSupport : ∀ p : ℕ, p.Prime → p ∣ d → p ≤ B)
    (hfactor : componentProduct C = d * z ^ 2) :
    d = componentSquareClass B C := by
  have hd : d ≠ 0 := hdPos.ne'
  have hz : z ^ 2 ≠ 0 := pow_ne_zero 2 hzPos.ne'
  have hparity :
      parityVec (componentProduct C) = parityVec d := by
    rw [hfactor, parityVec_mul hd hz, parityVec_pow_two, add_zero]
  have hprimeFactors :
      d.primeFactors =
        smallOddPrimeSupport B (componentProduct C) := by
    ext p
    constructor
    · intro hp
      have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hpDvd : p ∣ d := Nat.dvd_of_mem_primeFactors hp
      have hpFactorization : d.factorization p = 1 :=
        Nat.factorization_eq_one_of_squarefree
          hdSquarefree hpPrime hpDvd
      have hpParityD : parityVec d p ≠ 0 := by
        simp [parityVec_apply, hpFactorization]
      rw [mem_smallOddPrimeSupport_iff]
      refine ⟨hdSupport p hpPrime hpDvd, ?_⟩
      simpa only [hparity] using hpParityD
    · intro hp
      have hpParityP :
          parityVec (componentProduct C) p ≠ 0 :=
        (mem_smallOddPrimeSupport_iff.mp hp).2
      have hpParityD : parityVec d p ≠ 0 := by
        simpa only [hparity] using hpParityP
      exact Finsupp.support_mapRange
        (mem_oddPrimeSupport_iff_parityVec_ne_zero.mpr hpParityD)
  calc
    d = ∏ p ∈ d.primeFactors, p :=
      (Nat.prod_primeFactors_of_squarefree hdSquarefree).symm
    _ = ∏ p ∈ smallOddPrimeSupport B (componentProduct C), p := by
      rw [hprimeFactors]
    _ = componentSquareClass B C := by
      rfl

/--
The canonical squarefree factor and the positive square root are jointly
unique.
-/
theorem decomposition_unique
    {B : ℕ} {C : Finset ℕ}
    (hpos : ∀ n ∈ C, 0 < n)
    (hlarge :
      ∀ p : ℕ, p.Prime → B < p →
        (∑ n ∈ C, parityVec n p) = 0)
    {d z : ℕ}
    (hdPos : 0 < d)
    (hzPos : 0 < z)
    (hdSquarefree : Squarefree d)
    (hdSupport : ∀ p : ℕ, p.Prime → p ∣ d → p ≤ B)
    (hfactor : componentProduct C = d * z ^ 2) :
    d = componentSquareClass B C ∧ z = componentSquareRoot C := by
  have hd :
      d = componentSquareClass B C :=
    componentSquareClass_unique hdPos hzPos hdSquarefree hdSupport hfactor
  have hcanonical :=
    (canonical_decomposition hpos hlarge).2.2.2.2
  have hsquares :
      z ^ 2 = componentSquareRoot C ^ 2 := by
    apply mul_left_cancel₀ hdPos.ne'
    rw [← hfactor, hd]
    exact hcanonical
  exact ⟨hd, Nat.pow_left_injective (by decide : 2 ≠ 0) hsquares⟩

end ComponentSquareClass
end PaperC
