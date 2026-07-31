import PaperC.Combinatorics.CanonicalResidualPrimeProduct
import PaperC.Combinatorics.CertificateCRTInstantiation
import PaperC.Arithmetic.StartResidue

set_option maxHeartbeats 1800000

/-!
# The full canonical residual CRT certificate

This file turns the canonical certificates of Lemma 6.5 into one concrete
certificate to which the CRT machinery of Lemma 7.1 applies.  Its index set
is the finite type of canonical residual components, its moduli are the
selected primes, and its two residues encode divisibility of the left and
right start labels.
-/

namespace PaperC
namespace CanonicalResidualComponents

open LargePrimeGraph
open ResidualComponentCounts
open scoped BigOperators

noncomputable section

/-- The finite type indexing the canonical residual certificates. -/
abbrev CanonicalResidualCertificateIndex
    (A x y L : ℕ) :=
  {C : (largePrimeGraph x y L).ConnectedComponent //
    C ∈ canonicalResidualComponents A x y L}

/-- The modulus attached to a canonical residual component. -/
noncomputable def canonicalResidualCertificateModulus
    {A x y L : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y) :
    CanonicalResidualCertificateIndex A x y L → ℕ :=
  fun C ↦ (canonicalResidualCertificates hx hy C).prime

/-- The residue imposed on the left start by one residual certificate. -/
noncomputable def canonicalResidualCertificateLeftResidue
    {A x y L : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y) :
    CanonicalResidualCertificateIndex A x y L → ℕ :=
  fun C ↦
    CRT.startResidue
      (canonicalResidualCertificateModulus hx hy C)
      (canonicalResidualCertificates hx hy C).left

/-- The residue imposed on the right start by one residual certificate. -/
noncomputable def canonicalResidualCertificateRightResidue
    {A x y L : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y) :
    CanonicalResidualCertificateIndex A x y L → ℕ :=
  fun C ↦
    CRT.startResidue
      (canonicalResidualCertificateModulus hx hy C)
      (canonicalResidualCertificates hx hy C).right

/-- Every canonical residual modulus is prime. -/
theorem canonicalResidualCertificateModulus_prime
    {A x y L : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    (C : CanonicalResidualCertificateIndex A x y L) :
    (canonicalResidualCertificateModulus hx hy C).Prime :=
  (canonicalResidualCertificates hx hy C).prime_large.1

/--
The complete unordered certificate: it selects every canonical residual
component.  Its size is the corrected component count `c#`.
-/
noncomputable def canonicalResidualFullCertificate
    {A x y L : ℕ}
    (hx : 2 ≤ x) (hy : 2 ≤ y) :
    CRT.UnorderedCertificate
      (Finset.univ :
        Finset (CanonicalResidualCertificateIndex A x y L))
      (canonicalResidualComponentCount A x y L) := by
  classical
  refine ⟨Finset.univ, Finset.mem_powersetCard.mpr ⟨Finset.Subset.rfl, ?_⟩⟩
  rw [Finset.card_univ]
  exact card_canonicalResidualCertificateIndex hx hy

@[simp]
theorem canonicalResidualFullCertificate_coe
    {A x y L : ℕ}
    (hx : 2 ≤ x) (hy : 2 ≤ y) :
    (canonicalResidualFullCertificate (A := A) (L := L) hx hy).1 =
      (Finset.univ :
        Finset (CanonicalResidualCertificateIndex A x y L)) := by
  rfl

@[simp]
theorem canonicalResidualFullCertificate_card
    {A x y L : ℕ}
    (hx : 2 ≤ x) (hy : 2 ≤ y) :
    (canonicalResidualFullCertificate
        (A := A) (L := L) hx hy).1.card =
      canonicalResidualComponentCount A x y L := by
  classical
  exact
    CRT.unorderedCertificate_card
      (canonicalResidualFullCertificate (A := A) (L := L) hx hy)

/--
The CRT modulus product of the complete certificate is exactly the canonical
prime product `P#`.
-/
theorem canonicalResidualFullCertificate_modulusProduct
    {A x y L : ℕ}
    (hx : 2 ≤ x) (hy : 2 ≤ y) :
    CRT.certificateModulusProduct
        (canonicalResidualCertificateModulus
          (A := A) (L := L)
          (show 1 ≤ x by omega) (show 1 ≤ y by omega))
        (canonicalResidualFullCertificate (A := A) (L := L) hx hy) =
      canonicalResidualPrimeProduct
        (A := A) (L := L)
        (show 1 ≤ x by omega) (show 1 ≤ y by omega) := by
  rw [canonicalResidualPrimeProduct_eq_product_certificates]
  simp [CRT.certificateModulusProduct,
    canonicalResidualCertificateModulus]

/--
The moduli occurring in the complete certificate are pairwise distinct.
-/
theorem canonicalResidualFullCertificate_moduli_pairwise
    {A x y L : ℕ}
    (hx : 2 ≤ x) (hy : 2 ≤ y) :
    (canonicalResidualFullCertificate
      (A := A) (L := L) hx hy).1.toList.Pairwise
      (fun C₁ C₂ ↦
        canonicalResidualCertificateModulus
            (A := A) (L := L)
            (show 1 ≤ x by omega) (show 1 ≤ y by omega) C₁ ≠
          canonicalResidualCertificateModulus
            (A := A) (L := L)
            (show 1 ≤ x by omega) (show 1 ≤ y by omega) C₂) := by
  classical
  apply
    (canonicalResidualFullCertificate
      (A := A) (L := L) hx hy).1.nodup_toList
      |>.pairwise_of_forall_ne
  intro C₁ _hC₁ C₂ _hC₂ hC
  exact
    (canonicalResidualCertificates_prime_injective
      (A := A) (L := L)
      (show 1 ≤ x by omega) (show 1 ≤ y by omega)).ne hC

/--
Admissibility of the complete certificate is exactly the small-product
branch `P# ≤ N`.
-/
theorem canonicalResidualFullCertificate_admissible_iff
    {A x y L N : ℕ}
    (hx : 2 ≤ x) (hy : 2 ≤ y) :
    CRT.CertificateAdmissible
        (canonicalResidualCertificateModulus
          (A := A) (L := L)
          (show 1 ≤ x by omega) (show 1 ≤ y by omega))
        N
        (canonicalResidualFullCertificate
          (A := A) (L := L) hx hy) ↔
      CanonicalResidualPrimeProductAtMost
        (A := A) (L := L)
        (show 1 ≤ x by omega) (show 1 ≤ y by omega) N := by
  unfold CRT.CertificateAdmissible
  unfold CanonicalResidualPrimeProductAtMost
  constructor
  · intro h
    rw [canonicalResidualFullCertificate_modulusProduct
      (A := A) (L := L) hx hy] at h
    exact h.2
  · intro h
    constructor
    · exact
        canonicalResidualFullCertificate_moduli_pairwise
          (A := A) (L := L) hx hy
    · rw [canonicalResidualFullCertificate_modulusProduct
        (A := A) (L := L) hx hy]
      exact h

/-! ## The two starts satisfy every selected congruence -/

/-- The left start satisfies the congruence attached to one component. -/
theorem canonicalResidual_left_modEq
    {A x y L : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    (C : CanonicalResidualCertificateIndex A x y L) :
    x ≡ canonicalResidualCertificateLeftResidue hx hy C
      [MOD canonicalResidualCertificateModulus hx hy C] := by
  apply
    (CRT.modEq_startResidue_iff_dvd_startCompleteVertexLabel
      (canonicalResidualCertificates hx hy C).left
      (canonicalResidualCertificateModulus_prime hx hy C).pos
      hx).2
  exact (canonicalResidualCertificates hx hy C).prime_dvd_left_label

/-- The right start satisfies the congruence attached to one component. -/
theorem canonicalResidual_right_modEq
    {A x y L : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    (C : CanonicalResidualCertificateIndex A x y L) :
    y ≡ canonicalResidualCertificateRightResidue hx hy C
      [MOD canonicalResidualCertificateModulus hx hy C] := by
  apply
    (CRT.modEq_startResidue_iff_dvd_startCompleteVertexLabel
      (canonicalResidualCertificates hx hy C).right
      (canonicalResidualCertificateModulus_prime hx hy C).pos
      hy).2
  exact (canonicalResidualCertificates hx hy C).prime_dvd_right_label

/-- The left start satisfies all congruences of the complete certificate. -/
theorem canonicalResidual_left_satisfies_fullCertificate
    {A x y L : ℕ}
    (hx : 2 ≤ x) (hy : 2 ≤ y) :
    ∀ C ∈
        (canonicalResidualFullCertificate
          (A := A) (L := L) hx hy).1.toList,
      x ≡
        canonicalResidualCertificateLeftResidue
          (A := A) (L := L)
          (show 1 ≤ x by omega) (show 1 ≤ y by omega) C
        [MOD
          canonicalResidualCertificateModulus
            (A := A) (L := L)
            (show 1 ≤ x by omega) (show 1 ≤ y by omega) C] := by
  intro C _hC
  exact
    canonicalResidual_left_modEq
      (A := A) (L := L)
      (show 1 ≤ x by omega) (show 1 ≤ y by omega) C

/-- The right start satisfies all congruences of the complete certificate. -/
theorem canonicalResidual_right_satisfies_fullCertificate
    {A x y L : ℕ}
    (hx : 2 ≤ x) (hy : 2 ≤ y) :
    ∀ C ∈
        (canonicalResidualFullCertificate
          (A := A) (L := L) hx hy).1.toList,
      y ≡
        canonicalResidualCertificateRightResidue
          (A := A) (L := L)
          (show 1 ≤ x by omega) (show 1 ≤ y by omega) C
        [MOD
          canonicalResidualCertificateModulus
            (A := A) (L := L)
            (show 1 ≤ x by omega) (show 1 ≤ y by omega) C] := by
  intro C _hC
  exact
    canonicalResidual_right_modEq
      (A := A) (L := L)
      (show 1 ≤ x by omega) (show 1 ≤ y by omega) C

/--
If the two starts lie in the prescribed intervals, their pair belongs to
the rectangular CRT solution set of the complete residual certificate.
-/
theorem canonicalResidual_pair_mem_fullCertificateSolutions
    {A x y L a₁ b₁ a₂ b₂ : ℕ}
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hxI : x ∈ Finset.Ico a₁ b₁)
    (hyI : y ∈ Finset.Ico a₂ b₂) :
    (x, y) ∈
      (({z ∈ Finset.Ico a₁ b₁ |
          ∀ C ∈
              (canonicalResidualFullCertificate
                (A := A) (L := L) hx hy).1.toList,
            z ≡
              canonicalResidualCertificateLeftResidue
                (A := A) (L := L)
                (show 1 ≤ x by omega) (show 1 ≤ y by omega) C
              [MOD
                canonicalResidualCertificateModulus
                  (A := A) (L := L)
                  (show 1 ≤ x by omega) (show 1 ≤ y by omega) C]}) ×ˢ
        {z ∈ Finset.Ico a₂ b₂ |
          ∀ C ∈
              (canonicalResidualFullCertificate
                (A := A) (L := L) hx hy).1.toList,
            z ≡
              canonicalResidualCertificateRightResidue
                (A := A) (L := L)
                (show 1 ≤ x by omega) (show 1 ≤ y by omega) C
              [MOD
                canonicalResidualCertificateModulus
                  (A := A) (L := L)
                  (show 1 ≤ x by omega) (show 1 ≤ y by omega) C]}) := by
  rw [Finset.mem_product]
  constructor
  · rw [Finset.mem_filter]
    exact
      ⟨hxI, canonicalResidual_left_satisfies_fullCertificate hx hy⟩
  · rw [Finset.mem_filter]
    exact
      ⟨hyI, canonicalResidual_right_satisfies_fullCertificate hx hy⟩

end

end CanonicalResidualComponents
end PaperC
