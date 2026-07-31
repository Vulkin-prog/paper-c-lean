import PaperC.Arithmetic.CertificateCount
import PaperC.Combinatorics.CertificateSummation
import Mathlib.Data.Nat.Prime.Basic

/-!
# CRT instantiation of unordered certificate sums

This file joins the two finite ingredients of Paper C, Lemma 7.1:

* a certificate whose moduli are distinct primes is a pairwise-coprime CRT
  certificate;
* if its modulus product is at most `N`, its solutions in intervals of length
  at most `C₀ * N` satisfy the scaled one- and two-dimensional bounds.

The subsequent summation retains only admissible certificates and then drops
that restriction by nonnegativity, exposing the elementary-symmetric sum from
`CertificateSummation`.
-/

namespace PaperC
namespace CRT

open Finset
open scoped BigOperators
open scoped Function

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Product of the moduli selected by an unordered certificate. -/
def certificateModulusProduct
    {s : Finset ι} {r : ℕ} (modulus : ι → ℕ)
    (T : UnorderedCertificate s r) : ℕ :=
  ∏ i ∈ T.1, modulus i

/--
The admissibility conditions used in Lemma 7.1: distinct selected moduli and
product at most `N`.  Primality is imposed once on the ambient cell family.
-/
def CertificateAdmissible
    {s : Finset ι} {r : ℕ} (modulus : ι → ℕ) (N : ℕ)
    (T : UnorderedCertificate s r) : Prop :=
  T.1.toList.Pairwise (fun i j ↦ modulus i ≠ modulus j) ∧
    certificateModulusProduct modulus T ≤ N

noncomputable instance certificateAdmissibleDecidable
    {s : Finset ι} {r : ℕ} (modulus : ι → ℕ) (N : ℕ)
    (T : UnorderedCertificate s r) :
    Decidable (CertificateAdmissible modulus N T) :=
  Classical.dec _

/-- Distinct prime moduli in an admissible certificate are pairwise coprime. -/
theorem certificate_pairwise_coprime
    {s : Finset ι} {r : ℕ} (modulus : ι → ℕ)
    (T : UnorderedCertificate s r)
    (hprime : ∀ i, (modulus i).Prime)
    (hdistinct :
      T.1.toList.Pairwise (fun i j ↦ modulus i ≠ modulus j)) :
    T.1.toList.Pairwise (Nat.Coprime on modulus) := by
  exact hdistinct.imp fun {i j} hij ↦
    (Nat.coprime_primes (hprime i) (hprime j)).2 hij

/-- Number of one-dimensional interval solutions associated with `T`. -/
noncomputable def certificateSolutionCount
    {s : Finset ι} {r : ℕ}
    (residue modulus : ι → ℕ) (a b : ℕ)
    (T : UnorderedCertificate s r) : ℕ :=
  #{x ∈ Ico a b |
      ∀ i ∈ T.1.toList, x ≡ residue i [MOD modulus i]}

/-- Number of rectangular solutions associated with `T`. -/
noncomputable def certificatePairSolutionCount
    {s : Finset ι} {r : ℕ}
    (residue₁ residue₂ modulus : ι → ℕ)
    (a₁ b₁ a₂ b₂ : ℕ)
    (T : UnorderedCertificate s r) : ℕ :=
  (({x ∈ Ico a₁ b₁ |
        ∀ i ∈ T.1.toList, x ≡ residue₁ i [MOD modulus i]} ×ˢ
      {y ∈ Ico a₂ b₂ |
        ∀ i ∈ T.1.toList, y ≡ residue₂ i [MOD modulus i]}).card)

/--
Per-certificate one-dimensional CRT estimate, including the absorption of the
endpoint term under `P ≤ N`.
-/
theorem certificateSolutionCount_cast_le_scaled
    {s : Finset ι} {r : ℕ}
    (residue modulus : ι → ℕ)
    (hprime : ∀ i, (modulus i).Prime)
    (a b C₀ N : ℕ) (hab : a ≤ b)
    (hlength : b - a ≤ C₀ * N)
    (T : UnorderedCertificate s r)
    (hT : CertificateAdmissible modulus N T) :
    (certificateSolutionCount residue modulus a b T : ℚ) ≤
      ((((C₀ + 1) * N : ℕ) : ℚ) /
        (certificateModulusProduct modulus T : ℚ)) := by
  have hcoprime :
      T.1.toList.Pairwise (Nat.Coprime on modulus) :=
    certificate_pairwise_coprime modulus T hprime hT.1
  have hpositive : ∀ i ∈ T.1.toList, 0 < modulus i := by
    intro i hi
    exact (hprime i).pos
  simpa [certificateSolutionCount, certificateModulusProduct] using
    card_Ico_satisfies_cast_le_scaled
      residue modulus T.1.toList hcoprime hpositive
      a b C₀ N hab hlength (by
        simpa [certificateModulusProduct] using hT.2)

/--
Per-certificate two-dimensional CRT estimate on the explicit rectangular
domain of version 7c.
-/
theorem certificatePairSolutionCount_cast_le_scaled
    {s : Finset ι} {r : ℕ}
    (residue₁ residue₂ modulus : ι → ℕ)
    (hprime : ∀ i, (modulus i).Prime)
    (a₁ b₁ a₂ b₂ C₀ N : ℕ)
    (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂)
    (hlength₁ : b₁ - a₁ ≤ C₀ * N)
    (hlength₂ : b₂ - a₂ ≤ C₀ * N)
    (T : UnorderedCertificate s r)
    (hT : CertificateAdmissible modulus N T) :
    (certificatePairSolutionCount
        residue₁ residue₂ modulus a₁ b₁ a₂ b₂ T : ℚ) ≤
      (((((C₀ + 1) * N : ℕ) : ℚ) /
        (certificateModulusProduct modulus T : ℚ)) ^ 2) := by
  have hcoprime :
      T.1.toList.Pairwise (Nat.Coprime on modulus) :=
    certificate_pairwise_coprime modulus T hprime hT.1
  have hpositive : ∀ i ∈ T.1.toList, 0 < modulus i := by
    intro i hi
    exact (hprime i).pos
  simpa [certificatePairSolutionCount, certificateModulusProduct] using
    card_product_Ico_satisfies_cast_le_scaled
      residue₁ residue₂ modulus T.1.toList hcoprime hpositive
      a₁ b₁ a₂ b₂ C₀ N h₁ h₂ hlength₁ hlength₂ (by
        simpa [certificateModulusProduct] using hT.2)

/--
The product of the local one-dimensional weights is exactly `u^r / P`.
-/
theorem certificate_product_div_modulus
    {s : Finset ι} {r : ℕ} (modulus : ι → ℕ)
    (u : ℚ) (T : UnorderedCertificate s r) :
    (∏ i ∈ T.1, u / (modulus i : ℚ)) =
      u ^ r / (certificateModulusProduct modulus T : ℚ) := by
  rw [Finset.prod_div_distrib]
  simp [certificateModulusProduct, unorderedCertificate_card]

/--
The product of the local two-dimensional weights is exactly `u^r / P²`.
-/
theorem certificate_product_div_modulus_sq
    {s : Finset ι} {r : ℕ} (modulus : ι → ℕ)
    (u : ℚ) (T : UnorderedCertificate s r) :
    (∏ i ∈ T.1, u / (modulus i : ℚ) ^ 2) =
      u ^ r / (certificateModulusProduct modulus T : ℚ) ^ 2 := by
  rw [Finset.prod_div_distrib]
  simp [certificateModulusProduct, unorderedCertificate_card,
    Finset.prod_pow]

/--
Weighted sum of the one-dimensional solution counts over admissible
unordered certificates of one fixed size.
-/
noncomputable def admissibleCertificateSolutionMass
    (s : Finset ι) (r : ℕ)
    (residue modulus : ι → ℕ)
    (a b N : ℕ) (u : ℚ) : ℚ :=
  ∑ T : UnorderedCertificate s r,
    if CertificateAdmissible modulus N T then
      u ^ r * (certificateSolutionCount residue modulus a b T : ℚ)
    else 0

/--
Weighted sum of the rectangular solution counts over admissible unordered
certificates of one fixed size.
-/
noncomputable def admissibleCertificatePairSolutionMass
    (s : Finset ι) (r : ℕ)
    (residue₁ residue₂ modulus : ι → ℕ)
    (a₁ b₁ a₂ b₂ N : ℕ) (u : ℚ) : ℚ :=
  ∑ T : UnorderedCertificate s r,
    if CertificateAdmissible modulus N T then
      u ^ r *
        (certificatePairSolutionCount
          residue₁ residue₂ modulus a₁ b₁ a₂ b₂ T : ℚ)
    else 0

/--
Fixed-size one-dimensional form of equation (7.1), indexed directly by the
finite family of admissible cells.  Repeated primes are discarded by
`CertificateAdmissible`; dropping that restriction produces the symmetric
sum and hence the exact factor `1 / r!`.
-/
theorem admissibleCertificateSolutionMass_le
    (s : Finset ι) (r : ℕ)
    (residue modulus : ι → ℕ)
    (hprime : ∀ i, (modulus i).Prime)
    (a b C₀ N : ℕ) (hab : a ≤ b)
    (hlength : b - a ≤ C₀ * N)
    (u : ℚ) (hu : 0 ≤ u) :
    admissibleCertificateSolutionMass
        s r residue modulus a b N u ≤
      (((C₀ + 1) * N : ℕ) : ℚ) *
        ((∑ i ∈ s, u / (modulus i : ℚ)) ^ r /
          r.factorial) := by
  classical
  let V : ℚ := (((C₀ + 1) * N : ℕ) : ℚ)
  have hV : 0 ≤ V := by
    dsimp [V]
    positivity
  have hw : ∀ i ∈ s, 0 ≤ u / (modulus i : ℚ) := by
    intro i hi
    exact div_nonneg hu (by exact_mod_cast (hprime i).pos.le)
  calc
    admissibleCertificateSolutionMass
        s r residue modulus a b N u ≤
        ∑ T : UnorderedCertificate s r,
          V * ∏ i ∈ T.1, u / (modulus i : ℚ) := by
      unfold admissibleCertificateSolutionMass
      apply Finset.sum_le_sum
      intro T hTuniv
      by_cases hT : CertificateAdmissible modulus N T
      · simp only [if_pos hT]
        have hcount :=
          certificateSolutionCount_cast_le_scaled
            residue modulus hprime a b C₀ N hab hlength T hT
        have hweighted :=
          mul_le_mul_of_nonneg_left hcount (pow_nonneg hu r)
        calc
          u ^ r *
              (certificateSolutionCount residue modulus a b T : ℚ) ≤
              u ^ r * (V / (certificateModulusProduct modulus T : ℚ)) := by
            simpa [V] using hweighted
          _ = V * ∏ i ∈ T.1, u / (modulus i : ℚ) := by
            rw [certificate_product_div_modulus]
            ring
      · simp only [if_neg hT]
        exact mul_nonneg hV
          (Finset.prod_nonneg fun i hi ↦
            hw i (unorderedCertificate_subset T hi))
    _ = V * certificateWeightSum s r
        (fun i ↦ u / (modulus i : ℚ)) := by
      simp [certificateWeightSum, Finset.mul_sum]
    _ ≤ V *
        ((∑ i ∈ s, u / (modulus i : ℚ)) ^ r /
          r.factorial) := by
      exact mul_le_mul_of_nonneg_left
        (certificateWeightSum_le_pow_sum_div_factorial
          s r (fun i ↦ u / (modulus i : ℚ)) hw) hV
    _ = (((C₀ + 1) * N : ℕ) : ℚ) *
        ((∑ i ∈ s, u / (modulus i : ℚ)) ^ r /
          r.factorial) := by
      rfl

/--
Fixed-size two-dimensional form of equation (7.2), on the explicit product
of two intervals from version 7c.
-/
theorem admissibleCertificatePairSolutionMass_le
    (s : Finset ι) (r : ℕ)
    (residue₁ residue₂ modulus : ι → ℕ)
    (hprime : ∀ i, (modulus i).Prime)
    (a₁ b₁ a₂ b₂ C₀ N : ℕ)
    (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂)
    (hlength₁ : b₁ - a₁ ≤ C₀ * N)
    (hlength₂ : b₂ - a₂ ≤ C₀ * N)
    (u : ℚ) (hu : 0 ≤ u) :
    admissibleCertificatePairSolutionMass
        s r residue₁ residue₂ modulus a₁ b₁ a₂ b₂ N u ≤
      ((((C₀ + 1) * N : ℕ) : ℚ) ^ 2) *
        ((∑ i ∈ s, u / (modulus i : ℚ) ^ 2) ^ r /
          r.factorial) := by
  classical
  let V : ℚ := (((C₀ + 1) * N : ℕ) : ℚ)
  have hV : 0 ≤ V := by
    dsimp [V]
    positivity
  have hw : ∀ i ∈ s, 0 ≤ u / (modulus i : ℚ) ^ 2 := by
    intro i hi
    exact div_nonneg hu (sq_nonneg _)
  calc
    admissibleCertificatePairSolutionMass
        s r residue₁ residue₂ modulus a₁ b₁ a₂ b₂ N u ≤
        ∑ T : UnorderedCertificate s r,
          V ^ 2 * ∏ i ∈ T.1, u / (modulus i : ℚ) ^ 2 := by
      unfold admissibleCertificatePairSolutionMass
      apply Finset.sum_le_sum
      intro T hTuniv
      by_cases hT : CertificateAdmissible modulus N T
      · simp only [if_pos hT]
        have hcount :=
          certificatePairSolutionCount_cast_le_scaled
            residue₁ residue₂ modulus hprime
            a₁ b₁ a₂ b₂ C₀ N h₁ h₂
            hlength₁ hlength₂ T hT
        have hweighted :=
          mul_le_mul_of_nonneg_left hcount (pow_nonneg hu r)
        calc
          u ^ r *
              (certificatePairSolutionCount
                residue₁ residue₂ modulus a₁ b₁ a₂ b₂ T : ℚ) ≤
              u ^ r *
                (V / (certificateModulusProduct modulus T : ℚ)) ^ 2 := by
            simpa [V] using hweighted
          _ = V ^ 2 *
              ∏ i ∈ T.1, u / (modulus i : ℚ) ^ 2 := by
            rw [certificate_product_div_modulus_sq]
            ring
      · simp only [if_neg hT]
        exact mul_nonneg (sq_nonneg V)
          (Finset.prod_nonneg fun i hi ↦
            hw i (unorderedCertificate_subset T hi))
    _ = V ^ 2 * certificateWeightSum s r
        (fun i ↦ u / (modulus i : ℚ) ^ 2) := by
      simp [certificateWeightSum, Finset.mul_sum]
    _ ≤ V ^ 2 *
        ((∑ i ∈ s, u / (modulus i : ℚ) ^ 2) ^ r /
          r.factorial) := by
      exact mul_le_mul_of_nonneg_left
        (certificateWeightSum_le_pow_sum_div_factorial
          s r (fun i ↦ u / (modulus i : ℚ) ^ 2) hw)
        (sq_nonneg V)
    _ = ((((C₀ + 1) * N : ℕ) : ℚ) ^ 2) *
        ((∑ i ∈ s, u / (modulus i : ℚ) ^ 2) ^ r /
          r.factorial) := by
      rfl

/--
Finite partial-sum form of the one-dimensional conclusion (7.1).
Choosing `R = s.card + 1` includes every nonempty certificate size.
-/
theorem sum_admissibleCertificateSolutionMass_le
    (s : Finset ι) (R : ℕ)
    (residue modulus : ι → ℕ)
    (hprime : ∀ i, (modulus i).Prime)
    (a b C₀ N : ℕ) (hab : a ≤ b)
    (hlength : b - a ≤ C₀ * N)
    (u : ℚ) (hu : 0 ≤ u) :
    (∑ r ∈ Finset.range R,
        admissibleCertificateSolutionMass
          s r residue modulus a b N u) ≤
      (((C₀ + 1) * N : ℕ) : ℚ) *
        ∑ r ∈ Finset.range R,
          (∑ i ∈ s, u / (modulus i : ℚ)) ^ r /
            r.factorial := by
  calc
    (∑ r ∈ Finset.range R,
        admissibleCertificateSolutionMass
          s r residue modulus a b N u) ≤
        ∑ r ∈ Finset.range R,
          (((C₀ + 1) * N : ℕ) : ℚ) *
            ((∑ i ∈ s, u / (modulus i : ℚ)) ^ r /
              r.factorial) := by
      apply Finset.sum_le_sum
      intro r hr
      exact admissibleCertificateSolutionMass_le
        s r residue modulus hprime a b C₀ N hab hlength u hu
    _ = (((C₀ + 1) * N : ℕ) : ℚ) *
        ∑ r ∈ Finset.range R,
          (∑ i ∈ s, u / (modulus i : ℚ)) ^ r /
            r.factorial := by
      rw [Finset.mul_sum]

/--
Finite partial-sum form of the two-dimensional conclusion (7.2).
-/
theorem sum_admissibleCertificatePairSolutionMass_le
    (s : Finset ι) (R : ℕ)
    (residue₁ residue₂ modulus : ι → ℕ)
    (hprime : ∀ i, (modulus i).Prime)
    (a₁ b₁ a₂ b₂ C₀ N : ℕ)
    (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂)
    (hlength₁ : b₁ - a₁ ≤ C₀ * N)
    (hlength₂ : b₂ - a₂ ≤ C₀ * N)
    (u : ℚ) (hu : 0 ≤ u) :
    (∑ r ∈ Finset.range R,
        admissibleCertificatePairSolutionMass
          s r residue₁ residue₂ modulus a₁ b₁ a₂ b₂ N u) ≤
      ((((C₀ + 1) * N : ℕ) : ℚ) ^ 2) *
        ∑ r ∈ Finset.range R,
          (∑ i ∈ s, u / (modulus i : ℚ) ^ 2) ^ r /
            r.factorial := by
  calc
    (∑ r ∈ Finset.range R,
        admissibleCertificatePairSolutionMass
          s r residue₁ residue₂ modulus a₁ b₁ a₂ b₂ N u) ≤
        ∑ r ∈ Finset.range R,
          ((((C₀ + 1) * N : ℕ) : ℚ) ^ 2) *
            ((∑ i ∈ s, u / (modulus i : ℚ) ^ 2) ^ r /
              r.factorial) := by
      apply Finset.sum_le_sum
      intro r hr
      exact admissibleCertificatePairSolutionMass_le
        s r residue₁ residue₂ modulus hprime
        a₁ b₁ a₂ b₂ C₀ N h₁ h₂ hlength₁ hlength₂ u hu
    _ = ((((C₀ + 1) * N : ℕ) : ℚ) ^ 2) *
        ∑ r ∈ Finset.range R,
          (∑ i ∈ s, u / (modulus i : ℚ) ^ 2) ^ r /
            r.factorial := by
      rw [Finset.mul_sum]

end CRT
end PaperC
