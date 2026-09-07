import PaperCV282.ClosureCRTIntervals
import PaperCV282.ClosureCRTSummation

/-!
# Real weighted masses of actual unordered CRT certificates

The finite algebraic bound is instantiated with the proved integer interval
counts. All public interval bounds take only primality, interval length and
nonnegative weights, never a conjectural counting estimate.
-/

namespace PaperC.V282.ClosureCRTMass

open CRT Finset ClosureCRTIntervals
open scoped BigOperators

noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A fixed-size real weighted mass; admissibility enforces distinct primes and product ≤ M. -/
def certificateMass (s : Finset ι) (r : ℕ) (modulus : ι → ℕ)
    (count : UnorderedCertificate s r → ℕ) (M : ℕ) (u : ℝ) : ℝ :=
  ∑ T : UnorderedCertificate s r,
    if CertificateAdmissible modulus M T then u ^ r * count T else 0

/-- Exact factorization of the local weights in any coordinate dimension. -/
theorem product_local_weight {s : Finset ι} {r : ℕ} (modulus : ι → ℕ)
    (D : ℕ) (u : ℝ) (T : UnorderedCertificate s r) :
    (∏ i ∈ T.1, u / (modulus i : ℝ) ^ D) =
      u ^ r / (certificateModulusProduct modulus T : ℝ) ^ D := by
  rw [Finset.prod_div_distrib]
  simp [certificateModulusProduct, unorderedCertificate_card, Finset.prod_pow]

/-- Finite algebraic summation of individual counts; used below with actual CRT counts. -/
theorem certificateMass_le_of_count
    (s : Finset ι) (r : ℕ) (modulus : ι → ℕ)
    (count : UnorderedCertificate s r → ℕ) (M D : ℕ) (u V : ℝ)
    (hu : 0 ≤ u) (hV : 0 ≤ V)
    (hcount : ∀ T, CertificateAdmissible modulus M T →
      (count T : ℝ) ≤ V / (certificateModulusProduct modulus T : ℝ) ^ D) :
    certificateMass s r modulus count M u ≤
      V * ((∑ i ∈ s, u / (modulus i : ℝ) ^ D) ^ r / r.factorial) := by
  have hw : ∀ i ∈ s, 0 ≤ u / (modulus i : ℝ) ^ D := by intros; positivity
  calc
    certificateMass s r modulus count M u ≤
        ∑ T : UnorderedCertificate s r, V * ∏ i ∈ T.1, u / (modulus i : ℝ) ^ D := by
      unfold certificateMass
      apply Finset.sum_le_sum
      intro T hTuniv
      by_cases hT : CertificateAdmissible modulus M T
      · rw [if_pos hT, product_local_weight]
        calc
          u ^ r * (count T : ℝ) ≤
              u ^ r * (V / (certificateModulusProduct modulus T : ℝ) ^ D) :=
            mul_le_mul_of_nonneg_left (hcount T hT) (pow_nonneg hu r)
          _ = _ := by ring
      · rw [if_neg hT]
        exact mul_nonneg hV (Finset.prod_nonneg fun i hi => hw i (unorderedCertificate_subset T hi))
    _ = V * ClosureCRTSummation.certificateWeightSum s r (fun i => u / (modulus i : ℝ) ^ D) := by
      simp [ClosureCRTSummation.certificateWeightSum, Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (ClosureCRTSummation.certificateWeightSum_le_pow_sum_div_factorial s r _ hw) hV

/-- Actual weighted solutions in one integer interval. -/
def intervalMass (s : Finset ι) (r : ℕ) (residue : ι → ℤ) (modulus : ι → ℕ)
    (a b : ℤ) (M : ℕ) (u : ℝ) : ℝ :=
  certificateMass s r modulus (fun T => (integerSolutions residue modulus a b T).card) M u

/-- Actual weighted solutions in a rectangle of integer intervals. -/
def rectangleMass (s : Finset ι) (r : ℕ) (residue₁ residue₂ : ι → ℤ) (modulus : ι → ℕ)
    (a₁ b₁ a₂ b₂ : ℤ) (M : ℕ) (u : ℝ) : ℝ :=
  certificateMass s r modulus (fun T =>
    (integerSolutions residue₁ modulus a₁ b₁ T ×ˢ integerSolutions residue₂ modulus a₂ b₂ T).card) M u

/-- Fixed-size interval estimate for every nonnegative real weight. -/
theorem intervalMass_le (s : Finset ι) (r : ℕ) (residue : ι → ℤ) (modulus : ι → ℕ)
    (hprime : ∀ i, (modulus i).Prime) (a b : ℤ) (C₀ : ℝ) (M : ℕ)
    (hC : 0 ≤ C₀) (hab : a ≤ b) (hlen : (b - a : ℝ) ≤ C₀ * M)
    (u : ℝ) (hu : 0 ≤ u) :
    intervalMass s r residue modulus a b M u ≤
      ((C₀ + 1) * M) * ((∑ i ∈ s, u / (modulus i : ℝ)) ^ r / r.factorial) := by
  simpa only [intervalMass, pow_one] using certificateMass_le_of_count
    s r modulus (fun T => (integerSolutions residue modulus a b T).card)
    M 1 u ((C₀ + 1) * M) hu (by positivity)
    (fun T hT => by simpa only [pow_one] using
      integerSolutions_card_le residue modulus hprime a b C₀ M hC hab hlen T hT)

/-- Fixed-size rectangular estimate, with no restriction on the size of the real weight. -/
theorem rectangleMass_le (s : Finset ι) (r : ℕ) (residue₁ residue₂ : ι → ℤ) (modulus : ι → ℕ)
    (hprime : ∀ i, (modulus i).Prime) (a₁ b₁ a₂ b₂ : ℤ) (C₀ : ℝ) (M : ℕ)
    (hC : 0 ≤ C₀) (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂)
    (hlen₁ : (b₁ - a₁ : ℝ) ≤ C₀ * M) (hlen₂ : (b₂ - a₂ : ℝ) ≤ C₀ * M)
    (u : ℝ) (hu : 0 ≤ u) :
    rectangleMass s r residue₁ residue₂ modulus a₁ b₁ a₂ b₂ M u ≤
      ((C₀ + 1) * M) ^ 2 * ((∑ i ∈ s, u / (modulus i : ℝ) ^ 2) ^ r / r.factorial) := by
  apply certificateMass_le_of_count s r modulus _ M 2 u (((C₀ + 1) * M) ^ 2) hu (sq_nonneg _)
  intro T hT
  simpa only [div_pow] using
    rectangleSolutions_card_le residue₁ residue₂ modulus hprime a₁ b₁ a₂ b₂ C₀ M
      hC h₁ h₂ hlen₁ hlen₂ T hT

end
end PaperC.V282.ClosureCRTMass
