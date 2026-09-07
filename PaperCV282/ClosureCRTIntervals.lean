import PaperC.Combinatorics.CertificateCRTInstantiation
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# CRT counts on arbitrary translated integer intervals

The interval endpoints and residues may be negative. Its length is bounded
by `C₀*M` for a real constant `C₀`; the bound uses `C₀+1` exactly and does
not depend on the subsequent certificate weight.
-/

namespace PaperC.V282.ClosureCRTIntervals

open CRT Finset
open scoped BigOperators Function

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Genuine integer solutions of the congruences selected by an unordered certificate. -/
def integerSolutions {s : Finset ι} {r : ℕ} (residue : ι → ℤ) (modulus : ι → ℕ)
    (a b : ℤ) (T : UnorderedCertificate s r) : Finset ℤ :=
  (Ico a b).filter fun x => ∀ i ∈ T.1.toList, x ≡ residue i [ZMOD (modulus i : ℤ)]

omit [Fintype ι] [DecidableEq ι] in
/-- Only primes at most `M` can occur; thus the relevant prime family is always finite. -/
theorem modulus_le_of_admissible {s : Finset ι} {r M : ℕ} (modulus : ι → ℕ)
    (hprime : ∀ i, (modulus i).Prime) (T : UnorderedCertificate s r)
    (hT : CertificateAdmissible modulus M T) {i : ι} (hi : i ∈ T.1) :
    modulus i ≤ M := by
  have hpos : 0 < certificateModulusProduct modulus T :=
    Finset.prod_pos (fun j _ => (hprime j).pos)
  have hdiv : modulus i ∣ certificateModulusProduct modulus T :=
    Finset.dvd_prod_of_mem modulus hi
  exact (Nat.le_of_dvd hpos hdiv).trans hT.2

omit [Fintype ι] [DecidableEq ι] in
/-- Two integer solutions belong to one class modulo the full product. -/
theorem integer_solutions_modEq
    (residue : ι → ℤ) (modulus : ι → ℕ) (indices : List ι)
    (hcoprime : indices.Pairwise (Nat.Coprime on modulus)) {x y : ℤ}
    (hx : ∀ i ∈ indices, x ≡ residue i [ZMOD (modulus i : ℤ)])
    (hy : ∀ i ∈ indices, y ≡ residue i [ZMOD (modulus i : ℤ)]) :
    x ≡ y [ZMOD ((indices.map modulus).prod : ℤ)] := by
  apply Int.modEq_iff_dvd.mpr
  apply Int.natCast_dvd.mpr
  apply Nat.modEq_zero_iff_dvd.mp
  apply (Nat.modEq_list_map_prod_iff hcoprime).mpr
  intro i hi
  exact Nat.modEq_zero_iff_dvd.mpr (Int.natCast_dvd.mp ((hx i hi).trans (hy i hi).symm).dvd)

/-- The exact scaled one-coordinate bound for real interval constants. -/
theorem integerSolutions_card_le
    {s : Finset ι} {r : ℕ} (residue : ι → ℤ) (modulus : ι → ℕ)
    (hprime : ∀ i, (modulus i).Prime) (a b : ℤ) (C₀ : ℝ) (M : ℕ)
    (hC : 0 ≤ C₀) (hab : a ≤ b) (hlen : (b - a : ℝ) ≤ C₀ * M)
    (T : UnorderedCertificate s r) (hT : CertificateAdmissible modulus M T) :
    ((integerSolutions residue modulus a b T).card : ℝ) ≤
      (C₀ + 1) * M / certificateModulusProduct modulus T := by
  have hcoprime := certificate_pairwise_coprime modulus T hprime hT.1
  have hpos : 0 < certificateModulusProduct modulus T :=
    Finset.prod_pos (fun i _ => (hprime i).pos)
  have hposR : (0 : ℝ) < certificateModulusProduct modulus T := by exact_mod_cast hpos
  have hPM : (certificateModulusProduct modulus T : ℝ) ≤ M := by exact_mod_cast hT.2
  by_cases he : integerSolutions residue modulus a b T = ∅
  · rw [he]
    simp only [card_empty, Nat.cast_zero]
    positivity
  obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr he
  have hvprop := (Finset.mem_filter.mp hv).2
  have hsub : integerSolutions residue modulus a b T ⊆
      (Ico a b).filter (fun x => x ≡ v [ZMOD (certificateModulusProduct modulus T : ℤ)]) := by
    intro x hx
    have hxprop := Finset.mem_filter.mp hx
    refine Finset.mem_filter.mpr ⟨hxprop.1, ?_⟩
    simpa [certificateModulusProduct] using
      integer_solutions_modEq residue modulus T.1.toList hcoprime hxprop.2 hvprop
  have hcount := PaperC.card_Ico_modEq_cast_le_div_add_one a b v
    (certificateModulusProduct modulus T : ℤ) (by exact_mod_cast hpos) hab
  have hcountR : (((Ico a b).filter (fun x =>
      x ≡ v [ZMOD (certificateModulusProduct modulus T : ℤ)])).card : ℝ) ≤
      (b - a : ℝ) / certificateModulusProduct modulus T + 1 := by
    exact_mod_cast hcount
  calc
    ((integerSolutions residue modulus a b T).card : ℝ) ≤
        (((Ico a b).filter (fun x =>
          x ≡ v [ZMOD (certificateModulusProduct modulus T : ℤ)])).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    _ ≤ (b - a : ℝ) / certificateModulusProduct modulus T + 1 := hcountR
    _ ≤ (C₀ * M) / certificateModulusProduct modulus T +
        (M : ℝ) / certificateModulusProduct modulus T :=
      add_le_add (div_le_div_of_nonneg_right hlen hposR.le) ((one_le_div₀ hposR).mpr hPM)
    _ = _ := by ring

/-- Cartesian products retain the square of the same constant. -/
theorem rectangleSolutions_card_le
    {s : Finset ι} {r : ℕ} (residue₁ residue₂ : ι → ℤ) (modulus : ι → ℕ)
    (hprime : ∀ i, (modulus i).Prime) (a₁ b₁ a₂ b₂ : ℤ) (C₀ : ℝ) (M : ℕ)
    (hC : 0 ≤ C₀) (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂)
    (hlen₁ : (b₁ - a₁ : ℝ) ≤ C₀ * M) (hlen₂ : (b₂ - a₂ : ℝ) ≤ C₀ * M)
    (T : UnorderedCertificate s r) (hT : CertificateAdmissible modulus M T) :
    (((integerSolutions residue₁ modulus a₁ b₁ T ×ˢ
      integerSolutions residue₂ modulus a₂ b₂ T).card) : ℝ) ≤
      ((C₀ + 1) * M / certificateModulusProduct modulus T) ^ 2 := by
  rw [Finset.card_product, Nat.cast_mul, pow_two]
  exact mul_le_mul
    (integerSolutions_card_le residue₁ modulus hprime a₁ b₁ C₀ M hC h₁ hlen₁ T hT)
    (integerSolutions_card_le residue₂ modulus hprime a₂ b₂ C₀ M hC h₂ hlen₂ T hT)
    (by positivity) (by positivity)

end
end PaperC.V282.ClosureCRTIntervals
