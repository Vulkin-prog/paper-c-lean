import PaperC.Combinatorics.CertificateCRTInstantiation
import PaperC.Combinatorics.CertificateCellFamilies

/-!
# Cell-family form of Paper C, Lemma 7.1

This file packages the CRT certificate bounds with the cells grouped by their
prime label.  Its statements are the finite, explicit versions of equations
(7.1) and (7.2): the one-dimensional local mass is
`u ∑ₚ Eₚ / p`, while the two-dimensional mass is
`u ∑ₚ Eₚ / p²`, and is at most `u M ∑ₚ 1 / p²` when `Eₚ ≤ M`.
-/

namespace PaperC
namespace CRT

open Finset
open scoped BigOperators

variable {π κ : Type*} [Fintype π] [DecidableEq π] [DecidableEq κ]

/--
The fixed-size one-dimensional conclusion (7.1), with the cell count over
each prime displayed explicitly.
-/
theorem labeledCell_admissibleCertificateSolutionMass_le
    (cells : π → Finset κ) (r : ℕ)
    (residue : LabeledCell cells → ℕ) (modulus : π → ℕ)
    (hprime : ∀ p, (modulus p).Prime)
    (a b C₀ N : ℕ) (hab : a ≤ b)
    (hlength : b - a ≤ C₀ * N)
    (u : ℚ) (hu : 0 ≤ u) :
    admissibleCertificateSolutionMass
        (Finset.univ : Finset (LabeledCell cells)) r
        residue (labeledCellModulus cells modulus) a b N u ≤
      (((C₀ + 1) * N : ℕ) : ℚ) *
        ((u * ∑ p : π,
            ((cells p).card : ℚ) / (modulus p : ℚ)) ^ r /
          r.factorial) := by
  have hprime' :
      ∀ z : LabeledCell cells,
        (labeledCellModulus cells modulus z).Prime :=
    fun z ↦ hprime z.1
  simpa only [sum_labeledCell_div_eq] using
    admissibleCertificateSolutionMass_le
      (Finset.univ : Finset (LabeledCell cells)) r
      residue (labeledCellModulus cells modulus) hprime'
      a b C₀ N hab hlength u hu

/--
The fixed-size two-dimensional conclusion (7.2), retaining the exact number
of cells above each prime.
-/
theorem labeledCell_admissibleCertificatePairSolutionMass_le_exact
    (cells : π → Finset κ) (r : ℕ)
    (residue₁ residue₂ : LabeledCell cells → ℕ)
    (modulus : π → ℕ)
    (hprime : ∀ p, (modulus p).Prime)
    (a₁ b₁ a₂ b₂ C₀ N : ℕ)
    (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂)
    (hlength₁ : b₁ - a₁ ≤ C₀ * N)
    (hlength₂ : b₂ - a₂ ≤ C₀ * N)
    (u : ℚ) (hu : 0 ≤ u) :
    admissibleCertificatePairSolutionMass
        (Finset.univ : Finset (LabeledCell cells)) r
        residue₁ residue₂ (labeledCellModulus cells modulus)
        a₁ b₁ a₂ b₂ N u ≤
      ((((C₀ + 1) * N : ℕ) : ℚ) ^ 2) *
        ((u * ∑ p : π,
            ((cells p).card : ℚ) / (modulus p : ℚ) ^ 2) ^ r /
          r.factorial) := by
  have hprime' :
      ∀ z : LabeledCell cells,
        (labeledCellModulus cells modulus z).Prime :=
    fun z ↦ hprime z.1
  simpa only [sum_labeledCell_div_sq_eq] using
    admissibleCertificatePairSolutionMass_le
      (Finset.univ : Finset (LabeledCell cells)) r
      residue₁ residue₂ (labeledCellModulus cells modulus) hprime'
      a₁ b₁ a₂ b₂ C₀ N h₁ h₂ hlength₁ hlength₂ u hu

/--
The usual bounded-cell form of (7.2): if every prime supports at most `M`
cells, the local mass is bounded by `u M ∑ₚ 1 / p²`.
-/
theorem labeledCell_admissibleCertificatePairSolutionMass_le
    (cells : π → Finset κ) (r : ℕ)
    (residue₁ residue₂ : LabeledCell cells → ℕ)
    (modulus : π → ℕ) (M : ℕ)
    (hprime : ∀ p, (modulus p).Prime)
    (hcard : ∀ p, (cells p).card ≤ M)
    (a₁ b₁ a₂ b₂ C₀ N : ℕ)
    (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂)
    (hlength₁ : b₁ - a₁ ≤ C₀ * N)
    (hlength₂ : b₂ - a₂ ≤ C₀ * N)
    (u : ℚ) (hu : 0 ≤ u) :
    admissibleCertificatePairSolutionMass
        (Finset.univ : Finset (LabeledCell cells)) r
        residue₁ residue₂ (labeledCellModulus cells modulus)
        a₁ b₁ a₂ b₂ N u ≤
      ((((C₀ + 1) * N : ℕ) : ℚ) ^ 2) *
        ((u * (M : ℚ) *
            ∑ p : π, 1 / (modulus p : ℚ) ^ 2) ^ r /
          r.factorial) := by
  refine
    (labeledCell_admissibleCertificatePairSolutionMass_le_exact
      cells r residue₁ residue₂ modulus hprime
      a₁ b₁ a₂ b₂ C₀ N h₁ h₂ hlength₁ hlength₂ u hu).trans ?_
  have hmodulus : ∀ p, 0 < modulus p :=
    fun p ↦ (hprime p).pos
  have hbase :
      u * ∑ p : π,
          ((cells p).card : ℚ) / (modulus p : ℚ) ^ 2 ≤
        u * (M : ℚ) *
          ∑ p : π, 1 / (modulus p : ℚ) ^ 2 := by
    rw [← sum_labeledCell_div_sq_eq]
    exact
      sum_labeledCell_div_sq_le
        cells modulus M u hu hmodulus hcard
  have hbase_nonneg :
      0 ≤ u * ∑ p : π,
          ((cells p).card : ℚ) / (modulus p : ℚ) ^ 2 := by
    apply mul_nonneg hu
    apply Finset.sum_nonneg
    intro p hp
    exact div_nonneg (by positivity) (sq_nonneg _)
  apply mul_le_mul_of_nonneg_left
  · apply div_le_div_of_nonneg_right
    · exact pow_le_pow_left₀ hbase_nonneg hbase r
    · positivity
  · positivity

/--
The finite sum over certificate sizes `r < R` in the one-dimensional case.
-/
theorem sum_labeledCell_admissibleCertificateSolutionMass_le
    (cells : π → Finset κ) (R : ℕ)
    (residue : LabeledCell cells → ℕ) (modulus : π → ℕ)
    (hprime : ∀ p, (modulus p).Prime)
    (a b C₀ N : ℕ) (hab : a ≤ b)
    (hlength : b - a ≤ C₀ * N)
    (u : ℚ) (hu : 0 ≤ u) :
    (∑ r ∈ Finset.range R,
        admissibleCertificateSolutionMass
          (Finset.univ : Finset (LabeledCell cells)) r
          residue (labeledCellModulus cells modulus) a b N u) ≤
      (((C₀ + 1) * N : ℕ) : ℚ) *
        ∑ r ∈ Finset.range R,
          (u * ∑ p : π,
            ((cells p).card : ℚ) / (modulus p : ℚ)) ^ r /
            r.factorial := by
  have hprime' :
      ∀ z : LabeledCell cells,
        (labeledCellModulus cells modulus z).Prime :=
    fun z ↦ hprime z.1
  simpa only [sum_labeledCell_div_eq] using
    sum_admissibleCertificateSolutionMass_le
      (Finset.univ : Finset (LabeledCell cells)) R
      residue (labeledCellModulus cells modulus) hprime'
      a b C₀ N hab hlength u hu

/--
The finite sum over certificate sizes `r < R` in the exact two-dimensional
cell-count form.
-/
theorem sum_labeledCell_admissibleCertificatePairSolutionMass_le_exact
    (cells : π → Finset κ) (R : ℕ)
    (residue₁ residue₂ : LabeledCell cells → ℕ)
    (modulus : π → ℕ)
    (hprime : ∀ p, (modulus p).Prime)
    (a₁ b₁ a₂ b₂ C₀ N : ℕ)
    (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂)
    (hlength₁ : b₁ - a₁ ≤ C₀ * N)
    (hlength₂ : b₂ - a₂ ≤ C₀ * N)
    (u : ℚ) (hu : 0 ≤ u) :
    (∑ r ∈ Finset.range R,
        admissibleCertificatePairSolutionMass
          (Finset.univ : Finset (LabeledCell cells)) r
          residue₁ residue₂ (labeledCellModulus cells modulus)
          a₁ b₁ a₂ b₂ N u) ≤
      ((((C₀ + 1) * N : ℕ) : ℚ) ^ 2) *
        ∑ r ∈ Finset.range R,
          (u * ∑ p : π,
            ((cells p).card : ℚ) / (modulus p : ℚ) ^ 2) ^ r /
            r.factorial := by
  have hprime' :
      ∀ z : LabeledCell cells,
        (labeledCellModulus cells modulus z).Prime :=
    fun z ↦ hprime z.1
  simpa only [sum_labeledCell_div_sq_eq] using
    sum_admissibleCertificatePairSolutionMass_le
      (Finset.univ : Finset (LabeledCell cells)) R
      residue₁ residue₂ (labeledCellModulus cells modulus) hprime'
      a₁ b₁ a₂ b₂ C₀ N h₁ h₂ hlength₁ hlength₂ u hu

/--
The finite sum over `r < R` in the bounded-cell two-dimensional form.
-/
theorem sum_labeledCell_admissibleCertificatePairSolutionMass_le
    (cells : π → Finset κ) (R : ℕ)
    (residue₁ residue₂ : LabeledCell cells → ℕ)
    (modulus : π → ℕ) (M : ℕ)
    (hprime : ∀ p, (modulus p).Prime)
    (hcard : ∀ p, (cells p).card ≤ M)
    (a₁ b₁ a₂ b₂ C₀ N : ℕ)
    (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂)
    (hlength₁ : b₁ - a₁ ≤ C₀ * N)
    (hlength₂ : b₂ - a₂ ≤ C₀ * N)
    (u : ℚ) (hu : 0 ≤ u) :
    (∑ r ∈ Finset.range R,
        admissibleCertificatePairSolutionMass
          (Finset.univ : Finset (LabeledCell cells)) r
          residue₁ residue₂ (labeledCellModulus cells modulus)
          a₁ b₁ a₂ b₂ N u) ≤
      ((((C₀ + 1) * N : ℕ) : ℚ) ^ 2) *
        ∑ r ∈ Finset.range R,
          (u * (M : ℚ) *
            ∑ p : π, 1 / (modulus p : ℚ) ^ 2) ^ r /
            r.factorial := by
  refine
    (sum_labeledCell_admissibleCertificatePairSolutionMass_le_exact
      cells R residue₁ residue₂ modulus hprime
      a₁ b₁ a₂ b₂ C₀ N h₁ h₂ hlength₁ hlength₂ u hu).trans ?_
  have hmodulus : ∀ p, 0 < modulus p :=
    fun p ↦ (hprime p).pos
  have hbase :
      u * ∑ p : π,
          ((cells p).card : ℚ) / (modulus p : ℚ) ^ 2 ≤
        u * (M : ℚ) *
          ∑ p : π, 1 / (modulus p : ℚ) ^ 2 := by
    rw [← sum_labeledCell_div_sq_eq]
    exact
      sum_labeledCell_div_sq_le
        cells modulus M u hu hmodulus hcard
  have hbase_nonneg :
      0 ≤ u * ∑ p : π,
          ((cells p).card : ℚ) / (modulus p : ℚ) ^ 2 := by
    apply mul_nonneg hu
    apply Finset.sum_nonneg
    intro p hp
    exact div_nonneg (by positivity) (sq_nonneg _)
  apply mul_le_mul_of_nonneg_left
  · apply Finset.sum_le_sum
    intro r hr
    apply div_le_div_of_nonneg_right
    · exact pow_le_pow_left₀ hbase_nonneg hbase r
    · positivity
  · positivity

end CRT
end PaperC
