import PaperCV282.ClosureCRTSeries
import PaperC.Combinatorics.CertificateCellFamilies

/-!
# The literal cell-count form of article 3.11

The finite prime family and its actual cells are arbitrary. All unordered
certificates with product at most `M` are summed, with the exact factorial
series on the right. Both constants are independent of the real weight `u`.
-/

namespace PaperC.V282.ClosureCRTCellSeries

open CRT Finset ClosureCRTMass ClosureCRTSeries
open scoped BigOperators

noncomputable section

/-- Monotonicity of the entire factorial series, with summability established. -/
theorem factorialSeries_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    (∑' r : ℕ, x ^ r / r.factorial) ≤ ∑' r : ℕ, y ^ r / r.factorial := by
  exact (NormedSpace.expSeries_div_hasSum_exp x).summable.tsum_le_tsum
    (fun r => div_le_div_of_nonneg_right (pow_le_pow_left₀ hx hxy r) (by positivity))
    (NormedSpace.expSeries_div_hasSum_exp y).summable

variable {π κ : Type*} [Fintype π] [DecidableEq π] [DecidableEq κ]

omit [DecidableEq π] [DecidableEq κ] in
/-- Regrouping real local weights counts every actual cell above each prime. -/
theorem sum_labeledCell_weight (cells : π → Finset κ) (modulus : π → ℕ) (u : ℝ) (D : ℕ) :
    (∑ z : LabeledCell cells, u / (labeledCellModulus cells modulus z : ℝ) ^ D) =
      u * ∑ p : π, ((cells p).card : ℝ) / (modulus p : ℝ) ^ D := by
  rw [Fintype.sum_sigma]
  simp_rw [labeledCellModulus, Finset.sum_const, Finset.card_univ,
    Fintype.card_coe, nsmul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  ring

/-- Article 3.11 in one coordinate, including the complete unordered series.
The explicit implicit constant is `C₀+1`, for every real `u≥0`. -/
theorem lemma_three_eleven_interval
    (cells : π → Finset κ) (E modulus : π → ℕ) (residue : LabeledCell cells → ℤ)
    (hprime : ∀ p, (modulus p).Prime) (hE : ∀ p, (cells p).card ≤ E p)
    (a b : ℤ) (C₀ : ℝ) (M : ℕ) (hC : 0 ≤ C₀)
    (hab : a ≤ b) (hlen : (b - a : ℝ) ≤ C₀ * M) (u : ℝ) (hu : 0 ≤ u) :
    (∑' r, intervalMass (Finset.univ : Finset (LabeledCell cells)) r
      residue (labeledCellModulus cells modulus) a b M u) ≤
      ((C₀ + 1) * M) *
        ∑' r : ℕ, (u * ∑ p : π, (E p : ℝ) / (modulus p : ℝ)) ^ r / r.factorial := by
  have hgroup : (∑ z : LabeledCell cells, u / (labeledCellModulus cells modulus z : ℝ)) =
      u * ∑ p : π, ((cells p).card : ℝ) / (modulus p : ℝ) := by
    simpa only [pow_one] using sum_labeledCell_weight cells modulus u 1
  have hbase : u * ∑ p : π, ((cells p).card : ℝ) / (modulus p : ℝ) ≤
      u * ∑ p : π, (E p : ℝ) / (modulus p : ℝ) := by
    apply mul_le_mul_of_nonneg_left _ hu
    apply Finset.sum_le_sum
    intro p hp
    exact div_le_div_of_nonneg_right (by exact_mod_cast hE p) (by positivity)
  have hnonneg : 0 ≤ u * ∑ p : π, ((cells p).card : ℝ) / (modulus p : ℝ) := by
    positivity
  calc
    _ ≤ ((C₀ + 1) * M) * ∑' r : ℕ,
        (∑ z : LabeledCell cells, u / (labeledCellModulus cells modulus z : ℝ)) ^ r / r.factorial :=
      intervalMass_tsum_le _ residue _ (fun z => hprime z.1) a b C₀ M hC hab hlen u hu
    _ = ((C₀ + 1) * M) * ∑' r : ℕ,
        (u * ∑ p : π, ((cells p).card : ℝ) / (modulus p : ℝ)) ^ r / r.factorial := by rw [hgroup]
    _ ≤ _ := mul_le_mul_of_nonneg_left (factorialSeries_mono hnonneg hbase) (by positivity)

/-- Article 3.11 in two coordinates, with at most `E` actual cells per prime.
The explicit constant is `(C₀+1)²`, uniformly for every real `u≥0`. -/
theorem lemma_three_eleven_rectangle
    (cells : π → Finset κ) (E : ℕ) (modulus : π → ℕ)
    (residue₁ residue₂ : LabeledCell cells → ℤ)
    (hprime : ∀ p, (modulus p).Prime) (hE : ∀ p, (cells p).card ≤ E)
    (a₁ b₁ a₂ b₂ : ℤ) (C₀ : ℝ) (M : ℕ) (hC : 0 ≤ C₀)
    (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂)
    (hlen₁ : (b₁ - a₁ : ℝ) ≤ C₀ * M) (hlen₂ : (b₂ - a₂ : ℝ) ≤ C₀ * M)
    (u : ℝ) (hu : 0 ≤ u) :
    (∑' r, rectangleMass (Finset.univ : Finset (LabeledCell cells)) r
      residue₁ residue₂ (labeledCellModulus cells modulus) a₁ b₁ a₂ b₂ M u) ≤
      ((C₀ + 1) * M) ^ 2 *
        ∑' r : ℕ, (u * E * ∑ p : π, 1 / (modulus p : ℝ) ^ 2) ^ r / r.factorial := by
  have hbase : u * ∑ p : π, ((cells p).card : ℝ) / (modulus p : ℝ) ^ 2 ≤
      u * E * ∑ p : π, 1 / (modulus p : ℝ) ^ 2 := by
    calc
      _ ≤ u * ∑ p : π, (E : ℝ) / (modulus p : ℝ) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hu
        apply Finset.sum_le_sum
        intro p hp
        exact div_le_div_of_nonneg_right (by exact_mod_cast hE p) (sq_nonneg _)
      _ = _ := by simp only [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
  have hnonneg : 0 ≤ u * ∑ p : π, ((cells p).card : ℝ) / (modulus p : ℝ) ^ 2 := by
    positivity
  calc
    _ ≤ ((C₀ + 1) * M) ^ 2 * ∑' r : ℕ,
        (∑ z : LabeledCell cells, u / (labeledCellModulus cells modulus z : ℝ) ^ 2) ^ r / r.factorial :=
      rectangleMass_tsum_le _ residue₁ residue₂ _ (fun z => hprime z.1) a₁ b₁ a₂ b₂ C₀ M
        hC h₁ h₂ hlen₁ hlen₂ u hu
    _ = ((C₀ + 1) * M) ^ 2 * ∑' r : ℕ,
        (u * ∑ p : π, ((cells p).card : ℝ) / (modulus p : ℝ) ^ 2) ^ r / r.factorial := by
      rw [sum_labeledCell_weight]
    _ ≤ _ := mul_le_mul_of_nonneg_left (factorialSeries_mono hnonneg hbase) (sq_nonneg _)

end
end PaperC.V282.ClosureCRTCellSeries
