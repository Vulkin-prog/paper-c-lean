import PaperC.Combinatorics.CertificateSummation
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# The unordered factorial bound for arbitrary real weights

The ordering embedding is the existing exact one. Here the weighted finite
sums are over the reals, so no rational approximation restricts the moment
parameter. Distinctness is dropped only after its exact factorial multiplicity.
-/

namespace PaperC.V282.ClosureCRTSummation

open CRT Finset
open scoped BigOperators

noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The weighted sum over unordered certificates of fixed size. -/
def certificateWeightSum
    (s : Finset ι) (r : ℕ) (w : ι → ℝ) : ℝ :=
  ∑ T : UnorderedCertificate s r, ∏ i ∈ T.1, w i

theorem ordering_product_eq_certificate_product
    {s : Finset ι} {r : ℕ} (w : ι → ℝ)
    (T : UnorderedCertificate s r) (e : Fin r ↪ T.1) :
    (∏ j, w (e j).1) = ∏ i ∈ T.1, w i := by
  calc
    (∏ j, w (e j).1) = ∏ i : T.1, w i.1 :=
      (show Function.Bijective (e : Fin r → T.1) from
        (Fintype.bijective_iff_injective_and_card e).mpr ⟨e.injective, by simp⟩).prod_comp
        (fun i : T.1 ↦ w i.1)
    _ = ∏ i ∈ T.1, w i := by
      exact Finset.prod_coe_sort T.1 w

/-- Every unordered `r`-certificate has exactly `r!` weighted orderings. -/
theorem orderedCertificate_sum_eq_factorial_mul
    (s : Finset ι) (r : ℕ) (w : ι → ℝ) :
    (∑ z : OrderedCertificate s r,
        ∏ j, w (orderedCertificateToFunction z j).1) =
      (r.factorial : ℝ) * certificateWeightSum s r w := by
  rw [Fintype.sum_sigma]
  simp_rw [orderedCertificateToFunction,
    ordering_product_eq_certificate_product]
  have hcard :
      ∀ T : UnorderedCertificate s r,
        Fintype.card (Fin r ↪ T.1) = r.factorial := by
    intro T
    rw [Fintype.card_embedding_eq, Fintype.card_fin,
      Fintype.card_coe, unorderedCertificate_card,
      Nat.descFactorial_self]
  simp_rw [Finset.sum_const, Finset.card_univ, hcard,
    nsmul_eq_mul]
  unfold certificateWeightSum
  rw [Finset.mul_sum]

/--
The sum over ordered injective selections is at most the sum over all ordered
selections, provided the weights are nonnegative.
-/
theorem orderedCertificate_sum_le_all_functions
    (s : Finset ι) (r : ℕ) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ z : OrderedCertificate s r,
        ∏ j, w (orderedCertificateToFunction z j).1) ≤
      ∑ f : Fin r → s, ∏ j, w (f j).1 := by
  classical
  let E : OrderedCertificate s r ↪ (Fin r → s) :=
    orderedCertificateEmbedding
  let g : (Fin r → s) → ℝ := fun f ↦ ∏ j, w (f j).1
  calc
    (∑ z : OrderedCertificate s r,
        ∏ j, w (orderedCertificateToFunction z j).1) =
        ∑ f ∈ (Finset.univ.map E), g f := by
          rw [Finset.sum_map]
          rfl
    _ ≤ ∑ f ∈ (Finset.univ : Finset (Fin r → s)), g f := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · simp
      · intro f _ _
        dsimp [g]
        exact Finset.prod_nonneg fun j _ ↦ hw (f j).1 (f j).2
    _ = ∑ f : Fin r → s, ∏ j, w (f j).1 := by
      simp [g]

/--
The exact elementary-symmetric estimate furnishing the `1/r!` factor in
Lemma 7.1.
-/
theorem factorial_mul_certificateWeightSum_le_pow_sum
    (s : Finset ι) (r : ℕ) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    (r.factorial : ℝ) * certificateWeightSum s r w ≤
      (∑ i ∈ s, w i) ^ r := by
  rw [← orderedCertificate_sum_eq_factorial_mul]
  refine (orderedCertificate_sum_le_all_functions s r w hw).trans_eq ?_
  simpa only [Finset.sum_coe_sort] using
    (Fintype.sum_pow (fun i : s ↦ w i.1) r).symm

/-- Division form of the preceding bound. -/
theorem certificateWeightSum_le_pow_sum_div_factorial
    (s : Finset ι) (r : ℕ) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    certificateWeightSum s r w ≤
      (∑ i ∈ s, w i) ^ r / r.factorial := by
  rw [le_div_iff₀]
  · simpa [mul_comm] using
      factorial_mul_certificateWeightSum_le_pow_sum s r w hw
  · positivity

end
end PaperC.V282.ClosureCRTSummation
