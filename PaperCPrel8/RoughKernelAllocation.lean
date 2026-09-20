import PaperCPrel8.RoughKernelCRT
import PaperC.Arithmetic.LargeOddKernel
import PaperC.Probability.ArratiaGoldsteinGordonInput

/-! # The CRT allocation probability for the actual odd rough kernel

Uniform sampling on the Cartesian grid is the law of independent uniform
indices, including zero target blocks. The source vertex is fixed.
-/
namespace PaperC.Prel8.RoughKernelAllocation
open Finset RoughKernelCRT LargeOddKernel ArratiaGoldsteinGordonInput
noncomputable section
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- Uniform finite-set probabilities are exact normalized event cardinalities. -/
theorem uniform_finset_probability {α : Type*} (S : Finset α) [Nonempty S] (P : α → Prop) :
    eventProbability (FinitePMF.uniform S) (fun x ↦ P x.val) =
      ((S.filter P).card : ℝ) / S.card := by
  classical
  unfold eventProbability
  simp only [FinitePMF.uniform_prob,Fintype.card_coe]
  rw [← sum_subtype S (fun _ ↦ Iff.rfl) (fun x : α ↦ if P x then (S.card:ℝ)⁻¹ else 0),← sum_filter]
  simp [div_eq_mul_inv]

def grid (n h : ℕ) : Finset (Fin h → ℕ) := Fintype.piFinset (fun _ ↦ Icc 1 n)

/-- The sampling grid has n^h equally likely points. -/
theorem grid_card (n h : ℕ) : (grid n h).card = n^h := by
  simp [grid,Fintype.card_piFinset,Nat.card_Icc]

/-- Independent uniform target indices on {1,...,n}. -/
def gridLaw (n h : ℕ) (hn : 0 < n) : FinitePMF (grid n h) := by
  letI : Nonempty (grid n h) := ⟨⟨(fun _ ↦ 1),by simp [grid,Fintype.mem_piFinset]; omega⟩⟩
  exact FinitePMF.uniform _

/-- Probability that every odd rough prime of the fixed source is hosted by a target block. -/
theorem rough_allocation_probability (n h Q Y m : ℕ) (hn : 0 < n)
    (hr : largeOddKernel Y m ≤ 2*n) :
    eventProbability (gridLaw n h hn)
      (fun J ↦ ∀ p ∈ largeOddPrimeSupport Y m,
        ∃ b : Fin h, ∃ a : Fin (Q+1), p ∣ J.val b + a.val) ≤
      (3*(h:ℝ)*(Q+1))^ArithmeticFunction.cardDistinctFactors (largeOddKernel Y m) /
        (largeOddKernel Y m : ℝ) := by
  classical
  let S := largeOddPrimeSupport Y m
  have hp (i : S) : Nat.Prime i.val := (prime_and_large_of_mem_largeOddPrimeSupport i.property).1
  have he : (∏ i : S, i.val) = largeOddKernel Y m := by
    exact (prod_subtype S (fun _ ↦ Iff.rfl) (fun p : ℕ ↦ p)).symm
  have heR : (∏ i : S, (i.val:ℝ)) = (largeOddKernel Y m:ℝ) := by exact_mod_cast he
  have hh := hosted_fraction_le n h Q hn (fun i : S ↦ i.val) hp Subtype.val_injective (by rwa [he])
  rw [heR,Fintype.card_coe,← cardDistinctFactors_largeOddKernel] at hh
  let : Nonempty (grid n h) := ⟨⟨(fun _ ↦ 1),by simp [grid,Fintype.mem_piFinset]; omega⟩⟩
  change eventProbability (FinitePMF.uniform (grid n h)) _ ≤ _
  rw [uniform_finset_probability (grid n h) (fun J ↦ ∀ p ∈ largeOddPrimeSupport Y m,
    ∃ b : Fin h, ∃ a : Fin (Q+1), p ∣ J b + a.val),grid_card]
  push_cast
  convert hh using 2
  congr 2
  ext J
  simp [hostedGrid,grid,S]

/-- The paper's ambient r<=m<=2n discharges the product-size premise. -/
theorem rough_allocation_of_vertex_bound (n h Q Y m : ℕ) (hn : 0 < n)
    (hm : 0 < m) (hmn : m ≤ 2*n) :
    eventProbability (gridLaw n h hn)
      (fun J ↦ ∀ p ∈ largeOddPrimeSupport Y m,
        ∃ b : Fin h, ∃ a : Fin (Q+1), p ∣ J.val b + a.val) ≤
      (3*(h:ℝ)*(Q+1))^ArithmeticFunction.cardDistinctFactors (largeOddKernel Y m) /
        (largeOddKernel Y m : ℝ) :=
  rough_allocation_probability n h Q Y m hn ((largeOddKernel_le hm).trans hmn)

end
end PaperC.Prel8.RoughKernelAllocation
