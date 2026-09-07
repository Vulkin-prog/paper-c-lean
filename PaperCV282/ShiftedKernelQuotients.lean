import PaperC.Arithmetic.TerminalKernelCount

/-!
# Counting the quotients in shifted kernel energy

Removing the large odd kernel leaves a square times a squarefree product
of primes at most `B`. The quotient is itself a kernel-one integer.
If the original value is at most `X` and its kernel is at least `R>0`,
the quotient lies below `X/R`. The historical finite kernel count then
gives its square-root population bound, uniformly in the kernel range.
-/

namespace PaperC.V282.ShiftedKernelQuotients

open LargeOddKernel DefectivePredicate DefectCounting TerminalKernelCount
open scoped BigOperators

noncomputable section

/-- The complementary integer after removing the entire large odd kernel. -/
def kernelQuotient (B n : ℕ) : ℕ := n / largeOddKernel B n

/-- Exact reconstruction, including the harmless zero input. -/
theorem kernelQuotient_mul_kernel (B n : ℕ) :
    kernelQuotient B n * largeOddKernel B n = n :=
  Nat.div_mul_cancel (largeOddKernel_dvd B n)

/-- The quotient has its canonical square-times-small-prime representation. -/
theorem kernelQuotient_eq_square_mul_small {B n : ℕ} (hn : n ≠ 0) :
    kernelQuotient B n = DefectivePredicate.canonicalSquarePart n ^ 2 * smallOddPart B n := by
  unfold kernelQuotient
  calc
    n / largeOddKernel B n =
        (DefectivePredicate.canonicalSquarePart n ^ 2 * smallOddPart B n *
          largeOddKernel B n) / largeOddKernel B n :=
      congrArg (fun t => t / largeOddKernel B n) (canonical_largeOddKernel_decomposition hn)
    _ = _ := Nat.mul_div_cancel _ (Nat.pos_of_ne_zero (largeOddKernel_ne_zero B n))

theorem kernelQuotient_pos {B n : ℕ} (hn : 0 < n) : 0 < kernelQuotient B n := by
  have h := kernelQuotient_mul_kernel B n
  by_contra hq
  have hz : kernelQuotient B n = 0 := by omega
  rw [hz, zero_mul] at h
  omega

/-- The complementary quotient has no odd prime valuation above the cutoff. -/
theorem kernelQuotient_hDefective {B n : ℕ} (hn : n ≠ 0) :
    HDefective B (kernelQuotient B n) := by
  apply hDefective_of_HDefectRepresentation
    (show HDefectRepresentation B (kernelQuotient B n) from
      { support := smallOddPrimeSupport B n
        support_subset := by
          intro p hp
          exact mem_smallPrimesUpTo.mpr (prime_and_small_of_mem_smallOddPrimeSupport hp)
        squarePart := DefectivePredicate.canonicalSquarePart n
        value_eq := by
          rw [kernelQuotient_eq_square_mul_small hn]
          simp only [smallOddPart]
          ring })

/-- Exact kernel-one form, used by the finite kernel-counting interface. -/
theorem largeOddKernel_kernelQuotient_eq_one {B n : ℕ} (hn : n ≠ 0) :
    largeOddKernel B (kernelQuotient B n) = 1 :=
  (largeOddKernel_eq_one_iff_hDefective B _).mpr (kernelQuotient_hDefective hn)

/-- A lower cutoff on the original kernel supplies an upper cutoff on its quotient. -/
theorem kernelQuotient_le_div {B n X R : ℕ} (hR : 0 < R)
    (hnX : n ≤ X) (hkernel : R ≤ largeOddKernel B n) :
    kernelQuotient B n ≤ X / R := by
  apply (Nat.le_div_iff_mul_le hR).mpr
  calc
    kernelQuotient B n * R ≤ kernelQuotient B n * largeOddKernel B n :=
      Nat.mul_le_mul_left _ hkernel
    _ = n := kernelQuotient_mul_kernel B n
    _ ≤ X := hnX

/-- Distinct complementary quotients of bounded values above a kernel cutoff. -/
def kernelQuotients (B X R : ℕ) : Finset ℕ :=
  ((Finset.Icc 1 X).filter fun n => R ≤ largeOddKernel B n).image (kernelQuotient B)

/-- Forgetting the original value only enlarges the quotient population. -/
theorem kernelQuotients_subset_kernel_one (B X R : ℕ) (hR : 0 < R) :
    kernelQuotients B X R ⊆ boundedLargeKernelValues B 1 (X / R) := by
  intro q hq
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨hnX, hk⟩ := Finset.mem_filter.mp hn
  obtain ⟨hnpos, hnX⟩ := Finset.mem_Icc.mp hnX
  apply mem_boundedLargeKernelValues.mpr
  exact ⟨kernelQuotient_pos hnpos, kernelQuotient_le_div hR hnX hk,
    (largeOddKernel_kernelQuotient_eq_one (by omega)).le⟩

/-- Finite square-root quotient count before replacing natural division. -/
theorem card_kernelQuotients_le (B X R : ℕ) (hR : 0 < R) :
    ((kernelQuotients B X R).card : ℝ) ≤
      2 * Real.sqrt (X / R : ℕ) *
        ∏ p ∈ smallPrimesUpTo B, (1 + (Real.sqrt p)⁻¹) := by
  have hcard : ((kernelQuotients B X R).card : ℝ) ≤
      ((boundedLargeKernelValues B 1 (X / R)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (kernelQuotients_subset_kernel_one B X R hR)
  have hcount := card_boundedLargeKernelValues_cast_le B 1 (X / R)
  simpa only [Nat.cast_one, Real.sqrt_one, mul_one] using hcard.trans hcount

/-- The analytic shape used for each fixed dyadic kernel range. -/
theorem card_kernelQuotients_le_sqrt_ratio (B X R : ℕ) (hR : 0 < R) :
    ((kernelQuotients B X R).card : ℝ) ≤
      2 * Real.sqrt ((X : ℝ) / R) *
        ∏ p ∈ smallPrimesUpTo B, (1 + (Real.sqrt p)⁻¹) := by
  refine (card_kernelQuotients_le B X R hR).trans ?_
  gcongr
  exact Nat.cast_div_le

end
end PaperC.V282.ShiftedKernelQuotients
