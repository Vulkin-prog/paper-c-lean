import PaperC.Arithmetic.TerminalKernelCount
import PaperC.Model.FiniteRademacher
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Terminal-cutoff bad starts

Section 13 calls a start `x` bad when one of the values in its length-`L`
window has trivial large odd kernel at the terminal cutoff `Y`.  This module
formalizes the finite counting core of Lemma 13.3.

We retain the incidence which witnesses badness:

`(x,j)`, with `x ∈ [N,2N)`, `j < L`, and `𝒦_Y(x+j)=1`.

Projection to `x` covers the bad starts.  The injective recoding
`(x,j) ↦ (x+j,j)` then embeds these incidences in

`A_{Y,1}(2N+L) × {0,...,L-1}`.

Combining this exact injection with the terminal-kernel estimate from
Theorem 10.1 gives an explicit, unconditional finite upper bound retaining
the exact small-prime Euler product.  A coarser exponential corollary is also
recorded.

At the manuscript's terminal cutoff
`Y ≍ B² log B`, the coarse envelope `exp (2√Y)` is *not* sufficient to
deduce `N^(1/2+o(1))`.  That asymptotic conclusion still requires the
prime-sensitive Chebyshev/partial-summation estimate
`∑_{p≤Y} p⁻¹/² ≪ √Y / log Y`.  No such conclusion is claimed here.
-/

namespace PaperC
namespace BadStartCount

open LargeOddKernel
open TerminalKernelCount

/-- Positive values up to `X` whose large odd kernel is exactly one. -/
noncomputable def unitLargeKernelValues
    (B X : ℕ) : Finset ℕ :=
  (Finset.Icc 1 X).filter fun n ↦ largeOddKernel B n = 1

@[simp]
theorem mem_unitLargeKernelValues
    {B X n : ℕ} :
    n ∈ unitLargeKernelValues B X ↔
      1 ≤ n ∧ n ≤ X ∧ largeOddKernel B n = 1 := by
  simp [unitLargeKernelValues, and_assoc]

/--
The terminal bad-start set from §13: some offset in the run window has
trivial large odd kernel.
-/
noncomputable def terminalBadStarts
    (N L B : ℕ) : Finset ℕ :=
  (dyadicBlock N).filter fun x ↦
    ∃ j ∈ Finset.range L, largeOddKernel B (x + j) = 1

@[simp]
theorem mem_terminalBadStarts
    {N L B x : ℕ} :
    x ∈ terminalBadStarts N L B ↔
      x ∈ dyadicBlock N ∧
        ∃ j < L, largeOddKernel B (x + j) = 1 := by
  simp [terminalBadStarts]

/-- Incidences retaining both a bad start and a witnessing offset. -/
noncomputable def terminalBadStartIncidences
    (N L B : ℕ) : Finset (ℕ × ℕ) :=
  ((dyadicBlock N).product (Finset.range L)).filter fun xj ↦
    largeOddKernel B (xj.1 + xj.2) = 1

@[simp]
theorem mem_terminalBadStartIncidences
    {N L B : ℕ} {xj : ℕ × ℕ} :
    xj ∈ terminalBadStartIncidences N L B ↔
      xj.1 ∈ dyadicBlock N ∧
        xj.2 < L ∧
          largeOddKernel B (xj.1 + xj.2) = 1 := by
  simp [terminalBadStartIncidences, and_assoc]

/-- Projection of the incidence set is exactly the set of bad starts. -/
theorem image_fst_terminalBadStartIncidences
    (N L B : ℕ) :
    (terminalBadStartIncidences N L B).image Prod.fst =
      terminalBadStarts N L B := by
  ext x
  simp only [Finset.mem_image, mem_terminalBadStartIncidences,
    mem_terminalBadStarts]
  constructor
  · rintro ⟨xj, ⟨hxj, hj, hkernel⟩, rfl⟩
    exact ⟨hxj, ⟨xj.2, hj, hkernel⟩⟩
  · rintro ⟨hx, ⟨j, hj, hkernel⟩⟩
    exact ⟨(x, j), ⟨hx, hj, hkernel⟩, rfl⟩

/-- Every bad start has at least one incidence witness. -/
theorem card_terminalBadStarts_le_incidences
    (N L B : ℕ) :
    (terminalBadStarts N L B).card ≤
      (terminalBadStartIncidences N L B).card := by
  rw [← image_fst_terminalBadStartIncidences N L B]
  exact Finset.card_image_le

/-- Recode an incidence by the defective value and its offset. -/
def terminalBadIncidenceCode (xj : ℕ × ℕ) : ℕ × ℕ :=
  (xj.1 + xj.2, xj.2)

/-- The incidence recoding is injective. -/
theorem terminalBadIncidenceCode_injective :
    Function.Injective terminalBadIncidenceCode := by
  rintro ⟨x, j⟩ ⟨x', j'⟩ h
  have hsum : x + j = x' + j' :=
    congrArg Prod.fst h
  have hoffset : j = j' :=
    congrArg Prod.snd h
  apply Prod.ext
  · omega
  · exact hoffset

/-- The recoded incidences all lie in the bounded unit-kernel product. -/
theorem image_terminalBadIncidenceCode_subset
    {N L B : ℕ} (hN : 1 ≤ N) :
    (terminalBadStartIncidences N L B).image
        terminalBadIncidenceCode ⊆
      (unitLargeKernelValues B (dyadicCutoff N L)).product
        (Finset.range L) := by
  intro nj hnj
  obtain ⟨xj, hxj, rfl⟩ := Finset.mem_image.mp hnj
  have hxj' := mem_terminalBadStartIncidences.mp hxj
  change (xj.1 + xj.2, xj.2) ∈
    (unitLargeKernelValues B (dyadicCutoff N L)).product
      (Finset.range L)
  apply Finset.mem_product.mpr
  refine ⟨mem_unitLargeKernelValues.mpr ⟨?_, ?_, hxj'.2.2⟩, ?_⟩
  · have hxLower : N ≤ xj.1 := by
      exact
        (Finset.mem_Ico.mp
          (by simpa [dyadicBlock] using hxj'.1)).1
    omega
  · exact startWindow_le_dyadicCutoff hxj'.1 hxj'.2.1
  · simpa using hxj'.2.1

/-- Exact incidence bound supplied by the injective recoding. -/
theorem card_terminalBadStartIncidences_le
    {N L B : ℕ} (hN : 1 ≤ N) :
    (terminalBadStartIncidences N L B).card ≤
      (unitLargeKernelValues B (dyadicCutoff N L)).card * L := by
  calc
    (terminalBadStartIncidences N L B).card =
        ((terminalBadStartIncidences N L B).image
          terminalBadIncidenceCode).card := by
      rw [Finset.card_image_iff.mpr]
      intro a ha b hb hab
      exact terminalBadIncidenceCode_injective hab
    _ ≤ ((unitLargeKernelValues B (dyadicCutoff N L)).product
          (Finset.range L)).card :=
      Finset.card_le_card (image_terminalBadIncidenceCode_subset hN)
    _ = (unitLargeKernelValues B (dyadicCutoff N L)).card * L := by
      simp

/--
Finite counting core of Lemma 13.3.  The factor `L` is the maximum number of
offsets by which a fixed defective value can witness a bad start.
-/
theorem card_terminalBadStarts_le
    {N L B : ℕ} (hN : 1 ≤ N) :
    (terminalBadStarts N L B).card ≤
      L * (unitLargeKernelValues B (dyadicCutoff N L)).card := by
  calc
    (terminalBadStarts N L B).card ≤
        (terminalBadStartIncidences N L B).card :=
      card_terminalBadStarts_le_incidences N L B
    _ ≤ (unitLargeKernelValues B (dyadicCutoff N L)).card * L :=
      card_terminalBadStartIncidences_le hN
    _ = L * (unitLargeKernelValues B (dyadicCutoff N L)).card :=
      Nat.mul_comm _ _

/-- Kernel one is equivalent to the `T=1` terminal-kernel cutoff. -/
theorem unitLargeKernelValues_eq_bounded
    (B X : ℕ) :
    unitLargeKernelValues B X =
      boundedLargeKernelValues B 1 X := by
  ext n
  simp only [mem_unitLargeKernelValues, mem_boundedLargeKernelValues]
  constructor
  · rintro ⟨hn1, hnX, hkernel⟩
    exact ⟨hn1, hnX, hkernel.le⟩
  · rintro ⟨hn1, hnX, hkernel⟩
    exact ⟨hn1, hnX,
      Nat.le_antisymm hkernel (one_le_largeOddKernel B n)⟩

/--
Prime-sensitive finite form obtained by inserting `T=1` in the exact
terminal-kernel estimate:

`#D_B ≤ 2 L √(2N+L) ∏_{p≤B}(1+p⁻¹/²)`.
-/
theorem card_terminalBadStarts_cast_le_eulerProduct
    {N L B : ℕ} (hN : 1 ≤ N) :
    ((terminalBadStarts N L B).card : ℝ) ≤
      2 * L * Real.sqrt (dyadicCutoff N L) *
        ∏ p ∈ DefectCounting.smallPrimesUpTo B,
          (1 + (Real.sqrt p)⁻¹) := by
  have hcard := card_terminalBadStarts_le (N := N) (L := L) (B := B) hN
  have hkernel :=
    card_boundedLargeKernelValues_cast_le
      B 1 (dyadicCutoff N L)
  rw [← unitLargeKernelValues_eq_bounded B (dyadicCutoff N L)] at hkernel
  norm_num at hkernel
  calc
    ((terminalBadStarts N L B).card : ℝ) ≤
        (L : ℝ) *
          ((unitLargeKernelValues B (dyadicCutoff N L)).card : ℝ) := by
      exact_mod_cast hcard
    _ ≤ (L : ℝ) *
        (2 * Real.sqrt (dyadicCutoff N L) *
          ∏ p ∈ DefectCounting.smallPrimesUpTo B,
            (1 + (Real.sqrt p)⁻¹)) := by
      exact mul_le_mul_of_nonneg_left hkernel (Nat.cast_nonneg L)
    _ = 2 * L * Real.sqrt (dyadicCutoff N L) *
        ∏ p ∈ DefectCounting.smallPrimesUpTo B,
          (1 + (Real.sqrt p)⁻¹) := by
      ring

/--
Coarse unconditional corollary:

`#D_B ≤ 2 L √(2N+L) exp(2√B)`.

This estimate is useful as a finite sanity bound, but is deliberately not
advertised as sufficient for the terminal specialization `B=Y`.
-/
theorem card_terminalBadStarts_cast_le_exp
    {N L B : ℕ} (hN : 1 ≤ N) :
    ((terminalBadStarts N L B).card : ℝ) ≤
      2 * L * Real.sqrt (dyadicCutoff N L) *
        Real.exp (2 * Real.sqrt B) := by
  have hcard := card_terminalBadStarts_le (N := N) (L := L) (B := B) hN
  have hkernel :=
    card_boundedLargeKernelValues_cast_le_exp
      B 1 (dyadicCutoff N L)
  rw [← unitLargeKernelValues_eq_bounded B (dyadicCutoff N L)] at hkernel
  norm_num at hkernel
  calc
    ((terminalBadStarts N L B).card : ℝ) ≤
        (L : ℝ) *
          ((unitLargeKernelValues B (dyadicCutoff N L)).card : ℝ) := by
      exact_mod_cast hcard
    _ ≤ (L : ℝ) *
        (2 * Real.sqrt (dyadicCutoff N L) *
          Real.exp (2 * Real.sqrt B)) := by
      exact mul_le_mul_of_nonneg_left hkernel (Nat.cast_nonneg L)
    _ = 2 * L * Real.sqrt (dyadicCutoff N L) *
        Real.exp (2 * Real.sqrt B) := by
      ring

end BadStartCount
end PaperC
