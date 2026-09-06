import PaperCV282.SectorEightGeometry
import PaperCV282.KernelWindowEnergy
import PaperCV282.TerminalPartnerCount

set_option maxHeartbeats 1200000

/-!
# Terminal geometry at the scale of the larger start

Both starts are only required to be below `2X`. No lower comparison between
the two starts is used. Every isolated kernel appears in both windows, so
the small-kernel lower bound is supplied separately for both orientations.
-/

namespace PaperC.V282.TerminalSliceGeometry

open Affine LargeOddKernel BoundedRatioTerminalFibers
open BoundedRatioCanonicalTerminalPopulation PropositionSixteenOne
open ResidualSectorPartition SectorEightGeometry KernelWindowEnergy

noncomputable section

def kernelThreshold (X L : ℕ) : ℕ := Nat.sqrt (6 * X * (L + 1))

theorem kernelThreshold_le_sqrt (X L : ℕ) :
    (kernelThreshold X L : ℝ) ≤ 3 * Real.sqrt ((X : ℝ) * (L + 1)) := by
  have hn := Nat.sqrt_le' (6 * X * (L + 1))
  have hsq : (kernelThreshold X L : ℝ) ^ 2 ≤ 6 * (X : ℝ) * (L + 1) := by
    exact_mod_cast hn
  have hroot := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (X : ℝ) * (L + 1))
  have hrootpos := Real.sqrt_nonneg ((X : ℝ) * (L + 1))
  have hnonneg : (0 : ℝ) ≤ kernelThreshold X L := Nat.cast_nonneg _
  nlinarith

def componentKernel {N M A L : ℕ} (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L) (C : BoundedPairComponent A pair) : ℕ :=
  largeOddKernel (L + 1)
    (startCompleteVertexLabel pair.1.1 L (pairComponentCertificate hN pair C).left)

def smallComponents {N M A L : ℕ} (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L) (T : ℕ) :
    Finset (BoundedPairComponent A pair) :=
  (boundedCanonicalPairComponents A pair).attach.filter fun C =>
    componentKernel hN pair C ≤ T

theorem startCompleteVertexLabel_eq_sub_one_add {x L : ℕ} (hx : 1 ≤ x)
    (i : Fin (L + 1)) : startCompleteVertexLabel x L i = x - 1 + i.val := by
  unfold startCompleteVertexLabel
  split_ifs <;> omega

theorem startCompleteVertexLabel_le_three_mul {X x L : ℕ}
    (hx : x < 2 * X) (hL : L ≤ X) (i : Fin (L + 1)) :
    startCompleteVertexLabel x L i ≤ 3 * X := by
  unfold startCompleteVertexLabel
  have hi := i.isLt
  split_ifs <;> omega

theorem abs_crossDeterminant_le_six_mul {X x y L : ℕ}
    (hx : 2 ≤ x) (hy : 2 ≤ y) (hxX : x < 2 * X) (hyX : y < 2 * X)
    (hL : L ≤ X) (is js it jt : Fin (L + 1)) :
    |TerminalMatching.crossDeterminant
      (startCompleteVertexLabel x L is) (startCompleteVertexLabel y L js)
      (startCompleteVertexLabel x L it) (startCompleteVertexLabel y L jt)| ≤
      ((6 * X * (L + 1) : ℕ) : ℤ) := by
  have h := TerminalMatching.abs_crossDeterminant_le
    (startCompleteVertexLabel_le_three_mul hxX hL is)
    (startCompleteVertexLabel_le_three_mul hyX hL js)
    (Nat.le_of_lt (RelationalPrimeAssignment.startCompleteVertexLabel_dist_lt
      (by omega : 1 ≤ x) it is))
    (Nat.le_of_lt (RelationalPrimeAssignment.startCompleteVertexLabel_dist_lt
      (by omega : 1 ≤ y) jt js))
  convert h using 1
  congr 1
  ring

/-- The exact ambient constant in Lemma 3.22 comes from labels below `2M`. -/
theorem abs_crossDeterminant_le_four_mul {M x y L : ℕ}
    (hx : 2 ≤ x) (hy : 2 ≤ y) (hxM : x < M) (hyM : y < M)
    (hL : L ≤ M) (is js it jt : Fin (L + 1)) :
    |TerminalMatching.crossDeterminant
      (startCompleteVertexLabel x L is) (startCompleteVertexLabel y L js)
      (startCompleteVertexLabel x L it) (startCompleteVertexLabel y L jt)| ≤
      ((4 * M * (L + 1) : ℕ) : ℤ) := by
  have hleft : startCompleteVertexLabel x L is ≤ 2 * M := by
    unfold startCompleteVertexLabel
    split_ifs <;> omega
  have hright : startCompleteVertexLabel y L js ≤ 2 * M := by
    unfold startCompleteVertexLabel
    split_ifs <;> omega
  have h := TerminalMatching.abs_crossDeterminant_le hleft hright
    (Nat.le_of_lt (RelationalPrimeAssignment.startCompleteVertexLabel_dist_lt
      (by omega : 1 ≤ x) it is))
    (Nat.le_of_lt (RelationalPrimeAssignment.startCompleteVertexLabel_dist_lt
      (by omega : 1 ≤ y) jt js))
  convert h using 1
  congr 1
  ring

/-- The complete arithmetic package of Lemma 3.22 for actual sector-eight components. -/
theorem lemma_three_twenty_two {N M A L : ℕ} (hN : 2 ≤ N) (hA : 1 ≤ A)
    (hL : L ≤ M) (pair : SeparatedBoundedRatioPair N M L)
    (hsector : sectorOf A hN pair = 7)
    {Cs Ct : BoundedPairComponent A pair} (hST : Cs ≠ Ct) :
    let certS := pairComponentCertificate hN pair Cs
    let certT := pairComponentCertificate hN pair Ct
    let Xs := startCompleteVertexLabel pair.1.1 L certS.left
    let Ys := startCompleteVertexLabel pair.1.2 L certS.right
    let Xt := startCompleteVertexLabel pair.1.1 L certT.left
    let Yt := startCompleteVertexLabel pair.1.2 L certT.right
    let Rs := largeOddKernel (L + 1) Xs
    let Rt := largeOddKernel (L + 1) Xt
    Rs = largeOddKernel (L + 1) Ys ∧ Rt = largeOddKernel (L + 1) Yt ∧
      1 < Rs ∧ 1 < Rt ∧ Nat.Coprime Rs Rt ∧
      (((Rs * Rt : ℕ) : ℤ) ∣ TerminalMatching.crossDeterminant Xs Ys Xt Yt) ∧
      0 < |TerminalMatching.crossDeterminant Xs Ys Xt Yt| ∧
      |TerminalMatching.crossDeterminant Xs Ys Xt Yt| ≤ ((4 * M * (L + 1) : ℕ) : ℤ) := by
  have hp := distinct_pairComponents_kernel_package hN pair hST
  have hne := SectorEightGeometry.crossDeterminant_ne_zero hN hA pair hsector hST
  have hgeo := mem_separatedBoundedRatioPairs.mp pair.2
  exact ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2,
    abs_pos.mpr hne, abs_crossDeterminant_le_four_mul
      (pair_coordinates_two_le hN pair).1 (pair_coordinates_two_le hN pair).2
      (Finset.mem_Ico.mp hgeo.1).2 (Finset.mem_Ico.mp hgeo.2.1).2 hL _ _ _ _⟩

/-- The ambient product bound retains the literal factor `4MB`. -/
theorem componentKernel_product_le_ambient {N M A L : ℕ} (hN : 2 ≤ N)
    (hA : 1 ≤ A) (hL : L ≤ M) (pair : SeparatedBoundedRatioPair N M L)
    (hsector : sectorOf A hN pair = 7)
    {Cs Ct : BoundedPairComponent A pair} (hST : Cs ≠ Ct) :
    componentKernel hN pair Cs * componentKernel hN pair Ct ≤ 4 * M * (L + 1) := by
  have hp := lemma_three_twenty_two hN hA hL pair hsector hST
  exact BoundedRatioTerminalClosure.kernel_product_le_of_dvd_crossDeterminant
    hp.2.2.1 hp.2.2.2.1 (abs_pos.mp hp.2.2.2.2.2.2.1)
    hp.2.2.2.2.2.1 hp.2.2.2.2.2.2.2

theorem componentKernel_product_le {N M A L X : ℕ} (hN : 2 ≤ N)
    (hA : 1 ≤ A) (pair : SeparatedBoundedRatioPair N M L)
    (hsector : sectorOf A hN pair = 7)
    (hxX : pair.1.1 < 2 * X) (hyX : pair.1.2 < 2 * X) (hL : L ≤ X)
    {Cs Ct : BoundedPairComponent A pair} (hST : Cs ≠ Ct) :
    componentKernel hN pair Cs * componentKernel hN pair Ct ≤ 6 * X * (L + 1) := by
  have hp := distinct_pairComponents_kernel_package hN pair hST
  exact BoundedRatioTerminalClosure.kernel_product_le_of_dvd_crossDeterminant
    hp.2.2.1 hp.2.2.2.1 (SectorEightGeometry.crossDeterminant_ne_zero hN hA pair hsector hST)
    hp.2.2.2.2.2
    (abs_crossDeterminant_le_six_mul (pair_coordinates_two_le hN pair).1
      (pair_coordinates_two_le hN pair).2 hxX hyX hL _ _ _ _)

theorem card_largeComponents_le_one {N M A L X : ℕ} (hN : 2 ≤ N)
    (hA : 1 ≤ A) (pair : SeparatedBoundedRatioPair N M L)
    (hsector : sectorOf A hN pair = 7)
    (hxX : pair.1.1 < 2 * X) (hyX : pair.1.2 < 2 * X) (hL : L ≤ X) :
    ((boundedCanonicalPairComponents A pair).attach.filter fun C =>
      kernelThreshold X L < componentKernel hN pair C).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro C hC D hD
  by_contra hne
  have hp := componentKernel_product_le hN hA pair hsector hxX hyX hL hne
  have hC' := (Finset.mem_filter.mp hC).2
  have hD' := (Finset.mem_filter.mp hD).2
  have hs := Nat.lt_succ_sqrt (6 * X * (L + 1))
  unfold kernelThreshold at hC' hD'
  nlinarith

theorem terminalIndex_le_card_smallComponents {N M A L X : ℕ} (hN : 2 ≤ N)
    (hA : 1 ≤ A) (pair : SeparatedBoundedRatioPair N M L)
    (hsector : sectorOf A hN pair = 7)
    (hxX : pair.1.1 < 2 * X) (hyX : pair.1.2 < 2 * X) (hL : L ≤ X) :
    L + 1 - 3 * terminalIndex A pair - 1 ≤
      (smallComponents (A := A) hN pair (kernelThreshold X L)).card := by
  classical
  have hlarge := card_largeComponents_le_one hN hA pair hsector hxX hyX hL
  have hcount := terminalIndex_isolated_count (A := A) hN pair
  have hsplit : (smallComponents (A := A) hN pair (kernelThreshold X L)).card +
      ((boundedCanonicalPairComponents A pair).attach.filter fun C =>
        kernelThreshold X L < componentKernel hN pair C).card =
      (boundedCanonicalPairComponents A pair).card := by
    simpa only [smallComponents, not_le, Finset.card_attach] using
      (Finset.card_filter_add_card_filter_not
        (s := (boundedCanonicalPairComponents A pair).attach)
        (p := fun C => componentKernel hN pair C ≤ kernelThreshold X L))
  omega

theorem card_smallComponents_le_leftOffsets {N M A L T : ℕ} (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L) :
    (smallComponents (A := A) hN pair T).card ≤ (smallKernelOffsets (L + 1) T L pair.1.1).card := by
  classical
  apply Finset.card_le_card_of_injOn
    (fun C => (pairComponentCertificate hN pair C).left.val)
  · intro C hC
    have hkernel := (Finset.mem_filter.mp hC).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (pairComponentCertificate hN pair C).left.isLt, ?_⟩
    unfold componentKernel at hkernel
    rw [startCompleteVertexLabel_eq_sub_one_add
      (by have h := (pair_coordinates_two_le hN pair).1; omega)] at hkernel
    exact hkernel
  · intro C hC D hD heq
    exact certificate_left_injective hN pair (Fin.ext heq)

theorem card_smallComponents_le_rightOffsets {N M A L T : ℕ} (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L) :
    (smallComponents (A := A) hN pair T).card ≤ (smallKernelOffsets (L + 1) T L pair.1.2).card := by
  classical
  apply Finset.card_le_card_of_injOn
    (fun C => (pairComponentCertificate hN pair C).right.val)
  · intro C hC
    have hkernel := (Finset.mem_filter.mp hC).2
    have heq := (component_kernel_eq_and_one_lt hN pair C).1
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (pairComponentCertificate hN pair C).right.isLt, ?_⟩
    rw [← startCompleteVertexLabel_eq_sub_one_add
      (by have h := (pair_coordinates_two_le hN pair).2; omega), ← heq]
    exact hkernel
  · intro C hC D hD heq
    exact certificate_right_injective hN pair (Fin.ext heq)

theorem terminalIndex_le_smallKernelOffsets_both {N M A L X : ℕ} (hN : 2 ≤ N)
    (hA : 1 ≤ A) (pair : SeparatedBoundedRatioPair N M L)
    (hsector : sectorOf A hN pair = 7)
    (hxX : pair.1.1 < 2 * X) (hyX : pair.1.2 < 2 * X) (hL : L ≤ X) :
    L + 1 - 3 * terminalIndex A pair - 1 ≤
        (smallKernelOffsets (L + 1) (kernelThreshold X L) L pair.1.1).card ∧
      L + 1 - 3 * terminalIndex A pair - 1 ≤
        (smallKernelOffsets (L + 1) (kernelThreshold X L) L pair.1.2).card := by
  have h := terminalIndex_le_card_smallComponents hN hA pair hsector hxX hyX hL
  exact ⟨h.trans (card_smallComponents_le_leftOffsets hN pair),
    h.trans (card_smallComponents_le_rightOffsets hN pair)⟩

theorem smallKernelOffsets_nonempty_both {N M A L X : ℕ} (hN : 2 ≤ N)
    (hA : 1 ≤ A) (pair : SeparatedBoundedRatioPair N M L)
    (hsector : sectorOf A hN pair = 7)
    (hxX : pair.1.1 < 2 * X) (hyX : pair.1.2 < 2 * X) (hL : L ≤ X) :
    (smallKernelOffsets (L + 1) (kernelThreshold X L) L pair.1.1).Nonempty ∧
      (smallKernelOffsets (L + 1) (kernelThreshold X L) L pair.1.2).Nonempty := by
  have hbudget := terminalIndex_budget hN pair hsector
  have h := terminalIndex_le_smallKernelOffsets_both hN hA pair hsector hxX hyX hL
  exact ⟨Finset.card_pos.mp (by omega), Finset.card_pos.mp (by omega)⟩

theorem mem_twoKernelPartnerStarts_both {N M A L X : ℕ} (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L) (hsector : sectorOf A hN pair = 7)
    (hxX : pair.1.1 < 2 * X) (hyX : pair.1.2 < 2 * X) :
    pair.1.2 ∈ TerminalPartnerCount.twoKernelPartnerStarts X L pair.1.1 ∧
      pair.1.1 ∈ TerminalPartnerCount.twoKernelPartnerStarts X L pair.1.2 := by
  obtain ⟨Cs, Ct, hST⟩ := exists_distinct_pairComponents hN pair hsector
  obtain ⟨hS, hT, hSpos, hTpos, hcoprime, _⟩ :=
    distinct_pairComponents_kernel_package hN pair hST
  have hl : (pairComponentCertificate hN pair Cs).left ≠
      (pairComponentCertificate hN pair Ct).left :=
    fun h => hST (certificate_left_injective hN pair h)
  have hr : (pairComponentCertificate hN pair Cs).right ≠
      (pairComponentCertificate hN pair Ct).right :=
    fun h => hST (certificate_right_injective hN pair h)
  constructor
  · apply TerminalPartnerCount.mem_twoKernelPartnerStarts.mpr
    refine ⟨_, _, hSpos, hTpos, hcoprime, ?_⟩
    exact TerminalPartnerCount.mem_kernelPartnerStarts.mpr
      ⟨⟨(pair_coordinates_two_le hN pair).2, hyX.le⟩,
        (pairComponentCertificate hN pair Cs).right,
        (pairComponentCertificate hN pair Ct).right, hr, hS.symm, hT.symm⟩
  · apply TerminalPartnerCount.mem_twoKernelPartnerStarts.mpr
    rw [hS] at hSpos
    rw [hT] at hTpos
    rw [hS, hT] at hcoprime
    refine ⟨_, _, hSpos, hTpos, hcoprime, ?_⟩
    exact TerminalPartnerCount.mem_kernelPartnerStarts.mpr
      ⟨⟨(pair_coordinates_two_le hN pair).1, hxX.le⟩,
        (pairComponentCertificate hN pair Cs).left,
        (pairComponentCertificate hN pair Ct).left, hl, hS, hT⟩

end

end PaperC.V282.TerminalSliceGeometry
