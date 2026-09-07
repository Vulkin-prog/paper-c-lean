import PaperCV282.ResidualSectorPartition
import PaperC.Asymptotics.BoundedRatioTerminalFibers

set_option maxHeartbeats 1200000

/-!
# Isolated component certificates in the actual eighth sector

The index is the sum of the actual terminal slack and arithmetic row rank.
The rank test forces at least two isolated components. Their certificates
are extracted from the canonical graph, without a terminal-set hypothesis.
-/

namespace PaperC.V282.SectorEightGeometry

open Affine Affine.CanonicalRationalCode LargePrimeGraph LargeOddKernel
open LargePrimeOccurrences
open BoundedRatioCanonicalTerminalPopulation BoundedRatioTerminalFibers
open PropositionSixteenOne ResidualSectorPartition

noncomputable section

def terminalIndex {N M L : ℕ} (A : ℕ)
    (pair : SeparatedBoundedRatioPair N M L) : ℕ :=
  boundedTerminalSlack A pair + boundedCanonicalSmallRowRank A pair

theorem terminalIndex_budget {N M A L : ℕ} (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L)
    (hsector : sectorOf A hN pair = 7) :
    3 * terminalIndex A pair + 2 ≤ L + 1 := by
  have h := (sectorOf_eq_eight_iff.mp hsector).2.2.2.2.2.2
  unfold exceedsRankBudget rankBudget at h
  unfold terminalIndex
  omega

theorem terminalIndex_isolated_count {N M A L : ℕ} (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L) :
    L + 1 - 3 * terminalIndex A pair ≤
      (boundedCanonicalPairComponents A pair).card := by
  have h := (bounded_terminal_component_count (A := A) hN pair).2
  unfold terminalIndex
  omega

theorem two_le_isolated_count {N M A L : ℕ} (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L)
    (hsector : sectorOf A hN pair = 7) :
    2 ≤ (boundedCanonicalPairComponents A pair).card := by
  have hbudget := terminalIndex_budget hN pair hsector
  have hcount := terminalIndex_isolated_count (A := A) hN pair
  omega

theorem exists_distinct_pairComponents {N M A L : ℕ} (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L)
    (hsector : sectorOf A hN pair = 7) :
    ∃ Cs Ct : BoundedPairComponent A pair, Cs ≠ Ct := by
  classical
  obtain ⟨Cs, hs, Ct, ht, hne⟩ :=
    Finset.one_lt_card.mp (two_le_isolated_count hN pair hsector)
  exact ⟨⟨Cs, hs⟩, ⟨Ct, ht⟩, fun h => hne (congrArg Subtype.val h)⟩

theorem certificate_left_injective {N M A L : ℕ} (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L) :
    Function.Injective (fun C : BoundedPairComponent A pair =>
      (pairComponentCertificate hN pair C).left) := by
  intro C D h
  apply Subtype.ext
  exact (pairComponentCertificate hN pair C).left_component.symm.trans
    ((congrArg (fun i => (largePrimeGraph pair.1.1 pair.1.2 L).connectedComponentMk
      (Sum.inl i)) h).trans (pairComponentCertificate hN pair D).left_component)

theorem certificate_right_injective {N M A L : ℕ} (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L) :
    Function.Injective (fun C : BoundedPairComponent A pair =>
      (pairComponentCertificate hN pair C).right) := by
  intro C D h
  apply Subtype.ext
  exact (pairComponentCertificate hN pair C).right_component.symm.trans
    ((congrArg (fun i => (largePrimeGraph pair.1.1 pair.1.2 L).connectedComponentMk
      (Sum.inr i)) h).trans (pairComponentCertificate hN pair D).right_component)

theorem component_kernel_eq_and_one_lt {N M A L : ℕ} (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L) (C : BoundedPairComponent A pair) :
    let cert := pairComponentCertificate hN pair C
    largeOddKernel (L + 1) (startCompleteVertexLabel pair.1.1 L cert.left) =
        largeOddKernel (L + 1) (startCompleteVertexLabel pair.1.2 L cert.right) ∧
      1 < largeOddKernel (L + 1) (startCompleteVertexLabel pair.1.1 L cert.left) := by
  dsimp only
  have hm := pairComponentCertificate_mem hN pair C
  have hs := pairComponentCertificate_shape hN pair C
  constructor
  · simpa only [twoStartCompleteVertexLabel] using
      (TerminalMatching.largeOddKernel_eq_of_two_vertex_component
        (x := pair.1.1) (y := pair.1.2) (L := L)
        C.1 hm.1 hm.2 hs.1 hs.2.1 hs.2.2)
  · simpa only [twoStartCompleteVertexLabel] using
      (TerminalMatching.one_lt_largeOddKernel_of_not_isDefective
        (TerminalMatching.not_isDefective_of_distinct_mem_component hm.1 hm.2 hs.1))

theorem crossDeterminant_ne_zero {N M A L : ℕ} (hN : 2 ≤ N)
    (hA : 1 ≤ A) (pair : SeparatedBoundedRatioPair N M L)
    (hsector : sectorOf A hN pair = 7)
    {Cs Ct : BoundedPairComponent A pair} (hST : Cs ≠ Ct) :
    let certS := pairComponentCertificate hN pair Cs
    let certT := pairComponentCertificate hN pair Ct
    TerminalMatching.crossDeterminant
      (startCompleteVertexLabel pair.1.1 L certS.left)
      (startCompleteVertexLabel pair.1.2 L certS.right)
      (startCompleteVertexLabel pair.1.1 L certT.left)
      (startCompleteVertexLabel pair.1.2 L certT.right) ≠ 0 := by
  apply crossDeterminant_ne_of_canonicalNonaligned hA
    (pair_coordinates_two_le hN pair).1 (pair_coordinates_two_le hN pair).2
    (nonaligned_of_sector_at_least_five hN pair (by rw [hsector]; decide))
  exact fun h => hST (pairComponentCertificate_cell_injective hN pair h)

end

end PaperC.V282.SectorEightGeometry
