import PaperC.Combinatorics.CanonicalResidualComponents
import PaperC.Combinatorics.ExactUnitIsolation
import PaperC.Combinatorics.LargePrimeComponents
import PaperC.Combinatorics.OneUnitResidualExceptions

set_option maxHeartbeats 1800000

/-!
# Residual components free of exact aligned units

For a fixed primitive channel, this file removes from the canonical residual
family every component meeting either occurrence of an exact channel unit.
The operation costs at most two components.  In the active branch with at
least two exact units it costs nothing: the left occurrence was already
removed by `CanonicalResidualComponents`, while the exact-unit dichotomy
puts the right occurrence either in the same component or in a defective
singleton.  In the one-unit branch the two possible exceptional components
are those of `OneUnitResidualExceptions`; in the zero-unit branch there is
nothing to remove.
-/

namespace PaperC
namespace AlignedExactFreeComponents

open Affine
open Affine.RationalChannelCode
open CanonicalResidualComponents
open ExactUnitIsolation
open LargePrimeGraph
open LargePrimeGraphResolution
open OneUnitResidualExceptions
open PinnedGraphResolution
open ResidualComponentCounts

noncomputable section

noncomputable local instance instDecidableLargePrimeAdj
    (x y L : ℕ) :
    DecidableRel (largePrimeGraph x y L).Adj :=
  Classical.decRel _

/--
A component is exact-free for `(a,b,h)` when it contains neither occurrence
of any exact cell of that channel.
-/
def IsExactFreeComponent
    (x y L a b : ℕ) (h : ℤ)
    (C : (largePrimeGraph x y L).ConnectedComponent) : Prop :=
  ∀ cell ∈ rationalChannelUnits L a b h,
    (largePrimeGraph x y L).connectedComponentMk
          (Sum.inl cell.1) ≠ C ∧
      (largePrimeGraph x y L).connectedComponentMk
          (Sum.inr cell.2) ≠ C

/--
The exact-free part of the canonical residual component family for one
explicit channel.
-/
noncomputable def exactFreeResidualComponents
    (x y L a b : ℕ) (h : ℤ) :
    Finset (largePrimeGraph x y L).ConnectedComponent := by
  classical
  exact
    (residualComponents x y L a b h).filter
      (IsExactFreeComponent x y L a b h)

@[simp]
theorem mem_exactFreeResidualComponents
    {x y L a b : ℕ} {h : ℤ}
    {C : (largePrimeGraph x y L).ConnectedComponent} :
    C ∈ exactFreeResidualComponents x y L a b h ↔
      C ∈ residualComponents x y L a b h ∧
        IsExactFreeComponent x y L a b h C := by
  classical
  simp [exactFreeResidualComponents]

/-- Membership in the filtered family implies exact-freeness. -/
theorem isExactFreeComponent_of_mem
    {x y L a b : ℕ} {h : ℤ}
    {C : (largePrimeGraph x y L).ConnectedComponent}
    (hC : C ∈ exactFreeResidualComponents x y L a b h) :
    IsExactFreeComponent x y L a b h C :=
  (mem_exactFreeResidualComponents.mp hC).2

/-- Membership in the filtered family still implies residual membership. -/
theorem mem_residualComponents_of_mem_exactFree
    {x y L a b : ℕ} {h : ℤ}
    {C : (largePrimeGraph x y L).ConnectedComponent}
    (hC : C ∈ exactFreeResidualComponents x y L a b h) :
    C ∈ residualComponents x y L a b h :=
  (mem_exactFreeResidualComponents.mp hC).1

/-- Exact-free residual components remain nontrivial and unpinned. -/
theorem isNontrivialUnpinnedComponent_of_mem_exactFree
    {x y L a b : ℕ} {h : ℤ}
    {C : (largePrimeGraph x y L).ConnectedComponent}
    (hC : C ∈ exactFreeResidualComponents x y L a b h) :
    IsNontrivialUnpinnedComponent
      (largePrimeGraph x y L)
      (pinnedVertices x y L) C :=
  isNontrivialUnpinnedComponent_of_mem_residualComponents
    (mem_residualComponents_of_mem_exactFree hC)

/-! ## The branch with at least two exact units -/

/--
With at least two exact units, every residual component is already
exact-free.  The left occurrence is excluded by the definition of the
canonical residual family.  For the right occurrence, the exact-unit
dichotomy gives either a defective singleton or the same component as the
left occurrence.
-/
theorem isExactFreeComponent_of_mem_residual_of_two_le
    {x y L a b : ℕ} {h : ℤ}
    (ha : 0 < a) (hb : 0 < b)
    (hab : a.Coprime b)
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hheight : h = (b : ℤ) * y - (a : ℤ) * x)
    (hm : 2 ≤ channelUnitCount L a b h)
    {C : (largePrimeGraph x y L).ConnectedComponent}
    (hC : C ∈ residualComponents x y L a b h) :
    IsExactFreeComponent x y L a b h C := by
  classical
  intro cell hcell
  have hOnChannel :
      OnChannel a b h
        (channelVertexOffset cell.1,
          channelVertexOffset cell.2) :=
    mem_rationalChannelUnits.mp hcell
  have hleft :
      (largePrimeGraph x y L).connectedComponentMk
          (Sum.inl cell.1) ≠ C := by
    intro heq
    have hnot :=
      onChannel_component_not_mem_residualComponents
        (show 1 ≤ x by omega) (show 1 ≤ y by omega)
        hm cell hOnChannel
    exact hnot (heq ▸ hC)
  refine ⟨hleft, ?_⟩
  let unit : ChannelUnit L a b h := ⟨cell, hcell⟩
  have hmUnits :
      2 ≤ (rationalChannelUnits L a b h).card := by
    simpa [channelUnitCount_eq_card_rationalChannelUnits]
      using hm
  have hsmall : Nat.max a b < L + 1 := by
    have hle : Nat.max a b ≤ L :=
      max_channelCoefficients_le_length
        (L := L) (a := a) (b := b) (h := h)
        ha hb hab hmUnits
    omega
  obtain ⟨t, hfactor⟩ :=
    channelUnit_exactUnitFactorization
      ha hb hab hx hy hheight hsmall unit
  rcases
      exactUnit_graph_dichotomy
        (show 1 ≤ x by omega) (show 1 ≤ y by omega)
        hfactor with hdef | hjoined
  · intro hright
    have hisolated :=
      isIsolatedUnpinnedComponent_of_isDefective
        (show 1 ≤ x by omega) (show 1 ≤ y by omega)
        hdef.2
    have hnontrivial :=
      isNontrivialUnpinnedComponent_of_mem_residualComponents hC
    rw [IsIsolatedUnpinnedComponent] at hisolated
    rw [IsNontrivialUnpinnedComponent] at hnontrivial
    have hcardOne :
        Fintype.card C.supp = 1 := by
      have hcardRight := hisolated.2
      dsimp only [unit] at hcardRight
      rw [hright] at hcardRight
      exact hcardRight
    omega
  · intro hright
    have hsame :
        (largePrimeGraph x y L).connectedComponentMk
            (Sum.inl cell.1) =
          (largePrimeGraph x y L).connectedComponentMk
            (Sum.inr cell.2) := by
      simpa [unit] using
        SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
          hjoined.1
    exact hleft (hsame.trans hright)

/-- In the active branch the exact-free filter leaves the family unchanged. -/
theorem exactFreeResidualComponents_eq_of_two_le
    {x y L a b : ℕ} {h : ℤ}
    (ha : 0 < a) (hb : 0 < b)
    (hab : a.Coprime b)
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hheight : h = (b : ℤ) * y - (a : ℤ) * x)
    (hm : 2 ≤ channelUnitCount L a b h) :
    exactFreeResidualComponents x y L a b h =
      residualComponents x y L a b h := by
  classical
  ext C
  simp only [mem_exactFreeResidualComponents]
  constructor
  · exact And.left
  · intro hC
    exact
      ⟨hC,
        isExactFreeComponent_of_mem_residual_of_two_le
          ha hb hab hx hy hheight hm hC⟩

/-! ## The one-unit and zero-unit branches -/

/--
When there is one exact unit, every residual component which fails
exact-freeness belongs to the canonical two-component exceptional family.
-/
theorem mem_oneUnitExceptionalComponents_of_not_exactFree
    {x y L a b : ℕ} {h : ℤ}
    (hm : channelUnitCount L a b h = 1)
    {C : (largePrimeGraph x y L).ConnectedComponent}
    (hC : C ∈ residualComponents x y L a b h)
    (hbad : ¬IsExactFreeComponent x y L a b h C) :
    C ∈
      oneUnitExceptionalComponents
        (residualComponents x y L a b h) hm := by
  classical
  rw [mem_oneUnitExceptionalComponents]
  refine ⟨hC, ?_⟩
  simp only [IsExactFreeComponent, not_forall] at hbad
  obtain ⟨cell, hcell, hmeet⟩ := hbad
  have hcellEq :
      cell = (uniqueChannelUnit hm).1 :=
    channelCell_eq_uniqueChannelUnit hm hcell
  simp only [not_and_or] at hmeet
  rcases hmeet with hleft | hright
  · exact Or.inl (by simpa [hcellEq] using not_ne_iff.mp hleft)
  · exact Or.inr (by simpa [hcellEq] using not_ne_iff.mp hright)

/-- With no exact unit, every residual component is exact-free. -/
theorem isExactFreeComponent_of_channelUnitCount_eq_zero
    {x y L a b : ℕ} {h : ℤ}
    (hm : channelUnitCount L a b h = 0)
    (C : (largePrimeGraph x y L).ConnectedComponent) :
    IsExactFreeComponent x y L a b h C := by
  classical
  intro cell hcell
  have hcard :
      (rationalChannelUnits L a b h).card = 0 := by
    simpa [channelUnitCount_eq_card_rationalChannelUnits] using hm
  have hempty :
      rationalChannelUnits L a b h = ∅ :=
    Finset.card_eq_zero.mp hcard
  rw [hempty] at hcell
  simp at hcell

/-! ## Uniform cost of exact-unit removal -/

/--
Removing every component which meets an exact channel unit costs at most two
residual components.
-/
theorem card_residualComponents_le_card_exactFree_add_two
    {x y L a b : ℕ} {h : ℤ}
    (ha : 0 < a) (hb : 0 < b)
    (hab : a.Coprime b)
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hheight : h = (b : ℤ) * y - (a : ℤ) * x) :
    (residualComponents x y L a b h).card ≤
      (exactFreeResidualComponents x y L a b h).card + 2 := by
  classical
  let components := residualComponents x y L a b h
  let P :
      (largePrimeGraph x y L).ConnectedComponent → Prop :=
    IsExactFreeComponent x y L a b h
  have hsplit :
      (components.filter P).card +
          (components.filter fun C ↦ ¬P C).card =
        components.card :=
    Finset.filter_card_add_filter_neg_card_eq_card
      (s := components) P
  have hbad :
      (components.filter fun C ↦ ¬P C).card ≤ 2 := by
    by_cases hm₂ : 2 ≤ channelUnitCount L a b h
    · have hempty :
          components.filter (fun C ↦ ¬P C) = ∅ := by
        ext C
        simp only [Finset.mem_filter, Finset.not_mem_empty,
          iff_false, not_and]
        intro hC
        exact not_not_intro
          (isExactFreeComponent_of_mem_residual_of_two_le
            ha hb hab hx hy hheight hm₂ hC)
      simp [hempty]
    · have hm_cases :
          channelUnitCount L a b h = 0 ∨
            channelUnitCount L a b h = 1 := by
        omega
      rcases hm_cases with hm₀ | hm₁
      · have hempty :
            components.filter (fun C ↦ ¬P C) = ∅ := by
          ext C
          simp only [Finset.mem_filter, Finset.not_mem_empty,
            iff_false, not_and]
          intro _hC
          exact not_not_intro
            (isExactFreeComponent_of_channelUnitCount_eq_zero
              hm₀ C)
        simp [hempty]
      · calc
          (components.filter fun C ↦ ¬P C).card ≤
              (oneUnitExceptionalComponents components hm₁).card := by
            apply Finset.card_le_card
            intro C hC
            have hmem := (Finset.mem_filter.mp hC)
            exact
              mem_oneUnitExceptionalComponents_of_not_exactFree
                hm₁ hmem.1 hmem.2
          _ ≤ 2 :=
            card_oneUnitExceptionalComponents_le_two
              components hm₁
  change components.card ≤ (components.filter P).card + 2
  omega

end

end AlignedExactFreeComponents
end PaperC
