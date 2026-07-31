import PaperC.Arithmetic.CanonicalChannel
import PaperC.Asymptotics.BoundedRatioTerminalClosure
import PaperC.Diophantine.TerminalPartnerPell

set_option maxHeartbeats 800000

/-!
# Canonical fibres of the bounded-ratio terminal population

This file supplies the population-specific finite maps left open by
`BoundedRatioTerminalClosure`.  In particular, a size-two canonical residual
component is turned into the concrete certificate used by
`TerminalMatching`; canonical nonalignment is then used to prove that the
cross determinant of two distinct such certificates is nonzero.

No arithmetic bridge is introduced here.  The partner-fibre statements at
the end use `TerminalPartnerPell.TerminalPartnerPolynomialBoxStatement` as
an ordinary theorem hypothesis.
-/

namespace PaperC
namespace BoundedRatioTerminalFibers

open scoped BigOperators
open Affine
open Affine.CanonicalRationalCode
open BoundedRatioCanonicalTerminalPopulation
open BoundedRatioGeometry
open BoundedRatioTerminalClosure
open CanonicalResidualComponents
open LargePrimeComponents
open LargePrimeGraph
open LargePrimeOccurrences
open PropositionSixteenOne
open ResidualCertificates
open SectionElevenPartition
open TerminalComponentCount

noncomputable section

noncomputable local instance instDecidableLargePrimeAdj
    (x y L : ℕ) :
    DecidableRel (largePrimeGraph x y L).Adj :=
  Classical.decRel _

/-! ## Size-two components and their canonical certificates -/

/-- A canonical residual component of a pair whose support has size two. -/
abbrev BoundedPairComponent
    {N M L : ℕ} (A : ℕ)
    (pair : SeparatedBoundedRatioPair N M L) :=
  {C // C ∈ boundedCanonicalPairComponents A pair}

/-- Forgetting the size-two condition retains canonical residual membership. -/
def pairComponentAsResidual
    {N M A L : ℕ}
    {pair : SeparatedBoundedRatioPair N M L}
    (C : BoundedPairComponent A pair) :
    {C // C ∈ canonicalResidualComponents
      A pair.1.1 pair.1.2 L} :=
  ⟨C.1, (mem_pairComponents.mp C.2).1⟩

/-- The canonical Lemma 6.5 certificate attached to a size-two component. -/
noncomputable def pairComponentCertificate
    {N M A L : ℕ} (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L)
    (C : BoundedPairComponent A pair) :
    ComponentCertificate pair.1.1 pair.1.2 L C.1 :=
  canonicalResidualCertificates
    (show 1 ≤ pair.1.1 by
      have hxy := pair_coordinates_two_le hN pair
      omega)
    (show 1 ≤ pair.1.2 by
      have hxy := pair_coordinates_two_le hN pair
      omega)
    (pairComponentAsResidual C)

/-- Both certificate endpoints belong to their indexed component. -/
theorem pairComponentCertificate_mem
    {N M A L : ℕ} (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L)
    (C : BoundedPairComponent A pair) :
    (Sum.inl (pairComponentCertificate hN pair C).left :
        Occurrence L) ∈
        componentVertices pair.1.1 pair.1.2 L C.1 ∧
      (Sum.inr (pairComponentCertificate hN pair C).right :
        Occurrence L) ∈
        componentVertices pair.1.1 pair.1.2 L C.1 := by
  constructor
  · exact mem_componentVertices.mpr
      (pairComponentCertificate hN pair C).left_component
  · exact mem_componentVertices.mpr
      (pairComponentCertificate hN pair C).right_component

/-- A size-two component is unpinned and its certificate endpoints differ. -/
theorem pairComponentCertificate_shape
    {N M A L : ℕ} (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L)
    (C : BoundedPairComponent A pair) :
    (Sum.inl (pairComponentCertificate hN pair C).left :
        Occurrence L) ≠
        Sum.inr (pairComponentCertificate hN pair C).right ∧
      Fintype.card C.1.supp = 2 ∧
      ¬IsPinnedComponent pair.1.1 pair.1.2 L C.1 := by
  refine ⟨by simp, (mem_pairComponents.mp C.2).2, ?_⟩
  exact
    ComponentProductParity.not_isPinnedComponent_of_isNontrivialUnpinned
      (isNontrivialUnpinnedComponent_of_mem_canonicalResidualComponents
        (pairComponentAsResidual C).2)

/--
The full endpoint-kernel package for two distinct canonical size-two
components.
-/
theorem distinct_pairComponents_kernel_package
    {N M A L : ℕ} (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L)
    {Cs Ct : BoundedPairComponent A pair}
    (hST : Cs ≠ Ct) :
    let certS := pairComponentCertificate hN pair Cs
    let certT := pairComponentCertificate hN pair Ct
    let Xs := startCompleteVertexLabel pair.1.1 L certS.left
    let Ys := startCompleteVertexLabel pair.1.2 L certS.right
    let Xt := startCompleteVertexLabel pair.1.1 L certT.left
    let Yt := startCompleteVertexLabel pair.1.2 L certT.right
    let Rs := LargeOddKernel.largeOddKernel (L + 1) Xs
    let Rt := LargeOddKernel.largeOddKernel (L + 1) Xt
    Rs = LargeOddKernel.largeOddKernel (L + 1) Ys ∧
      Rt = LargeOddKernel.largeOddKernel (L + 1) Yt ∧
      1 < Rs ∧ 1 < Rt ∧
      Nat.Coprime Rs Rt ∧
      (((Rs * Rt : ℕ) : ℤ) ∣
        TerminalMatching.crossDeterminant Xs Ys Xt Yt) := by
  dsimp only
  let certS := pairComponentCertificate hN pair Cs
  let certT := pairComponentCertificate hN pair Ct
  have hmemS := pairComponentCertificate_mem hN pair Cs
  have hmemT := pairComponentCertificate_mem hN pair Ct
  have hshapeS := pairComponentCertificate_shape hN pair Cs
  have hshapeT := pairComponentCertificate_shape hN pair Ct
  have hcomponents : Cs.1 ≠ Ct.1 := by
    intro h
    apply hST
    exact Subtype.ext h
  have hpackage :=
    TerminalMatching.two_vertex_components_kernel_package
      (x := pair.1.1) (y := pair.1.2) (L := L)
      (Cs := Cs.1) (Ct := Ct.1)
      (vs := Sum.inl (pairComponentCertificate hN pair Cs).left)
      (ws := Sum.inr (pairComponentCertificate hN pair Cs).right)
      (vt := Sum.inl (pairComponentCertificate hN pair Ct).left)
      (wt := Sum.inr (pairComponentCertificate hN pair Ct).right)
      hmemS.1 hmemS.2 hshapeS.1 hshapeS.2.1 hshapeS.2.2
      hmemT.1 hmemT.2 hshapeT.1 hshapeT.2.1 hshapeT.2.2
      hcomponents
  simpa only [twoStartCompleteVertexLabel] using hpackage

/-! ## Canonical nonalignment forces determinant nonvanishing -/

/--
Two distinct complete-boundary cells with zero cross determinant define a
primitive rational channel containing both cells.  Hence that channel is a
canonical reduced candidate as soon as `A ≥ 1`.
-/
theorem reducedCandidate_of_crossDeterminant_eq_zero
    {A x y L : ℕ}
    (hA : 1 ≤ A) (hx : 2 ≤ x) (hy : 2 ≤ y)
    {is js it jt : Fin (L + 1)}
    (hcells : (is, js) ≠ (it, jt))
    (hzero :
      TerminalMatching.crossDeterminant
        (startCompleteVertexLabel x L is)
        (startCompleteVertexLabel y L js)
        (startCompleteVertexLabel x L it)
        (startCompleteVertexLabel y L jt) = 0) :
    ∃ a b : ℕ,
      (a, b) ∈
        reducedChannelCandidates x y (L + 1) ((L + 1) ^ A) := by
  let Xs := startCompleteVertexLabel x L is
  let Ys := startCompleteVertexLabel y L js
  let Xt := startCompleteVertexLabel x L it
  let Yt := startCompleteVertexLabel y L jt
  let g := Nat.gcd Xs Ys
  let a := Ys / g
  let b := Xs / g
  have hXs : 0 < Xs :=
    RationalChannelCode.startCompleteVertexLabel_pos hx is
  have hYs : 0 < Ys :=
    RationalChannelCode.startCompleteVertexLabel_pos hy js
  have hXt : 0 < Xt :=
    RationalChannelCode.startCompleteVertexLabel_pos hx it
  have hYt : 0 < Yt :=
    RationalChannelCode.startCompleteVertexLabel_pos hy jt
  have hg : 0 < g := by
    exact Nat.gcd_pos_of_pos_left Ys hXs
  have hXsg : b * g = Xs := by
    dsimp only [b, g]
    exact Nat.div_mul_cancel (Nat.gcd_dvd_left Xs Ys)
  have hYsg : a * g = Ys := by
    dsimp only [a, g]
    exact Nat.div_mul_cancel (Nat.gcd_dvd_right Xs Ys)
  have ha : 0 < a := by
    by_contra h
    have ha0 : a = 0 := Nat.eq_zero_of_not_pos h
    rw [ha0, zero_mul] at hYsg
    omega
  have hb : 0 < b := by
    by_contra h
    have hb0 : b = 0 := Nat.eq_zero_of_not_pos h
    rw [hb0, zero_mul] at hXsg
    omega
  have hab : Nat.Coprime a b := by
    dsimp only [a, b, g]
    exact (Nat.coprime_div_gcd_div_gcd hg).symm
  have hcrossNat : Xs * Yt = Xt * Ys :=
    TerminalMatching.crossDeterminant_eq_zero_iff.mp hzero
  have hfirst : a * Xs = b * Ys := by
    rw [← hXsg, ← hYsg]
    ring
  have hsecond : a * Xt = b * Yt := by
    apply Nat.eq_of_mul_eq_mul_right hg
    calc
      a * Xt * g = Xt * (a * g) := by ring
      _ = Xt * Ys := by rw [hYsg]
      _ = Xs * Yt := hcrossNat.symm
      _ = Yt * (b * g) := by rw [hXsg]; ring
      _ = b * Yt * g := by ring
  let h := pairChannelError x y a b
  have hcellS :
      (Affine.RationalChannelCode.channelVertexOffset is,
        Affine.RationalChannelCode.channelVertexOffset js) ∈
        channelCells L a b h := by
    rw [mem_channelCells]
    refine ⟨?_, ?_⟩
    · rw [mem_offsetBox]
      exact
        ⟨(by
            simpa only [mem_offsetInterval] using
              RationalChannelCode.channelVertexOffset_mem_offsetInterval is),
          (by
            simpa only [mem_offsetInterval] using
              RationalChannelCode.channelVertexOffset_mem_offsetInterval js)⟩
    · unfold OnChannel h pairChannelError
      dsimp only
      have hfirstZ :
          (a : ℤ) * (Xs : ℤ) =
            (b : ℤ) * (Ys : ℤ) := by
        exact_mod_cast hfirst
      dsimp only [Xs, Ys] at hfirstZ
      rw [RationalChannelCode.startCompleteVertexLabel_cast
          (show 1 ≤ x by omega) is,
        RationalChannelCode.startCompleteVertexLabel_cast
          (show 1 ≤ y by omega) js] at hfirstZ
      linarith
  have hcellT :
      (Affine.RationalChannelCode.channelVertexOffset it,
        Affine.RationalChannelCode.channelVertexOffset jt) ∈
        channelCells L a b h := by
    rw [mem_channelCells]
    refine ⟨?_, ?_⟩
    · rw [mem_offsetBox]
      exact
        ⟨(by
            simpa only [mem_offsetInterval] using
              RationalChannelCode.channelVertexOffset_mem_offsetInterval it),
          (by
            simpa only [mem_offsetInterval] using
              RationalChannelCode.channelVertexOffset_mem_offsetInterval jt)⟩
    · unfold OnChannel h pairChannelError
      dsimp only
      have hsecondZ :
          (a : ℤ) * (Xt : ℤ) =
            (b : ℤ) * (Yt : ℤ) := by
        exact_mod_cast hsecond
      dsimp only [Xt, Yt] at hsecondZ
      rw [RationalChannelCode.startCompleteVertexLabel_cast
          (show 1 ≤ x by omega) it,
        RationalChannelCode.startCompleteVertexLabel_cast
          (show 1 ≤ y by omega) jt] at hsecondZ
      linarith
  have hcellNe :
      (Affine.RationalChannelCode.channelVertexOffset is,
          Affine.RationalChannelCode.channelVertexOffset js) ≠
        (Affine.RationalChannelCode.channelVertexOffset it,
          Affine.RationalChannelCode.channelVertexOffset jt) := by
    intro hoffsets
    apply hcells
    apply Prod.ext
    · exact
        channelVertexOffset_injective
          (congrArg Prod.fst hoffsets)
    · exact
        channelVertexOffset_injective
          (congrArg Prod.snd hoffsets)
  have hcard :
      2 ≤ (channelCells L a b h).card := by
    exact Finset.one_lt_card.mpr
      ⟨_, hcellS, _, hcellT, hcellNe⟩
  refine ⟨a, b, ?_⟩
  exact
    channel_mem_reducedCandidates_of_two_units
      ha hb hab hA rfl hcard

/-- Canonical nonalignment makes every such distinct-cell determinant nonzero. -/
theorem crossDeterminant_ne_of_canonicalNonaligned
    {A x y L : ℕ}
    (hA : 1 ≤ A) (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hnonaligned : IsCanonicallyNonaligned A L x y)
    {is js it jt : Fin (L + 1)}
    (hcells : (is, js) ≠ (it, jt)) :
    TerminalMatching.crossDeterminant
      (startCompleteVertexLabel x L is)
      (startCompleteVertexLabel y L js)
      (startCompleteVertexLabel x L it)
      (startCompleteVertexLabel y L jt) ≠ 0 := by
  intro hzero
  obtain ⟨a, b, hab⟩ :=
    reducedCandidate_of_crossDeterminant_eq_zero
      hA hx hy hcells hzero
  unfold IsCanonicallyNonaligned at hnonaligned
  have hempty :
      reducedChannelCandidates x y (L + 1) ((L + 1) ^ A) = ∅ :=
    canonicalReducedCandidate?_eq_none_iff.mp hnonaligned
  rw [hempty] at hab
  simp at hab

/-- Distinct pair components have distinct canonical certificate cells. -/
theorem pairComponentCertificate_cell_injective
    {N M A L : ℕ} (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L) :
    Function.Injective
      (fun C : BoundedPairComponent A pair ↦
        ((pairComponentCertificate hN pair C).left,
          (pairComponentCertificate hN pair C).right)) := by
  intro C D hcell
  apply Subtype.ext
  have hleft :
      (pairComponentCertificate hN pair C).left =
        (pairComponentCertificate hN pair D).left :=
    congrArg Prod.fst hcell
  calc
    C.1 =
        (largePrimeGraph pair.1.1 pair.1.2 L).connectedComponentMk
          (Sum.inl (pairComponentCertificate hN pair C).left) :=
      (pairComponentCertificate hN pair C).left_component.symm
    _ =
        (largePrimeGraph pair.1.1 pair.1.2 L).connectedComponentMk
          (Sum.inl (pairComponentCertificate hN pair D).left) := by
      rw [hleft]
    _ = D.1 :=
      (pairComponentCertificate hN pair D).left_component

/--
For a rank-terminal pair, the determinant attached to any two distinct
canonical size-two components is nonzero.
-/
theorem pairComponents_crossDeterminant_ne
    {N M A L : ℕ} (hN : 2 ≤ N) (hA : 1 ≤ A)
    (K : ℝ) (pair : SeparatedBoundedRatioPair N M L)
    (hpair : pair ∈ boundedRankTerminalPairs N M A L hN K)
    {Cs Ct : BoundedPairComponent A pair}
    (hST : Cs ≠ Ct) :
    let certS := pairComponentCertificate hN pair Cs
    let certT := pairComponentCertificate hN pair Ct
    TerminalMatching.crossDeterminant
      (startCompleteVertexLabel pair.1.1 L certS.left)
      (startCompleteVertexLabel pair.1.2 L certS.right)
      (startCompleteVertexLabel pair.1.1 L certT.left)
      (startCompleteVertexLabel pair.1.2 L certT.right) ≠ 0 := by
  dsimp only
  have hxy := pair_coordinates_two_le hN pair
  have hcore := (mem_boundedRankTerminalPairs.mp hpair).1
  unfold boundedTerminalCoreConditions at hcore
  apply crossDeterminant_ne_of_canonicalNonaligned
    hA hxy.1 hxy.2 hcore.2.2.2.1
  exact
    fun hcell ↦ hST
      (pairComponentCertificate_cell_injective hN pair hcell)

end

end BoundedRatioTerminalFibers
end PaperC
