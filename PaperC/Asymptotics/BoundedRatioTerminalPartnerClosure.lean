import PaperC.Asymptotics.BoundedRatioTerminalFibers
import PaperC.Asymptotics.DependencyEdgesCritical
import PaperC.Arithmetic.SquarefreeSmoothCount
import PaperC.Combinatorics.AlignedRungeBridge

set_option maxHeartbeats 1800000

/-!
# Partner fibres for the bounded-ratio terminal population

This file connects the canonical terminal population to the concrete
generalized-Pell box in `TerminalPartnerPell`.

For a fixed first start `x`, two distinct canonical size-two components
produce four complete-boundary offsets.  After also fixing the two small
odd parts, every possible second start is sent injectively to one
`terminalPartnerWitnessBox`.  Thus the partner fibre is a finite union over

* four offsets in `Fin (L+1)`;
* two squarefree `(L+1)`-smooth small odd parts;
* one generalized-Pell fibre.

No new arithmetic assumption is introduced.  The public conditional APIs
take the registered `GeneralizedPellPolynomialBoxStatement` directly and
perform the conversion to `TerminalPartnerPolynomialBoxStatement`
internally, so the audit records the dependency.

The population treated here is the rank-defined
`boundedRankTerminalPairs`.  The later module
`BoundedRatioTerminalSummation` transports it exactly to the intrinsic
classifier using the proved source-scoped Lemma 9.10 equivalence.
Accordingly, this module supplies the finite rank-terminal closure used in
the complete discharge of the public Lemma 17.30 bridge.
-/

namespace PaperC
namespace BoundedRatioTerminalPartnerClosure

open scoped BigOperators
open Affine
open Affine.CanonicalRationalCode
open Affine.RationalChannelCode
open BalasubramanianShoreyInput
open BoundedRatioCanonicalTerminalPopulation
open BoundedRatioTerminalClosure
open BoundedRatioTerminalFibers
open DefectivePredicate
open LargeOddKernel
open LargePrimeGraph
open PropositionSixteenOne
open SquarefreeSmoothCount

noncomputable section

/-! ## The four canonical component offsets -/

/-- The two left and two right offsets selected from two components. -/
structure TerminalOffsetQuadruple (L : ℕ) where
  leftFirst : Fin (L + 1)
  rightFirst : Fin (L + 1)
  leftSecond : Fin (L + 1)
  rightSecond : Fin (L + 1)
deriving DecidableEq, Fintype

/-- There are exactly `(L+1)^4` offset quadruples. -/
@[simp]
theorem card_terminalOffsetQuadruple (L : ℕ) :
    Fintype.card (TerminalOffsetQuadruple L) = (L + 1) ^ 4 := by
  let e : TerminalOffsetQuadruple L ≃
      (Fin (L + 1) ×
        (Fin (L + 1) × (Fin (L + 1) × Fin (L + 1)))) :=
    { toFun := fun q ↦
        (q.leftFirst, q.rightFirst, q.leftSecond, q.rightSecond)
      invFun := fun q ↦
        ⟨q.1, q.2.1, q.2.2.1, q.2.2.2⟩
      left_inv := by intro q; cases q; rfl
      right_inv := by intro q; cases q; rfl }
  rw [Fintype.card_congr e]
  simp only [Fintype.card_prod, Fintype.card_fin]
  ring

/-- The offset quadruple canonically carried by two components. -/
noncomputable def componentOffsetQuadruple
    {N M A L : ℕ} (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L)
    (Cs Ct : BoundedPairComponent A pair) :
    TerminalOffsetQuadruple L where
  leftFirst := (pairComponentCertificate hN pair Cs).left
  rightFirst := (pairComponentCertificate hN pair Cs).right
  leftSecond := (pairComponentCertificate hN pair Ct).left
  rightSecond := (pairComponentCertificate hN pair Ct).right

/-- A canonical component is already determined by its left endpoint. -/
theorem pairComponentCertificate_left_injective
    {N M A L : ℕ} (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L) :
    Function.Injective
      (fun C : BoundedPairComponent A pair ↦
        (pairComponentCertificate hN pair C).left) := by
  intro C D hleft
  change
    (pairComponentCertificate hN pair C).left =
      (pairComponentCertificate hN pair D).left at hleft
  apply Subtype.ext
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

/-- A canonical component is also determined by its right endpoint. -/
theorem pairComponentCertificate_right_injective
    {N M A L : ℕ} (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L) :
    Function.Injective
      (fun C : BoundedPairComponent A pair ↦
        (pairComponentCertificate hN pair C).right) := by
  intro C D hright
  change
    (pairComponentCertificate hN pair C).right =
      (pairComponentCertificate hN pair D).right at hright
  apply Subtype.ext
  calc
    C.1 =
        (largePrimeGraph pair.1.1 pair.1.2 L).connectedComponentMk
          (Sum.inr (pairComponentCertificate hN pair C).right) :=
      (pairComponentCertificate hN pair C).right_component.symm
    _ =
        (largePrimeGraph pair.1.1 pair.1.2 L).connectedComponentMk
          (Sum.inr (pairComponentCertificate hN pair D).right) := by
      rw [hright]
    _ = D.1 :=
      (pairComponentCertificate hN pair D).right_component

/-- Distinct components give distinct offsets in both blocks. -/
theorem componentOffsetQuadruple_distinct
    {N M A L : ℕ} (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L)
    {Cs Ct : BoundedPairComponent A pair}
    (hST : Cs ≠ Ct) :
    (componentOffsetQuadruple hN pair Cs Ct).leftFirst ≠
        (componentOffsetQuadruple hN pair Cs Ct).leftSecond ∧
      (componentOffsetQuadruple hN pair Cs Ct).rightFirst ≠
        (componentOffsetQuadruple hN pair Cs Ct).rightSecond := by
  exact
    ⟨fun h ↦ hST
        (pairComponentCertificate_left_injective hN pair h),
      fun h ↦ hST
        (pairComponentCertificate_right_injective hN pair h)⟩

/-! ## Fixed-parameter partner fibres -/

/-- The left labels, which depend only on the fixed first start and code. -/
def codeLeftFirstLabel
    {L : ℕ} (x : ℕ) (q : TerminalOffsetQuadruple L) : ℕ :=
  startCompleteVertexLabel x L q.leftFirst

def codeLeftSecondLabel
    {L : ℕ} (x : ℕ) (q : TerminalOffsetQuadruple L) : ℕ :=
  startCompleteVertexLabel x L q.leftSecond

/-- The two labels in the varying partner block. -/
def codeRightFirstLabel
    {L : ℕ} (y : ℕ) (q : TerminalOffsetQuadruple L) : ℕ :=
  startCompleteVertexLabel y L q.rightFirst

def codeRightSecondLabel
    {L : ℕ} (y : ℕ) (q : TerminalOffsetQuadruple L) : ℕ :=
  startCompleteVertexLabel y L q.rightSecond

/-- The genuine partner witness associated with a second start. -/
noncomputable def codePartnerWitness
    {L : ℕ} (y : ℕ) (q : TerminalOffsetQuadruple L) :
    TerminalPartnerPell.TerminalPartnerWitness :=
  TerminalPartnerPell.canonicalPartnerWitness
    (codeRightFirstLabel y q)
    (codeRightSecondLabel y q)
    (y : ℤ)

/--
The part of `T_K` with fixed first start, four component offsets, and two
small odd parts.
-/
noncomputable def terminalParameterFiber
    (N M A L : ℕ) (hN : 2 ≤ N) (K : ℝ)
    (x : ℕ) (q : TerminalOffsetQuadruple L) (a b : ℕ) :
    Finset (SeparatedBoundedRatioPair N M L) := by
  classical
  exact
    (boundedRankTerminalPairs N M A L hN K).filter fun pair ↦
      pair.1.1 = x ∧
      smallOddPart (L + 1)
          (codeRightFirstLabel pair.1.2 q) = a ∧
      smallOddPart (L + 1)
          (codeRightSecondLabel pair.1.2 q) = b ∧
      ∃ Cs Ct : BoundedPairComponent A pair,
        Cs ≠ Ct ∧ componentOffsetQuadruple hN pair Cs Ct = q

@[simp]
theorem mem_terminalParameterFiber
    {N M A L : ℕ} {hN : 2 ≤ N} {K : ℝ}
    {x : ℕ} {q : TerminalOffsetQuadruple L} {a b : ℕ}
    {pair : SeparatedBoundedRatioPair N M L} :
    pair ∈ terminalParameterFiber N M A L hN K x q a b ↔
      pair ∈ boundedRankTerminalPairs N M A L hN K ∧
      pair.1.1 = x ∧
      smallOddPart (L + 1)
          (codeRightFirstLabel pair.1.2 q) = a ∧
      smallOddPart (L + 1)
          (codeRightSecondLabel pair.1.2 q) = b ∧
      ∃ Cs Ct : BoundedPairComponent A pair,
        Cs ≠ Ct ∧ componentOffsetQuadruple hN pair Cs Ct = q := by
  simp [terminalParameterFiber, and_assoc]

/-- With the first start fixed, the partner witness remembers the pair. -/
theorem codePartnerWitness_injective_on_first
    {N M L : ℕ} {x : ℕ} (q : TerminalOffsetQuadruple L)
    {u v : SeparatedBoundedRatioPair N M L}
    (hu : u.1.1 = x) (hv : v.1.1 = x)
    (h :
      codePartnerWitness u.1.2 q =
        codePartnerWitness v.1.2 q) :
    u = v := by
  apply Subtype.ext
  apply Prod.ext
  · exact hu.trans hv.symm
  · have hpartner :
        (u.1.2 : ℤ) = (v.1.2 : ℤ) :=
      congrArg TerminalPartnerPell.TerminalPartnerWitness.partner h
    exact_mod_cast hpartner

/-!
The next theorem is the central population-specific map.  It uses the
component package to identify the two right kernels with the two fixed
left kernels, and then invokes the already formalized canonical
factorization.
-/
theorem codePartnerWitness_mem_box
    {κ₀ N M A L : ℕ} (hN : 2 ≤ N)
    (hMκ : M ≤ κ₀ * N) (hL : L ≤ N) (K : ℝ)
    {x : ℕ} {q : TerminalOffsetQuadruple L} {a b : ℕ}
    {pair : SeparatedBoundedRatioPair N M L}
    (hpair :
      pair ∈ terminalParameterFiber N M A L hN K x q a b) :
    TerminalPartnerPell.terminalPartnerWitnessBox
      (largeOddKernel (L + 1) (codeLeftFirstLabel x q))
      (largeOddKernel (L + 1) (codeLeftSecondLabel x q))
      a b
      (channelVertexOffset q.rightFirst)
      (channelVertexOffset q.rightSecond)
      (terminalLabelCutoff κ₀ N)
      (codePartnerWitness pair.1.2 q) := by
  rcases mem_terminalParameterFiber.mp hpair with
    ⟨hterminal, hx, ha, hb, Cs, Ct, hST, hcode⟩
  have hpackage :=
    distinct_pairComponents_kernel_package
      hN pair (Cs := Cs) (Ct := Ct) hST
  dsimp only at hpackage
  have hleftFirst :
      (pairComponentCertificate hN pair Cs).left = q.leftFirst :=
    congrArg TerminalOffsetQuadruple.leftFirst hcode
  have hrightFirst :
      (pairComponentCertificate hN pair Cs).right = q.rightFirst :=
    congrArg TerminalOffsetQuadruple.rightFirst hcode
  have hleftSecond :
      (pairComponentCertificate hN pair Ct).left = q.leftSecond :=
    congrArg TerminalOffsetQuadruple.leftSecond hcode
  have hrightSecond :
      (pairComponentCertificate hN pair Ct).right = q.rightSecond :=
    congrArg TerminalOffsetQuadruple.rightSecond hcode
  have hrightFirstLabel :
      codeRightFirstLabel pair.1.2 q =
        startCompleteVertexLabel pair.1.2 L
          (pairComponentCertificate hN pair Cs).right := by
    simp only [codeRightFirstLabel, hrightFirst]
  have hleftFirstLabel :
      startCompleteVertexLabel pair.1.1 L
          (pairComponentCertificate hN pair Cs).left =
        codeLeftFirstLabel x q := by
    rw [hleftFirst]
    exact
      congrArg (fun z ↦ startCompleteVertexLabel z L q.leftFirst) hx
  have hrightSecondLabel :
      codeRightSecondLabel pair.1.2 q =
        startCompleteVertexLabel pair.1.2 L
          (pairComponentCertificate hN pair Ct).right := by
    simp only [codeRightSecondLabel, hrightSecond]
  have hleftSecondLabel :
      startCompleteVertexLabel pair.1.1 L
          (pairComponentCertificate hN pair Ct).left =
        codeLeftSecondLabel x q := by
    rw [hleftSecond]
    exact
      congrArg (fun z ↦ startCompleteVertexLabel z L q.leftSecond) hx
  have hR :
      largeOddKernel (L + 1) (codeRightFirstLabel pair.1.2 q) =
        largeOddKernel (L + 1) (codeLeftFirstLabel x q) := by
    calc
      largeOddKernel (L + 1) (codeRightFirstLabel pair.1.2 q) =
          largeOddKernel (L + 1)
            (startCompleteVertexLabel pair.1.2 L
              (pairComponentCertificate hN pair Cs).right) := by
        exact congrArg (largeOddKernel (L + 1)) hrightFirstLabel
      _ =
          largeOddKernel (L + 1)
            (startCompleteVertexLabel pair.1.1 L
              (pairComponentCertificate hN pair Cs).left) :=
        hpackage.1.symm
      _ =
          largeOddKernel (L + 1) (codeLeftFirstLabel x q) := by
        exact congrArg (largeOddKernel (L + 1)) hleftFirstLabel
  have hS :
      largeOddKernel (L + 1) (codeRightSecondLabel pair.1.2 q) =
        largeOddKernel (L + 1) (codeLeftSecondLabel x q) := by
    calc
      largeOddKernel (L + 1) (codeRightSecondLabel pair.1.2 q) =
          largeOddKernel (L + 1)
            (startCompleteVertexLabel pair.1.2 L
              (pairComponentCertificate hN pair Ct).right) := by
        exact congrArg (largeOddKernel (L + 1)) hrightSecondLabel
      _ =
          largeOddKernel (L + 1)
            (startCompleteVertexLabel pair.1.1 L
              (pairComponentCertificate hN pair Ct).left) :=
        hpackage.2.1.symm
      _ =
          largeOddKernel (L + 1) (codeLeftSecondLabel x q) := by
        exact congrArg (largeOddKernel (L + 1)) hleftSecondLabel
  have hxy := pair_coordinates_two_le hN pair
  have hm :
      codeRightFirstLabel pair.1.2 q ≠ 0 :=
    Nat.ne_of_gt
      (RationalChannelCode.startCompleteVertexLabel_pos
        hxy.2 q.rightFirst)
  have hn :
      codeRightSecondLabel pair.1.2 q ≠ 0 :=
    Nat.ne_of_gt
      (RationalChannelCode.startCompleteVertexLabel_pos
        hxy.2 q.rightSecond)
  have hyBlock :
      pair.1.2 ∈ boundedRatioBlock N M :=
    (mem_separatedBoundedRatioPairs.mp pair.2).2.1
  have hmCutoff :
      codeRightFirstLabel pair.1.2 q ≤ terminalLabelCutoff κ₀ N :=
    startCompleteVertexLabel_le_terminalLabelCutoff
      hN hMκ hL hyBlock q.rightFirst
  have hnCutoff :
      codeRightSecondLabel pair.1.2 q ≤ terminalLabelCutoff κ₀ N :=
    startCompleteVertexLabel_le_terminalLabelCutoff
      hN hMκ hL hyBlock q.rightSecond
  have hz :
      canonicalSquarePart (codeRightFirstLabel pair.1.2 q) ≤
        terminalLabelCutoff κ₀ N :=
    (TerminalPartnerPell.canonicalSquarePart_le_sqrt
      (B := L + 1) hm).trans
      ((Nat.sqrt_le_self _).trans hmCutoff)
  have hw :
      canonicalSquarePart (codeRightSecondLabel pair.1.2 q) ≤
        terminalLabelCutoff κ₀ N :=
    (TerminalPartnerPell.canonicalSquarePart_le_sqrt
      (B := L + 1) hn).trans
      ((Nat.sqrt_le_self _).trans hnCutoff)
  have hyOne : 1 ≤ pair.1.2 := by omega
  unfold codePartnerWitness
  simpa only [ha, hb] using
    (TerminalPartnerPell.canonical_decompositions_give_partner_box
      hm hn
      (RationalChannelCode.startCompleteVertexLabel_cast
        hyOne q.rightFirst).symm
      (RationalChannelCode.startCompleteVertexLabel_cast
        hyOne q.rightSecond).symm
      hR hS hz hw)

/-- A fixed parameter fibre injects into its single Pell box. -/
theorem card_terminalParameterFiber_cast_le
    {κ₀ N M A L : ℕ} (hN : 2 ≤ N)
    (hMκ : M ≤ κ₀ * N) (hL : L ≤ N) (K : ℝ)
    {x : ℕ} {q : TerminalOffsetQuadruple L} {a b : ℕ}
    {bound : ℝ}
    (hbox :
      PellInput.HasAtMostSolutionsReal
        (TerminalPartnerPell.terminalPartnerWitnessBox
          (largeOddKernel (L + 1) (codeLeftFirstLabel x q))
          (largeOddKernel (L + 1) (codeLeftSecondLabel x q))
          a b
          (channelVertexOffset q.rightFirst)
          (channelVertexOffset q.rightSecond)
          (terminalLabelCutoff κ₀ N))
        bound) :
    ((terminalParameterFiber
        N M A L hN K x q a b).card : ℝ) ≤ bound := by
  classical
  let population :=
    terminalParameterFiber N M A L hN K x q a b
  let f : SeparatedBoundedRatioPair N M L →
      TerminalPartnerPell.TerminalPartnerWitness :=
    fun pair ↦ codePartnerWitness pair.1.2 q
  have himage :
      ∀ w ∈ population.image f,
        TerminalPartnerPell.terminalPartnerWitnessBox
          (largeOddKernel (L + 1) (codeLeftFirstLabel x q))
          (largeOddKernel (L + 1) (codeLeftSecondLabel x q))
          a b
          (channelVertexOffset q.rightFirst)
          (channelVertexOffset q.rightSecond)
          (terminalLabelCutoff κ₀ N) w := by
    intro w hw
    obtain ⟨pair, hpair, rfl⟩ := Finset.mem_image.mp hw
    exact codePartnerWitness_mem_box
      hN hMκ hL K hpair
  have hcount := hbox (population.image f) himage
  have hcard :
      (population.image f).card = population.card := by
    rw [Finset.card_image_iff]
    intro u hu v hv huv
    exact
      codePartnerWitness_injective_on_first q
        (mem_terminalParameterFiber.mp hu).2.1
        (mem_terminalParameterFiber.mp hv).2.1 huv
  simpa only [population, hcard] using hcount

/-! ## The finite union over offsets and smooth parts -/

/-- The relevant small odd parts up to the common label cutoff. -/
noncomputable def terminalSmallParts
    (κ₀ N L : ℕ) : Finset ℕ :=
  squarefreeSmoothUpTo (L + 1) (terminalLabelCutoff κ₀ N)

/-- Every canonical small odd part of a positive bounded label occurs here. -/
theorem smallOddPart_mem_terminalSmallParts
    {κ₀ N L n : ℕ} (hn : 0 < n)
    (hnCutoff : n ≤ terminalLabelCutoff κ₀ N) :
    smallOddPart (L + 1) n ∈ terminalSmallParts κ₀ N L := by
  rw [terminalSmallParts, mem_squarefreeSmoothUpTo]
  refine
    ⟨Nat.one_le_iff_ne_zero.mpr (smallOddPart_ne_zero (L + 1) n),
      ?_, smallOddPart_squarefree (L + 1) n, ?_⟩
  · exact
      (Nat.le_of_dvd hn (smallOddPart_dvd (L + 1) n)).trans
        hnCutoff
  · intro p hp
    rw [primeFactors_smallOddPart] at hp
    exact
      (prime_and_small_of_mem_smallOddPrimeSupport hp).2

/--
The union of all fixed-code, fixed-small-part fibres for one first start.
-/
noncomputable def terminalParameterUnion
    (κ₀ N M A L : ℕ) (hN : 2 ≤ N) (K : ℝ) (x : ℕ) :
    Finset (SeparatedBoundedRatioPair N M L) := by
  classical
  exact
    (Finset.univ : Finset (TerminalOffsetQuadruple L)).biUnion fun q ↦
      (terminalSmallParts κ₀ N L).biUnion fun a ↦
        (terminalSmallParts κ₀ N L).biUnion fun b ↦
          terminalParameterFiber N M A L hN K x q a b

/-- The terminal partner fibre restricted to pairs with two size-two components. -/
noncomputable def twoComponentTerminalPartnerFiber
    (N M A L : ℕ) (hN : 2 ≤ N) (K : ℝ) (x : ℕ) :
    Finset (SeparatedBoundedRatioPair N M L) := by
  classical
  exact
    (boundedRankTerminalPairs N M A L hN K).filter fun pair ↦
      pair.1.1 = x ∧
        2 ≤ (boundedCanonicalPairComponents A pair).card

/-- The complete partner fibre of the literal terminal population. -/
noncomputable def boundedRankTerminalPartnerFiber
    (N M A L : ℕ) (hN : 2 ≤ N) (K : ℝ) (x : ℕ) :
    Finset (SeparatedBoundedRatioPair N M L) :=
  (boundedRankTerminalPairs N M A L hN K).filter fun pair ↦
    pair.1.1 = x

@[simp]
theorem mem_twoComponentTerminalPartnerFiber
    {N M A L : ℕ} {hN : 2 ≤ N} {K : ℝ} {x : ℕ}
    {pair : SeparatedBoundedRatioPair N M L} :
    pair ∈ twoComponentTerminalPartnerFiber N M A L hN K x ↔
      pair ∈ boundedRankTerminalPairs N M A L hN K ∧
      pair.1.1 = x ∧
      2 ≤ (boundedCanonicalPairComponents A pair).card := by
  simp [twoComponentTerminalPartnerFiber, and_assoc]

@[simp]
theorem mem_boundedRankTerminalPartnerFiber
    {N M A L : ℕ} {hN : 2 ≤ N} {K : ℝ} {x : ℕ}
    {pair : SeparatedBoundedRatioPair N M L} :
    pair ∈ boundedRankTerminalPartnerFiber N M A L hN K x ↔
      pair ∈ boundedRankTerminalPairs N M A L hN K ∧
      pair.1.1 = x := by
  simp [boundedRankTerminalPartnerFiber]

/--
As soon as `B-3R_K(B)≥2`, every literal terminal pair has two size-two
components, so the restricted and complete partner fibres coincide.
-/
theorem twoComponentTerminalPartnerFiber_eq
    {N M A L : ℕ} (hN : 2 ≤ N) (K : ℝ) (x : ℕ)
    (htwo : 2 ≤ L + 1 - 3 * terminalRankBudget K L) :
    twoComponentTerminalPartnerFiber N M A L hN K x =
      boundedRankTerminalPartnerFiber N M A L hN K x := by
  ext pair
  rw [mem_twoComponentTerminalPartnerFiber,
    mem_boundedRankTerminalPartnerFiber]
  constructor
  · rintro ⟨hpair, hx, _hcomponents⟩
    exact ⟨hpair, hx⟩
  · rintro ⟨hpair, hx⟩
    have hterminal := mem_boundedRankTerminalPairs.mp hpair
    have hslack :
        boundedTerminalSlack A pair ≤ terminalRankBudget K L := by
      omega
    have hcomponents :=
      (bounded_terminal_component_count
        (A := A) hN pair).2
    exact ⟨hpair, hx, by omega⟩

/-- Every terminal pair having two canonical size-two components is covered. -/
theorem twoComponentTerminalPartnerFiber_subset_parameterUnion
    {κ₀ N M A L : ℕ} (hN : 2 ≤ N)
    (hMκ : M ≤ κ₀ * N) (hL : L ≤ N)
    (K : ℝ) (x : ℕ) :
    twoComponentTerminalPartnerFiber N M A L hN K x ⊆
      terminalParameterUnion κ₀ N M A L hN K x := by
  classical
  intro pair hpair
  rcases mem_twoComponentTerminalPartnerFiber.mp hpair with
    ⟨hterminal, hx, hcard⟩
  obtain ⟨CsVal, hCs, CtVal, hCt, hSTVal⟩ :=
    Finset.one_lt_card.mp hcard
  let Cs : BoundedPairComponent A pair := ⟨CsVal, hCs⟩
  let Ct : BoundedPairComponent A pair := ⟨CtVal, hCt⟩
  have hST : Cs ≠ Ct := by
    intro h
    exact hSTVal (congrArg Subtype.val h)
  let q := componentOffsetQuadruple hN pair Cs Ct
  let a :=
    smallOddPart (L + 1)
      (codeRightFirstLabel pair.1.2 q)
  let b :=
    smallOddPart (L + 1)
      (codeRightSecondLabel pair.1.2 q)
  have hxy := pair_coordinates_two_le hN pair
  have hyBlock :
      pair.1.2 ∈ boundedRatioBlock N M :=
    (mem_separatedBoundedRatioPairs.mp pair.2).2.1
  have hmPos :
      0 < codeRightFirstLabel pair.1.2 q :=
    RationalChannelCode.startCompleteVertexLabel_pos
      hxy.2 q.rightFirst
  have hnPos :
      0 < codeRightSecondLabel pair.1.2 q :=
    RationalChannelCode.startCompleteVertexLabel_pos
      hxy.2 q.rightSecond
  have hmCutoff :
      codeRightFirstLabel pair.1.2 q ≤ terminalLabelCutoff κ₀ N :=
    startCompleteVertexLabel_le_terminalLabelCutoff
      hN hMκ hL hyBlock q.rightFirst
  have hnCutoff :
      codeRightSecondLabel pair.1.2 q ≤ terminalLabelCutoff κ₀ N :=
    startCompleteVertexLabel_le_terminalLabelCutoff
      hN hMκ hL hyBlock q.rightSecond
  have ha : a ∈ terminalSmallParts κ₀ N L :=
    smallOddPart_mem_terminalSmallParts hmPos hmCutoff
  have hb : b ∈ terminalSmallParts κ₀ N L :=
    smallOddPart_mem_terminalSmallParts hnPos hnCutoff
  unfold terminalParameterUnion
  rw [Finset.mem_biUnion]
  refine ⟨q, Finset.mem_univ q, ?_⟩
  rw [Finset.mem_biUnion]
  refine ⟨a, ha, ?_⟩
  rw [Finset.mem_biUnion]
  refine ⟨b, hb, ?_⟩
  rw [mem_terminalParameterFiber]
  exact
    ⟨hterminal, hx, rfl, rfl, Cs, Ct, hST, rfl⟩

/--
Three finite-union bounds give the precise combinatorial factor
`(L+1)^4 * (#small parts)^2`.
-/
theorem card_terminalParameterUnion_cast_le
    {κ₀ N M A L : ℕ} {hN : 2 ≤ N} {K : ℝ} {x : ℕ}
    {bound : ℝ}
    (hcount :
      ∀ q : TerminalOffsetQuadruple L,
        ∀ a ∈ terminalSmallParts κ₀ N L,
        ∀ b ∈ terminalSmallParts κ₀ N L,
          ((terminalParameterFiber
              N M A L hN K x q a b).card : ℝ) ≤ bound) :
    ((terminalParameterUnion κ₀ N M A L hN K x).card : ℝ) ≤
      ((L + 1 : ℕ) : ℝ) ^ 4 *
        ((terminalSmallParts κ₀ N L).card : ℝ) ^ 2 *
        bound := by
  classical
  let D := terminalSmallParts κ₀ N L
  let Q := (Finset.univ : Finset (TerminalOffsetQuadruple L))
  have hb :
      ∀ q ∈ Q, ∀ a ∈ D,
        (((D.biUnion fun b ↦
            terminalParameterFiber
              N M A L hN K x q a b).card : ℕ) : ℝ) ≤
          (D.card : ℝ) * bound := by
    intro q hq a ha
    calc
      (((D.biUnion fun b ↦
          terminalParameterFiber
            N M A L hN K x q a b).card : ℕ) : ℝ) ≤
          ∑ b ∈ D,
            ((terminalParameterFiber
              N M A L hN K x q a b).card : ℝ) := by
        rw [← Nat.cast_sum]
        exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _b ∈ D, bound :=
        Finset.sum_le_sum fun b hbD ↦
          hcount q a (by simpa only [D] using ha)
            b (by simpa only [D] using hbD)
      _ = (D.card : ℝ) * bound := by simp
  have ha :
      ∀ q ∈ Q,
        (((D.biUnion fun a ↦
            D.biUnion fun b ↦
              terminalParameterFiber
                N M A L hN K x q a b).card : ℕ) : ℝ) ≤
          (D.card : ℝ) ^ 2 * bound := by
    intro q hq
    calc
      (((D.biUnion fun a ↦
          D.biUnion fun b ↦
            terminalParameterFiber
              N M A L hN K x q a b).card : ℕ) : ℝ) ≤
          ∑ a ∈ D,
            (((D.biUnion fun b ↦
              terminalParameterFiber
                N M A L hN K x q a b).card : ℕ) : ℝ) := by
        rw [← Nat.cast_sum]
        exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _a ∈ D, (D.card : ℝ) * bound :=
        Finset.sum_le_sum fun a haD ↦ hb q hq a haD
      _ = (D.card : ℝ) ^ 2 * bound := by
        simp
        ring
  calc
    ((terminalParameterUnion κ₀ N M A L hN K x).card : ℝ) ≤
        ∑ q ∈ Q,
          (((D.biUnion fun a ↦
            D.biUnion fun b ↦
              terminalParameterFiber
                N M A L hN K x q a b).card : ℕ) : ℝ) := by
      unfold terminalParameterUnion
      dsimp only [Q, D]
      rw [← Nat.cast_sum]
      exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _q ∈ Q, (D.card : ℝ) ^ 2 * bound :=
      Finset.sum_le_sum fun q hq ↦ ha q hq
    _ = ((L + 1 : ℕ) : ℝ) ^ 4 *
          (D.card : ℝ) ^ 2 * bound := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [show Q.card = (L + 1) ^ 4 by
        simp only [Q, Finset.card_univ,
          card_terminalOffsetQuadruple]]
      push_cast
      ring
    _ = ((L + 1 : ℕ) : ℝ) ^ 4 *
          ((terminalSmallParts κ₀ N L).card : ℝ) ^ 2 *
          bound := by
      simp only [D]

/-- The preceding union bound applies to the actual two-component fibre. -/
theorem card_twoComponentTerminalPartnerFiber_cast_le
    {κ₀ N M A L : ℕ} {hN : 2 ≤ N} {K : ℝ} {x : ℕ}
    {bound : ℝ}
    (hMκ : M ≤ κ₀ * N) (hL : L ≤ N)
    (hcount :
      ∀ q : TerminalOffsetQuadruple L,
        ∀ a ∈ terminalSmallParts κ₀ N L,
        ∀ b ∈ terminalSmallParts κ₀ N L,
          ((terminalParameterFiber
              N M A L hN K x q a b).card : ℝ) ≤ bound) :
    ((twoComponentTerminalPartnerFiber
        N M A L hN K x).card : ℝ) ≤
      ((L + 1 : ℕ) : ℝ) ^ 4 *
        ((terminalSmallParts κ₀ N L).card : ℝ) ^ 2 *
        bound := by
  calc
    ((twoComponentTerminalPartnerFiber
        N M A L hN K x).card : ℝ) ≤
        ((terminalParameterUnion
          κ₀ N M A L hN K x).card : ℝ) := by
      exact_mod_cast
        Finset.card_le_card
          (twoComponentTerminalPartnerFiber_subset_parameterUnion
            hN hMκ hL K x)
    _ ≤
        ((L + 1 : ℕ) : ℝ) ^ 4 *
          ((terminalSmallParts κ₀ N L).card : ℝ) ^ 2 *
          bound :=
      card_terminalParameterUnion_cast_le hcount

/-! ## Specialization of the registered generalized-Pell input -/

/-- The difference of two boundary offsets fits in the common cutoff. -/
theorem codeRightOffsetDifference_natAbs_le_cutoff
    {κ₀ N L : ℕ} (hN : 2 ≤ N) (hκ₀ : 2 ≤ κ₀)
    (hL : L ≤ N) (q : TerminalOffsetQuadruple L) :
    (channelVertexOffset q.rightFirst -
        channelVertexOffset q.rightSecond).natAbs ≤
      terminalLabelCutoff κ₀ N := by
  have hfirstInt :=
    AlignedRungeBridge.abs_channelVertexOffset_le q.rightFirst
  have hsecondInt :=
    AlignedRungeBridge.abs_channelVertexOffset_le q.rightSecond
  rw [Int.abs_eq_natAbs] at hfirstInt hsecondInt
  have hfirst :
      (channelVertexOffset q.rightFirst).natAbs ≤ L + 1 := by
    exact_mod_cast hfirstInt
  have hsecond :
      (channelVertexOffset q.rightSecond).natAbs ≤ L + 1 := by
    exact_mod_cast hsecondInt
  calc
    (channelVertexOffset q.rightFirst -
        channelVertexOffset q.rightSecond).natAbs ≤
        (channelVertexOffset q.rightFirst).natAbs +
          (channelVertexOffset q.rightSecond).natAbs :=
      Int.natAbs_sub_le _ _
    _ ≤ 2 * (L + 1) := by omega
    _ ≤ 3 * N := by omega
    _ ≤ (κ₀ + 1) * N := by
      exact Nat.mul_le_mul_right N (by omega)
    _ = terminalLabelCutoff κ₀ N := by
      rfl

/--
The generalized-Pell polynomial box bounds every fixed terminal parameter
fibre.  The ambient height is the endpoint-independent cutoff
`(κ₀+1)N`; exponent one already suffices.
-/
theorem terminalParameterFibers_polynomialBox
    (hPell :
      PellInput.GeneralizedPellPolynomialBoxStatement) :
    ∃ c : ℝ, 0 ≤ c ∧
      ∃ X₀ : ℕ, ∀ X ≥ X₀,
        ∀ (κ₀ N M A L : ℕ) (hN : 2 ≤ N),
          2 ≤ κ₀ →
          M ≤ κ₀ * N →
          L ≤ N →
          terminalLabelCutoff κ₀ N = X →
          ∀ (K : ℝ) (x : ℕ)
            (q : TerminalOffsetQuadruple L) (a b : ℕ),
            ((terminalParameterFiber
                N M A L hN K x q a b).card : ℝ) ≤
              PellInput.expLogLogBound c X := by
  have hPartner :=
    TerminalPartnerPell.terminalPartnerPolynomialBox_of_generalizedPell
      hPell
  obtain ⟨c, hc, X₀, hX₀⟩ := hPartner 1 (by omega)
  refine ⟨c, hc, X₀, ?_⟩
  intro X hX κ₀ N M A L hN hκ₀ hMκ hL hcutoff
    K x q a b
  let fibre :=
    terminalParameterFiber N M A L hN K x q a b
  by_cases hempty : fibre = ∅
  · have hnonneg :
        0 ≤ PellInput.expLogLogBound c X := by
      unfold PellInput.expLogLogBound
      positivity
    simpa only [fibre, hempty, Finset.card_empty, Nat.cast_zero] using
      hnonneg
  · obtain ⟨pair, hpair⟩ :=
      Finset.nonempty_iff_ne_empty.mpr hempty
    change pair ∈
      terminalParameterFiber N M A L hN K x q a b at hpair
    rcases mem_terminalParameterFiber.mp hpair with
      ⟨_hterminal, hx, ha, hb, Cs, Ct, hST, hcode⟩
    have hpackage :=
      distinct_pairComponents_kernel_package
        hN pair (Cs := Cs) (Ct := Ct) hST
    dsimp only at hpackage
    rcases hpackage with
      ⟨hkFirst, hkSecond, hkFirstGt, hkSecondGt,
        hkCoprime, _hdiv⟩
    have hleftFirst :
        (pairComponentCertificate hN pair Cs).left = q.leftFirst :=
      congrArg TerminalOffsetQuadruple.leftFirst hcode
    have hrightFirst :
        (pairComponentCertificate hN pair Cs).right = q.rightFirst :=
      congrArg TerminalOffsetQuadruple.rightFirst hcode
    have hleftSecond :
        (pairComponentCertificate hN pair Ct).left = q.leftSecond :=
      congrArg TerminalOffsetQuadruple.leftSecond hcode
    have hrightSecond :
        (pairComponentCertificate hN pair Ct).right = q.rightSecond :=
      congrArg TerminalOffsetQuadruple.rightSecond hcode
    have hrightFirstLabel :
        codeRightFirstLabel pair.1.2 q =
          startCompleteVertexLabel pair.1.2 L
            (pairComponentCertificate hN pair Cs).right := by
      simp only [codeRightFirstLabel, hrightFirst]
    have hleftFirstLabel :
        startCompleteVertexLabel pair.1.1 L
            (pairComponentCertificate hN pair Cs).left =
          codeLeftFirstLabel x q := by
      rw [hleftFirst]
      exact
        congrArg (fun z ↦ startCompleteVertexLabel z L q.leftFirst) hx
    have hrightSecondLabel :
        codeRightSecondLabel pair.1.2 q =
          startCompleteVertexLabel pair.1.2 L
            (pairComponentCertificate hN pair Ct).right := by
      simp only [codeRightSecondLabel, hrightSecond]
    have hleftSecondLabel :
        startCompleteVertexLabel pair.1.1 L
            (pairComponentCertificate hN pair Ct).left =
          codeLeftSecondLabel x q := by
      rw [hleftSecond]
      exact
        congrArg (fun z ↦ startCompleteVertexLabel z L q.leftSecond) hx
    have hR :
        largeOddKernel (L + 1)
            (codeRightFirstLabel pair.1.2 q) =
          largeOddKernel (L + 1) (codeLeftFirstLabel x q) := by
      calc
        largeOddKernel (L + 1)
            (codeRightFirstLabel pair.1.2 q) =
            largeOddKernel (L + 1)
              (startCompleteVertexLabel pair.1.2 L
                (pairComponentCertificate hN pair Cs).right) := by
          exact congrArg (largeOddKernel (L + 1)) hrightFirstLabel
        _ =
            largeOddKernel (L + 1)
              (startCompleteVertexLabel pair.1.1 L
                (pairComponentCertificate hN pair Cs).left) :=
          hkFirst.symm
        _ =
            largeOddKernel (L + 1) (codeLeftFirstLabel x q) := by
          exact congrArg (largeOddKernel (L + 1)) hleftFirstLabel
    have hS :
        largeOddKernel (L + 1)
            (codeRightSecondLabel pair.1.2 q) =
          largeOddKernel (L + 1) (codeLeftSecondLabel x q) := by
      calc
        largeOddKernel (L + 1)
            (codeRightSecondLabel pair.1.2 q) =
            largeOddKernel (L + 1)
              (startCompleteVertexLabel pair.1.2 L
                (pairComponentCertificate hN pair Ct).right) := by
          exact congrArg (largeOddKernel (L + 1)) hrightSecondLabel
        _ =
            largeOddKernel (L + 1)
              (startCompleteVertexLabel pair.1.1 L
                (pairComponentCertificate hN pair Ct).left) :=
          hkSecond.symm
        _ =
            largeOddKernel (L + 1) (codeLeftSecondLabel x q) := by
          exact congrArg (largeOddKernel (L + 1)) hleftSecondLabel
    have hxy := pair_coordinates_two_le hN pair
    have hm :
        codeRightFirstLabel pair.1.2 q ≠ 0 :=
      Nat.ne_of_gt
        (RationalChannelCode.startCompleteVertexLabel_pos
          hxy.2 q.rightFirst)
    have hn :
        codeRightSecondLabel pair.1.2 q ≠ 0 :=
      Nat.ne_of_gt
        (RationalChannelCode.startCompleteVertexLabel_pos
          hxy.2 q.rightSecond)
    have hyBlock :
        pair.1.2 ∈ boundedRatioBlock N M :=
      (mem_separatedBoundedRatioPairs.mp pair.2).2.1
    have hmCutoff :
        codeRightFirstLabel pair.1.2 q ≤ X := by
      rw [← hcutoff]
      exact
        startCompleteVertexLabel_le_terminalLabelCutoff
          hN hMκ hL hyBlock q.rightFirst
    have hnCutoff :
        codeRightSecondLabel pair.1.2 q ≤ X := by
      rw [← hcutoff]
      exact
        startCompleteVertexLabel_le_terminalLabelCutoff
          hN hMκ hL hyBlock q.rightSecond
    have hcoefficientFirst :
        largeOddKernel (L + 1)
              (codeRightFirstLabel pair.1.2 q) *
            smallOddPart (L + 1)
              (codeRightFirstLabel pair.1.2 q) ≤
          X ^ 1 := by
      simpa only [pow_one] using
        (TerminalPartnerPell.canonical_terminal_coefficient_le hm).trans
          hmCutoff
    have hcoefficientSecond :
        largeOddKernel (L + 1)
              (codeRightSecondLabel pair.1.2 q) *
            smallOddPart (L + 1)
              (codeRightSecondLabel pair.1.2 q) ≤
          X ^ 1 := by
      simpa only [pow_one] using
        (TerminalPartnerPell.canonical_terminal_coefficient_le hn).trans
          hnCutoff
    have hdelta :
        (channelVertexOffset q.rightFirst -
            channelVertexOffset q.rightSecond).natAbs ≤ X ^ 1 := by
      simp only [pow_one]
      rw [← hcutoff]
      exact
        codeRightOffsetDifference_natAbs_le_cutoff
          hN hκ₀ hL q
    have hrightNe :
        q.rightFirst ≠ q.rightSecond := by
      have hdistinct :=
        componentOffsetQuadruple_distinct
          hN pair (Cs := Cs) (Ct := Ct) hST
      simpa only [hcode] using hdistinct.2
    have hoffsetNe :
        channelVertexOffset q.rightFirst ≠
          channelVertexOffset q.rightSecond :=
      ResidualCertificates.channelVertexOffset_injective.ne hrightNe
    have hboxRaw :=
      hX₀ X hX
        (L + 1)
        (codeRightFirstLabel pair.1.2 q)
        (codeRightSecondLabel pair.1.2 q)
        (channelVertexOffset q.rightFirst)
        (channelVertexOffset q.rightSecond)
        hm hn
        (by
          rw [hR]
          simpa only [hleftFirstLabel] using hkFirstGt)
        (by
          rw [hS]
          simpa only [hleftSecondLabel] using hkSecondGt)
        (by
          rw [hR, hS]
          simpa only [hleftFirstLabel, hleftSecondLabel] using hkCoprime)
        hoffsetNe hcoefficientFirst hcoefficientSecond hdelta
    have hbox :
        PellInput.HasAtMostSolutionsReal
          (TerminalPartnerPell.terminalPartnerWitnessBox
            (largeOddKernel (L + 1) (codeLeftFirstLabel x q))
            (largeOddKernel (L + 1) (codeLeftSecondLabel x q))
            a b
            (channelVertexOffset q.rightFirst)
            (channelVertexOffset q.rightSecond)
            X)
          (PellInput.expLogLogBound c X) := by
      simpa only [hR, hS, ha, hb, pow_one] using hboxRaw
    have hboxCutoff :
        PellInput.HasAtMostSolutionsReal
          (TerminalPartnerPell.terminalPartnerWitnessBox
            (largeOddKernel (L + 1) (codeLeftFirstLabel x q))
            (largeOddKernel (L + 1) (codeLeftSecondLabel x q))
            a b
            (channelVertexOffset q.rightFirst)
            (channelVertexOffset q.rightSecond)
            (terminalLabelCutoff κ₀ N))
          (PellInput.expLogLogBound c X) := by
      simpa only [hcutoff] using hbox
    exact
      card_terminalParameterFiber_cast_le
        hN hMκ hL K hboxCutoff

/--
Finite partner-fibre estimate conditional only on generalized Pell.  The
two-component restriction is explicit; it is removed by
`twoComponentTerminalPartnerFiber_eq` under the displayed slack condition
`2 ≤ B - 3 R_K(B)`.
-/
theorem twoComponentTerminalPartnerFiber_polynomialBound
    (hPell :
      PellInput.GeneralizedPellPolynomialBoxStatement) :
    ∃ c : ℝ, 0 ≤ c ∧
      ∃ X₀ : ℕ, ∀ X ≥ X₀,
        ∀ (κ₀ N M A L : ℕ) (hN : 2 ≤ N),
          2 ≤ κ₀ →
          M ≤ κ₀ * N →
          L ≤ N →
          terminalLabelCutoff κ₀ N = X →
          ∀ (K : ℝ) (x : ℕ),
            ((twoComponentTerminalPartnerFiber
                N M A L hN K x).card : ℝ) ≤
              ((L + 1 : ℕ) : ℝ) ^ 4 *
                ((terminalSmallParts κ₀ N L).card : ℝ) ^ 2 *
                PellInput.expLogLogBound c X := by
  obtain ⟨c, hc, X₀, hfixed⟩ :=
    terminalParameterFibers_polynomialBox hPell
  refine ⟨c, hc, X₀, ?_⟩
  intro X hX κ₀ N M A L hN hκ₀ hMκ hL hcutoff K x
  apply card_twoComponentTerminalPartnerFiber_cast_le hMκ hL
  intro q a ha b hb
  exact
    hfixed X hX κ₀ N M A L hN hκ₀ hMκ hL hcutoff
      K x q a b

/-- The same bound for the complete partner fibre in the finite terminal range. -/
theorem boundedRankTerminalPartnerFiber_polynomialBound
    (hPell :
      PellInput.GeneralizedPellPolynomialBoxStatement) :
    ∃ c : ℝ, 0 ≤ c ∧
      ∃ X₀ : ℕ, ∀ X ≥ X₀,
        ∀ (κ₀ N M A L : ℕ) (hN : 2 ≤ N),
          2 ≤ κ₀ →
          M ≤ κ₀ * N →
          L ≤ N →
          terminalLabelCutoff κ₀ N = X →
          ∀ (K : ℝ) (x : ℕ),
            2 ≤ L + 1 - 3 * terminalRankBudget K L →
            ((boundedRankTerminalPartnerFiber
                N M A L hN K x).card : ℝ) ≤
              ((L + 1 : ℕ) : ℝ) ^ 4 *
                ((terminalSmallParts κ₀ N L).card : ℝ) ^ 2 *
                PellInput.expLogLogBound c X := by
  obtain ⟨c, hc, X₀, hbound⟩ :=
    twoComponentTerminalPartnerFiber_polynomialBound hPell
  refine ⟨c, hc, X₀, ?_⟩
  intro X hX κ₀ N M A L hN hκ₀ hMκ hL hcutoff
    K x htwo
  rw [← twoComponentTerminalPartnerFiber_eq hN K x htwo]
  exact
    hbound X hX κ₀ N M A L hN hκ₀ hMκ hL hcutoff K x

/-! ## Incidence of first starts with bounded-kernel labels -/

/-- The size-two component finset, with membership bundled in the index. -/
noncomputable def attachedPairComponents
    {N M L : ℕ} (A : ℕ)
    (pair : SeparatedBoundedRatioPair N M L) :
    Finset (BoundedPairComponent A pair) :=
  (boundedCanonicalPairComponents A pair).attach

/-- The complete-boundary label selected in the first block. -/
noncomputable def pairComponentLeftLabel
    {N M A L : ℕ} (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L)
    (C : BoundedPairComponent A pair) : ℕ :=
  startCompleteVertexLabel pair.1.1 L
    (pairComponentCertificate hN pair C).left

/-- The large odd kernel carried by that first-block label. -/
noncomputable def pairComponentLeftKernel
    {N M A L : ℕ} (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L)
    (C : BoundedPairComponent A pair) : ℕ :=
  largeOddKernel (L + 1) (pairComponentLeftLabel hN pair C)

/-- Components whose selected first-block label has nonexceptional kernel. -/
noncomputable def nonexceptionalPairComponents
    {N M A L : ℕ} (κ₀ : ℕ) (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L) :
    Finset (BoundedPairComponent A pair) :=
  (attachedPairComponents A pair).filter fun C ↦
    ¬kernelThreshold κ₀ N L < pairComponentLeftKernel hN pair C

/-- Components above the square-root threshold. -/
noncomputable def exceptionalPairComponents
    {N M A L : ℕ} (κ₀ : ℕ) (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L) :
    Finset (BoundedPairComponent A pair) :=
  (attachedPairComponents A pair).filter fun C ↦
    kernelThreshold κ₀ N L < pairComponentLeftKernel hN pair C

/--
For a terminal pair, kernels of two distinct size-two components have
product at most the determinant budget.
-/
theorem pairComponentLeftKernel_product_le
    {κ₀ N M A L : ℕ} (hN : 2 ≤ N) (hA : 1 ≤ A)
    (hMκ : M ≤ κ₀ * N) (hL : L ≤ N) (K : ℝ)
    (pair : SeparatedBoundedRatioPair N M L)
    (hpair : pair ∈ boundedRankTerminalPairs N M A L hN K)
    {Cs Ct : BoundedPairComponent A pair}
    (hST : Cs ≠ Ct) :
    pairComponentLeftKernel hN pair Cs *
        pairComponentLeftKernel hN pair Ct ≤
      determinantBudget κ₀ N L := by
  have hpackage :=
    distinct_pairComponents_kernel_package
      hN pair (Cs := Cs) (Ct := Ct) hST
  rcases hpackage with
    ⟨_hkFirst, _hkSecond, hkFirstGt, hkSecondGt,
      _hkCoprime, hdiv⟩
  have hne :=
    pairComponents_crossDeterminant_ne
      hN hA K pair hpair hST
  have hpairData :=
    mem_separatedBoundedRatioPairs.mp pair.2
  have habs :=
    abs_crossDeterminant_startCompleteVertexLabel_le
      hN hMκ hL hpairData.1 hpairData.2.1
      (pairComponentCertificate hN pair Cs).left
      (pairComponentCertificate hN pair Cs).right
      (pairComponentCertificate hN pair Ct).left
      (pairComponentCertificate hN pair Ct).right
  exact
    kernel_product_le_of_dvd_crossDeterminant
      hkFirstGt hkSecondGt hne hdiv habs

/-- There is at most one exceptional component in a terminal pair. -/
theorem card_exceptionalPairComponents_le_one
    {κ₀ N M A L : ℕ} (hN : 2 ≤ N) (hA : 1 ≤ A)
    (hMκ : M ≤ κ₀ * N) (hL : L ≤ N) (K : ℝ)
    (pair : SeparatedBoundedRatioPair N M L)
    (hpair : pair ∈ boundedRankTerminalPairs N M A L hN K) :
    (exceptionalPairComponents (A := A) κ₀ hN pair).card ≤ 1 := by
  unfold exceptionalPairComponents
  apply card_filter_kernel_above_threshold_le_one
  intro s t _hs _ht hst
  exact
    pairComponentLeftKernel_product_le
      hN hA hMκ hL K pair hpair hst

/-- Nonexceptional selected labels are all counted by the incidence fibre. -/
theorem card_nonexceptionalPairComponents_le_incident
    {κ₀ N M A L : ℕ} (hN : 2 ≤ N)
    (hMκ : M ≤ κ₀ * N) (hL : L ≤ N)
    (pair : SeparatedBoundedRatioPair N M L) :
    (nonexceptionalPairComponents (A := A) κ₀ hN pair).card ≤
      (incidentPossibleKernelValues
        κ₀ N L pair.1.1).card := by
  classical
  let components :=
    nonexceptionalPairComponents (A := A) κ₀ hN pair
  let label : BoundedPairComponent A pair → ℕ :=
    pairComponentLeftLabel hN pair
  have hinjective : Function.Injective label := by
    intro C D hlabel
    apply pairComponentCertificate_left_injective hN pair
    exact
      Affine.RelationalPrimeAssignment.startCompleteVertexLabel_injective
        (by
          have := (pair_coordinates_two_le hN pair).1
          omega)
        hlabel
  have hcard :
      (components.image label).card = components.card := by
    exact Finset.card_image_iff.mpr fun C _ D _ h ↦
      hinjective h
  have hsubset :
      components.image label ⊆
        incidentPossibleKernelValues κ₀ N L pair.1.1 := by
    intro n hn
    obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hn
    have hCData := Finset.mem_filter.mp hC
    rw [incidentPossibleKernelValues, Finset.mem_filter]
    constructor
    · rw [possibleKernelValues,
        TerminalKernelCount.mem_boundedLargeKernelValues]
      refine ⟨?_, ?_, ?_⟩
      · exact
          (RationalChannelCode.startCompleteVertexLabel_pos
            (pair_coordinates_two_le hN pair).1
            (pairComponentCertificate hN pair C).left)
      · exact
          startCompleteVertexLabel_le_terminalLabelCutoff
            hN hMκ hL
            (mem_separatedBoundedRatioPairs.mp pair.2).1
            (pairComponentCertificate hN pair C).left
      · simpa only [pairComponentLeftKernel] using
          Nat.le_of_not_gt hCData.2
    · exact
        ⟨(pairComponentCertificate hN pair C).left, rfl⟩
  calc
    components.card = (components.image label).card := hcard.symm
    _ ≤ (incidentPossibleKernelValues κ₀ N L pair.1.1).card :=
      Finset.card_le_card hsubset

/--
Deleting the unique exceptional component loses at most one incidence.
-/
theorem attachedPairComponents_card_sub_one_le_incident
    {κ₀ N M A L : ℕ} (hN : 2 ≤ N) (hA : 1 ≤ A)
    (hMκ : M ≤ κ₀ * N) (hL : L ≤ N) (K : ℝ)
    (pair : SeparatedBoundedRatioPair N M L)
    (hpair : pair ∈ boundedRankTerminalPairs N M A L hN K) :
    (attachedPairComponents A pair).card - 1 ≤
      (incidentPossibleKernelValues
        κ₀ N L pair.1.1).card := by
  have hexceptional :=
    card_exceptionalPairComponents_le_one
      hN hA hMκ hL K pair hpair
  have hbounded :=
    card_nonexceptionalPairComponents_le_incident
      (A := A) hN hMκ hL pair
  have hpartition :=
    Finset.filter_card_add_filter_neg_card_eq_card
      (s := attachedPairComponents A pair)
      (fun C ↦
        kernelThreshold κ₀ N L <
          pairComponentLeftKernel hN pair C)
  change
    (exceptionalPairComponents (A := A) κ₀ hN pair).card +
        (nonexceptionalPairComponents (A := A) κ₀ hN pair).card =
      (attachedPairComponents A pair).card at hpartition
  omega

/--
A rank-terminal pair supplies at least
`B - 3 R_K(B) - 1` bounded-kernel labels at its first start.
-/
theorem terminalPair_incidentPossibleKernelValues_lower
    {κ₀ N M A L : ℕ} (hN : 2 ≤ N) (hA : 1 ≤ A)
    (hMκ : M ≤ κ₀ * N) (hL : L ≤ N) (K : ℝ)
    (pair : SeparatedBoundedRatioPair N M L)
    (hpair : pair ∈ boundedRankTerminalPairs N M A L hN K) :
    L + 1 - 3 * terminalRankBudget K L - 1 ≤
      (incidentPossibleKernelValues
        κ₀ N L pair.1.1).card := by
  have hterminal := mem_boundedRankTerminalPairs.mp hpair
  have hslack :
      boundedTerminalSlack A pair ≤ terminalRankBudget K L := by
    omega
  have hcomponents :=
    (bounded_terminal_component_count
      (A := A) hN pair).2
  have hattach :
      (attachedPairComponents A pair).card =
        (boundedCanonicalPairComponents A pair).card := by
    simp [attachedPairComponents]
  have hlower :
      L + 1 - 3 * terminalRankBudget K L ≤
        (attachedPairComponents A pair).card := by
    rw [hattach]
    omega
  exact
    (show
      L + 1 - 3 * terminalRankBudget K L - 1 ≤
        (attachedPairComponents A pair).card - 1 by
      omega).trans
      (attachedPairComponents_card_sub_one_le_incident
        hN hA hMκ hL K pair hpair)

/--
The abstract first-start incidence theorem is now instantiated on the
literal population `T_K`.
-/
theorem card_boundedRankTerminalFirstStarts_le_twice_possibleKernelValues
    {κ₀ N M A L : ℕ} (hN : 2 ≤ N) (hA : 1 ≤ A)
    (hMκ : M ≤ κ₀ * N) (hL : L ≤ N) (K : ℝ)
    (hhalf :
      L + 1 ≤
        2 * (L + 1 - 3 * terminalRankBudget K L - 1)) :
    (boundedRankTerminalFirstStarts N M A L hN K).card ≤
      2 * (possibleKernelValues κ₀ N L).card := by
  apply card_firstStarts_le_twice_possibleKernelValues
    (m := L + 1 - 3 * terminalRankBudget K L - 1)
  · omega
  · intro x hx
    obtain ⟨pair, hpair, rfl⟩ := Finset.mem_image.mp hx
    exact (mem_separatedBoundedRatioPairs.mp pair.2).1
  · omega
  · exact hhalf
  · intro x hx
    obtain ⟨pair, hpair, hfirst⟩ := Finset.mem_image.mp hx
    rw [← hfirst]
    exact
      terminalPair_incidentPossibleKernelValues_lower
        hN hA hMκ hL K pair hpair

/-! ## Eventual discharge of the finite slack conditions -/

/--
For fixed nonnegative `K`, the rank budget is eventually smaller than
`(B-2)/6`.  This is the elementary comparison
`K sqrt(B) / log(B) = o(B)`, recorded in the exact natural form used above.
-/
theorem six_mul_terminalRankBudget_add_two_le_eventually
    {K : ℝ} (hK : 0 ≤ K) :
    ∃ B₀ : ℕ, ∀ B ≥ B₀,
      6 * terminalRankBudget K (B - 1) + 2 ≤ B := by
  let D : ℝ := max 1 (6 * K + 2)
  obtain ⟨B₀, hB₀⟩ :=
    exists_nat_gt (max (Real.exp 1) (D ^ 2))
  refine ⟨max B₀ 2, ?_⟩
  intro B hB
  have hB₀B : B₀ ≤ B :=
    (le_max_left B₀ 2).trans hB
  have hBtwo : 2 ≤ B :=
    (le_max_right B₀ 2).trans hB
  have hthreshold :
      max (Real.exp 1) (D ^ 2) < (B : ℝ) :=
    hB₀.trans_le (by exact_mod_cast hB₀B)
  have hexpB : Real.exp 1 < (B : ℝ) :=
    (le_max_left _ _).trans_lt hthreshold
  have hDsq : D ^ 2 < (B : ℝ) :=
    (le_max_right _ _).trans_lt hthreshold
  have hlogB : 1 ≤ Real.log (B : ℝ) := by
    have hlogs :=
      Real.log_lt_log (Real.exp_pos 1) hexpB
    simpa only [Real.log_exp] using hlogs.le
  have hlogPos : 0 < Real.log (B : ℝ) :=
    lt_of_lt_of_le zero_lt_one hlogB
  have hDnonneg : 0 ≤ D := by
    dsimp only [D]
    exact le_max_of_le_left zero_le_one
  have hDleSqrt :
      D ≤ Real.sqrt (B : ℝ) :=
    (Real.le_sqrt hDnonneg (by positivity)).2 hDsq.le
  have hsixK :
      6 * K + 2 ≤ Real.sqrt (B : ℝ) :=
    (le_max_right 1 (6 * K + 2)).trans hDleSqrt
  have hsqrtOne :
      1 ≤ Real.sqrt (B : ℝ) :=
    (le_max_left 1 (6 * K + 2)).trans hDleSqrt
  have hscale :
      terminalRankScale K (B - 1) ≤
        K * Real.sqrt (B : ℝ) := by
    have hBsub : B - 1 + 1 = B := by omega
    unfold terminalRankScale
    rw [hBsub]
    apply (div_le_iff₀ hlogPos).2
    have hnonneg :
        0 ≤ K * Real.sqrt (B : ℝ) := by positivity
    nlinarith
  have hbudget :
      (terminalRankBudget K (B - 1) : ℝ) ≤
        K * Real.sqrt (B : ℝ) := by
    exact
      (terminalRankBudget_cast_le_scale hK
        (show 2 ≤ B - 1 + 1 by omega)).trans hscale
  have hsqrtSq :
      Real.sqrt (B : ℝ) ^ 2 = (B : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hmul :
      0 ≤
        (Real.sqrt (B : ℝ) - (6 * K + 2)) *
          Real.sqrt (B : ℝ) :=
    mul_nonneg (sub_nonneg.mpr hsixK)
      (Real.sqrt_nonneg _)
  have hreal :
      (6 : ℝ) *
          (terminalRankBudget K (B - 1) : ℝ) + 2 ≤
        (B : ℝ) := by
    nlinarith
  exact_mod_cast hreal

/--
Uniformly in the critical run-length window, the two finite conditions
needed by both the incidence and partner arguments eventually hold.
-/
theorem terminalRankBudget_slack_conditions_eventually
    {C K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L,
      CriticalRunWindow.InRunLengthWindow C N L →
      2 ≤ L + 1 - 3 * terminalRankBudget K L ∧
      L + 1 ≤
        2 * (L + 1 - 3 * terminalRankBudget K L - 1) := by
  obtain ⟨B₀, hB₀⟩ :=
    six_mul_terminalRankBudget_add_two_le_eventually hK
  obtain ⟨N₀, hN₀⟩ :=
    DependencyEdgesCritical.runLengthAddOne_tends_to_infinity hC B₀
  refine ⟨N₀, ?_⟩
  intro N hN L hrun
  have hB : B₀ ≤ L + 1 :=
    hN₀ N hN L hrun
  have hbudget :
      6 * terminalRankBudget K L + 2 ≤ L + 1 := by
    simpa only [Nat.add_sub_cancel] using
      hB₀ (L + 1) hB
  omega

end

end BoundedRatioTerminalPartnerClosure
end PaperC
