import PaperC.Affine.CanonicalRationalCode
import PaperC.Combinatorics.LargePrimeRelationBoundary

set_option maxHeartbeats 1800000

/-!
# Corrected defect and component counts

This file implements the finite counting part of Lemma 6.4.  Exact units of
one positive primitive channel are partitioned into:

* units whose left (equivalently right) occurrence is defective;
* units whose two occurrences form an isolated nonpinned component.

The two classes inject respectively into the defective vertices and the
nontrivial unpinned components.  Subtracting their cardinalities in the
active branch `m ≥ 2` gives the manuscript's corrected counts `D#` and `c#`.
-/

namespace PaperC
namespace ResidualComponentCounts

open Affine
open Affine.CanonicalRationalCode
open Affine.RationalChannelCode
open ExactUnitIsolation
open LargePrimeOccurrences
open LargePrimeGraph
open LargePrimeGraphResolution
open LargePrimeRelationBoundary
open PinnedGraphResolution

noncomputable section

noncomputable local instance instDecidableLargePrimeAdj
    (x y L : ℕ) :
    DecidableRel (largePrimeGraph x y L).Adj :=
  Classical.decRel _

/-- Exact units in the defective branch of Lemma 6.3. -/
abbrev DefectiveChannelUnit
    (x y L a b : ℕ) (h : ℤ) :=
  {unit : ChannelUnit L a b h //
    IsDefective x y L (Sum.inl unit.1.1)}

/-- Exact units in the nondefective branch of Lemma 6.3. -/
abbrev NondefectiveChannelUnit
    (x y L a b : ℕ) (h : ℤ) :=
  {unit : ChannelUnit L a b h //
    ¬IsDefective x y L (Sum.inl unit.1.1)}

/-- Total number `m` of exact units in the channel. -/
noncomputable def channelUnitCount
    (L a b : ℕ) (h : ℤ) : ℕ :=
  Fintype.card (ChannelUnit L a b h)

/-- Number `d` of exact units yielding two defective occurrences. -/
noncomputable def defectiveExactUnitCount
    (x y L a b : ℕ) (h : ℤ) : ℕ := by
  classical
  exact Fintype.card (DefectiveChannelUnit x y L a b h)

/-- Number `n=m-d` of exact units yielding isolated two-vertex components. -/
noncomputable def nondefectiveExactUnitCount
    (x y L a b : ℕ) (h : ℤ) : ℕ := by
  classical
  exact Fintype.card (NondefectiveChannelUnit x y L a b h)

/-- The type-level unit count agrees with the original occurrence finset. -/
theorem channelUnitCount_eq_card_rationalChannelUnits
    (L a b : ℕ) (h : ℤ) :
    channelUnitCount L a b h =
      (rationalChannelUnits L a b h).card := by
  simp [channelUnitCount]

/-- It also agrees with the integer-cell multiplicity used in Section 5. -/
theorem channelUnitCount_eq_card_channelCells
    (L a b : ℕ) (h : ℤ) :
    channelUnitCount L a b h =
      (channelCells L a b h).card := by
  rw [channelUnitCount_eq_card_rationalChannelUnits,
    card_rationalChannelUnits_eq_channelCells]

/-- The defective and nondefective classes form a partition of all units. -/
theorem defective_add_nondefective_eq_channelUnitCount
    (x y L a b : ℕ) (h : ℤ) :
    defectiveExactUnitCount x y L a b h +
        nondefectiveExactUnitCount x y L a b h =
      channelUnitCount L a b h := by
  classical
  let P : ChannelUnit L a b h → Prop :=
    fun unit =>
      IsDefective x y L (Sum.inl unit.1.1)
  change
    Fintype.card {unit : ChannelUnit L a b h // P unit} +
        Fintype.card {unit : ChannelUnit L a b h // ¬P unit} =
      Fintype.card (ChannelUnit L a b h)
  rw [Fintype.card_subtype_compl P]
  exact Nat.add_sub_of_le (Fintype.card_subtype_le P)

/-- A defective exact unit maps to its left defective occurrence. -/
def defectiveUnitVertex
    {x y L a b : ℕ} {h : ℤ} :
    DefectiveChannelUnit x y L a b h →
      {v : Occurrence L // v ∈ defectiveVertices x y L} :=
  fun unit =>
    ⟨Sum.inl unit.1.1.1,
      mem_defectiveVertices.mpr unit.2⟩

/-- Distinct units give distinct defective vertices. -/
theorem defectiveUnitVertex_injective
    {x y L a b : ℕ} {h : ℤ}
    (hb : 0 < b) :
    Function.Injective
      (defectiveUnitVertex
        (x := x) (y := y) (L := L)
        (a := a) (b := b) (h := h)) := by
  intro unit₁ unit₂ huv
  apply Subtype.ext
  apply channelUnit_left_injective hb
  exact Sum.inl.inj (congrArg Subtype.val huv)

/-- Hence `d ≤ D`. -/
theorem defectiveExactUnitCount_le_defectiveVertexCount
    {x y L a b : ℕ} {h : ℤ}
    (hb : 0 < b) :
    defectiveExactUnitCount x y L a b h ≤
      defectiveVertexCount x y L := by
  classical
  let f :=
    defectiveUnitVertex
      (x := x) (y := y) (L := L)
      (a := a) (b := b) (h := h)
  change
    Fintype.card (DefectiveChannelUnit x y L a b h) ≤
      (defectiveVertices x y L).card
  calc
    Fintype.card (DefectiveChannelUnit x y L a b h) ≤
        Fintype.card
          {v : Occurrence L //
            v ∈ defectiveVertices x y L} :=
      Fintype.card_le_of_injective f
        (defectiveUnitVertex_injective
          (x := x) (y := y) (L := L)
          (a := a) (b := b) (h := h) hb)
    _ = (defectiveVertices x y L).card :=
      Fintype.card_coe (defectiveVertices x y L)

/--
A nondefective exact unit maps canonically to its isolated nontrivial
unpinned component.
-/
noncomputable def nondefectiveUnitComponent
    {x y L a b : ℕ} {h : ℤ}
    (ha : 0 < a) (hb : 0 < b)
    (hab : a.Coprime b)
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hheight : h = (b : ℤ) * y - (a : ℤ) * x)
    (hsmall : Nat.max a b < L + 1) :
    NondefectiveChannelUnit x y L a b h →
      {C : (largePrimeGraph x y L).ConnectedComponent //
        C ∈ nontrivialUnpinnedComponents
          (largePrimeGraph x y L)
          (pinnedVertices x y L)} := by
  intro unit
  let C :=
    (largePrimeGraph x y L).connectedComponentMk
      (Sum.inl unit.1.1.1)
  refine
    ⟨C,
      (mem_nontrivialUnpinnedComponents
        (largePrimeGraph x y L)).mpr ?_⟩
  obtain ⟨t, hfactor⟩ :=
    channelUnit_exactUnitFactorization
      ha hb hab hx hy hheight hsmall unit.1
  rcases
      exactUnit_graph_dichotomy
        (show 1 ≤ x by omega) (show 1 ≤ y by omega)
        hfactor with hdef | hnontrivial
  · exact (unit.2 hdef.1).elim
  · exact hnontrivial.2.1

/-- Distinct nondefective units determine distinct residual components. -/
theorem nondefectiveUnitComponent_injective
    {x y L a b : ℕ} {h : ℤ}
    (ha : 0 < a) (hb : 0 < b)
    (hab : a.Coprime b)
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hheight : h = (b : ℤ) * y - (a : ℤ) * x)
    (hsmall : Nat.max a b < L + 1) :
    Function.Injective
      (nondefectiveUnitComponent
        ha hb hab hx hy hheight hsmall) := by
  intro unit₁ unit₂ hcomponents
  apply Subtype.ext
  by_contra hne
  have hdistinct :=
    distinct_channelUnits_components_ne
      ha hb hab hx hy hheight hsmall hne
  exact hdistinct (congrArg Subtype.val hcomponents)

/-- Hence `n ≤ c`. -/
theorem nondefectiveExactUnitCount_le_nontrivialComponentCount
    {x y L a b : ℕ} {h : ℤ}
    (ha : 0 < a) (hb : 0 < b)
    (hab : a.Coprime b)
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hheight : h = (b : ℤ) * y - (a : ℤ) * x)
    (hsmall : Nat.max a b < L + 1) :
    nondefectiveExactUnitCount x y L a b h ≤
      nontrivialComponentCount x y L := by
  classical
  let f :=
    nondefectiveUnitComponent
      ha hb hab hx hy hheight hsmall
  change
    Fintype.card (NondefectiveChannelUnit x y L a b h) ≤
      (nontrivialUnpinnedComponents
        (largePrimeGraph x y L)
        (pinnedVertices x y L)).card
  calc
    Fintype.card (NondefectiveChannelUnit x y L a b h) ≤
        Fintype.card
          {C : (largePrimeGraph x y L).ConnectedComponent //
            C ∈ nontrivialUnpinnedComponents
              (largePrimeGraph x y L)
              (pinnedVertices x y L)} :=
      Fintype.card_le_of_injective f
        (nondefectiveUnitComponent_injective
          ha hb hab hx hy hheight hsmall)
    _ =
        (nontrivialUnpinnedComponents
          (largePrimeGraph x y L)
          (pinnedVertices x y L)).card :=
      Fintype.card_coe
        (nontrivialUnpinnedComponents
          (largePrimeGraph x y L)
          (pinnedVertices x y L))

/--
The corrected defect count `D#`.  No correction is made unless the channel
has at least two exact units, exactly as in the manuscript.
-/
noncomputable def correctedDefectCount
    (x y L a b : ℕ) (h : ℤ) : ℕ :=
  if 2 ≤ channelUnitCount L a b h then
    defectiveVertexCount x y L -
      defectiveExactUnitCount x y L a b h
  else
    defectiveVertexCount x y L

/-- The residual nontrivial-component count `c#`. -/
noncomputable def residualComponentCount
    (x y L a b : ℕ) (h : ℤ) : ℕ :=
  if 2 ≤ channelUnitCount L a b h then
    nontrivialComponentCount x y L -
      nondefectiveExactUnitCount x y L a b h
  else
    nontrivialComponentCount x y L

/-- Local residual dimension `ρ-(m-1)`, equal to `τ` for a selected channel. -/
noncomputable def localResidualTau
    (M x y L a b : ℕ) (h : ℤ) : ℕ :=
  relationRho (twoStartSystem M x y L) -
    (channelUnitCount L a b h - 1)

/-- Corrected counts never exceed their uncorrected counterparts. -/
theorem correctedDefectCount_le
    (x y L a b : ℕ) (h : ℤ) :
    correctedDefectCount x y L a b h ≤
      defectiveVertexCount x y L := by
  unfold correctedDefectCount
  split_ifs <;> omega

theorem residualComponentCount_le
    (x y L a b : ℕ) (h : ℤ) :
    residualComponentCount x y L a b h ≤
      nontrivialComponentCount x y L := by
  unfold residualComponentCount
  split_ifs <;> omega

/-- The vertex budget survives removal of the systematic exact components. -/
theorem corrected_add_twice_residual_le
    (x y L a b : ℕ) (h : ℤ)
    (hx : 1 ≤ x) (hy : 1 ≤ y) :
    correctedDefectCount x y L a b h +
        2 * residualComponentCount x y L a b h ≤
      2 * (L + 1) := by
  have hbudget :=
    defectiveVertex_add_twice_nontrivial_le
      (x := x) (y := y) (L := L)
      hx hy
  have hD :=
    correctedDefectCount_le x y L a b h
  have hc :=
    residualComponentCount_le x y L a b h
  omega

/--
Finite quotient-core inequality of Lemma 6.4 for one explicit primitive
channel.
-/
theorem localResidualTau_le_corrected_add_residual
    {M x y L a b : ℕ} {h : ℤ}
    (ha : 0 < a) (hb : 0 < b)
    (hab : a.Coprime b)
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hxM : x + L ≤ M) (hyM : y + L ≤ M)
    (hheight : h = (b : ℤ) * y - (a : ℤ) * x) :
    localResidualTau M x y L a b h ≤
      correctedDefectCount x y L a b h +
        residualComponentCount x y L a b h := by
  have hdimW :=
    finrank_largePrimeSolution_eq_defective_add_components
      (L := L)
      (show 1 ≤ x by omega) (show 1 ≤ y by omega)
  by_cases hm : 2 ≤ channelUnitCount L a b h
  · have hunit :
        Nonempty (ChannelUnit L a b h) := by
      rw [← Fintype.card_pos_iff]
      exact Nat.zero_lt_of_lt hm
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
    let unit : ChannelUnit L a b h := Classical.choice hunit
    have hrho :=
      relationRho_le_finrank_largePrimeSolution_sub_one
        ha hb hab hx hy hxM hyM hheight hsmall unit
    have hd :=
      defectiveExactUnitCount_le_defectiveVertexCount
        (x := x) (y := y) (L := L)
        (a := a) (b := b) (h := h) hb
    have hn :=
      nondefectiveExactUnitCount_le_nontrivialComponentCount
        ha hb hab hx hy hheight hsmall
    have hpartition :=
      defective_add_nondefective_eq_channelUnitCount
        x y L a b h
    simp only [localResidualTau, correctedDefectCount,
      residualComponentCount, if_pos hm]
    rw [hdimW] at hrho
    omega
  · have hrho :=
      relationRho_le_finrank_largePrimeSolution
        hx hy hxM hyM
    have hmle : channelUnitCount L a b h ≤ 1 := by
      omega
    simp only [localResidualTau, correctedDefectCount,
      residualComponentCount, if_neg hm]
    rw [hdimW] at hrho
    omega

/-! ## Canonical channel wrapper -/

/-- Canonical corrected defect count of Lemma 6.4. -/
noncomputable def canonicalCorrectedDefectCount
    (A x y L : ℕ) : ℕ :=
  match canonicalReducedCandidate?
      x y (L + 1) ((L + 1) ^ A) with
  | none => defectiveVertexCount x y L
  | some c =>
      correctedDefectCount x y L c.1.1 c.1.2
        (pairChannelError x y c.1.1 c.1.2)

/-- Canonical residual nontrivial-component count of Lemma 6.4. -/
noncomputable def canonicalResidualComponentCount
    (A x y L : ℕ) : ℕ :=
  match canonicalReducedCandidate?
      x y (L + 1) ((L + 1) ^ A) with
  | none => nontrivialComponentCount x y L
  | some c =>
      residualComponentCount x y L c.1.1 c.1.2
        (pairChannelError x y c.1.1 c.1.2)

/--
The canonical `τ` of Section 5 is the local expression `ρ-(m-1)` whenever
a candidate has been selected.
-/
theorem residualTau_eq_localResidualTau_of_choice
    {M A x y L : ℕ}
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (c : ReducedCandidate
      x y (L + 1) ((L + 1) ^ A))
    (hchoice :
      canonicalReducedCandidate?
          x y (L + 1) ((L + 1) ^ A) =
        some c) :
    residualTau M A x y L hx hy =
      localResidualTau M x y L c.1.1 c.1.2
        (pairChannelError x y c.1.1 c.1.2) := by
  unfold residualTau localResidualTau
  rw [rationalSigma_eq_canonicalMultiplicity_sub_one]
  have hm :
      canonicalMultiplicity A L x y =
        channelUnitCount L c.1.1 c.1.2
          (pairChannelError x y c.1.1 c.1.2) := by
    calc
      canonicalMultiplicity A L x y =
          candidateMultiplicity L c := by
        unfold canonicalMultiplicity
        rw [hchoice]
      _ =
          (channelCells L c.1.1 c.1.2
            (pairChannelError x y c.1.1 c.1.2)).card :=
        rfl
      _ =
          channelUnitCount L c.1.1 c.1.2
            (pairChannelError x y c.1.1 c.1.2) :=
        (channelUnitCount_eq_card_channelCells
          L c.1.1 c.1.2
          (pairChannelError x y c.1.1 c.1.2)).symm
  rw [hm]

/--
Canonical finite form of (6.3): no height hypothesis is used in the
degenerate branch `m<2`; in the active branch it follows from the presence
of two exact units.
-/
theorem residualTau_le_canonicalCorrected_add_residual
    {M A x y L : ℕ}
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hxM : x + L ≤ M) (hyM : y + L ≤ M) :
    residualTau M A x y L hx hy ≤
      canonicalCorrectedDefectCount A x y L +
        canonicalResidualComponentCount A x y L := by
  generalize hchoice :
      canonicalReducedCandidate?
        x y (L + 1) ((L + 1) ^ A) = choice
  cases choice with
  | none =>
      have hm :
          canonicalMultiplicity A L x y ≤ 1 := by
        simp [canonicalMultiplicity, hchoice]
      have htau :=
        (degenerate_canonical_channel
          (M := M) (hx := hx) (hy := hy) hm).2.2
      have hrho :=
        relationRho_le_finrank_largePrimeSolution
          hx hy hxM hyM
      have hdimW :=
        finrank_largePrimeSolution_eq_defective_add_components
          (L := L)
          (show 1 ≤ x by omega) (show 1 ≤ y by omega)
      rw [htau]
      rw [hdimW] at hrho
      simpa [canonicalCorrectedDefectCount,
        canonicalResidualComponentCount, hchoice] using hrho
  | some c =>
      have hlocal :=
        localResidualTau_le_corrected_add_residual
          (M := M) (x := x) (y := y) (L := L)
          (a := c.1.1) (b := c.1.2)
          (h := pairChannelError x y c.1.1 c.1.2)
          (candidate_fst_pos c) (candidate_snd_pos c)
          (candidate_coprime c)
          hx hy hxM hyM rfl
      rw [residualTau_eq_localResidualTau_of_choice
        hx hy c hchoice]
      simpa [canonicalCorrectedDefectCount,
        canonicalResidualComponentCount, hchoice] using hlocal

/-- Canonical finite form of the vertex budget (6.5). -/
theorem canonicalCorrected_add_twice_residual_le
    (A x y L : ℕ)
    (hx : 1 ≤ x) (hy : 1 ≤ y) :
    canonicalCorrectedDefectCount A x y L +
        2 * canonicalResidualComponentCount A x y L ≤
      2 * (L + 1) := by
  generalize hchoice :
      canonicalReducedCandidate?
        x y (L + 1) ((L + 1) ^ A) = choice
  cases choice with
  | none =>
      have hbudget :=
        defectiveVertex_add_twice_nontrivial_le
          (L := L) hx hy
      simpa [canonicalCorrectedDefectCount,
        canonicalResidualComponentCount, hchoice] using hbudget
  | some c =>
      have hbudget :=
        corrected_add_twice_residual_le
          x y L c.1.1 c.1.2
          (pairChannelError x y c.1.1 c.1.2)
          hx hy
      simpa [canonicalCorrectedDefectCount,
        canonicalResidualComponentCount, hchoice] using hbudget

end

end ResidualComponentCounts
end PaperC
