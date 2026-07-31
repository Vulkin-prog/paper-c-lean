import PaperC.Asymptotics.CriticalRationalMass
import PaperC.Asymptotics.PropositionNineNine
import PaperC.Asymptotics.PropositionSevenThreeCritical
import PaperC.Asymptotics.PropositionSevenFourCritical
import PaperC.Asymptotics.PropositionSevenFiveCritical
import PaperC.Asymptotics.RationalPowerLittleO
import PaperC.Asymptotics.TheoremEightAlignedClosure
import PaperC.Combinatorics.CanonicalSectionElevenPartition

set_option maxHeartbeats 1800000

/-!
# Proposition 11.2: the separated two-block homogeneous mass

This module performs the exact finite assembly at the start of Section 11.
For every separated ordered pair it proves the natural-number identity

`2^ρ - 1 = (2^σ - 1) + 2^σ * (2^τ - 1)`.

It then sums this identity over the literal finite population of separated
dyadic pairs.  The residual summand is further disintegrated over the
canonical seven-sector partition of Lemma 11.1.  Both the cover and all
disjointness needed by this disintegration are theorems, not assumptions.

The first three residual sectors are connected to Propositions 7.3--7.5.
The aligned deep-core sector is eventually empty by the closed form of
Theorem 8.1.  Sector five is dominated by the literal population of
Proposition 9.9.  The remaining two asymptotic inputs are exposed by the
named propositions `NonterminalSectorMassStatement` and
`TerminalSectorMassStatement`.  They are internal assembly debts for
Proposition 9.11 and Theorem 10.1, respectively.

The final theorem is stated with the repository's fully quantified
`UniformLittleOOn`; no informal use of `o(N²)` is hidden in a comment.
-/

namespace PaperC
namespace PropositionElevenTwo

open scoped BigOperators
open Affine
open Affine.CanonicalRationalCode
open CanonicalSectionElevenPartition
open RationalMassFinite
open ResidualComponentCounts
open ResidualMasses
open SectionElevenPartition

noncomputable section

/-! ## The exact pointwise decomposition (11.1) -/

/--
The elementary natural-number identity underlying (11.1).

The proof explicitly accounts for truncated subtraction; both powers are
at least one.
-/
theorem two_pow_add_sub_one
    (σ τ : ℕ) :
    2 ^ (σ + τ) - 1 =
      (2 ^ σ - 1) + 2 ^ σ * (2 ^ τ - 1) := by
  have hσ : 1 ≤ 2 ^ σ := Nat.one_le_two_pow
  have hτ : 1 ≤ 2 ^ τ := Nat.one_le_two_pow
  have hprod : 1 ≤ 2 ^ σ * 2 ^ τ :=
    Nat.mul_pos (by omega) (by omega)
  rw [pow_add]
  apply Nat.cast_injective (R := ℤ)
  push_cast [Nat.cast_sub hσ, Nat.cast_sub hτ,
    Nat.cast_sub hprod]
  ring

/-- The full homogeneous weight `2^ρ-1` of a separated pair. -/
noncomputable def homogeneousWeight
    {N L : ℕ} (pair : SeparatedDyadicPair N L) : ℕ :=
  2 ^ pairRho pair - 1

/-- The systematic summand `2^σ-1` of a separated pair. -/
noncomputable def systematicWeight
    {N L : ℕ} (A : ℕ)
    (pair : SeparatedDyadicPair N L) : ℕ :=
  2 ^ pairSigma A pair - 1

/--
Literal pairwise form of (11.1):

`2^ρ-1 = (2^σ-1) + 2^σ(2^τ-1)`.
-/
theorem homogeneousWeight_eq_systematic_add_residual
    {N A L : ℕ} (hN : 2 ≤ N)
    (pair : SeparatedDyadicPair N L) :
    homogeneousWeight pair =
      systematicWeight A pair +
        linearResidualWeight A hN pair := by
  unfold homogeneousWeight systematicWeight linearResidualWeight
  rw [pairRho_eq_pairSigma_add_pairTau (A := A) hN pair]
  exact two_pow_add_sub_one
    (pairSigma A pair) (pairTau A hN pair)

/-! ## Literal finite masses -/

/-- The finite homogeneous mass over all separated ordered pairs. -/
noncomputable def homogeneousMassNat
    {N L : ℕ} (_hN : 2 ≤ N) : ℕ :=
  ∑ pair : SeparatedDyadicPair N L, homogeneousWeight pair

/-- The finite systematic mass over the same separated population. -/
noncomputable def systematicMassNat
    {N L : ℕ} (A : ℕ) (_hN : 2 ≤ N) : ℕ :=
  ∑ pair : SeparatedDyadicPair N L, systematicWeight A pair

/-- The finite residual mass over every separated pair. -/
noncomputable def residualMassNat
    {N L : ℕ} (A : ℕ) (hN : 2 ≤ N) : ℕ :=
  linearResidualMass (L := L) A hN Finset.univ

/-- Summed form of (11.1) on the literal finite pair population. -/
theorem homogeneousMassNat_eq_systematic_add_residual
    {N A L : ℕ} (hN : 2 ≤ N) :
    homogeneousMassNat (L := L) hN =
      systematicMassNat (L := L) A hN +
        residualMassNat (L := L) A hN := by
  unfold homogeneousMassNat systematicMassNat residualMassNat
    linearResidualMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro pair _hpair
  exact homogeneousWeight_eq_systematic_add_residual hN pair

/--
The subtype sum defining the systematic mass is exactly the base-two
rational mass of Proposition 5.4.
-/
theorem systematicMassNat_eq_rationalMass
    {N A L : ℕ} (hN : 2 ≤ N) :
    systematicMassNat (L := L) A hN =
      rationalMass N A L 2 := by
  classical
  unfold systematicMassNat systematicWeight rationalMass pairSigma
  symm
  apply Finset.sum_subtype
  intro pair
  rfl

/-! ## Proof-independent real totals -/

/--
The paper's separated homogeneous sum, with the finite range made literal.
Below the harmless threshold `N=2` it is set to zero.
-/
noncomputable def homogeneousMass
    (_A N L : ℕ) : ℝ :=
  if hN : 2 ≤ N then
    (homogeneousMassNat (L := L) hN : ℝ)
  else 0

/-- Proof-independent real systematic mass. -/
noncomputable def systematicMass
    (A N L : ℕ) : ℝ :=
  if hN : 2 ≤ N then
    (systematicMassNat (L := L) A hN : ℝ)
  else 0

/-- Proof-independent real residual mass. -/
noncomputable def residualMass
    (A N L : ℕ) : ℝ :=
  if hN : 2 ≤ N then
    (residualMassNat (L := L) A hN : ℝ)
  else 0

/-- Real-valued summed form of (11.1). -/
theorem homogeneousMass_eq_systematic_add_residual
    (A N L : ℕ) :
    homogeneousMass A N L =
      systematicMass A N L + residualMass A N L := by
  by_cases hN : 2 ≤ N
  · simp only [homogeneousMass, systematicMass, residualMass,
      dif_pos hN]
    exact_mod_cast
      homogeneousMassNat_eq_systematic_add_residual
        (A := A) (L := L) hN
  · simp [homogeneousMass, systematicMass, residualMass, hN]

/-- The public systematic total is the base-two rational mass. -/
theorem systematicMass_eq_rationalMass
    {A N L : ℕ} (hN : 2 ≤ N) :
    systematicMass A N L =
      (rationalMass N A L 2 : ℝ) := by
  simp only [systematicMass, dif_pos hN]
  exact_mod_cast systematicMassNat_eq_rationalMass
    (A := A) (L := L) hN

/-! ## Sector masses and exact disintegration -/

/-- The residual mass carried by one concrete Section 11 sector. -/
noncomputable def sectorResidualMassNat
    {N L : ℕ} (A : ℕ) (hN : 2 ≤ N)
    (smallRowRank : SeparatedDyadicPair N L → ℕ)
    (rankBudget : ℕ)
    (sector : ResidualSector) : ℕ :=
  linearResidualMass A hN
    (canonicalSectionElevenSectorPairs
      N A L hN smallRowRank rankBudget sector)

/--
Exact fiberwise disintegration of the residual mass over all seven sectors.
-/
theorem residualMassNat_eq_sum_sectors
    {N A L : ℕ} (hN : 2 ≤ N)
    (smallRowRank : SeparatedDyadicPair N L → ℕ)
    (rankBudget : ℕ) :
    residualMassNat (L := L) A hN =
      ∑ sector : ResidualSector,
        sectorResidualMassNat A hN
          smallRowRank rankBudget sector := by
  classical
  let tests :=
    canonicalSectionElevenTests
      N A L hN smallRowRank rankBudget
  let weight : SeparatedDyadicPair N L → ℕ :=
    linearResidualWeight A hN
  have hfiber :=
    Finset.sum_fiberwise
      (Finset.univ : Finset (SeparatedDyadicPair N L))
      (sectorOf tests)
      weight
  unfold residualMassNat linearResidualMass
  simpa only [tests, weight, sectorResidualMassNat,
    canonicalSectionElevenSectorPairs,
    sectorPopulation] using hfiber.symm

/--
Summation over the union of two distinct canonical sectors is additive.
This is the union-disjointness step used when the seven fiber sums are
expanded in manuscript order.
-/
theorem linearResidualMass_union_canonicalSectors
    {N A L : ℕ} (hN : 2 ≤ N)
    (smallRowRank : SeparatedDyadicPair N L → ℕ)
    (rankBudget : ℕ)
    {s t : ResidualSector} (hst : s ≠ t) :
    linearResidualMass A hN
        (canonicalSectionElevenSectorPairs
            N A L hN smallRowRank rankBudget s ∪
          canonicalSectionElevenSectorPairs
            N A L hN smallRowRank rankBudget t) =
      sectorResidualMassNat A hN smallRowRank rankBudget s +
        sectorResidualMassNat A hN smallRowRank rankBudget t := by
  simpa only [linearResidualMass, sectorResidualMassNat] using
    (Finset.sum_union
      (canonicalSectionElevenSectorPairs_disjoint
        hN smallRowRank rankBudget hst)
      (f := linearResidualWeight A hN))

/-! ## Proof-independent sector totals -/

/-- A family of concrete small-row ranks, uniform in the two parameters. -/
abbrev SmallRowRankFamily :=
  ∀ (N L : ℕ), SeparatedDyadicPair N L → ℕ

/-- A family of integer terminal budgets, uniform in `N,L`. -/
abbrev RankBudgetFamily := ℕ → ℕ → ℕ

/-- Proof-independent real mass of one canonical Section 11 sector. -/
noncomputable def sectorResidualMass
    (A : ℕ)
    (smallRowRank : SmallRowRankFamily)
    (rankBudget : RankBudgetFamily)
    (sector : ResidualSector)
    (N L : ℕ) : ℝ :=
  if hN : 2 ≤ N then
    (sectorResidualMassNat A hN
      (smallRowRank N L) (rankBudget N L) sector : ℝ)
  else 0

/-- Real-valued exact disintegration of the complete residual mass. -/
theorem residualMass_eq_sum_sectorResidualMass
    (A : ℕ)
    (smallRowRank : SmallRowRankFamily)
    (rankBudget : RankBudgetFamily)
    (N L : ℕ) :
    residualMass A N L =
      ∑ sector : ResidualSector,
        sectorResidualMass A smallRowRank rankBudget
          sector N L := by
  by_cases hN : 2 ≤ N
  · simp only [residualMass, sectorResidualMass, dif_pos hN]
    exact_mod_cast
      residualMassNat_eq_sum_sectors
        (A := A) (L := L) hN
        (smallRowRank N L) (rankBudget N L)
  · simp [residualMass, sectorResidualMass, hN]

/-- Sector one is literally the Proposition 7.3 residual mass. -/
theorem sectorResidualMass_smallPrimeProduct_eq
    (A : ℕ)
    (smallRowRank : SmallRowRankFamily)
    (rankBudget : RankBudgetFamily)
    (N L : ℕ) :
    sectorResidualMass A smallRowRank rankBudget
        .smallPrimeProduct N L =
      PropositionSevenThreeCritical.smallProductLinearResidualMassTotal
        A N L := by
  by_cases hN : 2 ≤ N
  · simp only [sectorResidualMass,
      PropositionSevenThreeCritical.smallProductLinearResidualMassTotal,
      dif_pos hN, sectorResidualMassNat]
    have hpop :
        canonicalSectionElevenSectorPairs
            N A L hN (smallRowRank N L) (rankBudget N L)
            .smallPrimeProduct =
          smallProductPairs N A L hN := by
      simpa only [canonicalSectionElevenSectorPairs,
        canonicalSectionElevenTests] using
        (sectionElevenSectorPairs_one_eq_smallProductPairs
          hN
          (fun pair ↦
            pair ∈ CanonicalTerminalPopulation.terminalPairsAtBudget
              N A L hN (smallRowRank N L) (rankBudget N L)))
    rw [hpop]
    rfl
  · simp [sectorResidualMass,
      PropositionSevenThreeCritical.smallProductLinearResidualMassTotal,
      hN]

/-- Sector two is literally the Proposition 7.4 residual mass. -/
theorem sectorResidualMass_smallCanonicalHeight_eq
    (A : ℕ)
    (smallRowRank : SmallRowRankFamily)
    (rankBudget : RankBudgetFamily)
    (N L : ℕ) :
    sectorResidualMass A smallRowRank rankBudget
        .smallCanonicalHeight N L =
      PropositionSevenFourCritical.smallHeightLargeProductLinearResidualMassTotal
        A N L := by
  by_cases hN : 2 ≤ N
  · simp only [sectorResidualMass,
      PropositionSevenFourCritical.smallHeightLargeProductLinearResidualMassTotal,
      dif_pos hN, sectorResidualMassNat]
    have hpop :
        canonicalSectionElevenSectorPairs
            N A L hN (smallRowRank N L) (rankBudget N L)
            .smallCanonicalHeight =
          SmallHeightLargeProductPairs.smallHeightLargeProductPairs
            N A L hN := by
      simpa only [canonicalSectionElevenSectorPairs,
        canonicalSectionElevenTests] using
        (sectionElevenSectorPairs_two_eq_smallHeightLargeProductPairs
          hN
          (fun pair ↦
            pair ∈ CanonicalTerminalPopulation.terminalPairsAtBudget
              N A L hN (smallRowRank N L) (rankBudget N L)))
    rw [hpop]
    rfl
  · simp [sectorResidualMass,
      PropositionSevenFourCritical.smallHeightLargeProductLinearResidualMassTotal,
      hN]

/-- Sector three is literally the Proposition 7.5 residual mass. -/
theorem sectorResidualMass_shallowCore_eq
    (A : ℕ)
    (smallRowRank : SmallRowRankFamily)
    (rankBudget : RankBudgetFamily)
    (N L : ℕ) :
    sectorResidualMass A smallRowRank rankBudget
        .shallowCore N L =
      PropositionSevenFiveCritical.shallowCoreLinearResidualMassTotal
        A N L := by
  by_cases hN : 2 ≤ N
  · simp only [sectorResidualMass,
      PropositionSevenFiveCritical.shallowCoreLinearResidualMassTotal,
      dif_pos hN, sectorResidualMassNat]
    have hpop :
        canonicalSectionElevenSectorPairs
            N A L hN (smallRowRank N L) (rankBudget N L)
            .shallowCore =
          ShallowCorePairs.shallowCorePairs N A L hN := by
      simpa only [canonicalSectionElevenSectorPairs,
        canonicalSectionElevenTests] using
        (sectionElevenSectorPairs_three_eq_shallowCorePairs
          hN
          (fun pair ↦
            pair ∈ CanonicalTerminalPopulation.terminalPairsAtBudget
              N A L hN (smallRowRank N L) (rankBudget N L)))
    rw [hpop]
    rfl
  · simp [sectorResidualMass,
      PropositionSevenFiveCritical.shallowCoreLinearResidualMassTotal,
      hN]

/-! ## The two deep-core sectors already controlled internally -/

/--
The concrete fifth sector is contained in the literal Proposition 9.9
population.  The inclusion is all that is needed for mass domination;
the converse would incorrectly identify `σ=0` with nonalignment.
-/
theorem manyDefectsSector_subset_propositionNineNine
    {N A L : ℕ} (hN : 2 ≤ N)
    (smallRowRank : SeparatedDyadicPair N L → ℕ)
    (rankBudget : ℕ) :
    canonicalSectionElevenSectorPairs
        N A L hN smallRowRank rankBudget .manyDefects ⊆
      PropositionNineNine.sigmaZeroDeepCoreAtLeastThreeDefectsPairs
        N A L hN := by
  intro pair hpair
  have hsector :
      canonicalSectionElevenSectorOf
          A hN smallRowRank rankBudget pair =
        .manyDefects :=
    mem_canonicalSectionElevenSectorPairs.mp hpair
  have h :
      HasLargeCanonicalPrimeProduct A hN pair ∧
        ¬SmallHeightLargeProductPairs.HasSmallCanonicalHeight
          A L pair.1.1 pair.1.2 ∧
        ¬ShallowCorePairs.HasCoreDensityAtMostThreeSixteenths
          A L pair.1.1 pair.1.2 ∧
        IsCanonicallyNonaligned
          A L pair.1.1 pair.1.2 ∧
        HasAtLeastThreeCorrectedDefects
          A L pair.1.1 pair.1.2 := by
    simpa only [canonicalSectionElevenSectorOf,
      canonicalSectionElevenTests] using
      (sectionElevenSectorOf_eq_five_iff.mp hsector)
  have hdeep :
      pair ∈ SectionSevenPartition.deepCorePairs N A L hN :=
    CanonicalSectionElevenPartition.mem_deepCorePairs_iff_sectionEleven_prefix.mpr
      ⟨h.1, h.2.1, h.2.2.1⟩
  exact
    PropositionNineNine.mem_sigmaZeroDeepCoreAtLeastThreeDefectsPairs.mpr
      ⟨hdeep,
        pairSigma_eq_zero_of_isCanonicallyNonaligned h.2.2.2.1,
        h.2.2.2.2⟩

/-- Finite fifth-sector mass is dominated by Proposition 9.9's mass. -/
theorem manyDefectsSectorResidualMassNat_le_propositionNineNine
    {N A L : ℕ} (hN : 2 ≤ N)
    (smallRowRank : SeparatedDyadicPair N L → ℕ)
    (rankBudget : ℕ) :
    sectorResidualMassNat A hN smallRowRank rankBudget
        .manyDefects ≤
      linearResidualMass A hN
        (PropositionNineNine.sigmaZeroDeepCoreAtLeastThreeDefectsPairs
          N A L hN) := by
  unfold sectorResidualMassNat linearResidualMass
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (manyDefectsSector_subset_propositionNineNine
      hN smallRowRank rankBudget)
    (fun _pair _hbig _hsmall ↦ Nat.zero_le _)

/-- Public fifth-sector domination by Proposition 9.9's real mass. -/
theorem sectorResidualMass_manyDefects_le
    {A N L : ℕ} (hN : 2 ≤ N)
    (smallRowRank : SmallRowRankFamily)
    (rankBudget : RankBudgetFamily) :
    sectorResidualMass A smallRowRank rankBudget
        .manyDefects N L ≤
      PropositionNineNine.linearMass A N L := by
  have hfinite :=
    manyDefectsSectorResidualMassNat_le_propositionNineNine
      (A := A) (L := L) hN
      (smallRowRank N L) (rankBudget N L)
  have hcast :
      (sectorResidualMassNat A hN
          (smallRowRank N L) (rankBudget N L)
          .manyDefects : ℝ) ≤
        (linearResidualMass A hN
          (PropositionNineNine.sigmaZeroDeepCoreAtLeastThreeDefectsPairs
            N A L hN) : ℝ) := by
    exact_mod_cast hfinite
  simpa only [sectorResidualMass, PropositionNineNine.linearMass,
    dif_pos hN] using hcast

/--
The fourth canonical sector is eventually empty in every fixed critical
window.  This is a direct population-level consequence of the unconditional
closure of Theorem 8.1.
-/
theorem alignedDeepCoreSector_eventually_empty
    {C : ℝ} (hC : 0 ≤ C) (A : ℕ)
    (smallRowRank : SmallRowRankFamily)
    (rankBudget : RankBudgetFamily) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧
      ∀ N ≥ N₀, ∀ L,
        CriticalRunWindow.InRunLengthWindow C N L →
        ∀ hNtwo : 2 ≤ N,
        canonicalSectionElevenSectorPairs
            N A L hNtwo
            (smallRowRank N L) (rankBudget N L)
            .alignedDeepCore =
          ∅ := by
  obtain ⟨Nalign, hNalign⟩ :=
    TheoremEightAlignedClosure.no_aligned_deep_core_eventually
      hC A
  refine ⟨max 2 Nalign, le_max_left _ _, ?_⟩
  intro N hN L hrun hNtwo
  have hNlarge : Nalign ≤ N := (le_max_right _ _).trans hN
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro pair hpair
  have hsector :
      canonicalSectionElevenSectorOf
          A hNtwo (smallRowRank N L) (rankBudget N L) pair =
        .alignedDeepCore :=
    mem_canonicalSectionElevenSectorPairs.mp
      hpair
  have h :
      HasLargeCanonicalPrimeProduct A hNtwo pair ∧
        ¬SmallHeightLargeProductPairs.HasSmallCanonicalHeight
          A L pair.1.1 pair.1.2 ∧
        ¬ShallowCorePairs.HasCoreDensityAtMostThreeSixteenths
          A L pair.1.1 pair.1.2 ∧
        IsCanonicallyAligned
          A L pair.1.1 pair.1.2 := by
    simpa only [canonicalSectionElevenSectorOf,
      canonicalSectionElevenTests] using
      (sectionElevenSectorOf_eq_four_iff.mp hsector)
  rcases h.2.2.2 with ⟨candidate, hchoice⟩
  have hpairData := mem_separatedDyadicPairs.mp pair.2
  have hcoords := pair_coordinates_two_le hNtwo pair
  have hcard :=
    CanonicalResidualComponents.card_residualComponents
      (x := pair.1.1) (y := pair.1.2) (L := L)
      (a := candidate.1.1) (b := candidate.1.2)
      (h := pairChannelError
        pair.1.1 pair.1.2 candidate.1.1 candidate.1.2)
      (candidate_fst_pos candidate)
      (candidate_snd_pos candidate)
      (candidate_coprime candidate)
      hcoords.1 hcoords.2 rfl
  have hdensity :
      3 * (L + 1) <
        16 *
          (CanonicalResidualComponents.residualComponents
            pair.1.1 pair.1.2 L candidate.1.1 candidate.1.2
            (pairChannelError
              pair.1.1 pair.1.2 candidate.1.1 candidate.1.2)).card := by
    rw [hcard]
    unfold ShallowCorePairs.HasCoreDensityAtMostThreeSixteenths at h
    have hcount :
        3 * (L + 1) <
          16 * canonicalResidualComponentCount
            A pair.1.1 pair.1.2 L := by omega
    simpa only [canonicalResidualComponentCount, hchoice] using hcount
  exact
    hNalign N hNlarge L hrun
      ((L + 1) ^ A)
      (Nat.one_le_pow _ _ (by omega))
      le_rfl
      pair.1.1 hpairData.1
      pair.1.2 hpairData.2.1
      candidate hdensity

/-! ## Uniform little-oh closure tools -/

/-- Uniform little-oh is stable under pointwise addition. -/
theorem uniformLittleOOn_add
    {admissible : ℕ → ℕ → Prop}
    {f g scale : ℕ → ℕ → ℝ}
    (hf : UniformLittleOOn admissible f scale)
    (hg : UniformLittleOOn admissible g scale) :
    UniformLittleOOn admissible
      (fun N L ↦ f N L + g N L) scale := by
  intro ε hε
  have hhalf : 0 < ε / 2 := by positivity
  obtain ⟨Nf, hNf⟩ := hf (ε / 2) hhalf
  obtain ⟨Ng, hNg⟩ := hg (ε / 2) hhalf
  refine ⟨max Nf Ng, ?_⟩
  intro N hN L hNL
  calc
    |f N L + g N L| ≤ |f N L| + |g N L| :=
      abs_add _ _
    _ ≤
        (ε / 2) * |scale N L| +
          (ε / 2) * |scale N L| :=
      add_le_add
        (hNf N ((le_max_left _ _).trans hN) L hNL)
        (hNg N ((le_max_right _ _).trans hN) L hNL)
    _ = ε * |scale N L| := by ring

/-- A finite sum of uniformly little-oh families is uniformly little-oh. -/
theorem uniformLittleOOn_finset_sum
    {ι : Type*}
    {admissible : ℕ → ℕ → Prop}
    {F : ι → ℕ → ℕ → ℝ}
    {scale : ℕ → ℕ → ℝ}
    (s : Finset ι)
    (hF :
      ∀ i ∈ s, UniformLittleOOn admissible (F i) scale) :
    UniformLittleOOn admissible
      (fun N L ↦ ∑ i ∈ s, F i N L) scale := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa only [Finset.sum_empty] using
        uniformLittleOOn_zero admissible scale
  | @insert i s hi ih =>
      have hhead := hF i (Finset.mem_insert_self i s)
      have htail :
          ∀ j ∈ s,
            UniformLittleOOn admissible (F j) scale := by
        intro j hj
        exact hF j (Finset.mem_insert_of_mem hj)
      have hsum := uniformLittleOOn_add hhead (ih htail)
      simpa only [Finset.sum_insert hi] using hsum

/-- Fintype-indexed specialization of finite little-oh summation. -/
theorem uniformLittleOOn_fintype_sum
    {ι : Type*} [Fintype ι]
    {admissible : ℕ → ℕ → Prop}
    {F : ι → ℕ → ℕ → ℝ}
    {scale : ℕ → ℕ → ℝ}
    (hF :
      ∀ i, UniformLittleOOn admissible (F i) scale) :
    UniformLittleOOn admissible
      (fun N L ↦ ∑ i, F i N L) scale := by
  classical
  apply uniformLittleOOn_finset_sum Finset.univ
  intro i _hi
  exact hF i

/-! ## Closed sectors and named remaining interfaces -/

/-- Proposition 5.4 gives the required systematic little-oh estimate. -/
theorem systematicMass_uniformLittleOQuadratic
    {C : ℝ} (hC : 0 ≤ C) (A : ℕ) (hA : 1 ≤ A) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (systematicMass A)
      (fun N _ ↦ (N : ℝ) ^ 2) := by
  have hfourThird :
      UniformRationalPowerSubpolynomialOn 4 3
        (CriticalRunWindow.InRunLengthWindow C)
        (systematicMass A) := by
    apply UniformRationalPower.mono
      (CriticalRationalMass.rationalMass_two_uniformFourThird
        hC A hA)
    refine ⟨2, ?_⟩
    intro N hN L _hrun
    have hsys : 0 ≤ systematicMass A N L := by
      simp [systematicMass, hN]
    have hrat : 0 ≤ (rationalMass N A L 2 : ℝ) := by
      positivity
    rw [abs_of_nonneg hsys, abs_of_nonneg hrat,
      systematicMass_eq_rationalMass hN]
  exact UniformRationalPower.littleO_natPower_of_lt
    (p := 4) (q := 3) (r := 2) (by omega) hfourThird

/-- Sector one is little-oh of the quadratic scale. -/
theorem smallPrimeProductSector_uniformLittleOQuadratic
    {C : ℝ} (hC : 0 ≤ C) (A : ℕ)
    (smallRowRank : SmallRowRankFamily)
    (rankBudget : RankBudgetFamily) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (sectorResidualMass A smallRowRank rankBudget
        .smallPrimeProduct)
      (fun N _ ↦ (N : ℝ) ^ 2) := by
  have hrate :=
    PropositionSevenThreeCritical.smallProductLinearResidualMass_uniformSevenFourths
      hC A
  have hlittle :=
    UniformRationalPower.littleO_natPower_of_lt
      (p := 7) (q := 4) (r := 2) (by omega) hrate
  have heq :
      sectorResidualMass A smallRowRank rankBudget
          .smallPrimeProduct =
        PropositionSevenThreeCritical.smallProductLinearResidualMassTotal
          A := by
    funext N L
    exact sectorResidualMass_smallPrimeProduct_eq
      A smallRowRank rankBudget N L
  rw [heq]
  exact hlittle

/-- Sector two is little-oh of the quadratic scale. -/
theorem smallCanonicalHeightSector_uniformLittleOQuadratic
    {C : ℝ} (hC : 0 ≤ C) (A : ℕ) (hA : 1 ≤ A)
    (smallRowRank : SmallRowRankFamily)
    (rankBudget : RankBudgetFamily) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (sectorResidualMass A smallRowRank rankBudget
        .smallCanonicalHeight)
      (fun N _ ↦ (N : ℝ) ^ 2) := by
  have heq :
      sectorResidualMass A smallRowRank rankBudget
          .smallCanonicalHeight =
        PropositionSevenFourCritical.smallHeightLargeProductLinearResidualMassTotal
          A := by
    funext N L
    exact sectorResidualMass_smallCanonicalHeight_eq
      A smallRowRank rankBudget N L
  rw [heq]
  exact
    PropositionSevenFourCritical.smallHeightLargeProductLinearResidualMass_uniformLittleOQuadratic
      hC A hA

/-- Sector three is little-oh of the quadratic scale. -/
theorem shallowCoreSector_uniformLittleOQuadratic
    {C : ℝ} (hC : 0 ≤ C) (A : ℕ)
    (smallRowRank : SmallRowRankFamily)
    (rankBudget : RankBudgetFamily) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (sectorResidualMass A smallRowRank rankBudget
        .shallowCore)
      (fun N _ ↦ (N : ℝ) ^ 2) := by
  have heq :
      sectorResidualMass A smallRowRank rankBudget
          .shallowCore =
        PropositionSevenFiveCritical.shallowCoreLinearResidualMassTotal
          A := by
    funext N L
    exact sectorResidualMass_shallowCore_eq
      A smallRowRank rankBudget N L
  rw [heq]
  exact
    PropositionSevenFiveCritical.shallowCoreLinearResidualMass_uniformLittleOQuadratic
      hC A

/-- The eventually empty aligned sector has zero asymptotic mass. -/
theorem alignedDeepCoreSector_uniformLittleOQuadratic
    {C : ℝ} (hC : 0 ≤ C) (A : ℕ)
    (smallRowRank : SmallRowRankFamily)
    (rankBudget : RankBudgetFamily) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (sectorResidualMass A smallRowRank rankBudget
        .alignedDeepCore)
      (fun N _ ↦ (N : ℝ) ^ 2) := by
  obtain ⟨Nempty, hNemptyTwo, hNempty⟩ :=
    alignedDeepCoreSector_eventually_empty
      hC A smallRowRank rankBudget
  intro ε hε
  refine ⟨Nempty, ?_⟩
  intro N hN L hrun
  have hNtwo : 2 ≤ N := hNemptyTwo.trans hN
  have hempty :=
    hNempty N hN L hrun hNtwo
  have hmass :
      sectorResidualMass A smallRowRank rankBudget
          .alignedDeepCore N L = 0 := by
    simp only [sectorResidualMass, dif_pos hNtwo,
      sectorResidualMassNat, hempty, linearResidualMass,
      Finset.sum_empty, Nat.cast_zero]
  rw [hmass, abs_zero]
  exact mul_nonneg hε.le (abs_nonneg _)

/-- Sector five is little-oh, conditional only on Proposition 9.9's host count. -/
theorem manyDefectsSector_uniformLittleOQuadratic
    {C : ℝ} (hC : 0 ≤ C) (A : ℕ)
    (smallRowRank : SmallRowRankFamily)
    (rankBudget : RankBudgetFamily)
    (hhosts : PropositionNineNine.HostCountStatement C A) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (sectorResidualMass A smallRowRank rankBudget
        .manyDefects)
      (fun N _ ↦ (N : ℝ) ^ 2) := by
  have hthreeHalves :
      UniformThreeHalvesSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C)
        (sectorResidualMass A smallRowRank rankBudget
          .manyDefects) := by
    apply UniformThreeHalves.mono
      (PropositionNineNine.proposition_nine_nine_uniformThreeHalves
        hC A hhosts)
    refine ⟨2, ?_⟩
    intro N hN L _hrun
    have hleft :
        0 ≤ sectorResidualMass A smallRowRank rankBudget
          .manyDefects N L := by
      simp [sectorResidualMass, hN]
    have hright : 0 ≤ PropositionNineNine.linearMass A N L := by
      simp [PropositionNineNine.linearMass, hN]
    rw [abs_of_nonneg hleft, abs_of_nonneg hright]
    exact sectorResidualMass_manyDefects_le
      hN smallRowRank rankBudget
  have hrational :
      UniformRationalPowerSubpolynomialOn 3 2
        (CriticalRunWindow.InRunLengthWindow C)
        (sectorResidualMass A smallRowRank rankBudget
          .manyDefects) := by
    simpa only [UniformThreeHalvesSubpolynomialOn,
      UniformRationalPowerSubpolynomialOn] using hthreeHalves
  exact UniformRationalPower.littleO_natPower_of_lt
    (p := 3) (q := 2) (r := 2) (by omega) hrational

/--
Named internal interface for Proposition 9.11's sixth-sector mass.
It is exactly the manuscript's `o_C(N²)` conclusion, with every quantifier
made explicit; no stronger power bound is inserted.
-/
/- AUDIT_BRIDGE
{
  "id": "PCv07c-P9.11-nonterminal-sector-mass",
  "kind": "internal",
  "status": "open",
  "lean_name": "PaperC.PropositionElevenTwo.NonterminalSectorMassStatement",
  "citation": {
    "authors": ["Brice Pouly"],
    "title": "Loi de Poisson critique dans un bloc dyadique — Débuts de longues plages constantes d’une fonction aléatoire complètement multiplicative de Rademacher étendue",
    "version": "7c, juillet 2026",
    "target_pdf_sha256": "23a5db3c8d024cab3fb8ca9f8f1443f40cf9502b1fb6682a331f5948f57a3336",
    "locator": "Proposition 9.11, énoncé, p. 33"
  },
  "source_statement": {
    "verbatim": "Il existe une constante K = K(A, C) > 0, fixée avant N, telle que la masse du coeur profond non aligné en dehors de T_K soit o_C(N^2).",
    "source_url": "paper_C_complete_v07c.pdf#page=33",
    "verification": "manual_primary_source_check_required"
  },
  "manuscript_locator": {
    "result": "Proposition 9.11",
    "equation": "mass outside T_K",
    "pages": "33"
  },
  "formalization_relation": "legacy arbitrary-family API: its canonical bounded-ratio instance is absorbed by the proved nonterminal assembly and therefore does not propagate to canonical theorem-level endpoints; the unrestricted smallRowRank/rankBudget statement remains open and nonblocking"
}
AUDIT_BRIDGE -/
def NonterminalSectorMassStatement
    (C : ℝ) (A : ℕ)
    (smallRowRank : SmallRowRankFamily)
    (rankBudget : RankBudgetFamily) : Prop :=
  UniformLittleOOn
    (CriticalRunWindow.InRunLengthWindow C)
    (sectorResidualMass A smallRowRank rankBudget
      .nonterminal)
    (fun N _ ↦ (N : ℝ) ^ 2)

/--
The seventh sector is a subset of the complete integer-budget terminal
population used by Theorem 10.1.
-/
theorem terminalSector_subset_terminalPairsAtBudget
    {N A L : ℕ} (hN : 2 ≤ N)
    (smallRowRank : SeparatedDyadicPair N L → ℕ)
    (rankBudget : ℕ) :
    canonicalSectionElevenSectorPairs
        N A L hN smallRowRank rankBudget .terminal ⊆
      CanonicalTerminalPopulation.terminalPairsAtBudget
        N A L hN smallRowRank rankBudget := by
  classical
  rw [canonicalSectionElevenSectorPairs_terminal_eq_filter
    hN smallRowRank rankBudget]
  exact Finset.filter_subset _ _

/-- Finite terminal-sector mass is bounded by the full terminal mass. -/
theorem terminalSectorResidualMassNat_le_terminalResidualMassAtBudget
    {N A L : ℕ} (hN : 2 ≤ N)
    (smallRowRank : SeparatedDyadicPair N L → ℕ)
    (rankBudget : ℕ) :
    sectorResidualMassNat A hN smallRowRank rankBudget
        .terminal ≤
      CanonicalTerminalPopulation.terminalResidualMassAtBudget
        N A L hN smallRowRank rankBudget := by
  unfold sectorResidualMassNat
    CanonicalTerminalPopulation.terminalResidualMassAtBudget
    linearResidualMass
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (terminalSector_subset_terminalPairsAtBudget
      hN smallRowRank rankBudget)
    (fun _pair _hbig _hsmall ↦ Nat.zero_le _)

/--
Concrete Step 4 of Theorem 10.1, now specialized to the actual seventh
sector of Lemma 11.1.
-/
theorem terminalSectorResidualMassNat_le_card_mul_weight
    {N A L : ℕ} (hN : 2 ≤ N)
    (smallRowRank : SeparatedDyadicPair N L → ℕ)
    (rankBudget : ℕ) :
    sectorResidualMassNat A hN smallRowRank rankBudget
        .terminal ≤
      (CanonicalTerminalPopulation.terminalPairsAtBudget
          N A L hN smallRowRank rankBudget).card *
        (4 * 2 ^ (L + 1)) :=
  (terminalSectorResidualMassNat_le_terminalResidualMassAtBudget
      hN smallRowRank rankBudget).trans
    (CanonicalTerminalPopulation.terminalResidualMassAtBudget_le
      hN smallRowRank rankBudget)

/--
Named internal interface for Theorem 10.1's terminal weighted mass.
The exponent is the manuscript's `N^(7/4+o_C(1))`.
-/
/- AUDIT_BRIDGE
{
  "id": "PCv07c-T10.1-terminal-sector-mass",
  "kind": "internal",
  "status": "open",
  "lean_name": "PaperC.PropositionElevenTwo.TerminalSectorMassStatement",
  "citation": {
    "authors": ["Brice Pouly"],
    "title": "Loi de Poisson critique dans un bloc dyadique — Débuts de longues plages constantes d’une fonction aléatoire complètement multiplicative de Rademacher étendue",
    "version": "7c, juillet 2026",
    "target_pdf_sha256": "23a5db3c8d024cab3fb8ca9f8f1443f40cf9502b1fb6682a331f5948f57a3336",
    "locator": "Théorème 10.1, équation (10.2), p. 34 ; démonstration, étape 4, p. 36"
  },
  "source_statement": {
    "verbatim": "et ∑_{(x,y)∈T_K} (2^{τ(x,y)} − 1) ≤ N^{7/4+o_C(1)} = o(N^2).",
    "source_url": "paper_C_complete_v07c.pdf#page=34",
    "verification": "manual_primary_source_check_required"
  },
  "manuscript_locator": {
    "result": "Theorem 10.1",
    "equation": "(10.2)",
    "pages": "34–36"
  },
  "formalization_relation": "legacy arbitrary-family endpoint: the canonical terminal population and bounded-ratio summation are proved and bypass this interface in every canonical theorem-level route; no exact transport for arbitrary smallRowRank/rankBudget is claimed, so the generic bridge remains open and nonblocking"
}
AUDIT_BRIDGE -/
def TerminalSectorMassStatement
    (C : ℝ) (A : ℕ)
    (smallRowRank : SmallRowRankFamily)
    (rankBudget : RankBudgetFamily) : Prop :=
  UniformRationalPowerSubpolynomialOn 7 4
    (CriticalRunWindow.InRunLengthWindow C)
    (sectorResidualMass A smallRowRank rankBudget
      .terminal)

/-- The named sixth-sector interface implies quadratic little-oh. -/
theorem nonterminalSector_uniformLittleOQuadratic
    {C : ℝ} {A : ℕ}
    {smallRowRank : SmallRowRankFamily}
    {rankBudget : RankBudgetFamily}
    (hnonterminal :
      NonterminalSectorMassStatement
        C A smallRowRank rankBudget) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (sectorResidualMass A smallRowRank rankBudget
        .nonterminal)
      (fun N _ ↦ (N : ℝ) ^ 2) :=
  hnonterminal

/-- The named seventh-sector interface implies quadratic little-oh. -/
theorem terminalSector_uniformLittleOQuadratic
    {C : ℝ} {A : ℕ}
    {smallRowRank : SmallRowRankFamily}
    {rankBudget : RankBudgetFamily}
    (hterminal :
      TerminalSectorMassStatement
        C A smallRowRank rankBudget) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (sectorResidualMass A smallRowRank rankBudget
        .terminal)
      (fun N _ ↦ (N : ℝ) ^ 2) :=
  UniformRationalPower.littleO_natPower_of_lt
    (p := 7) (q := 4) (r := 2) (by omega) hterminal

/--
All seven residual sectors are uniformly negligible once the three named
deep-nonaligned inputs have been supplied.
-/
theorem everySector_uniformLittleOQuadratic
    {C : ℝ} (hC : 0 ≤ C) (A : ℕ) (hA : 1 ≤ A)
    (smallRowRank : SmallRowRankFamily)
    (rankBudget : RankBudgetFamily)
    (hhosts : PropositionNineNine.HostCountStatement C A)
    (hnonterminal :
      NonterminalSectorMassStatement
        C A smallRowRank rankBudget)
    (hterminal :
      TerminalSectorMassStatement
        C A smallRowRank rankBudget) :
    ∀ sector : ResidualSector,
      UniformLittleOOn
        (CriticalRunWindow.InRunLengthWindow C)
        (sectorResidualMass A smallRowRank rankBudget sector)
        (fun N _ ↦ (N : ℝ) ^ 2) := by
  intro sector
  cases sector with
  | smallPrimeProduct =>
      exact smallPrimeProductSector_uniformLittleOQuadratic
        hC A smallRowRank rankBudget
  | smallCanonicalHeight =>
      exact smallCanonicalHeightSector_uniformLittleOQuadratic
        hC A hA smallRowRank rankBudget
  | shallowCore =>
      exact shallowCoreSector_uniformLittleOQuadratic
        hC A smallRowRank rankBudget
  | alignedDeepCore =>
      exact alignedDeepCoreSector_uniformLittleOQuadratic
        hC A smallRowRank rankBudget
  | manyDefects =>
      exact manyDefectsSector_uniformLittleOQuadratic
        hC A smallRowRank rankBudget hhosts
  | nonterminal =>
      exact nonterminalSector_uniformLittleOQuadratic hnonterminal
  | terminal =>
      exact terminalSector_uniformLittleOQuadratic hterminal

/--
Conditional closure of the complete residual term in (11.1).
-/
theorem residualMass_uniformLittleOQuadratic
    {C : ℝ} (hC : 0 ≤ C) (A : ℕ) (hA : 1 ≤ A)
    (smallRowRank : SmallRowRankFamily)
    (rankBudget : RankBudgetFamily)
    (hhosts : PropositionNineNine.HostCountStatement C A)
    (hnonterminal :
      NonterminalSectorMassStatement
        C A smallRowRank rankBudget)
    (hterminal :
      TerminalSectorMassStatement
        C A smallRowRank rankBudget) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (residualMass A)
      (fun N _ ↦ (N : ℝ) ^ 2) := by
  have hsum :
      UniformLittleOOn
        (CriticalRunWindow.InRunLengthWindow C)
        (fun N L ↦
          ∑ sector : ResidualSector,
            sectorResidualMass A smallRowRank rankBudget
              sector N L)
        (fun N _ ↦ (N : ℝ) ^ 2) :=
    uniformLittleOOn_fintype_sum
      (everySector_uniformLittleOQuadratic
        hC A hA smallRowRank rankBudget
        hhosts hnonterminal hterminal)
  have heq :
      residualMass A =
        fun N L ↦
          ∑ sector : ResidualSector,
            sectorResidualMass A smallRowRank rankBudget
              sector N L := by
    funext N L
    exact residualMass_eq_sum_sectorResidualMass
      A smallRowRank rankBudget N L
  rw [heq]
  exact hsum

/--
Proposition 11.2 in fully quantified conditional form.

The conclusion is the literal homogeneous sum over separated ordered pairs.
The systematic term and sectors one through four are unconditional; sector
five uses the named host-count interface of Proposition 9.9; sectors six and
seven use the two explicit internal statements above.
-/
theorem proposition_eleven_two_uniformLittleOQuadratic
    {C : ℝ} (hC : 0 ≤ C) (A : ℕ) (hA : 1 ≤ A)
    (smallRowRank : SmallRowRankFamily)
    (rankBudget : RankBudgetFamily)
    (hhosts : PropositionNineNine.HostCountStatement C A)
    (hnonterminal :
      NonterminalSectorMassStatement
        C A smallRowRank rankBudget)
    (hterminal :
      TerminalSectorMassStatement
        C A smallRowRank rankBudget) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (homogeneousMass A)
      (fun N _ ↦ (N : ℝ) ^ 2) := by
  have hsystematic :=
    systematicMass_uniformLittleOQuadratic hC A hA
  have hresidual :=
    residualMass_uniformLittleOQuadratic
      hC A hA smallRowRank rankBudget
      hhosts hnonterminal hterminal
  have hsum := uniformLittleOOn_add hsystematic hresidual
  have heq :
      homogeneousMass A =
        fun N L ↦
          systematicMass A N L + residualMass A N L := by
    funext N L
    exact homogeneousMass_eq_systematic_add_residual A N L
  rw [heq]
  exact hsum

end

end PropositionElevenTwo
end PaperC
