import PaperC.Asymptotics.BoundedRatioCorrectedDefectEnvelope
import PaperC.Asymptotics.BoundedRatioSectorClosure
import PaperC.Asymptotics.PropositionNineNine
import PaperC.Asymptotics.RationalPowerLittleO
import PaperC.Combinatorics.CanonicalSectionElevenPartition

set_option maxHeartbeats 3600000

/-!
# Finite reduction of the bounded-ratio many-defects sector

This file carries out the parts of Lemma 17.26 that follow from the current
repository without a new arithmetic input.

For the literal fifth fibre of the ordered Section 17 classifier, Lean proves
that

* nonalignment forces the systematic exponent to vanish;
* one of the two start windows contains at least two concrete defects;
* the deep-core density supplies a canonical residual component on between
  two and ten vertices;
* zero-mass pairs may be deleted;
* the remaining linear mass is bounded by the active host count times a
  common `N^(1+o)` residual-weight envelope.

The final theorem below is deliberately parametrized by an endpoint-independent
`N^(1/2+o)` envelope for the two oriented active-host populations.  The
downstream modules `BoundedRatioManyDefectsDegreeTwoSum`,
`BoundedRatioManyDefectsEvertseSum`, `BoundedRatioManyDefectsDegreeAssembly`
and `BoundedRatioManyDefectsAssembly` construct that envelope from the
registered Evertse--Silverman and generalized-Pell inputs and close Lemma
17.26.  No replacement bridge is introduced here.
-/

namespace PaperC
namespace BoundedRatioManyDefectsReduction

open Affine
open BoundedRatioCorrectedDefectEnvelope
open BoundedRatioResidualMasses
open CanonicalResidualComponents
open LargePrimeGraph
open LargePrimeGraphResolution
open LargePrimeOccurrences
open PropositionSixteenOne
open ResidualComponentCounts
open SectionElevenPartition

noncomputable section

noncomputable local instance instDecidableLargePrimeAdj
    (x y L : ℕ) :
    DecidableRel (largePrimeGraph x y L).Adj :=
  Classical.decRel _

/-! ## Exact data carried by the fifth sector -/

/--
The literal fifth-sector test data, together with activity of the residual
weight.
-/
theorem manyDefects_tests_of_mem_active
    {N M A L : ℕ} {hN : 2 ≤ N}
    {terminal : TerminalPredicateFamily}
    {pair : SeparatedBoundedRatioPair N M L}
    (hpair :
      pair ∈
        activeSectorPairs
          N M A L hN terminal .manyDefects) :
    (¬HasSmallCanonicalPrimeProduct A hN pair) ∧
      (¬SmallHeightLargeProductPairs.HasSmallCanonicalHeight
        A L pair.1.1 pair.1.2) ∧
      (¬ShallowCorePairs.HasCoreDensityAtMostThreeSixteenths
        A L pair.1.1 pair.1.2) ∧
      (¬IsCanonicallyAligned A L pair.1.1 pair.1.2) ∧
      HasAtLeastThreeCorrectedDefects
        A L pair.1.1 pair.1.2 ∧
      0 < pairTau A hN pair := by
  have hactive := mem_activeSectorPairs.mp hpair
  have hsector :
      sectorOf
          (boundedRatioSectorTests N M A L hN terminal)
          pair =
        .manyDefects := by
    simpa only [boundedRatioSectorOf] using hactive.1
  have htests :=
    (sectorOf_eq_manyDefects_iff
      (tests := boundedRatioSectorTests N M A L hN terminal)
      (z := pair)).mp hsector
  rcases htests with
    ⟨hproduct, hheight, hdensity, haligned, hdefects⟩
  simpa only [boundedRatioSectorTests] using
    And.intro hproduct
      (And.intro hheight
        (And.intro hdensity
          (And.intro haligned
            (And.intro hdefects hactive.2))))

/-- Every active fifth-sector pair is canonically nonaligned. -/
theorem isCanonicallyNonaligned_of_mem_active
    {N M A L : ℕ} {hN : 2 ≤ N}
    {terminal : TerminalPredicateFamily}
    {pair : SeparatedBoundedRatioPair N M L}
    (hpair :
      pair ∈
        activeSectorPairs
          N M A L hN terminal .manyDefects) :
    IsCanonicallyNonaligned
      A L pair.1.1 pair.1.2 := by
  exact
    not_isCanonicallyAligned_iff_nonaligned.mp
      (manyDefects_tests_of_mem_active hpair).2.2.2.1

/-- Nonalignment makes the systematic exponent of the fifth sector zero. -/
theorem pairSigma_eq_zero_of_mem_active
    {N M A L : ℕ} {hN : 2 ≤ N}
    {terminal : TerminalPredicateFamily}
    {pair : SeparatedBoundedRatioPair N M L}
    (hpair :
      pair ∈
        activeSectorPairs
          N M A L hN terminal .manyDefects) :
    pairSigma A pair = 0 := by
  have hnonaligned :=
    isCanonicallyNonaligned_of_mem_active hpair
  unfold IsCanonicallyNonaligned at hnonaligned
  unfold pairSigma
  simp [RationalMassFinite.canonicalPairSigma,
    Affine.CanonicalRationalCode.canonicalMultiplicity,
    hnonaligned]

/-- Every active fifth-sector pair has at least three corrected defects. -/
theorem three_le_correctedDefectCount_of_mem_active
    {N M A L : ℕ} {hN : 2 ≤ N}
    {terminal : TerminalPredicateFamily}
    {pair : SeparatedBoundedRatioPair N M L}
    (hpair :
      pair ∈
        activeSectorPairs
          N M A L hN terminal .manyDefects) :
    3 ≤ canonicalCorrectedDefectCount
      A pair.1.1 pair.1.2 L := by
  exact (manyDefects_tests_of_mem_active hpair).2.2.2.2.1

/--
The strict deep-core test is the integer density
`3(L+1) < 16 c#`.
-/
theorem deepCore_density_of_mem_active
    {N M A L : ℕ} {hN : 2 ≤ N}
    {terminal : TerminalPredicateFamily}
    {pair : SeparatedBoundedRatioPair N M L}
    (hpair :
      pair ∈
        activeSectorPairs
          N M A L hN terminal .manyDefects) :
    3 * (L + 1) <
      16 * canonicalResidualComponentCount
        A pair.1.1 pair.1.2 L := by
  have hnot :=
    (manyDefects_tests_of_mem_active hpair).2.2.1
  unfold ShallowCorePairs.HasCoreDensityAtMostThreeSixteenths at hnot
  omega

/--
Every active fifth-sector pair satisfies any rational density no stronger
than the literal strict `3/16` test.  The cross-multiplication hypothesis is
the denominator-free form of `alphaNum / alphaDen ≤ 3 / 16`.
-/
theorem rational_deepCore_density_of_mem_active
    {N M A L alphaNum alphaDen : ℕ} {hN : 2 ≤ N}
    {terminal : TerminalPredicateFamily}
    {pair : SeparatedBoundedRatioPair N M L}
    (hpair :
      pair ∈
        activeSectorPairs
          N M A L hN terminal .manyDefects)
    (hden : 0 < alphaDen)
    (hratio : 16 * alphaNum ≤ 3 * alphaDen) :
    alphaNum * (L + 1) ≤
      alphaDen * canonicalResidualComponentCount
        A pair.1.1 pair.1.2 L := by
  exact
    PaperC.PropositionNineNineHostGeometry.rational_density_of_three_sixteenths
      hden (deepCore_density_of_mem_active hpair) hratio

/--
At least one of the two concrete start windows contains two defective
values.
-/
theorem two_defects_in_one_window_of_mem_active
    {N M A L : ℕ} {hN : 2 ≤ N}
    {terminal : TerminalPredicateFamily}
    {pair : SeparatedBoundedRatioPair N M L}
    (hpair :
      pair ∈
        activeSectorPairs
          N M A L hN terminal .manyDefects) :
    2 ≤
        (IntervalDefectBound.defectsInInterval
          (L + 1) (pair.1.1 - 1)).card ∨
      2 ≤
        (IntervalDefectBound.defectsInInterval
          (L + 1) (pair.1.2 - 1)).card := by
  have hcoords := pair_coordinates_two_le hN pair
  exact
    PaperC.PropositionNineNineHostGeometry.two_le_one_defectInterval_of_three_le_corrected
      A (by omega) (by omega)
      (three_le_correctedDefectCount_of_mem_active hpair)

/--
Exact rational-density extraction for a bounded-ratio host.  This theorem
does not depend on the fifth-sector classifier: callers provide the density
and cutoff inequalities explicitly.
-/
theorem exists_bounded_component_of_rational_density
    {N M A L alphaNum alphaDen K : ℕ}
    (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L)
    (hden : 0 < alphaDen)
    (hdensity :
      alphaNum * (L + 1) ≤
        alphaDen * canonicalResidualComponentCount
          A pair.1.1 pair.1.2 L)
    (hcutoff :
      2 * alphaDen < alphaNum * (K + 1)) :
    ∃ C ∈
        canonicalResidualComponents
          A pair.1.1 pair.1.2 L,
      2 ≤ Fintype.card C.supp ∧
        Fintype.card C.supp ≤ K := by
  classical
  have hcoords := pair_coordinates_two_le hN pair
  have hcard :
      (canonicalResidualComponents
          A pair.1.1 pair.1.2 L).card =
        canonicalResidualComponentCount
          A pair.1.1 pair.1.2 L :=
    card_canonicalResidualComponents hcoords.1 hcoords.2
  have hdensityFamily :
      alphaNum * (L + 1) ≤
        alphaDen *
          (canonicalResidualComponents
            A pair.1.1 pair.1.2 L).card := by
    rw [hcard]
    exact hdensity
  have hambient :
      Fintype.card (Occurrence L) ≤ 2 * (L + 1) := by
    rw [card_occurrence]
  apply
    PaperC.DeepCoreSmallComponent.exists_bounded_connectedComponent_of_rational_density
      (largePrimeGraph pair.1.1 pair.1.2 L)
      (canonicalResidualComponents
        A pair.1.1 pair.1.2 L)
      (B := L + 1) (alphaNum := alphaNum)
      (alphaDen := alphaDen) (K := K)
      (Nat.succ_pos L) hden hambient
  · intro C hC
    exact
      (isNontrivialUnpinnedComponent_of_mem_canonicalResidualComponents
        hC).2
  · exact hdensityFamily
  · exact hcutoff

/--
The active fifth-sector deep-core test supplies a bounded component at every
weaker rational density and every compatible integer cutoff.
-/
theorem exists_bounded_component_of_mem_active_of_deepCore_rational_density
    {N M A L alphaNum alphaDen K : ℕ} {hN : 2 ≤ N}
    {terminal : TerminalPredicateFamily}
    {pair : SeparatedBoundedRatioPair N M L}
    (hpair :
      pair ∈
        activeSectorPairs
          N M A L hN terminal .manyDefects)
    (hden : 0 < alphaDen)
    (hratio : 16 * alphaNum ≤ 3 * alphaDen)
    (hcutoff :
      2 * alphaDen < alphaNum * (K + 1)) :
    ∃ C ∈
        canonicalResidualComponents
          A pair.1.1 pair.1.2 L,
      2 ≤ Fintype.card C.supp ∧
        Fintype.card C.supp ≤ K := by
  exact
    exists_bounded_component_of_rational_density
      hN pair hden
      (rational_deepCore_density_of_mem_active hpair hden hratio)
      hcutoff

/--
The deep-core density provides a canonical residual component with support
between two and ten vertices.  This preserves the literal `3/16`
interface as a corollary of the rational theorem.
-/
theorem exists_bounded_component_of_mem_active
    {N M A L : ℕ} {hN : 2 ≤ N}
    {terminal : TerminalPredicateFamily}
    {pair : SeparatedBoundedRatioPair N M L}
    (hpair :
      pair ∈
        activeSectorPairs
          N M A L hN terminal .manyDefects) :
    ∃ C ∈
        canonicalResidualComponents
          A pair.1.1 pair.1.2 L,
      2 ≤ Fintype.card C.supp ∧
        Fintype.card C.supp ≤ 10 := by
  exact
    exists_bounded_component_of_mem_active_of_deepCore_rational_density
      (alphaNum := 3) (alphaDen := 16) (K := 10)
      hpair (by omega) (by omega) (by omega)

/--
The two structural certificates needed by Lemma 17.26 from an explicitly
supplied rational density.
-/
theorem active_host_certificates_of_rational_density
    {N M A L alphaNum alphaDen K : ℕ} {hN : 2 ≤ N}
    {terminal : TerminalPredicateFamily}
    {pair : SeparatedBoundedRatioPair N M L}
    (hpair :
      pair ∈
        activeSectorPairs
          N M A L hN terminal .manyDefects)
    (hden : 0 < alphaDen)
    (hdensity :
      alphaNum * (L + 1) ≤
        alphaDen * canonicalResidualComponentCount
          A pair.1.1 pair.1.2 L)
    (hcutoff :
      2 * alphaDen < alphaNum * (K + 1)) :
    (2 ≤
          (IntervalDefectBound.defectsInInterval
            (L + 1) (pair.1.1 - 1)).card ∨
        2 ≤
          (IntervalDefectBound.defectsInInterval
            (L + 1) (pair.1.2 - 1)).card) ∧
      ∃ C ∈
          canonicalResidualComponents
            A pair.1.1 pair.1.2 L,
        2 ≤ Fintype.card C.supp ∧
          Fintype.card C.supp ≤ K :=
  ⟨two_defects_in_one_window_of_mem_active hpair,
    exists_bounded_component_of_rational_density
      hN pair hden hdensity hcutoff⟩

/--
The two structural certificates needed by Lemma 17.26, with a rational
component cutoff no stronger than the active classifier's `3/16` test.
-/
theorem active_host_certificates_of_deepCore_rational_density
    {N M A L alphaNum alphaDen K : ℕ} {hN : 2 ≤ N}
    {terminal : TerminalPredicateFamily}
    {pair : SeparatedBoundedRatioPair N M L}
    (hpair :
      pair ∈
        activeSectorPairs
          N M A L hN terminal .manyDefects)
    (hden : 0 < alphaDen)
    (hratio : 16 * alphaNum ≤ 3 * alphaDen)
    (hcutoff :
      2 * alphaDen < alphaNum * (K + 1)) :
    (2 ≤
          (IntervalDefectBound.defectsInInterval
            (L + 1) (pair.1.1 - 1)).card ∨
        2 ≤
          (IntervalDefectBound.defectsInInterval
            (L + 1) (pair.1.2 - 1)).card) ∧
      ∃ C ∈
          canonicalResidualComponents
            A pair.1.1 pair.1.2 L,
        2 ≤ Fintype.card C.supp ∧
          Fintype.card C.supp ≤ K := by
  exact
    active_host_certificates_of_rational_density
      hpair hden
      (rational_deepCore_density_of_mem_active
        hpair hden hratio)
      hcutoff

/--
The literal `3/16`, cutoff-`10` structural certificates needed by
Lemma 17.26.
-/
theorem active_host_certificates
    {N M A L : ℕ} {hN : 2 ≤ N}
    {terminal : TerminalPredicateFamily}
    {pair : SeparatedBoundedRatioPair N M L}
    (hpair :
      pair ∈
        activeSectorPairs
          N M A L hN terminal .manyDefects) :
    (2 ≤
          (IntervalDefectBound.defectsInInterval
            (L + 1) (pair.1.1 - 1)).card ∨
        2 ≤
          (IntervalDefectBound.defectsInInterval
            (L + 1) (pair.1.2 - 1)).card) ∧
      ∃ C ∈
          canonicalResidualComponents
            A pair.1.1 pair.1.2 L,
        2 ≤ Fintype.card C.supp ∧
          Fintype.card C.supp ≤ 10 := by
  exact
    active_host_certificates_of_deepCore_rational_density
      (alphaNum := 3) (alphaDen := 16) (K := 10)
      hpair (by omega) (by omega) (by omega)

/-! ## The two oriented active-host populations -/

/-- The branch whose first start window supplies two defects. -/
noncomputable def leftTwoDefectActiveHosts
    (N M A L : ℕ) (hN : 2 ≤ N)
    (terminal : TerminalPredicateFamily) :
    Finset (SeparatedBoundedRatioPair N M L) :=
  (activeSectorPairs
    N M A L hN terminal .manyDefects).filter fun pair ↦
      2 ≤
        (IntervalDefectBound.defectsInInterval
          (L + 1) (pair.1.1 - 1)).card

/-- The branch whose second start window supplies two defects. -/
noncomputable def rightTwoDefectActiveHosts
    (N M A L : ℕ) (hN : 2 ≤ N)
    (terminal : TerminalPredicateFamily) :
    Finset (SeparatedBoundedRatioPair N M L) :=
  (activeSectorPairs
    N M A L hN terminal .manyDefects).filter fun pair ↦
      2 ≤
        (IntervalDefectBound.defectsInInterval
          (L + 1) (pair.1.2 - 1)).card

@[simp]
theorem mem_leftTwoDefectActiveHosts
    {N M A L : ℕ} {hN : 2 ≤ N}
    {terminal : TerminalPredicateFamily}
    {pair : SeparatedBoundedRatioPair N M L} :
    pair ∈ leftTwoDefectActiveHosts
        N M A L hN terminal ↔
      pair ∈ activeSectorPairs
          N M A L hN terminal .manyDefects ∧
        2 ≤
          (IntervalDefectBound.defectsInInterval
            (L + 1) (pair.1.1 - 1)).card := by
  simp [leftTwoDefectActiveHosts]

@[simp]
theorem mem_rightTwoDefectActiveHosts
    {N M A L : ℕ} {hN : 2 ≤ N}
    {terminal : TerminalPredicateFamily}
    {pair : SeparatedBoundedRatioPair N M L} :
    pair ∈ rightTwoDefectActiveHosts
        N M A L hN terminal ↔
      pair ∈ activeSectorPairs
          N M A L hN terminal .manyDefects ∧
        2 ≤
          (IntervalDefectBound.defectsInInterval
            (L + 1) (pair.1.2 - 1)).card := by
  simp [rightTwoDefectActiveHosts]

/-- The two oriented populations cover every active fifth-sector host. -/
theorem activeHosts_subset_left_union_right
    {N M A L : ℕ} (hN : 2 ≤ N)
    (terminal : TerminalPredicateFamily) :
    activeSectorPairs
        N M A L hN terminal .manyDefects ⊆
      leftTwoDefectActiveHosts N M A L hN terminal ∪
        rightTwoDefectActiveHosts N M A L hN terminal := by
  intro pair hpair
  rw [Finset.mem_union]
  rcases
      two_defects_in_one_window_of_mem_active hpair with
    hleft | hright
  · exact Or.inl
      (mem_leftTwoDefectActiveHosts.mpr
        ⟨hpair, hleft⟩)
  · exact Or.inr
      (mem_rightTwoDefectActiveHosts.mpr
        ⟨hpair, hright⟩)

/-- Cardinality form of the oriented cover. -/
theorem card_activeHosts_le_oriented_sum
    {N M A L : ℕ} (hN : 2 ≤ N)
    (terminal : TerminalPredicateFamily) :
    (activeSectorPairs
        N M A L hN terminal .manyDefects).card ≤
      (leftTwoDefectActiveHosts
          N M A L hN terminal).card +
        (rightTwoDefectActiveHosts
          N M A L hN terminal).card := by
  calc
    (activeSectorPairs
        N M A L hN terminal .manyDefects).card ≤
        (leftTwoDefectActiveHosts N M A L hN terminal ∪
          rightTwoDefectActiveHosts N M A L hN terminal).card :=
      Finset.card_le_card
        (activeHosts_subset_left_union_right hN terminal)
    _ ≤
        (leftTwoDefectActiveHosts
            N M A L hN terminal).card +
          (rightTwoDefectActiveHosts
            N M A L hN terminal).card :=
      Finset.card_union_le _ _

/-! ## Pointwise residual-weight transfer -/

/--
The canonical inequality `τ ≤ D# + c#` for a bounded-ratio pair.  Only
adequacy of the common cutoff `M+L` is used.
-/
theorem pairTau_le_correctedDefect_add_componentCount
    {N M A L : ℕ} (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L) :
    pairTau A hN pair ≤
      canonicalCorrectedDefectCount
          A pair.1.1 pair.1.2 L +
        canonicalResidualComponentCount
          A pair.1.1 pair.1.2 L := by
  have hp := mem_separatedBoundedRatioPairs.mp pair.2
  unfold pairTau
  apply
    residualTau_le_canonicalCorrected_add_residual
      (pair_coordinates_two_le hN pair).1
      (pair_coordinates_two_le hN pair).2
  · exact
      startWindow_le_boundedRatioCutoff
        hp.1 (le_refl L)
  · exact
      startWindow_le_boundedRatioCutoff
        hp.2.1 (le_refl L)

/--
The canonical vertex budget gives
`D# + c# ≤ L+1 + max(D#)/2` uniformly in the endpoint.
-/
theorem canonicalCoreExponent_le_height_add_half_maxDefect
    {κ₀ N M A L : ℕ} (hN : 2 ≤ N)
    (hMκ : M ≤ κ₀ * N)
    (pair : SeparatedBoundedRatioPair N M L) :
    canonicalCorrectedDefectCount
          A pair.1.1 pair.1.2 L +
        canonicalResidualComponentCount
          A pair.1.1 pair.1.2 L ≤
      (L + 1) +
        maxCanonicalCorrectedDefectCount
          κ₀ A N L / 2 := by
  have hcoords := pair_coordinates_two_le hN pair
  have hbudget :
      canonicalCorrectedDefectCount
            A pair.1.1 pair.1.2 L +
          2 * canonicalResidualComponentCount
            A pair.1.1 pair.1.2 L ≤
        2 * (L + 1) :=
    canonicalCorrected_add_twice_residual_le
      A pair.1.1 pair.1.2 L
      (by omega) (by omega)
  have hD :
      canonicalCorrectedDefectCount
          A pair.1.1 pair.1.2 L ≤
        maxCanonicalCorrectedDefectCount
          κ₀ A N L :=
    canonicalCorrectedDefectCount_le_max
      hMκ pair.2
  exact
    PropositionNineNine.defect_add_component_le_height_add_half_envelope
      hbudget hD

/-- Natural-valued common pointwise envelope for the fifth sector. -/
def residualWeightEnvelopeNat
    (κ₀ A N L : ℕ) : ℕ :=
  2 ^ ((L + 1) +
    maxCanonicalCorrectedDefectCount κ₀ A N L / 2)

/-- Real-valued form of the common residual-weight envelope. -/
def residualWeightEnvelope
    (κ₀ A N L : ℕ) : ℝ :=
  (residualWeightEnvelopeNat κ₀ A N L : ℝ)

/--
Every active fifth-sector residual weight is bounded by the common
endpoint-independent envelope.
-/
theorem linearResidualWeight_le_envelope_of_mem_active
    {κ₀ N M A L : ℕ} {hN : 2 ≤ N}
    {terminal : TerminalPredicateFamily}
    {pair : SeparatedBoundedRatioPair N M L}
    (hMκ : M ≤ κ₀ * N)
    (hpair :
      pair ∈
        activeSectorPairs
          N M A L hN terminal .manyDefects) :
    linearResidualWeight A hN pair ≤
      residualWeightEnvelopeNat κ₀ A N L := by
  have htau :
      pairTau A hN pair ≤
        (L + 1) +
          maxCanonicalCorrectedDefectCount
            κ₀ A N L / 2 :=
    (pairTau_le_correctedDefect_add_componentCount
      (A := A) hN pair).trans
      (canonicalCoreExponent_le_height_add_half_maxDefect
        hN hMκ pair)
  unfold linearResidualWeight residualWeight
    residualWeightEnvelopeNat
  simp only [pairSigma_eq_zero_of_mem_active hpair,
    pow_zero, one_mul]
  exact
    (Nat.sub_le _ _).trans
      (Nat.pow_le_pow_right (by omega) htau)

/--
Finite active-host count times pointwise-weight estimate for the exact
fifth-sector mass.
-/
theorem sectorResidualMassNat_le_active_card_mul_envelope
    {κ₀ N M A L : ℕ} (hN : 2 ≤ N)
    (hMκ : M ≤ κ₀ * N)
    (terminal : TerminalPredicateFamily) :
    sectorResidualMassNat
        (M := M) (L := L) A hN terminal .manyDefects ≤
      (activeSectorPairs
          N M A L hN terminal .manyDefects).card *
        residualWeightEnvelopeNat κ₀ A N L := by
  rw [
    sectorResidualMassNat_eq_activeLinearResidualMass
      hN terminal .manyDefects]
  unfold linearResidualMass
  calc
    (∑ pair ∈
        activeSectorPairs
          N M A L hN terminal .manyDefects,
        linearResidualWeight A hN pair) ≤
      ∑ _pair ∈
        activeSectorPairs
          N M A L hN terminal .manyDefects,
        residualWeightEnvelopeNat κ₀ A N L :=
      Finset.sum_le_sum fun pair hpair ↦
        linearResidualWeight_le_envelope_of_mem_active
          hMκ hpair
    _ =
        (activeSectorPairs
            N M A L hN terminal .manyDefects).card *
          residualWeightEnvelopeNat κ₀ A N L := by
      simp

/-! ## Proof-independent host counts -/

/-- Real cardinality of the active fifth-sector population. -/
noncomputable def activeHostCount
    (A : ℕ) (terminal : TerminalPredicateFamily)
    (N M L : ℕ) : ℝ :=
  if hN : 2 ≤ N then
    ((activeSectorPairs
      N M A L hN terminal .manyDefects).card : ℝ)
  else 0

/-- Real cardinality of the two oriented populations, counted with overlap. -/
noncomputable def orientedHostCoverCount
    (A : ℕ) (terminal : TerminalPredicateFamily)
    (N M L : ℕ) : ℝ :=
  if hN : 2 ≤ N then
    (((leftTwoDefectActiveHosts
          N M A L hN terminal).card +
        (rightTwoDefectActiveHosts
          N M A L hN terminal).card : ℕ) : ℝ)
  else 0

/-- The active host count is bounded by its two oriented branches. -/
theorem activeHostCount_le_orientedHostCoverCount
    {N M A L : ℕ} (hN : 2 ≤ N)
    (terminal : TerminalPredicateFamily) :
    activeHostCount A terminal N M L ≤
      orientedHostCoverCount A terminal N M L := by
  simp only [activeHostCount, orientedHostCoverCount,
    dif_pos hN]
  exact_mod_cast
    card_activeHosts_le_oriented_sum hN terminal

/-- The finite fifth-sector mass is bounded by oriented hosts times weight. -/
theorem sectorResidualMassNat_cast_le_orientedHostCover_mul_envelope
    {κ₀ N M A L : ℕ} (hN : 2 ≤ N)
    (hMκ : M ≤ κ₀ * N)
    (terminal : TerminalPredicateFamily) :
    (sectorResidualMassNat
        (M := M) (L := L) A hN terminal .manyDefects : ℝ) ≤
      orientedHostCoverCount A terminal N M L *
        residualWeightEnvelope κ₀ A N L := by
  have hfinite :=
    sectorResidualMassNat_le_active_card_mul_envelope
      (κ₀ := κ₀) (M := M) (A := A) (L := L)
      hN hMκ terminal
  have hcast :
      (sectorResidualMassNat
          (M := M) (L := L) A hN terminal .manyDefects : ℝ) ≤
        ((activeSectorPairs
            N M A L hN terminal .manyDefects).card : ℝ) *
          residualWeightEnvelope κ₀ A N L := by
    unfold residualWeightEnvelope
    exact_mod_cast hfinite
  have hactive :
      ((activeSectorPairs
          N M A L hN terminal .manyDefects).card : ℝ) ≤
        orientedHostCoverCount A terminal N M L := by
    simpa only [activeHostCount, dif_pos hN] using
      activeHostCount_le_orientedHostCoverCount
        hN terminal
  exact hcast.trans
    (mul_le_mul_of_nonneg_right hactive (by
      unfold residualWeightEnvelope residualWeightEnvelopeNat
      positivity))

/-! ## The certified `N^(1+o)` pointwise envelope -/

/--
The half-defect exponential attached to the complete bounded-ratio block is
uniformly subpolynomial.
-/
theorem two_pow_half_maxDefect_uniformSubpolynomial
    {C : ℝ} (hC : 0 ≤ C) (κ₀ A : ℕ) :
    UniformSubpolynomialOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun N L =>
        (((2 ^
          (maxCanonicalCorrectedDefectCount
            κ₀ A N L / 2) : ℕ) : ℝ))) := by
  have hfour :=
    four_pow_maxCanonicalCorrectedDefectCount_uniformSubpolynomial
      hC κ₀ A
  intro k hk
  obtain ⟨N₀, hN₀⟩ := hfour k hk
  refine ⟨N₀, ?_⟩
  intro N hN L hrun
  have hbase :
      (((2 ^
        (maxCanonicalCorrectedDefectCount
          κ₀ A N L / 2) : ℕ) : ℝ)) ≤
        (((4 ^
          maxCanonicalCorrectedDefectCount
            κ₀ A N L : ℕ) : ℝ)) := by
    exact_mod_cast
      (calc
        2 ^
              (maxCanonicalCorrectedDefectCount
                κ₀ A N L / 2) ≤
            2 ^
              maxCanonicalCorrectedDefectCount
                κ₀ A N L :=
          Nat.pow_le_pow_right (by omega)
            (Nat.div_le_self _ _)
        _ ≤
            4 ^
              maxCanonicalCorrectedDefectCount
                κ₀ A N L :=
          Nat.pow_le_pow_left (by omega) _)
  rw [abs_of_nonneg (by positivity)]
  have hfourBound := hN₀ N hN L hrun
  rw [abs_of_nonneg (by positivity)] at hfourBound
  exact
    (pow_le_pow_left₀ (by positivity) hbase k).trans
      hfourBound

/--
The common pointwise envelope has rate `N^(1+o_{C,κ₀}(1))`.
-/
theorem residualWeightEnvelope_uniformLinear
    {C : ℝ} (hC : 0 ≤ C) (κ₀ A : ℕ) :
    UniformLinearSubpolynomialOn
      (CriticalRunWindow.InRunLengthWindow C)
      (residualWeightEnvelope κ₀ A) := by
  let defectFactor : ℕ → ℕ → ℝ :=
    fun N L =>
      (((2 ^
        (maxCanonicalCorrectedDefectCount
          κ₀ A N L / 2) : ℕ) : ℝ))
  let loss : ℕ → ℕ → ℝ :=
    fun N L =>
      (2 * CriticalRunWindow.balanceConstant C) *
        defectFactor N L
  have hdefect :
      UniformSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C)
        defectFactor := by
    simpa only [defectFactor] using
      two_pow_half_maxDefect_uniformSubpolynomial
        hC κ₀ A
  have hloss :
      UniformSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C)
        loss := by
    simpa only [loss] using
      ExpSqrtLog.uniformSubpolynomialOn_const_mul
        (2 * CriticalRunWindow.balanceConstant C)
        hdefect
  apply UniformLinear.of_linear_mul_subpolynomial hloss
  refine ⟨1, ?_⟩
  intro N hN L hrun
  have hNpos : 0 < N := by omega
  have hcritical :=
    CriticalChannelPowers.two_pow_runLength_le_balance_mul
      hNpos hrun
  have hrunPower :
      (((2 ^ (L + 1) : ℕ) : ℝ)) ≤
        (2 * CriticalRunWindow.balanceConstant C) *
          (N : ℝ) := by
    calc
      (((2 ^ (L + 1) : ℕ) : ℝ)) =
          2 * (2 : ℝ) ^ L := by
        push_cast
        rw [pow_succ]
        ring
      _ ≤
          2 *
            (CriticalRunWindow.balanceConstant C *
              (N : ℝ)) :=
        mul_le_mul_of_nonneg_left hcritical
          (by norm_num)
      _ =
          (2 * CriticalRunWindow.balanceConstant C) *
            (N : ℝ) := by
        ring
  have hdefectNonneg :
      0 ≤ defectFactor N L := by
    dsimp only [defectFactor]
    positivity
  rw [abs_of_nonneg (show
      0 ≤ residualWeightEnvelope κ₀ A N L by
        unfold residualWeightEnvelope residualWeightEnvelopeNat
        positivity)]
  rw [abs_of_nonneg (show
      0 ≤ loss N L by
        dsimp only [loss]
        exact mul_nonneg
          (mul_nonneg (by norm_num)
            (CriticalRunWindow.balanceConstant_nonneg C))
          hdefectNonneg)]
  unfold residualWeightEnvelope
    residualWeightEnvelopeNat
  rw [pow_add]
  push_cast
  dsimp only [loss, defectFactor]
  calc
    (2 : ℝ) ^ (L + 1) *
          (2 : ℝ) ^
            (maxCanonicalCorrectedDefectCount
              κ₀ A N L / 2) ≤
        ((2 * CriticalRunWindow.balanceConstant C) *
            (N : ℝ)) *
          (2 : ℝ) ^
            (maxCanonicalCorrectedDefectCount
              κ₀ A N L / 2) :=
      mul_le_mul_of_nonneg_right
        (by
          simpa only [Nat.cast_pow, Nat.cast_ofNat]
            using hrunPower)
        (by positivity)
    _ =
        (N : ℝ) *
          ((2 * CriticalRunWindow.balanceConstant C) *
            (((2 ^
              (maxCanonicalCorrectedDefectCount
                κ₀ A N L / 2) : ℕ) : ℝ))) := by
      norm_num only [Nat.cast_pow, Nat.cast_ofNat]
      ring

/-! ## Closure from the exact missing host envelope -/

/--
An endpoint-independent envelope for the two oriented host populations
gives both the source-exact `N^(3/2+o)` rate and its quadratic little-oh
consequence for the literal fifth sector.

This is a factorization theorem, not a new arithmetic assumption: the host
envelope and its finite domination proof are explicit parameters.
-/
theorem manyDefectsSector_rates_of_orientedHostEnvelope
    {C : ℝ} (hC : 0 ≤ C) (κ₀ A : ℕ)
    (terminal : TerminalPredicateFamily)
    {hostEnvelope : ℕ → ℕ → ℝ}
    (hhostRate :
      UniformHalfPowerSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C)
        hostEnvelope)
    (hhostNonneg :
      ∀ N L, 0 ≤ hostEnvelope N L)
    (hhostDom :
      ∃ N₁ : ℕ, ∀ N ≥ N₁, ∀ M L,
        2 * N ≤ M →
        M ≤ κ₀ * N →
        CriticalRunWindow.InRunLengthWindow C N L →
        orientedHostCoverCount
            A terminal N M L ≤
          hostEnvelope N L) :
    UniformRationalPowerInBoundedRatioWindow 3 2 C κ₀
        (sectorResidualMass A terminal .manyDefects) ∧
      UniformLittleOInBoundedRatioWindow C κ₀
        (sectorResidualMass A terminal .manyDefects) := by
  let massEnvelope : ℕ → ℕ → ℝ :=
    fun N L =>
      hostEnvelope N L *
        residualWeightEnvelope κ₀ A N L
  have hthreeHalves :
      UniformThreeHalvesSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C)
        massEnvelope := by
    exact
      PropositionNineNine.halfPower_mul_linear
        hhostRate
        (residualWeightEnvelope_uniformLinear
          hC κ₀ A)
  have hrational :
      UniformRationalPowerSubpolynomialOn 3 2
        (CriticalRunWindow.InRunLengthWindow C)
        massEnvelope := by
    simpa only [UniformThreeHalvesSubpolynomialOn,
      UniformRationalPowerSubpolynomialOn] using
      hthreeHalves
  have henvelope :
      UniformLittleOOn
        (CriticalRunWindow.InRunLengthWindow C)
        massEnvelope
        (fun N _ ↦ (N : ℝ) ^ 2) :=
    UniformRationalPower.littleO_natPower_of_lt
      (p := 3) (q := 2) (r := 2)
      (by omega) hrational
  have hmassNonneg :
      ∀ N M L,
        0 ≤ sectorResidualMass A terminal .manyDefects N M L := by
    intro N M L
    unfold sectorResidualMass
    split_ifs
    · positivity
    · exact le_rfl
  have henvelopeNonneg :
      ∀ N L, 0 ≤ massEnvelope N L := by
    intro N L
    dsimp only [massEnvelope]
    exact mul_nonneg
      (hhostNonneg N L)
      (by
        unfold residualWeightEnvelope residualWeightEnvelopeNat
        positivity)
  have hmassDom :
      ∃ N₁ : ℕ, ∀ N ≥ N₁, ∀ M L,
        2 * N ≤ M →
        M ≤ κ₀ * N →
        CriticalRunWindow.InRunLengthWindow C N L →
        sectorResidualMass A terminal .manyDefects N M L ≤
          massEnvelope N L := by
    obtain ⟨Nhost, hNhost⟩ := hhostDom
    refine ⟨max 2 Nhost, ?_⟩
    intro N hN M L hNM hMκ hrun
    have hNtwo : 2 ≤ N :=
      (le_max_left _ _).trans hN
    have hNhostN : Nhost ≤ N :=
      (le_max_right _ _).trans hN
    have hfinite :=
      sectorResidualMassNat_cast_le_orientedHostCover_mul_envelope
        (κ₀ := κ₀) (M := M) (A := A) (L := L)
        hNtwo hMκ terminal
    have hhosts :=
      hNhost N hNhostN M L hNM hMκ hrun
    simp only [sectorResidualMass, dif_pos hNtwo,
      massEnvelope]
    exact hfinite.trans
      (mul_le_mul_of_nonneg_right hhosts
        (by
          unfold residualWeightEnvelope residualWeightEnvelopeNat
          positivity))
  constructor
  · exact
      BoundedRatioSectorClosure.uniformRationalPowerInBoundedRatioWindow_of_nonnegative_envelope
        hrational hmassNonneg henvelopeNonneg hmassDom
  · exact
      BoundedRatioSectorClosure.uniformLittleOInBoundedRatioWindow_of_nonnegative_envelope
        henvelope hmassNonneg henvelopeNonneg hmassDom

/--
Source-exact `N^(3/2+o)` form of the oriented-host reduction.
-/
theorem manyDefectsSector_uniformThreeHalves_of_orientedHostEnvelope
    {C : ℝ} (hC : 0 ≤ C) (κ₀ A : ℕ)
    (terminal : TerminalPredicateFamily)
    {hostEnvelope : ℕ → ℕ → ℝ}
    (hhostRate :
      UniformHalfPowerSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C)
        hostEnvelope)
    (hhostNonneg :
      ∀ N L, 0 ≤ hostEnvelope N L)
    (hhostDom :
      ∃ N₁ : ℕ, ∀ N ≥ N₁, ∀ M L,
        2 * N ≤ M →
        M ≤ κ₀ * N →
        CriticalRunWindow.InRunLengthWindow C N L →
        orientedHostCoverCount
            A terminal N M L ≤
          hostEnvelope N L) :
    UniformRationalPowerInBoundedRatioWindow 3 2 C κ₀
      (sectorResidualMass A terminal .manyDefects) :=
  (manyDefectsSector_rates_of_orientedHostEnvelope
    hC κ₀ A terminal hhostRate hhostNonneg hhostDom).1

/--
Quadratic little-oh consequence of the oriented-host reduction.
-/
theorem manyDefectsSector_uniformLittleO_of_orientedHostEnvelope
    {C : ℝ} (hC : 0 ≤ C) (κ₀ A : ℕ)
    (terminal : TerminalPredicateFamily)
    {hostEnvelope : ℕ → ℕ → ℝ}
    (hhostRate :
      UniformHalfPowerSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C)
        hostEnvelope)
    (hhostNonneg :
      ∀ N L, 0 ≤ hostEnvelope N L)
    (hhostDom :
      ∃ N₁ : ℕ, ∀ N ≥ N₁, ∀ M L,
        2 * N ≤ M →
        M ≤ κ₀ * N →
        CriticalRunWindow.InRunLengthWindow C N L →
        orientedHostCoverCount
            A terminal N M L ≤
          hostEnvelope N L) :
    UniformLittleOInBoundedRatioWindow C κ₀
      (sectorResidualMass A terminal .manyDefects) :=
  (manyDefectsSector_rates_of_orientedHostEnvelope
    hC κ₀ A terminal hhostRate hhostNonneg hhostDom).2

/--
Interface-level form: a proof of the missing oriented-host envelope would
discharge `ManyDefectsSectorStabilityStatement`.  The existing
Evertse--Silverman and Pell hypotheses remain visible in the target
statement, but the current repository does not yet derive `hhostDom` from
them.
-/
theorem manyDefectsSectorStability_of_orientedHostEnvelope
    {C : ℝ} (hC : 0 ≤ C) (κ₀ A : ℕ)
    (terminal : TerminalPredicateFamily)
    {hostEnvelope : ℕ → ℕ → ℝ}
    (hhostRate :
      UniformHalfPowerSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C)
        hostEnvelope)
    (hhostNonneg :
      ∀ N L, 0 ≤ hostEnvelope N L)
    (hhostDom :
      ∃ N₁ : ℕ, ∀ N ≥ N₁, ∀ M L,
        2 * N ≤ M →
        M ≤ κ₀ * N →
        CriticalRunWindow.InRunLengthWindow C N L →
        orientedHostCoverCount
            A terminal N M L ≤
          hostEnvelope N L) :
    ManyDefectsSectorStabilityStatement
      C κ₀ A terminal := by
  intro _hES _hPell
  exact
    manyDefectsSector_uniformLittleO_of_orientedHostEnvelope
      hC κ₀ A terminal hhostRate hhostNonneg hhostDom

end

end BoundedRatioManyDefectsReduction
end PaperC
