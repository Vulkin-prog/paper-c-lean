import PaperC.Analysis.CriticalWeightedDefect
import PaperC.Asymptotics.BoundedRatioCorrectedDefectEnvelope
import PaperC.Asymptotics.BoundedRatioSectorClosure
import PaperC.Asymptotics.CriticalRationalMassEnvelopes
import PaperC.Asymptotics.QuadraticAndInterpolationClosure
import PaperC.Asymptotics.RationalPowerClosure
import PaperC.Asymptotics.RationalPowerLittleO
import PaperC.Asymptotics.SmallHeightComponentEnvelopeCritical
import PaperC.Combinatorics.SmallHeightResidualComponentEnvelope

set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 300000

/-!
# The bounded-ratio small-canonical-height sector

This file closes the internal bridge corresponding to Lemma 17.15.  It
keeps the two finite mechanisms visible.

* On the active `σ = 0` branch, the quadratic residual mass is bounded by
  the common small-height `τ` factor times the bounded relational-host
  cardinality.
* On the active `σ > 0` branch, the systematic fourth-power sum is charged
  to the exact bounded base-four rational mass.

The base-four bounded mass has a volumetric height-two term, hence the
quadratic envelope used here is `N^(2+o(1))`.  Combining it with the
`N^(3/2+o(1))` host envelope by Cauchy--Schwarz gives
`N^(7/4+o(1))`, which is uniformly little-oh of `N²`.

No external bridge, axiom, or unproved declaration is used.
-/

namespace PaperC
namespace BoundedRatioSmallHeightSector

open scoped BigOperators
open Affine
open BoundedRatioCorrectedDefectEnvelope
open BoundedRatioGeometry
open BoundedRatioRelationalHosts
open BoundedRatioRelationalHostsCritical
open BoundedRatioResidualMasses
open BoundedRatioSectorClosure
open PropositionSixteenOne
open RationalMassFinite
open ResidualComponentCounts
open SectionElevenPartition
open SmallHeightLargeProductPairs
open SmallHeightResidualComponentEnvelope
open SmallHeightResidualPrimeSupport

noncomputable section

/-! ## A common bounded-ratio `τ` envelope -/

/-- Endpoint-independent upper envelope for `τ` in the second sector. -/
noncomputable def boundedSmallHeightTauEnvelope
    (κ₀ A N L : ℕ) : ℕ :=
  maxCanonicalCorrectedDefectCount κ₀ A N L +
    smallHeightResidualComponentEnvelope L

/-- Membership in the literal second sector exposes the selected
small-height canonical candidate. -/
theorem hasSmallCanonicalHeight_of_mem_activeSectorPairs
    {N M A L : ℕ} {hN : 2 ≤ N}
    {terminal : TerminalPredicateFamily}
    {pair : SeparatedBoundedRatioPair N M L}
    (hpair :
      pair ∈ activeSectorPairs
        N M A L hN terminal .smallCanonicalHeight) :
    HasSmallCanonicalHeight A L pair.1.1 pair.1.2 := by
  have hsector :=
    (mem_activeSectorPairs.mp hpair).1
  have htests :
      ¬HasSmallCanonicalPrimeProduct A hN pair ∧
        HasSmallCanonicalHeight A L pair.1.1 pair.1.2 := by
    simpa only [boundedRatioSectorOf, boundedRatioSectorTests] using
      (sectorOf_eq_smallCanonicalHeight_iff.mp hsector)
  exact htests.2

/-- The small-height prime-support argument is insensitive to the position
of the two coordinates inside the bounded-ratio block. -/
theorem canonicalResidualComponentCount_le_smallHeightEnvelope
    {N M A L : ℕ} {hN : 2 ≤ N}
    (hB : 8 ≤ L + 1)
    {terminal : TerminalPredicateFamily}
    {pair : SeparatedBoundedRatioPair N M L}
    (hpair :
      pair ∈ activeSectorPairs
        N M A L hN terminal .smallCanonicalHeight) :
    canonicalResidualComponentCount
        A pair.1.1 pair.1.2 L ≤
      smallHeightResidualComponentEnvelope L := by
  obtain ⟨c, hchoice, hqReal⟩ :=
    hasSmallCanonicalHeight_of_mem_activeSectorPairs hpair
  have hqNat :
      Nat.max c.1.1 c.1.2 ≤
        Nat.sqrt (Nat.log 2 (L + 1)) :=
    height_le_natSqrt_natLog_of_le_realSqrt_realLog
      hB hqReal
  have hcoordinates := pair_coordinates_two_le hN pair
  have hcomponent :
      canonicalResidualComponentCount
          A pair.1.1 pair.1.2 L ≤
        2 +
          PrimesUpTo.count
            (4 * Nat.max c.1.1 c.1.2 * (L + 1)) :=
    canonicalResidualComponentCount_le_two_add_primeCount_of_choice
      hcoordinates.1 hcoordinates.2 c hchoice
  have hcutoff :
      4 * Nat.max c.1.1 c.1.2 * (L + 1) ≤
        smallHeightPrimeCutoff L := by
    unfold smallHeightPrimeCutoff
    exact
      Nat.mul_le_mul_right (L + 1)
        (Nat.mul_le_mul_left 4 hqNat)
  have hcount :
      PrimesUpTo.count
          (4 * Nat.max c.1.1 c.1.2 * (L + 1)) ≤
        PrimesUpTo.count (smallHeightPrimeCutoff L) :=
    primeCount_mono hcutoff
  unfold smallHeightResidualComponentEnvelope
  exact hcomponent.trans (Nat.add_le_add_left hcount 2)

/-- Bounded-ratio form of the canonical quotient-core estimate
`τ ≤ D# + c#`. -/
theorem pairTau_le_canonicalCorrected_add_residual
    {N M A L : ℕ} (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L) :
    pairTau A hN pair ≤
      canonicalCorrectedDefectCount
          A pair.1.1 pair.1.2 L +
        canonicalResidualComponentCount
          A pair.1.1 pair.1.2 L := by
  have hsep :=
    PropositionSixteenOne.mem_separatedBoundedRatioPairs.mp pair.2
  have hcoordinates := pair_coordinates_two_le hN pair
  unfold pairTau
  apply
    residualTau_le_canonicalCorrected_add_residual
      hcoordinates.1 hcoordinates.2
  · exact startWindow_le_boundedRatioCutoff hsep.1 (le_refl L)
  · exact startWindow_le_boundedRatioCutoff hsep.2.1 (le_refl L)

/-- Every active pair in the second sector has `τ` bounded by the common
endpoint-independent envelope. -/
theorem pairTau_le_boundedSmallHeightTauEnvelope
    {κ₀ N M A L : ℕ} {hN : 2 ≤ N}
    (hM : M ≤ κ₀ * N) (hB : 8 ≤ L + 1)
    {terminal : TerminalPredicateFamily}
    {pair : SeparatedBoundedRatioPair N M L}
    (hpair :
      pair ∈ activeSectorPairs
        N M A L hN terminal .smallCanonicalHeight) :
    pairTau A hN pair ≤
      boundedSmallHeightTauEnvelope κ₀ A N L := by
  have hcore :=
    pairTau_le_canonicalCorrected_add_residual (A := A) hN pair
  have hcorrected :
      canonicalCorrectedDefectCount
          A pair.1.1 pair.1.2 L ≤
        maxCanonicalCorrectedDefectCount κ₀ A N L :=
    canonicalCorrectedDefectCount_le_max hM pair.2
  have hresidual :=
    canonicalResidualComponentCount_le_smallHeightEnvelope
      hB hpair
  unfold boundedSmallHeightTauEnvelope
  exact hcore.trans (Nat.add_le_add hcorrected hresidual)

/-- Pointwise extraction of the common `τ` factor. -/
theorem quadraticResidualWeight_le_tauEnvelope_mul_four_pow_sigma
    {κ₀ N M A L : ℕ} {hN : 2 ≤ N}
    (hM : M ≤ κ₀ * N) (hB : 8 ≤ L + 1)
    {terminal : TerminalPredicateFamily}
    {pair : SeparatedBoundedRatioPair N M L}
    (hpair :
      pair ∈ activeSectorPairs
        N M A L hN terminal .smallCanonicalHeight) :
    quadraticResidualWeight A hN pair ≤
      4 ^ boundedSmallHeightTauEnvelope κ₀ A N L *
        4 ^ pairSigma A pair := by
  have htau :=
    pairTau_le_boundedSmallHeightTauEnvelope
      hM hB hpair
  unfold quadraticResidualWeight
  calc
    4 ^ pairSigma A pair *
          (4 ^ pairTau A hN pair - 1) ≤
        4 ^ pairSigma A pair * 4 ^ pairTau A hN pair :=
      Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    _ ≤
        4 ^ pairSigma A pair *
          4 ^ boundedSmallHeightTauEnvelope κ₀ A N L :=
      Nat.mul_le_mul_left _
        (Nat.pow_le_pow_right (by norm_num) htau)
    _ =
        4 ^ boundedSmallHeightTauEnvelope κ₀ A N L *
          4 ^ pairSigma A pair := by
      rw [Nat.mul_comm]

/-! ## The exact split into `σ=0` and `σ>0` -/

noncomputable def sigmaZeroActiveSmallHeightSectorPairs
    (N M A L : ℕ) (hN : 2 ≤ N)
    (terminal : TerminalPredicateFamily) :
    Finset (SeparatedBoundedRatioPair N M L) := by
  classical
  exact
    (activeSectorPairs N M A L hN terminal
      .smallCanonicalHeight).filter fun pair ↦
        pairSigma A pair = 0

noncomputable def positiveSigmaActiveSmallHeightSectorPairs
    (N M A L : ℕ) (hN : 2 ≤ N)
    (terminal : TerminalPredicateFamily) :
    Finset (SeparatedBoundedRatioPair N M L) := by
  classical
  exact
    (activeSectorPairs N M A L hN terminal
      .smallCanonicalHeight).filter fun pair ↦
        0 < pairSigma A pair

@[simp]
theorem mem_sigmaZeroActiveSmallHeightSectorPairs
    {N M A L : ℕ} {hN : 2 ≤ N}
    {terminal : TerminalPredicateFamily}
    {pair : SeparatedBoundedRatioPair N M L} :
    pair ∈ sigmaZeroActiveSmallHeightSectorPairs
        N M A L hN terminal ↔
      pair ∈ activeSectorPairs
          N M A L hN terminal .smallCanonicalHeight ∧
        pairSigma A pair = 0 := by
  simp [sigmaZeroActiveSmallHeightSectorPairs]

@[simp]
theorem mem_positiveSigmaActiveSmallHeightSectorPairs
    {N M A L : ℕ} {hN : 2 ≤ N}
    {terminal : TerminalPredicateFamily}
    {pair : SeparatedBoundedRatioPair N M L} :
    pair ∈ positiveSigmaActiveSmallHeightSectorPairs
        N M A L hN terminal ↔
      pair ∈ activeSectorPairs
          N M A L hN terminal .smallCanonicalHeight ∧
        0 < pairSigma A pair := by
  simp [positiveSigmaActiveSmallHeightSectorPairs]

noncomputable def sigmaZeroQuadraticResidualMass
    {N M L : ℕ} (A : ℕ) (hN : 2 ≤ N)
    (terminal : TerminalPredicateFamily) : ℕ :=
  quadraticResidualMass A hN
    (sigmaZeroActiveSmallHeightSectorPairs
      N M A L hN terminal)

noncomputable def positiveSigmaQuadraticResidualMass
    {N M L : ℕ} (A : ℕ) (hN : 2 ≤ N)
    (terminal : TerminalPredicateFamily) : ℕ :=
  quadraticResidualMass A hN
    (positiveSigmaActiveSmallHeightSectorPairs
      N M A L hN terminal)

/-- The active quadratic mass is the disjoint sum of its two `σ` branches. -/
theorem activeSectorQuadraticResidualMass_eq_sigma_branches
    {N M A L : ℕ} (hN : 2 ≤ N)
    (terminal : TerminalPredicateFamily) :
    activeSectorQuadraticResidualMass
        (M := M) (L := L) A hN terminal
        .smallCanonicalHeight =
      sigmaZeroQuadraticResidualMass
          (M := M) (L := L) A hN terminal +
        positiveSigmaQuadraticResidualMass
          (M := M) (L := L) A hN terminal := by
  classical
  let zero :=
    sigmaZeroActiveSmallHeightSectorPairs
      N M A L hN terminal
  let positive :=
    positiveSigmaActiveSmallHeightSectorPairs
      N M A L hN terminal
  let active :=
    activeSectorPairs
      N M A L hN terminal .smallCanonicalHeight
  have hdisjoint : Disjoint zero positive := by
    apply Finset.disjoint_left.mpr
    intro pair hzero hpositive
    have hz :=
      (mem_sigmaZeroActiveSmallHeightSectorPairs.mp hzero).2
    have hp :=
      (mem_positiveSigmaActiveSmallHeightSectorPairs.mp hpositive).2
    omega
  have hunion : zero ∪ positive = active := by
    ext pair
    simp only [Finset.mem_union, zero, positive, active,
      mem_sigmaZeroActiveSmallHeightSectorPairs,
      mem_positiveSigmaActiveSmallHeightSectorPairs]
    constructor
    · rintro (h | h)
      · exact h.1
      · exact h.1
    · intro h
      by_cases hz : pairSigma A pair = 0
      · exact Or.inl ⟨h, hz⟩
      · exact Or.inr ⟨h, Nat.pos_of_ne_zero hz⟩
  unfold activeSectorQuadraticResidualMass
    sigmaZeroQuadraticResidualMass
    positiveSigmaQuadraticResidualMass
    quadraticResidualMass
  change
    (∑ pair ∈ active,
      quadraticResidualWeight A hN pair) =
      (∑ pair ∈ zero,
        quadraticResidualWeight A hN pair) +
      ∑ pair ∈ positive,
        quadraticResidualWeight A hN pair
  rw [← Finset.sum_union hdisjoint, hunion]

/-! ## Finite branch bounds -/

/-- Any subtype population has systematic base-four mass no larger than
the full bounded rational mass. -/
theorem sum_four_pow_pairSigma_sub_one_le_boundedRationalMass
    {N M A L : ℕ}
    (population : Finset (SeparatedBoundedRatioPair N M L)) :
    (∑ pair ∈ population,
        (4 ^ pairSigma A pair - 1)) ≤
      boundedRationalMass N M A L 4 := by
  classical
  let values : Finset (ℕ × ℕ) :=
    population.image Subtype.val
  have hvalues :
      values ⊆
        PropositionSixteenOne.separatedBoundedRatioPairs N M L := by
    intro pair hpair
    dsimp only [values] at hpair
    rw [Finset.mem_image] at hpair
    obtain ⟨z, _hz, rfl⟩ := hpair
    exact z.2
  have hsumImage :
      (∑ pair ∈ values,
          (4 ^ canonicalPairSigma A L pair.1 pair.2 - 1)) =
        ∑ pair ∈ population,
          (4 ^ pairSigma A pair - 1) := by
    unfold values
    rw [Finset.sum_image]
    · rfl
    · intro pair _hpair other _hother hval
      exact Subtype.val_injective hval
  calc
    (∑ pair ∈ population,
        (4 ^ pairSigma A pair - 1)) =
        ∑ pair ∈ values,
          (4 ^ canonicalPairSigma A L pair.1 pair.2 - 1) :=
      hsumImage.symm
    _ ≤
        ∑ pair ∈
          PropositionSixteenOne.separatedBoundedRatioPairs N M L,
          (4 ^ canonicalPairSigma A L pair.1 pair.2 - 1) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hvalues
      intro pair _hpair _hnot
      exact Nat.zero_le _
    _ = boundedRationalMass N M A L 4 := by
      rfl

/-- For positive `σ`, the unsubtracted fourth power costs at most a factor
two. -/
theorem four_pow_le_two_mul_four_pow_sub_one
    {σ : ℕ} (hσ : 0 < σ) :
    4 ^ σ ≤ 2 * (4 ^ σ - 1) := by
  have hpow :
      4 ^ 1 ≤ 4 ^ σ :=
    Nat.pow_le_pow_right (by norm_num) hσ
  norm_num at hpow
  omega

theorem sum_four_pow_pairSigma_positive_le_two_mul_boundedRationalMass
    {N M A L : ℕ} (hN : 2 ≤ N)
    (terminal : TerminalPredicateFamily) :
    (∑ pair ∈
        positiveSigmaActiveSmallHeightSectorPairs
          N M A L hN terminal,
        4 ^ pairSigma A pair) ≤
      2 * boundedRationalMass N M A L 4 := by
  let population :=
    positiveSigmaActiveSmallHeightSectorPairs
      N M A L hN terminal
  calc
    (∑ pair ∈ population, 4 ^ pairSigma A pair) ≤
        ∑ pair ∈ population,
          2 * (4 ^ pairSigma A pair - 1) := by
      apply Finset.sum_le_sum
      intro pair hpair
      exact
        four_pow_le_two_mul_four_pow_sub_one
          (mem_positiveSigmaActiveSmallHeightSectorPairs.mp hpair).2
    _ =
        2 * ∑ pair ∈ population,
          (4 ^ pairSigma A pair - 1) := by
      rw [Finset.mul_sum]
    _ ≤ 2 * boundedRationalMass N M A L 4 :=
      Nat.mul_le_mul_left 2
        (sum_four_pow_pairSigma_sub_one_le_boundedRationalMass
          population)

/-- The `σ=0` branch is charged only to the host cardinality. -/
theorem sigmaZeroQuadraticResidualMass_le
    {κ₀ N M A L : ℕ} (hN : 2 ≤ N)
    (hM : M ≤ κ₀ * N) (hB : 8 ≤ L + 1)
    (terminal : TerminalPredicateFamily) :
    sigmaZeroQuadraticResidualMass
        (M := M) (L := L) A hN terminal ≤
      4 ^ boundedSmallHeightTauEnvelope κ₀ A N L *
        (boundedRelationalHosts N M L).card := by
  let population :=
    sigmaZeroActiveSmallHeightSectorPairs
      N M A L hN terminal
  let factor :=
    4 ^ boundedSmallHeightTauEnvelope κ₀ A N L
  have hpopulationCard :
      population.card ≤
        (activeSectorPairs
          N M A L hN terminal .smallCanonicalHeight).card := by
    dsimp only [population]
    unfold sigmaZeroActiveSmallHeightSectorPairs
    exact Finset.card_filter_le _ _
  unfold sigmaZeroQuadraticResidualMass quadraticResidualMass
  calc
    (∑ pair ∈ population,
        quadraticResidualWeight A hN pair) ≤
        ∑ _pair ∈ population, factor := by
      apply Finset.sum_le_sum
      intro pair hpair
      have hactive :=
        (mem_sigmaZeroActiveSmallHeightSectorPairs.mp hpair).1
      have hpoint :=
        quadraticResidualWeight_le_tauEnvelope_mul_four_pow_sigma
          hM hB hactive
      have hsigma :=
        (mem_sigmaZeroActiveSmallHeightSectorPairs.mp hpair).2
      simpa only [factor, hsigma, pow_zero, Nat.mul_one] using hpoint
    _ = population.card * factor := by
      simp
    _ ≤ (boundedRelationalHosts N M L).card * factor :=
      Nat.mul_le_mul_right factor
        (hpopulationCard.trans
          (card_activeSectorPairs_le_boundedRelationalHosts
            hN terminal .smallCanonicalHeight))
    _ =
        4 ^ boundedSmallHeightTauEnvelope κ₀ A N L *
          (boundedRelationalHosts N M L).card := by
      dsimp only [factor]
      rw [Nat.mul_comm]

/-- The `σ>0` branch is charged to the base-four bounded rational mass. -/
theorem positiveSigmaQuadraticResidualMass_le
    {κ₀ N M A L : ℕ} (hN : 2 ≤ N)
    (hM : M ≤ κ₀ * N) (hB : 8 ≤ L + 1)
    (terminal : TerminalPredicateFamily) :
    positiveSigmaQuadraticResidualMass
        (M := M) (L := L) A hN terminal ≤
      2 * 4 ^ boundedSmallHeightTauEnvelope κ₀ A N L *
        boundedRationalMass N M A L 4 := by
  let population :=
    positiveSigmaActiveSmallHeightSectorPairs
      N M A L hN terminal
  let factor :=
    4 ^ boundedSmallHeightTauEnvelope κ₀ A N L
  have hsystematic :
      (∑ pair ∈ population, 4 ^ pairSigma A pair) ≤
        2 * boundedRationalMass N M A L 4 := by
    simpa only [population] using
      sum_four_pow_pairSigma_positive_le_two_mul_boundedRationalMass
        hN terminal
  unfold positiveSigmaQuadraticResidualMass quadraticResidualMass
  calc
    (∑ pair ∈ population,
        quadraticResidualWeight A hN pair) ≤
        ∑ pair ∈ population,
          factor * 4 ^ pairSigma A pair := by
      apply Finset.sum_le_sum
      intro pair hpair
      exact
        quadraticResidualWeight_le_tauEnvelope_mul_four_pow_sigma
          hM hB
          (mem_positiveSigmaActiveSmallHeightSectorPairs.mp hpair).1
    _ = factor * ∑ pair ∈ population,
        4 ^ pairSigma A pair := by
      rw [Finset.mul_sum]
    _ ≤ factor * (2 * boundedRationalMass N M A L 4) :=
      Nat.mul_le_mul_left factor hsystematic
    _ =
        2 * 4 ^ boundedSmallHeightTauEnvelope κ₀ A N L *
          boundedRationalMass N M A L 4 := by
      dsimp only [factor]
      ring

/-- Complete finite quadratic estimate for the second sector. -/
theorem activeSectorQuadraticResidualMass_le_finite_envelope
    {κ₀ N M A L : ℕ} (hN : 2 ≤ N)
    (hM : M ≤ κ₀ * N) (hB : 8 ≤ L + 1)
    (terminal : TerminalPredicateFamily) :
    activeSectorQuadraticResidualMass
        (M := M) (L := L) A hN terminal
        .smallCanonicalHeight ≤
      4 ^ boundedSmallHeightTauEnvelope κ₀ A N L *
          (boundedRelationalHosts N M L).card +
        2 * 4 ^ boundedSmallHeightTauEnvelope κ₀ A N L *
          boundedRationalMass N M A L 4 := by
  rw [activeSectorQuadraticResidualMass_eq_sigma_branches
    hN terminal]
  exact Nat.add_le_add
    (sigmaZeroQuadraticResidualMass_le hN hM hB terminal)
    (positiveSigmaQuadraticResidualMass_le hN hM hB terminal)

/-! ## The bounded base-four mass -/

/--
Base-four analogue of the common finite bound used for the systematic
base-two mass.  The proof is included here because the height-two term has
the genuinely different critical size `N · 4^(L/2) = O_C(N²)`.
-/
theorem boundedRationalMass_four_le_common
    {N M A L κ₀ : ℕ}
    (hN : 1 ≤ N) (hNM : N ≤ M) (hM : M ≤ κ₀ * N)
    (hA : 1 ≤ A) :
    boundedRationalMass N M A L 4 ≤
      16 * (κ₀ + 1) * (L + 1) ^ 4 * N *
        4 ^ (L / 2) := by
  have hfinite :=
    boundedRationalMass_le N M A L 4 hNM hA (by norm_num)
  have hfactorTwo :
      1 + (M - N) / 2 ≤ (κ₀ + 1) * N := by
    calc
      1 + (M - N) / 2 ≤ 1 + (M - N) :=
        Nat.add_le_add_left (Nat.div_le_self (M - N) 2) 1
      _ ≤ N + κ₀ * N := by
        have hwidth : M - N ≤ κ₀ * N :=
          (Nat.sub_le M N).trans hM
        omega
      _ = (κ₀ + 1) * N := by ring
  have hfactorThree :
      1 + (M - N) / 3 ≤ (κ₀ + 1) * N := by
    calc
      1 + (M - N) / 3 ≤ 1 + (M - N) :=
        Nat.add_le_add_left (Nat.div_le_self (M - N) 3) 1
      _ ≤ N + κ₀ * N := by
        have hwidth : M - N ≤ κ₀ * N :=
          (Nat.sub_le M N).trans hM
        omega
      _ = (κ₀ + 1) * N := by ring
  have hHpos : 0 < L + 1 := Nat.succ_pos L
  have hL : L ≤ L + 1 := Nat.le_succ L
  have hlinear : 3 * L + 1 ≤ 4 * (L + 1) := by
    omega
  have hHpow : L + 1 ≤ (L + 1) ^ 4 := by
    calc
      L + 1 = (L + 1) ^ 1 := by simp
      _ ≤ (L + 1) ^ 4 :=
        Nat.pow_le_pow_right hHpos (by omega)
  have hsmall :
      2 * ((3 * L + 1) * (1 + (M - N) / 2)) *
          4 ^ (L / 2) ≤
        8 * (κ₀ + 1) * (L + 1) ^ 4 * N *
          4 ^ (L / 2) := by
    calc
      2 * ((3 * L + 1) * (1 + (M - N) / 2)) *
            4 ^ (L / 2) ≤
          2 * ((4 * (L + 1)) * ((κ₀ + 1) * N)) *
            4 ^ (L / 2) :=
        Nat.mul_le_mul_right _
          (Nat.mul_le_mul_left 2
            (Nat.mul_le_mul hlinear hfactorTwo))
      _ = 8 * (κ₀ + 1) * (L + 1) * N *
          4 ^ (L / 2) := by ring
      _ ≤ 8 * (κ₀ + 1) * (L + 1) ^ 4 * N *
          4 ^ (L / 2) := by
        exact Nat.mul_le_mul_right _
          (Nat.mul_le_mul_right N
            (Nat.mul_le_mul_left (8 * (κ₀ + 1)) hHpow))
  have htwoL : 2 * L ≤ 2 * (L + 1) :=
    Nat.mul_le_mul_left 2 hL
  have honeSquare : 1 ≤ (L + 1) * (L + 1) := by
    nlinarith
  have hinner :
      (2 * L) * L + 1 ≤
        (2 * (L + 1)) * (L + 1) +
          (L + 1) * (L + 1) :=
    Nat.add_le_add
      (Nat.mul_le_mul htwoL hL) honeSquare
  have hfront :
      L * (2 * L) ≤
        (L + 1) * (2 * (L + 1)) :=
    Nat.mul_le_mul hL htwoL
  have hlargePoly :
      L * (2 * L) * ((2 * L) * L + 1) ≤
        6 * (L + 1) ^ 4 := by
    calc
      L * (2 * L) * ((2 * L) * L + 1) ≤
          ((L + 1) * (2 * (L + 1))) *
            ((2 * (L + 1)) * (L + 1) +
              (L + 1) * (L + 1)) :=
        Nat.mul_le_mul hfront hinner
      _ = 6 * (L + 1) ^ 4 := by ring
  have hthirdHalf : L / 3 ≤ L / 2 :=
    Nat.div_le_div_left (by omega : 2 ≤ 3) (by omega)
  have hpow :
      4 ^ (L / 3) ≤ 4 ^ (L / 2) :=
    Nat.pow_le_pow_right (by norm_num) hthirdHalf
  have hlarge :
      L * (2 * L) * ((2 * L) * L + 1) *
          (1 + (M - N) / 3) * 4 ^ (L / 3) ≤
        6 * (κ₀ + 1) * (L + 1) ^ 4 * N *
          4 ^ (L / 2) := by
    calc
      L * (2 * L) * ((2 * L) * L + 1) *
            (1 + (M - N) / 3) * 4 ^ (L / 3) ≤
          (6 * (L + 1) ^ 4) * ((κ₀ + 1) * N) *
            4 ^ (L / 2) :=
        Nat.mul_le_mul
          (Nat.mul_le_mul hlargePoly hfactorThree)
          hpow
      _ = 6 * (κ₀ + 1) * (L + 1) ^ 4 * N *
          4 ^ (L / 2) := by ring
  calc
    boundedRationalMass N M A L 4 ≤
        2 * ((3 * L + 1) * (1 + (M - N) / 2)) *
            4 ^ (L / 2) +
          L * (2 * L) * ((2 * L) * L + 1) *
            (1 + (M - N) / 3) * 4 ^ (L / 3) :=
      hfinite
    _ ≤
        8 * (κ₀ + 1) * (L + 1) ^ 4 * N *
            4 ^ (L / 2) +
          6 * (κ₀ + 1) * (L + 1) ^ 4 * N *
            4 ^ (L / 2) :=
      Nat.add_le_add hsmall hlarge
    _ = 14 * (κ₀ + 1) * (L + 1) ^ 4 * N *
        4 ^ (L / 2) := by ring
    _ ≤ 16 * (κ₀ + 1) * (L + 1) ^ 4 * N *
        4 ^ (L / 2) := by
      exact Nat.mul_le_mul_right _
        (Nat.mul_le_mul_right N
          (Nat.mul_le_mul_right ((L + 1) ^ 4)
            (Nat.mul_le_mul_right (κ₀ + 1) (by omega))))

/-! ## Endpoint-independent real envelopes -/

noncomputable def boundedSmallHeightTauFactor
    (κ₀ A N L : ℕ) : ℝ :=
  ((4 ^ boundedSmallHeightTauEnvelope κ₀ A N L : ℕ) : ℝ)

/-- Critical `N²` envelope for the exact bounded base-four rational mass. -/
noncomputable def boundedRationalMassFourEnvelope
    (C : ℝ) (κ₀ N L : ℕ) : ℝ :=
  (16 * (κ₀ + 1) : ℝ) *
    CriticalRunWindow.balanceConstant C *
    ((L + 1 : ℝ) ^ 4) * (N : ℝ) ^ 2

/-- Quadratic enlargement of the common host envelope. -/
noncomputable def boundedRelationalHostQuadraticEnvelope
    (κ₀ N L : ℕ) : ℝ :=
  (N : ℝ) ^ 2 *
    boundedRelationalHostResidual κ₀ N L

noncomputable def sigmaZeroQuadraticEnvelope
    (κ₀ A N L : ℕ) : ℝ :=
  boundedSmallHeightTauFactor κ₀ A N L *
    boundedRelationalHostQuadraticEnvelope κ₀ N L

noncomputable def positiveSigmaQuadraticEnvelope
    (C : ℝ) (κ₀ A N L : ℕ) : ℝ :=
  2 * boundedSmallHeightTauFactor κ₀ A N L *
    boundedRationalMassFourEnvelope C κ₀ N L

/-- Common quadratic envelope for the complete second sector. -/
noncomputable def boundedSmallHeightQuadraticEnvelope
    (C : ℝ) (κ₀ A N L : ℕ) : ℝ :=
  sigmaZeroQuadraticEnvelope κ₀ A N L +
    positiveSigmaQuadraticEnvelope C κ₀ A N L

/-- Cauchy--Schwarz envelope for the linear residual mass. -/
noncomputable def boundedSmallHeightLinearEnvelope
    (C : ℝ) (κ₀ A N L : ℕ) : ℝ :=
  Real.sqrt (boundedRelationalHostEnvelope κ₀ N L) *
    Real.sqrt
      (boundedSmallHeightQuadraticEnvelope C κ₀ A N L)

theorem four_pow_boundedSmallHeightTauEnvelope_uniformSubpolynomial
    {C : ℝ} (hC : 0 ≤ C) (κ₀ A : ℕ) :
    UniformSubpolynomialOn
      (CriticalRunWindow.InRunLengthWindow C)
      (boundedSmallHeightTauFactor κ₀ A) := by
  have hcorrected :
      UniformSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C)
        (fun N L =>
          (((4 ^
            maxCanonicalCorrectedDefectCount κ₀ A N L :
              ℕ) : ℝ))) :=
    four_pow_maxCanonicalCorrectedDefectCount_uniformSubpolynomial
      hC κ₀ A
  have hcomponents :
      UniformSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C)
        (fun _ L =>
          (((4 ^
            smallHeightResidualComponentEnvelope L :
              ℕ) : ℝ))) :=
    SmallHeightComponentEnvelopeCritical.four_pow_smallHeightResidualComponentEnvelope_uniformSubpolynomial
      hC
  have hproduct :=
    ExpSqrtLog.uniformSubpolynomialOn_mul
      hcorrected hcomponents
  unfold boundedSmallHeightTauFactor
  simpa only [
    boundedSmallHeightTauEnvelope, pow_add, Nat.cast_mul] using
      hproduct

/-- The exact bounded base-four mass is dominated by its quadratic real
envelope in the critical window. -/
theorem boundedRationalMass_cast_le_fourEnvelope
    {C : ℝ} {κ₀ N M A L : ℕ}
    (hN : 1 ≤ N) (hNM : N ≤ M) (hM : M ≤ κ₀ * N)
    (hA : 1 ≤ A)
    (hrun : CriticalRunWindow.InRunLengthWindow C N L) :
    (boundedRationalMass N M A L 4 : ℝ) ≤
      boundedRationalMassFourEnvelope C κ₀ N L := by
  have hfinite :=
    boundedRationalMass_four_le_common
      (L := L) hN hNM hM hA
  have hfiniteCast :
      (boundedRationalMass N M A L 4 : ℝ) ≤
        (16 * (κ₀ + 1) : ℝ) *
          ((L + 1 : ℝ) ^ 4) * (N : ℝ) *
            ((4 ^ (L / 2) : ℕ) : ℝ) := by
    exact_mod_cast hfinite
  have hpow :=
    CriticalChannelPowers.four_pow_half_cast_le_balance_mul
      (by omega : 0 < N) hrun
  calc
    (boundedRationalMass N M A L 4 : ℝ) ≤
        (16 * (κ₀ + 1) : ℝ) *
          ((L + 1 : ℝ) ^ 4) * (N : ℝ) *
            ((4 ^ (L / 2) : ℕ) : ℝ) :=
      hfiniteCast
    _ ≤
        (16 * (κ₀ + 1) : ℝ) *
          ((L + 1 : ℝ) ^ 4) * (N : ℝ) *
            (CriticalRunWindow.balanceConstant C * (N : ℝ)) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = boundedRationalMassFourEnvelope C κ₀ N L := by
      unfold boundedRationalMassFourEnvelope
      ring

/-- The quadratic enlargement really dominates the sharper
`N sqrt N` host envelope. -/
theorem boundedRelationalHostEnvelope_le_quadraticEnvelope
    {κ₀ N L : ℕ} (hN : 1 ≤ N) :
    boundedRelationalHostEnvelope κ₀ N L ≤
      boundedRelationalHostQuadraticEnvelope κ₀ N L := by
  have hNone : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hN
  have hsqrtNonneg : 0 ≤ Real.sqrt (N : ℝ) :=
    Real.sqrt_nonneg _
  have hsqrtSq :
      (Real.sqrt (N : ℝ)) ^ 2 = (N : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hsqrt : Real.sqrt (N : ℝ) ≤ (N : ℝ) := by
    nlinarith
  have hresidual :
      0 ≤ boundedRelationalHostResidual κ₀ N L := by
    unfold boundedRelationalHostResidual
    positivity
  unfold boundedRelationalHostEnvelope
    boundedRelationalHostQuadraticEnvelope
  calc
    (N : ℝ) * Real.sqrt N *
          boundedRelationalHostResidual κ₀ N L ≤
        (N : ℝ) * (N : ℝ) *
          boundedRelationalHostResidual κ₀ N L := by
      exact
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsqrt (by positivity))
          hresidual
    _ =
        (N : ℝ) ^ 2 *
          boundedRelationalHostResidual κ₀ N L := by ring

/-- The pure square has the repository's quadratic rational-power bound. -/
theorem natSquare_uniformQuadratic
    (admissible : ℕ → ℕ → Prop) :
    UniformRationalPowerSubpolynomialOn 2 1 admissible
      (fun N _ ↦ (N : ℝ) ^ 2) := by
  intro k hk
  refine ⟨1, ?_⟩
  intro N hN L _hNL
  have hNone : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hN
  rw [abs_of_nonneg (by positivity), one_mul, ← pow_mul]
  exact pow_le_pow_right₀ hNone (by omega)

/-- The critical base-four mass envelope is `N^(2+o(1))`. -/
theorem boundedRationalMassFourEnvelope_uniformQuadratic
    {C : ℝ} (hC : 0 ≤ C) (κ₀ : ℕ) :
    UniformRationalPowerSubpolynomialOn 2 1
      (CriticalRunWindow.InRunLengthWindow C)
      (boundedRationalMassFourEnvelope C κ₀) := by
  let admissible := CriticalRunWindow.InRunLengthWindow C
  let loss : ℕ → ℕ → ℝ :=
    fun _ L =>
      (16 * (κ₀ + 1) : ℝ) *
        CriticalRunWindow.balanceConstant C *
          ((L + 1 : ℝ) ^ 4)
  have hH :=
    CriticalRationalMassEnvelopes.runLengthAddOne_uniformSubpolynomial
      hC
  have hH2 :=
    ExpSqrtLog.uniformSubpolynomialOn_mul hH hH
  have hH4 :=
    ExpSqrtLog.uniformSubpolynomialOn_mul hH2 hH2
  have hloss :
      UniformSubpolynomialOn admissible loss := by
    have hconst :=
      ExpSqrtLog.uniformSubpolynomialOn_const_mul
        ((16 * (κ₀ + 1) : ℝ) *
          CriticalRunWindow.balanceConstant C)
        hH4
    convert hconst using 1
    funext N L
    dsimp only [loss]
    push_cast
    ring
  have hsquare :=
    natSquare_uniformQuadratic admissible
  have hproduct :=
    UniformRationalPower.mul_subpolynomial
      (p := 2) (q := 1) (by omega) hsquare hloss
  exact hproduct

/-- The quadratic enlargement of the host envelope is still
`N^(2+o(1))`. -/
theorem boundedRelationalHostQuadraticEnvelope_uniformQuadratic
    {C : ℝ} (hC : 0 ≤ C) (κ₀ : ℕ) :
    UniformRationalPowerSubpolynomialOn 2 1
      (CriticalRunWindow.InRunLengthWindow C)
      (boundedRelationalHostQuadraticEnvelope κ₀) := by
  let admissible := CriticalRunWindow.InRunLengthWindow C
  have hsquare :=
    natSquare_uniformQuadratic admissible
  have hresidual :
      UniformSubpolynomialOn admissible
        (boundedRelationalHostResidual κ₀) := by
    simpa only [admissible] using
      boundedRelationalHostResidual_uniformSubpolynomial hC κ₀
  have hproduct :=
    UniformRationalPower.mul_subpolynomial
      (p := 2) (q := 1) (by omega) hsquare hresidual
  convert hproduct using 1
  funext N L
  unfold boundedRelationalHostQuadraticEnvelope
  ring

theorem sigmaZeroQuadraticEnvelope_uniformQuadratic
    {C : ℝ} (hC : 0 ≤ C) (κ₀ A : ℕ) :
    UniformRationalPowerSubpolynomialOn 2 1
      (CriticalRunWindow.InRunLengthWindow C)
      (sigmaZeroQuadraticEnvelope κ₀ A) := by
  have hhost :=
    boundedRelationalHostQuadraticEnvelope_uniformQuadratic
      hC κ₀
  have htau :=
    four_pow_boundedSmallHeightTauEnvelope_uniformSubpolynomial
      hC κ₀ A
  exact
    UniformRationalPower.mul_subpolynomial
      (p := 2) (q := 1) (by omega) hhost htau

theorem positiveSigmaQuadraticEnvelope_uniformQuadratic
    {C : ℝ} (hC : 0 ≤ C) (κ₀ A : ℕ) :
    UniformRationalPowerSubpolynomialOn 2 1
      (CriticalRunWindow.InRunLengthWindow C)
      (positiveSigmaQuadraticEnvelope C κ₀ A) := by
  have hbase :=
    boundedRationalMassFourEnvelope_uniformQuadratic hC κ₀
  have htau :=
    four_pow_boundedSmallHeightTauEnvelope_uniformSubpolynomial
      hC κ₀ A
  have hfactor :
      UniformSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C)
        (fun N L =>
          2 * boundedSmallHeightTauFactor κ₀ A N L) :=
    ExpSqrtLog.uniformSubpolynomialOn_const_mul 2 htau
  exact
    UniformRationalPower.mul_subpolynomial
      (p := 2) (q := 1) (by omega) hbase hfactor

/-- The complete quadratic envelope has size `N^(2+o(1))`. -/
theorem boundedSmallHeightQuadraticEnvelope_uniformQuadratic
    {C : ℝ} (hC : 0 ≤ C) (κ₀ A : ℕ) :
    UniformRationalPowerSubpolynomialOn 2 1
      (CriticalRunWindow.InRunLengthWindow C)
      (boundedSmallHeightQuadraticEnvelope C κ₀ A) := by
  exact
    UniformRationalPower.add_quadratic
      (sigmaZeroQuadraticEnvelope_uniformQuadratic hC κ₀ A)
      (positiveSigmaQuadraticEnvelope_uniformQuadratic
        hC κ₀ A)

/-! ## Finite domination by the real envelopes -/

theorem boundedRationalMassFourEnvelope_nonneg
    (C : ℝ) (κ₀ N L : ℕ) :
    0 ≤ boundedRationalMassFourEnvelope C κ₀ N L := by
  have hbalance :=
    CriticalRunWindow.balanceConstant_nonneg C
  unfold boundedRationalMassFourEnvelope
  positivity

theorem boundedRelationalHostQuadraticEnvelope_nonneg
    (κ₀ N L : ℕ) :
    0 ≤ boundedRelationalHostQuadraticEnvelope κ₀ N L := by
  unfold boundedRelationalHostQuadraticEnvelope
    boundedRelationalHostResidual
  positivity

theorem sigmaZeroQuadraticEnvelope_nonneg
    (κ₀ A N L : ℕ) :
    0 ≤ sigmaZeroQuadraticEnvelope κ₀ A N L := by
  unfold sigmaZeroQuadraticEnvelope
    boundedSmallHeightTauFactor
  exact mul_nonneg (by positivity)
    (boundedRelationalHostQuadraticEnvelope_nonneg κ₀ N L)

theorem positiveSigmaQuadraticEnvelope_nonneg
    (C : ℝ) (κ₀ A N L : ℕ) :
    0 ≤ positiveSigmaQuadraticEnvelope C κ₀ A N L := by
  unfold positiveSigmaQuadraticEnvelope
    boundedSmallHeightTauFactor
  exact
    mul_nonneg
      (mul_nonneg (by norm_num) (by positivity))
      (boundedRationalMassFourEnvelope_nonneg C κ₀ N L)

theorem boundedSmallHeightQuadraticEnvelope_nonneg
    (C : ℝ) (κ₀ A N L : ℕ) :
    0 ≤ boundedSmallHeightQuadraticEnvelope C κ₀ A N L := by
  unfold boundedSmallHeightQuadraticEnvelope
  exact add_nonneg
    (sigmaZeroQuadraticEnvelope_nonneg κ₀ A N L)
    (positiveSigmaQuadraticEnvelope_nonneg C κ₀ A N L)

theorem boundedSmallHeightLinearEnvelope_nonneg
    (C : ℝ) (κ₀ A N L : ℕ) :
    0 ≤ boundedSmallHeightLinearEnvelope C κ₀ A N L := by
  unfold boundedSmallHeightLinearEnvelope
  exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/-- Real form of the complete finite quadratic estimate. -/
theorem activeSectorQuadraticResidualMass_cast_le_quadraticEnvelope
    {C : ℝ} {κ₀ N M A L : ℕ}
    (hN : 2 ≤ N) (hNM : N ≤ M) (hM : M ≤ κ₀ * N)
    (hL : L ≤ N) (hB : 8 ≤ L + 1) (hA : 1 ≤ A)
    (terminal : TerminalPredicateFamily)
    (hrun : CriticalRunWindow.InRunLengthWindow C N L) :
    (activeSectorQuadraticResidualMass
        (M := M) (L := L) A hN terminal
        .smallCanonicalHeight : ℝ) ≤
      boundedSmallHeightQuadraticEnvelope C κ₀ A N L := by
  have hfinite :=
    activeSectorQuadraticResidualMass_le_finite_envelope
      (A := A) hN hM hB terminal
  have hfiniteReal :
      (activeSectorQuadraticResidualMass
          (M := M) (L := L) A hN terminal
          .smallCanonicalHeight : ℝ) ≤
        boundedSmallHeightTauFactor κ₀ A N L *
            ((boundedRelationalHosts N M L).card : ℝ) +
          2 * boundedSmallHeightTauFactor κ₀ A N L *
            (boundedRationalMass N M A L 4 : ℝ) := by
    unfold boundedSmallHeightTauFactor
    exact_mod_cast hfinite
  have hhost :
      ((boundedRelationalHosts N M L).card : ℝ) ≤
        boundedRelationalHostQuadraticEnvelope κ₀ N L := by
    exact
      (card_boundedRelationalHosts_cast_le_common
        hN hNM hM hL).trans
        (boundedRelationalHostEnvelope_le_quadraticEnvelope
          (by omega))
  have hrational :
      (boundedRationalMass N M A L 4 : ℝ) ≤
        boundedRationalMassFourEnvelope C κ₀ N L :=
    boundedRationalMass_cast_le_fourEnvelope
      (by omega) hNM hM hA hrun
  calc
    (activeSectorQuadraticResidualMass
          (M := M) (L := L) A hN terminal
          .smallCanonicalHeight : ℝ) ≤
        boundedSmallHeightTauFactor κ₀ A N L *
            ((boundedRelationalHosts N M L).card : ℝ) +
          2 * boundedSmallHeightTauFactor κ₀ A N L *
            (boundedRationalMass N M A L 4 : ℝ) :=
      hfiniteReal
    _ ≤
        boundedSmallHeightTauFactor κ₀ A N L *
            boundedRelationalHostQuadraticEnvelope κ₀ N L +
          2 * boundedSmallHeightTauFactor κ₀ A N L *
            boundedRationalMassFourEnvelope C κ₀ N L :=
      add_le_add
        (mul_le_mul_of_nonneg_left hhost
          (by
            unfold boundedSmallHeightTauFactor
            positivity))
        (mul_le_mul_of_nonneg_left hrational
          (by
            exact mul_nonneg (by norm_num)
              (by
                unfold boundedSmallHeightTauFactor
                positivity)))
    _ = boundedSmallHeightQuadraticEnvelope C κ₀ A N L := by
      unfold boundedSmallHeightQuadraticEnvelope
        sigmaZeroQuadraticEnvelope
        positiveSigmaQuadraticEnvelope
      rfl

/-- The literal linear residual sector is dominated by the two-variable
Cauchy--Schwarz envelope. -/
theorem sectorResidualMassNat_cast_le_linearEnvelope
    {C : ℝ} {κ₀ N M A L : ℕ}
    (hN : 2 ≤ N) (hNM : N ≤ M) (hM : M ≤ κ₀ * N)
    (hL : L ≤ N) (hB : 8 ≤ L + 1) (hA : 1 ≤ A)
    (terminal : TerminalPredicateFamily)
    (hrun : CriticalRunWindow.InRunLengthWindow C N L) :
    (sectorResidualMassNat
        (M := M) (L := L) A hN terminal
        .smallCanonicalHeight : ℝ) ≤
      boundedSmallHeightLinearEnvelope C κ₀ A N L := by
  have hinterp :=
    sectorResidualMassNat_cast_le_host_sqrt_mul_quadratic_sqrt
      (M := M) (A := A) (L := L)
      hN terminal .smallCanonicalHeight
  have hhost :
      ((boundedRelationalHosts N M L).card : ℝ) ≤
        boundedRelationalHostEnvelope κ₀ N L :=
    card_boundedRelationalHosts_cast_le_common
      hN hNM hM hL
  have hquadratic :=
    activeSectorQuadraticResidualMass_cast_le_quadraticEnvelope
      hN hNM hM hL hB hA terminal hrun
  calc
    (sectorResidualMassNat
          (M := M) (L := L) A hN terminal
          .smallCanonicalHeight : ℝ) ≤
        Real.sqrt ((boundedRelationalHosts N M L).card : ℝ) *
          Real.sqrt
            (activeSectorQuadraticResidualMass
              (M := M) (L := L) A hN terminal
              .smallCanonicalHeight : ℝ) :=
      hinterp
    _ ≤
        Real.sqrt (boundedRelationalHostEnvelope κ₀ N L) *
          Real.sqrt
            (boundedSmallHeightQuadraticEnvelope
              C κ₀ A N L) :=
      mul_le_mul
        (Real.sqrt_le_sqrt hhost)
        (Real.sqrt_le_sqrt hquadratic)
        (Real.sqrt_nonneg _)
        (Real.sqrt_nonneg _)
    _ = boundedSmallHeightLinearEnvelope C κ₀ A N L := by
      rfl

/-! ## Interpolation and little-oh -/

/-- The endpoint-independent linear envelope has exponent `7/4`. -/
theorem boundedSmallHeightLinearEnvelope_uniformSevenFourths
    {C : ℝ} (hC : 0 ≤ C) (κ₀ A : ℕ) :
    UniformRationalPowerSubpolynomialOn 7 4
      (CriticalRunWindow.InRunLengthWindow C)
      (boundedSmallHeightLinearEnvelope C κ₀ A) := by
  have hhosts :=
    boundedRelationalHostEnvelope_uniformThreeHalves hC κ₀
  have hquadratic :=
    boundedSmallHeightQuadraticEnvelope_uniformQuadratic
      hC κ₀ A
  apply
    UniformRationalPower.interpolate_threeHalves_quadratic
      hhosts hquadratic
  refine ⟨0, ?_⟩
  intro N _hN L _hrun
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold boundedRelationalHostEnvelope
      boundedRelationalHostResidual
    positivity
  · exact
      boundedSmallHeightQuadraticEnvelope_nonneg
        C κ₀ A N L
  · exact
      boundedSmallHeightLinearEnvelope_nonneg
        C κ₀ A N L
  · rfl

/-- The interpolated envelope is uniformly negligible relative to `N²`. -/
theorem boundedSmallHeightLinearEnvelope_uniformLittleO_square
    {C : ℝ} (hC : 0 ≤ C) (κ₀ A : ℕ) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (boundedSmallHeightLinearEnvelope C κ₀ A)
      (fun N _ ↦ (N : ℝ) ^ 2) := by
  apply UniformRationalPower.littleO_natPower_of_lt
    (p := 7) (q := 4) (r := 2) (by omega)
  exact
    boundedSmallHeightLinearEnvelope_uniformSevenFourths
      hC κ₀ A

/--
Closure of the internal bridge for Lemma 17.15: the literal second sector
is uniformly little-oh of `N²` for every bounded endpoint ratio.
-/
theorem smallCanonicalHeightSectorStability
    {C : ℝ} (hC : 0 ≤ C)
    (κ₀ A : ℕ) (hA : 1 ≤ A)
    (terminal : TerminalPredicateFamily) :
    SmallCanonicalHeightSectorStabilityStatement
      C κ₀ A terminal := by
  unfold SmallCanonicalHeightSectorStabilityStatement
  apply
    uniformLittleOInBoundedRatioWindow_of_nonnegative_envelope
      (boundedSmallHeightLinearEnvelope_uniformLittleO_square
        hC κ₀ A)
  · intro N M L
    unfold sectorResidualMass
    split_ifs <;> positivity
  · exact
      boundedSmallHeightLinearEnvelope_nonneg C κ₀ A
  · obtain ⟨Nwindow, hwindow⟩ :=
      CriticalRunWindow.firstMomentWindow_eventually hC
    have hupperNonneg :
        0 ≤ CriticalRunWindow.upperConstant :=
      (CriticalRunWindow.lowerConstant_pos.trans
        CriticalRunWindow.lowerConstant_lt_upperConstant).le
    obtain ⟨Nlength, hlength⟩ :=
      ExpSqrtLog.linear_log_add_one_pow_le_nat_eventually
        CriticalRunWindow.upperConstant hupperNonneg 1 (by omega)
    obtain ⟨Nadm, hNadm⟩ :=
      CriticalWeightedDefect.admissible_eventually
        CriticalRunWindow.lowerConstant_pos
        CriticalRunWindow.lowerConstant_lt_upperConstant
    obtain ⟨Nheight, hNheight⟩ :=
      CriticalWeightedDefect.height_tends_to_infinity
        (c₂ := CriticalRunWindow.upperConstant)
        CriticalRunWindow.lowerConstant_pos 8
    refine
      ⟨max 2
        (max Nwindow (max Nlength (max Nadm Nheight))), ?_⟩
    intro N hN M L hNM hM hrun
    have hNtwo : 2 ≤ N :=
      (le_max_left 2
        (max Nwindow (max Nlength (max Nadm Nheight)))).trans hN
    have htail :
        max Nwindow (max Nlength (max Nadm Nheight)) ≤ N :=
      (le_max_right 2
        (max Nwindow (max Nlength (max Nadm Nheight)))).trans hN
    have hNwindow : Nwindow ≤ N :=
      (le_max_left Nwindow
        (max Nlength (max Nadm Nheight))).trans htail
    have htail₂ :
        max Nlength (max Nadm Nheight) ≤ N :=
      (le_max_right Nwindow
        (max Nlength (max Nadm Nheight))).trans htail
    have hNlength : Nlength ≤ N :=
      (le_max_left Nlength (max Nadm Nheight)).trans htail₂
    have htail₃ : max Nadm Nheight ≤ N :=
      (le_max_right Nlength (max Nadm Nheight)).trans htail₂
    have hNadmN : Nadm ≤ N :=
      (le_max_left Nadm Nheight).trans htail₃
    have hNheightN : Nheight ≤ N :=
      (le_max_right Nadm Nheight).trans htail₃
    have hfirst := hwindow N hNwindow L hrun
    have hLplusTwoReal :
        (((L + 1) + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by
      simpa using
        hlength N hNlength (L + 1) hfirst.1.2.2.2
    have hL : L ≤ N := by
      have hLplusTwo : (L + 1) + 1 ≤ N := by
        exact_mod_cast hLplusTwoReal
      omega
    have hadmissible :
        CriticalWeightedDefect.Admissible
          CriticalRunWindow.lowerConstant
          CriticalRunWindow.upperConstant N (L + 1) :=
      hNadm N hNadmN (L + 1) hfirst.1
    have hB : 8 ≤ L + 1 :=
      hNheight N hNheightN (L + 1) hadmissible
    have hbase : N ≤ M := by omega
    have hfinite :=
      sectorResidualMassNat_cast_le_linearEnvelope
        hNtwo hbase hM hL hB hA terminal hrun
    simpa only [sectorResidualMass, dif_pos hNtwo] using hfinite

end

end BoundedRatioSmallHeightSector
end PaperC
