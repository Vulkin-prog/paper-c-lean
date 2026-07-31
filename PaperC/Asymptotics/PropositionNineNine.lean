import PaperC.Asymptotics.CorrectedDefectEnvelope
import PaperC.Asymptotics.CriticalChannelPowers
import PaperC.Asymptotics.HalfPower
import PaperC.Asymptotics.LinearPower
import PaperC.Asymptotics.PropositionNineNineHostGeometry
import PaperC.Asymptotics.ThreeHalvesPower
import PaperC.Combinatorics.SectionSevenPartition

set_option maxHeartbeats 1800000

/-!
# Proposition 9.9: the branch with at least three corrected defects

This module formalizes the finite and asymptotic bookkeeping in
Proposition 9.9.  The population used below is the literal subset of the
deep core on which

* the systematic exponent is zero; and
* the corrected defect count satisfies `3 ≤ D#`.

The name `sigmaZero` is deliberate: identifying this finite predicate with
the manuscript's nonaligned branch uses the Section 8 exclusion and is not
silently built into the definition.

The exact vertex budget

`D# + 2*c# ≤ 2*B`

implies the integral form

`D# + c# ≤ B + D#/2`.

Together with Lemma 6.4, this bounds every linear residual weight by

`2^(B + max(D#)/2)`.

The existing uniform defect envelope proves that the second factor is
subpolynomial, while the critical run-length window makes `2^B` linear in
`N`.  Consequently, a uniform `N^(1/2+o_C(1))` bound for the number of
hosts implies the claimed `N^(3/2+o_C(1))` mass bound.

The host-count premise is retained explicitly.  Its proof is precisely the
still-unassembled Diophantine passage combining Lemmas 9.4 and 9.8 with the
bounded-component extraction.
-/

namespace PaperC
namespace PropositionNineNine

open Affine
open CorrectedDefectEnvelope
open LargePrimeGraph
open RationalMassFinite
open ResidualComponentCounts
open ResidualMasses
open SectionSevenPartition

noncomputable section

noncomputable local instance instDecidableLargePrimeAdj
    (x y L : ℕ) :
    DecidableRel (largePrimeGraph x y L).Adj :=
  Classical.decRel _

/-! ## Exact arithmetic of the core budget -/

/--
Division-free form of the exponent estimate in Proposition 9.9:

`2 * (D + c) ≤ 2 * B + D`.
-/
theorem twice_defect_add_component_le
    {B D c : ℕ}
    (hbudget : D + 2 * c ≤ 2 * B) :
    2 * (D + c) ≤ 2 * B + D := by
  omega

/--
Integral form of

`D + c ≤ B + D/2`.

Natural-number division records the floor automatically, so this statement
is slightly sharper than the corresponding real-valued inequality.
-/
theorem defect_add_component_le_height_add_half_defect
    {B D c : ℕ}
    (hbudget : D + 2 * c ≤ 2 * B) :
    D + c ≤ B + D / 2 := by
  omega

/--
If `D` is bounded by an auxiliary envelope `E`, then
`D + c ≤ B + E/2`.
-/
theorem defect_add_component_le_height_add_half_envelope
    {B D c E : ℕ}
    (hbudget : D + 2 * c ≤ 2 * B)
    (hD : D ≤ E) :
    D + c ≤ B + E / 2 := by
  exact
    (defect_add_component_le_height_add_half_defect hbudget).trans
      (Nat.add_le_add_left (Nat.div_le_div_right hD) B)

/--
An exact `o(B)`-style slack interface: if `D ≤ 2*s`, then
`D + c ≤ B + s`.
-/
theorem defect_add_component_le_height_add_slack
    {B D c s : ℕ}
    (hbudget : D + 2 * c ≤ 2 * B)
    (hD : D ≤ 2 * s) :
    D + c ≤ B + s := by
  have hhalf : D / 2 ≤ s := by omega
  exact
    (defect_add_component_le_height_add_half_defect hbudget).trans
      (Nat.add_le_add_left hhalf B)

/-! ## The literal finite population -/

/--
The finite branch of Proposition 9.9 before the host-counting argument:
deep core, zero systematic exponent, and at least three corrected defects.
-/
noncomputable def sigmaZeroDeepCoreAtLeastThreeDefectsPairs
    (N A L : ℕ) (hN : 2 ≤ N) :
    Finset (SeparatedDyadicPair N L) := by
  classical
  exact (deepCorePairs N A L hN).filter fun pair ↦
    pairSigma A pair = 0 ∧
      3 ≤ canonicalCorrectedDefectCount
        A pair.1.1 pair.1.2 L

@[simp]
theorem mem_sigmaZeroDeepCoreAtLeastThreeDefectsPairs
    {N A L : ℕ} {hN : 2 ≤ N}
    {pair : SeparatedDyadicPair N L} :
    pair ∈ sigmaZeroDeepCoreAtLeastThreeDefectsPairs N A L hN ↔
      pair ∈ deepCorePairs N A L hN ∧
        pairSigma A pair = 0 ∧
          3 ≤ canonicalCorrectedDefectCount
            A pair.1.1 pair.1.2 L := by
  simp [sigmaZeroDeepCoreAtLeastThreeDefectsPairs]

/-- Every member of the branch has zero systematic exponent. -/
theorem pairSigma_eq_zero_of_mem
    {N A L : ℕ} {hN : 2 ≤ N}
    {pair : SeparatedDyadicPair N L}
    (hpair :
      pair ∈ sigmaZeroDeepCoreAtLeastThreeDefectsPairs N A L hN) :
    pairSigma A pair = 0 :=
  (mem_sigmaZeroDeepCoreAtLeastThreeDefectsPairs.mp hpair).2.1

/-- Every member of the branch has at least three corrected defects. -/
theorem three_le_correctedDefectCount_of_mem
    {N A L : ℕ} {hN : 2 ≤ N}
    {pair : SeparatedDyadicPair N L}
    (hpair :
      pair ∈ sigmaZeroDeepCoreAtLeastThreeDefectsPairs N A L hN) :
    3 ≤ canonicalCorrectedDefectCount
      A pair.1.1 pair.1.2 L :=
  (mem_sigmaZeroDeepCoreAtLeastThreeDefectsPairs.mp hpair).2.2

/--
The mass-contributing subpopulation.  Pairs with `τ=0` have exactly zero
linear residual weight, so they need not enter the Diophantine host count.
-/
noncomputable def activeSigmaZeroDeepCoreAtLeastThreeDefectsPairs
    (N A L : ℕ) (hN : 2 ≤ N) :
    Finset (SeparatedDyadicPair N L) :=
  (sigmaZeroDeepCoreAtLeastThreeDefectsPairs N A L hN).filter
    fun pair ↦ 0 < pairTau A hN pair

@[simp]
theorem mem_activeSigmaZeroDeepCoreAtLeastThreeDefectsPairs
    {N A L : ℕ} {hN : 2 ≤ N}
    {pair : SeparatedDyadicPair N L} :
    pair ∈
        activeSigmaZeroDeepCoreAtLeastThreeDefectsPairs
          N A L hN ↔
      pair ∈
          sigmaZeroDeepCoreAtLeastThreeDefectsPairs
            N A L hN ∧
        0 < pairTau A hN pair := by
  simp [activeSigmaZeroDeepCoreAtLeastThreeDefectsPairs]

/-- The active population is a literal subset of the original branch. -/
theorem activeSigmaZeroDeepCoreAtLeastThreeDefectsPairs_subset
    {N A L : ℕ} (hN : 2 ≤ N) :
    activeSigmaZeroDeepCoreAtLeastThreeDefectsPairs
        N A L hN ⊆
      sigmaZeroDeepCoreAtLeastThreeDefectsPairs
        N A L hN :=
  Finset.filter_subset _ _

/--
Every active host has the two concrete structural certificates used in the
manuscript proof: one block has at least two interval defects, and the
canonical residual family contains a component with at most ten vertices.
-/
theorem activeHost_defectInterval_and_boundedComponent
    {N A L : ℕ} {hN : 2 ≤ N}
    {pair : SeparatedDyadicPair N L}
    (hpair :
      pair ∈
        activeSigmaZeroDeepCoreAtLeastThreeDefectsPairs
          N A L hN) :
    (2 ≤
          (IntervalDefectBound.defectsInInterval
            (L + 1) (pair.1.1 - 1)).card ∨
        2 ≤
          (IntervalDefectBound.defectsInInterval
            (L + 1) (pair.1.2 - 1)).card) ∧
      ∃ C ∈
          CanonicalResidualComponents.canonicalResidualComponents
            A pair.1.1 pair.1.2 L,
        2 ≤ Fintype.card C.supp ∧
          Fintype.card C.supp ≤ 10 := by
  have hbranch :=
    (mem_activeSigmaZeroDeepCoreAtLeastThreeDefectsPairs.mp
      hpair).1
  exact
    PropositionNineNineHostGeometry.defectInterval_and_boundedComponent_of_deepCore
      hN
      (mem_sigmaZeroDeepCoreAtLeastThreeDefectsPairs.mp
        hbranch).1
      (three_le_correctedDefectCount_of_mem hbranch)

/-! ## Active hosts and the two oriented Diophantine branches -/

/-- The active subtype population viewed as ordinary ordered pairs. -/
noncomputable def activeHostPairValues
    (N A L : ℕ) (hN : 2 ≤ N) :
    Finset (ℕ × ℕ) :=
  (activeSigmaZeroDeepCoreAtLeastThreeDefectsPairs
    N A L hN).image Subtype.val

theorem card_activeHostPairValues
    (N A L : ℕ) (hN : 2 ≤ N) :
    (activeHostPairValues N A L hN).card =
      (activeSigmaZeroDeepCoreAtLeastThreeDefectsPairs
        N A L hN).card := by
  unfold activeHostPairValues
  exact Finset.card_image_of_injective
    (activeSigmaZeroDeepCoreAtLeastThreeDefectsPairs
      N A L hN)
    Subtype.val_injective

/--
Every active member is a relational host.  This connects the concrete
population to the already proved global host estimate, although that
estimate has exponent `3/2` rather than the `1/2` needed here.
-/
theorem activeHostPairValues_subset_relationalHosts
    {N A L : ℕ} (hN : 2 ≤ N) :
    activeHostPairValues N A L hN ⊆
      RelationalHosts.relationalHosts N L := by
  intro value hvalue
  rw [activeHostPairValues, Finset.mem_image] at hvalue
  obtain ⟨pair, hpair, rfl⟩ := hvalue
  have hactive :=
    mem_activeSigmaZeroDeepCoreAtLeastThreeDefectsPairs.mp
      hpair
  have hsep := mem_separatedDyadicPairs.mp pair.2
  rw [RelationalHosts.mem_relationalHosts]
  refine ⟨hsep.1, hsep.2.1, hsep.2.2, ?_⟩
  have hrho :=
    pairRho_eq_pairSigma_add_pairTau
      (A := A) hN pair
  unfold pairRho at hrho
  calc
    0 < pairSigma A pair + pairTau A hN pair := by
      omega
    _ =
        relationRho
          (twoStartSystem
            (dyadicCutoff N L)
            pair.1.1 pair.1.2 L) :=
      hrho.symm

/-- Finite cardinality comparison with the global relational-host set. -/
theorem card_activeHosts_le_relationalHosts
    {N A L : ℕ} (hN : 2 ≤ N) :
    (activeSigmaZeroDeepCoreAtLeastThreeDefectsPairs
        N A L hN).card ≤
      (RelationalHosts.relationalHosts N L).card := by
  rw [← card_activeHostPairValues N A L hN]
  exact
    Finset.card_le_card
      (activeHostPairValues_subset_relationalHosts
        (A := A) hN)

/--
The oriented branch in which the first block supplies the two-defect start.
-/
noncomputable def leftTwoDefectActiveHosts
    (N A L : ℕ) (hN : 2 ≤ N) :
    Finset (SeparatedDyadicPair N L) :=
  (activeSigmaZeroDeepCoreAtLeastThreeDefectsPairs
    N A L hN).filter fun pair ↦
      2 ≤
        (IntervalDefectBound.defectsInInterval
          (L + 1) (pair.1.1 - 1)).card

/--
The oriented branch in which the second block supplies the two-defect
start.
-/
noncomputable def rightTwoDefectActiveHosts
    (N A L : ℕ) (hN : 2 ≤ N) :
    Finset (SeparatedDyadicPair N L) :=
  (activeSigmaZeroDeepCoreAtLeastThreeDefectsPairs
    N A L hN).filter fun pair ↦
      2 ≤
        (IntervalDefectBound.defectsInInterval
          (L + 1) (pair.1.2 - 1)).card

@[simp]
theorem mem_leftTwoDefectActiveHosts
    {N A L : ℕ} {hN : 2 ≤ N}
    {pair : SeparatedDyadicPair N L} :
    pair ∈ leftTwoDefectActiveHosts N A L hN ↔
      pair ∈
          activeSigmaZeroDeepCoreAtLeastThreeDefectsPairs
            N A L hN ∧
        2 ≤
          (IntervalDefectBound.defectsInInterval
            (L + 1) (pair.1.1 - 1)).card := by
  simp [leftTwoDefectActiveHosts]

@[simp]
theorem mem_rightTwoDefectActiveHosts
    {N A L : ℕ} {hN : 2 ≤ N}
    {pair : SeparatedDyadicPair N L} :
    pair ∈ rightTwoDefectActiveHosts N A L hN ↔
      pair ∈
          activeSigmaZeroDeepCoreAtLeastThreeDefectsPairs
            N A L hN ∧
        2 ≤
          (IntervalDefectBound.defectsInInterval
            (L + 1) (pair.1.2 - 1)).card := by
  simp [rightTwoDefectActiveHosts]

/--
The two oriented branches cover every active host.  The bounded component
certificate for either branch is supplied by
`activeHost_defectInterval_and_boundedComponent`.
-/
theorem activeHosts_subset_left_union_right
    {N A L : ℕ} (hN : 2 ≤ N) :
    activeSigmaZeroDeepCoreAtLeastThreeDefectsPairs
        N A L hN ⊆
      leftTwoDefectActiveHosts N A L hN ∪
        rightTwoDefectActiveHosts N A L hN := by
  intro pair hpair
  have horientation :=
    (activeHost_defectInterval_and_boundedComponent
      (A := A) hpair).1
  rw [Finset.mem_union]
  rcases horientation with hleft | hright
  · exact Or.inl
      (mem_leftTwoDefectActiveHosts.mpr
        ⟨hpair, hleft⟩)
  · exact Or.inr
      (mem_rightTwoDefectActiveHosts.mpr
        ⟨hpair, hright⟩)

/-- The active cardinality is bounded by the sum of the oriented counts. -/
theorem card_activeHosts_le_oriented_sum
    {N A L : ℕ} (hN : 2 ≤ N) :
    (activeSigmaZeroDeepCoreAtLeastThreeDefectsPairs
        N A L hN).card ≤
      (leftTwoDefectActiveHosts N A L hN).card +
        (rightTwoDefectActiveHosts N A L hN).card := by
  calc
    (activeSigmaZeroDeepCoreAtLeastThreeDefectsPairs
        N A L hN).card ≤
        (leftTwoDefectActiveHosts N A L hN ∪
          rightTwoDefectActiveHosts N A L hN).card :=
      Finset.card_le_card
        (activeHosts_subset_left_union_right hN)
    _ ≤
        (leftTwoDefectActiveHosts N A L hN).card +
          (rightTwoDefectActiveHosts N A L hN).card :=
      Finset.card_union_le _ _

/-! ## Pointwise and finite mass transfer -/

/--
Concrete `D# + c#` estimate for every separated pair.  It is the direct
combination of the canonical vertex budget with the integral half-defect
inequality above.
-/
theorem canonicalCoreExponent_le_height_add_half_defect
    {N A L : ℕ} (hN : 2 ≤ N)
    (pair : SeparatedDyadicPair N L) :
    canonicalCorrectedDefectCount
          A pair.1.1 pair.1.2 L +
        canonicalResidualComponentCount
          A pair.1.1 pair.1.2 L ≤
      (L + 1) +
        canonicalCorrectedDefectCount
          A pair.1.1 pair.1.2 L / 2 := by
  have hcoords := pair_coordinates_two_le hN pair
  apply defect_add_component_le_height_add_half_defect
  exact canonicalCorrected_add_twice_residual_le
    A pair.1.1 pair.1.2 L (by omega) (by omega)

/--
Uniform finite version obtained by replacing the pair's `D#` with the
maximum over the dyadic block.
-/
theorem canonicalCoreExponent_le_height_add_half_maxDefect
    {N A L : ℕ} (hN : 2 ≤ N)
    (pair : SeparatedDyadicPair N L) :
    canonicalCorrectedDefectCount
          A pair.1.1 pair.1.2 L +
        canonicalResidualComponentCount
          A pair.1.1 pair.1.2 L ≤
      (L + 1) +
        maxCanonicalCorrectedDefectCount A N L / 2 := by
  have hbudget :
      canonicalCorrectedDefectCount
            A pair.1.1 pair.1.2 L +
          2 * canonicalResidualComponentCount
            A pair.1.1 pair.1.2 L ≤
        2 * (L + 1) := by
    have hcoords := pair_coordinates_two_le hN pair
    exact canonicalCorrected_add_twice_residual_le
      A pair.1.1 pair.1.2 L (by omega) (by omega)
  have hD :
      canonicalCorrectedDefectCount A pair.1.1 pair.1.2 L ≤
        maxCanonicalCorrectedDefectCount A N L :=
    canonicalCorrectedDefectCount_le_max pair.2
  exact
    defect_add_component_le_height_add_half_envelope hbudget hD

/--
Every zero-systematic member has linear residual weight at most

`2^(B + max(D#)/2)`.
-/
theorem linearResidualWeight_le_two_pow_height_add_half_maxDefect
    {N A L : ℕ} (hN : 2 ≤ N)
    {pair : SeparatedDyadicPair N L}
    (hsigma : pairSigma A pair = 0) :
    linearResidualWeight A hN pair ≤
      2 ^ ((L + 1) +
        maxCanonicalCorrectedDefectCount A N L / 2) := by
  have htau :
      pairTau A hN pair ≤
        (L + 1) +
          maxCanonicalCorrectedDefectCount A N L / 2 :=
    (pairTau_le_canonicalCorrected_add_residual
      (A := A) hN pair).trans
      (canonicalCoreExponent_le_height_add_half_maxDefect hN pair)
  unfold linearResidualWeight
  simp only [hsigma, pow_zero, one_mul]
  exact
    (Nat.sub_le _ _).trans
      (Nat.pow_le_pow_right (by omega) htau)

/--
Generic finite host-count times pointwise-weight transfer.
-/
theorem linearResidualMass_le_card_mul
    {N A L W : ℕ} (hN : 2 ≤ N)
    (population : Finset (SeparatedDyadicPair N L))
    (hweight :
      ∀ pair ∈ population,
        linearResidualWeight A hN pair ≤ W) :
    linearResidualMass A hN population ≤
      population.card * W := by
  unfold linearResidualMass
  calc
    (∑ pair ∈ population,
        linearResidualWeight A hN pair) ≤
        ∑ _pair ∈ population, W :=
      Finset.sum_le_sum fun pair hpair ↦ hweight pair hpair
    _ = population.card * W := by simp

/--
Deleting the inactive pairs does not change the linear residual mass.
-/
theorem sigmaZeroDeepCoreAtLeastThreeDefects_linearResidualMass_eq_active
    {N A L : ℕ} (hN : 2 ≤ N) :
    linearResidualMass A hN
        (sigmaZeroDeepCoreAtLeastThreeDefectsPairs N A L hN) =
      linearResidualMass A hN
        (activeSigmaZeroDeepCoreAtLeastThreeDefectsPairs
          N A L hN) := by
  classical
  unfold linearResidualMass
  rw [activeSigmaZeroDeepCoreAtLeastThreeDefectsPairs,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro pair _hpair
  by_cases hactive : 0 < pairTau A hN pair
  · simp [hactive]
  · have htau : pairTau A hN pair = 0 :=
      Nat.eq_zero_of_not_pos hactive
    simp [hactive,
      linearResidualWeight_eq_zero_of_pairTau_eq_zero htau]

/--
Exact finite mass estimate for the Proposition 9.9 population, with the
strictly smaller active host count.
-/
theorem sigmaZeroDeepCoreAtLeastThreeDefects_linearResidualMass_le
    {N A L : ℕ} (hN : 2 ≤ N) :
    linearResidualMass A hN
        (sigmaZeroDeepCoreAtLeastThreeDefectsPairs N A L hN) ≤
      (activeSigmaZeroDeepCoreAtLeastThreeDefectsPairs
          N A L hN).card *
        2 ^ ((L + 1) +
          maxCanonicalCorrectedDefectCount A N L / 2) := by
  rw [
    sigmaZeroDeepCoreAtLeastThreeDefects_linearResidualMass_eq_active
      hN]
  apply linearResidualMass_le_card_mul hN
  intro pair hpair
  exact
    linearResidualWeight_le_two_pow_height_add_half_maxDefect
      hN
      (pairSigma_eq_zero_of_mem
        ((mem_activeSigmaZeroDeepCoreAtLeastThreeDefectsPairs.mp
          hpair).1))

/-! ## Uniform asymptotic closure of the residual-weight factor -/

/--
The half-defect exponential is subpolynomial.  This is a monotone
consequence of the already certified `4^max(D#) = N^o(1)` envelope.
-/
theorem two_pow_half_maxDefect_uniformSubpolynomial
    {C : ℝ} (hC : 0 ≤ C) (A : ℕ) :
    UniformSubpolynomialOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun N L =>
        (((2 ^ (maxCanonicalCorrectedDefectCount A N L / 2) :
          ℕ) : ℝ))) := by
  have hfour :=
    four_pow_maxCanonicalCorrectedDefectCount_uniformSubpolynomial
      hC A
  intro k hk
  obtain ⟨N₀, hN₀⟩ := hfour k hk
  refine ⟨N₀, ?_⟩
  intro N hN L hrun
  have hbase :
      (((2 ^ (maxCanonicalCorrectedDefectCount A N L / 2) :
          ℕ) : ℝ)) ≤
        (((4 ^ maxCanonicalCorrectedDefectCount A N L : ℕ) : ℝ)) := by
    exact_mod_cast
      (calc
        2 ^ (maxCanonicalCorrectedDefectCount A N L / 2) ≤
            2 ^ maxCanonicalCorrectedDefectCount A N L :=
          Nat.pow_le_pow_right (by omega) (Nat.div_le_self _ _)
        _ ≤ 4 ^ maxCanonicalCorrectedDefectCount A N L :=
          Nat.pow_le_pow_left (by omega) _)
  rw [abs_of_nonneg (by positivity)]
  have hfourBound :=
    hN₀ N hN L hrun
  rw [abs_of_nonneg (by positivity)] at hfourBound
  exact
    (pow_le_pow_left₀ (by positivity) hbase k).trans
      hfourBound

/--
The complete pointwise residual-weight envelope in Proposition 9.9.
-/
noncomputable def residualWeightEnvelope
    (A N L : ℕ) : ℝ :=
  ((2 ^ ((L + 1) +
    maxCanonicalCorrectedDefectCount A N L / 2) : ℕ) : ℝ)

/--
In the critical run-length window,

`2^(B + max(D#)/2) = N^(1+o_C(1))`

uniformly.
-/
theorem residualWeightEnvelope_uniformLinear
    {C : ℝ} (hC : 0 ≤ C) (A : ℕ) :
    UniformLinearSubpolynomialOn
      (CriticalRunWindow.InRunLengthWindow C)
      (residualWeightEnvelope A) := by
  let defectFactor : ℕ → ℕ → ℝ :=
    fun N L =>
      (((2 ^ (maxCanonicalCorrectedDefectCount A N L / 2) :
        ℕ) : ℝ))
  let loss : ℕ → ℕ → ℝ :=
    fun N L =>
      (2 * CriticalRunWindow.balanceConstant C) *
        defectFactor N L
  have hdefect :
      UniformSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C)
        defectFactor := by
    simpa only [defectFactor] using
      two_pow_half_maxDefect_uniformSubpolynomial hC A
  have hloss :
      UniformSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C)
        loss := by
    simpa only [loss] using
      ExpSqrtLog.uniformSubpolynomialOn_const_mul
        (2 * CriticalRunWindow.balanceConstant C) hdefect
  apply UniformLinear.of_linear_mul_subpolynomial hloss
  refine ⟨1, ?_⟩
  intro N hN L hrun
  have hNpos : 0 < N := by omega
  have hcritical :=
    CriticalChannelPowers.two_pow_runLength_le_balance_mul
      hNpos hrun
  have hrunPower :
      (((2 ^ (L + 1) : ℕ) : ℝ)) ≤
        (2 * CriticalRunWindow.balanceConstant C) * (N : ℝ) := by
    calc
      (((2 ^ (L + 1) : ℕ) : ℝ)) =
          2 * (2 : ℝ) ^ L := by
        push_cast
        rw [pow_succ]
        ring
      _ ≤
          2 * (CriticalRunWindow.balanceConstant C * (N : ℝ)) :=
        mul_le_mul_of_nonneg_left hcritical (by norm_num)
      _ =
          (2 * CriticalRunWindow.balanceConstant C) * (N : ℝ) := by
        ring
  have hdefectNonneg : 0 ≤ defectFactor N L := by
    dsimp only [defectFactor]
    positivity
  rw [abs_of_nonneg (show 0 ≤ residualWeightEnvelope A N L by
    unfold residualWeightEnvelope
    positivity)]
  rw [abs_of_nonneg (show 0 ≤ loss N L by
    dsimp only [loss]
    exact mul_nonneg
      (mul_nonneg (by norm_num)
        (CriticalRunWindow.balanceConstant_nonneg C))
      hdefectNonneg)]
  unfold residualWeightEnvelope
  rw [pow_add]
  push_cast
  dsimp only [loss, defectFactor]
  calc
    (2 : ℝ) ^ (L + 1) *
          (2 : ℝ) ^
            (maxCanonicalCorrectedDefectCount A N L / 2) ≤
        ((2 * CriticalRunWindow.balanceConstant C) * (N : ℝ)) *
          (2 : ℝ) ^
            (maxCanonicalCorrectedDefectCount A N L / 2) :=
      mul_le_mul_of_nonneg_right
        (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using hrunPower)
        (by positivity)
    _ =
        (N : ℝ) *
          ((2 * CriticalRunWindow.balanceConstant C) *
            (((2 ^
              (maxCanonicalCorrectedDefectCount A N L / 2) :
                ℕ) : ℝ))) := by
      norm_num only [Nat.cast_pow, Nat.cast_ofNat]
      ring

/-! ## Products and the conditional Proposition 9.9 closure -/

/--
The product of a uniform half-power count and a uniform linear weight is a
uniform three-halves quantity.
-/
theorem halfPower_mul_linear
    {admissible : ℕ → ℕ → Prop}
    {hosts weight : ℕ → ℕ → ℝ}
    (hhosts : UniformHalfPowerSubpolynomialOn admissible hosts)
    (hweight : UniformLinearSubpolynomialOn admissible weight) :
    UniformThreeHalvesSubpolynomialOn admissible
      (fun N L => hosts N L * weight N L) := by
  intro k hk
  have htwok : 0 < 2 * k := Nat.mul_pos (by omega) hk
  have hfourk : 0 < 4 * k := Nat.mul_pos (by omega) hk
  obtain ⟨Nh, hNh⟩ := hhosts (2 * k) htwok
  obtain ⟨Nw, hNw⟩ := hweight (4 * k) hfourk
  refine ⟨max Nh Nw, ?_⟩
  intro N hN L hNL
  have hh :
      |hosts N L| ^ (4 * k) ≤
        (N : ℝ) ^ (2 * k + 1) := by
    simpa only [show 2 * (2 * k) = 4 * k by omega] using
      hNh N ((le_max_left _ _).trans hN) L hNL
  have hw :
      |weight N L| ^ (4 * k) ≤
        (N : ℝ) ^ (4 * k + 1) := by
    exact hNw N ((le_max_right _ _).trans hN) L hNL
  have hsquare :
      (|hosts N L * weight N L| ^ (2 * k)) ^ 2 ≤
        ((N : ℝ) ^ (3 * k + 1)) ^ 2 := by
    calc
      (|hosts N L * weight N L| ^ (2 * k)) ^ 2 =
          |hosts N L| ^ (4 * k) *
            |weight N L| ^ (4 * k) := by
        rw [abs_mul, mul_pow, mul_pow]
        simp only [← pow_mul]
        congr 2 <;> omega
      _ ≤
          (N : ℝ) ^ (2 * k + 1) *
            (N : ℝ) ^ (4 * k + 1) :=
        mul_le_mul hh hw (by positivity) (by positivity)
      _ =
          ((N : ℝ) ^ (3 * k + 1)) ^ 2 := by
        rw [← pow_add, ← pow_mul]
        congr 1
        omega
  exact
    (sq_le_sq₀ (by positivity)
      (show 0 ≤ (N : ℝ) ^ (3 * k + 1) by positivity)).mp hsquare

/--
Proof-independent real cardinality of the active Proposition 9.9
population.  This is strictly smaller than the literal branch: pairs with
zero residual exponent have been removed because their mass is zero.
-/
noncomputable def hostCount
    (A N L : ℕ) : ℝ :=
  if hN : 2 ≤ N then
    ((activeSigmaZeroDeepCoreAtLeastThreeDefectsPairs
      N A L hN).card : ℝ)
  else 0

/--
The concrete two-branch cover consumed by the remaining Diophantine
argument.  Its first term fixes the first block as the two-defect start;
the second term fixes the second block.
-/
noncomputable def orientedHostCoverCount
    (A N L : ℕ) : ℝ :=
  if hN : 2 ≤ N then
    (((leftTwoDefectActiveHosts N A L hN).card +
      (rightTwoDefectActiveHosts N A L hN).card : ℕ) : ℝ)
  else 0

/-- The active host count is bounded by its two oriented branches. -/
theorem hostCount_le_orientedHostCoverCount
    {A N L : ℕ} (hN : 2 ≤ N) :
    hostCount A N L ≤ orientedHostCoverCount A N L := by
  simp only [hostCount, orientedHostCoverCount, dif_pos hN]
  exact_mod_cast card_activeHosts_le_oriented_sum hN

/--
Internal bridge statement for the still-unassembled oriented host count in
Proposition 9.9.

Unlike the published Evertse--Silverman input, this proposition is a
formalization debt internal to Paper C.  The literal population has now
been reduced in Lean to its active part, split according to the block
carrying two concrete defects, and equipped with a canonical residual
component of support at most ten.  Lemmas 9.4 and 9.8 provide the
fixed-parameter Diophantine reductions, but their summation over offsets,
square classes and bounded-component certificates is not yet assembled.
-/
/- AUDIT_BRIDGE
{
  "id": "PCv07c-P9.9-host-count",
  "kind": "internal",
  "status": "open",
  "lean_name": "PaperC.PropositionNineNine.HostCountStatement",
  "citation": {
    "authors": ["Brice Pouly"],
    "title": "Loi de Poisson critique dans un bloc dyadique — Débuts de longues plages constantes d’une fonction aléatoire complètement multiplicative de Rademacher étendue",
    "version": "7c, juillet 2026",
    "target_pdf_sha256": "23a5db3c8d024cab3fb8ca9f8f1443f40cf9502b1fb6682a331f5948f57a3336",
    "locator": "Proposition 9.9, démonstration, p. 32"
  },
  "source_statement": {
    "verbatim": "Le nombre total d’hôtes est donc N^{1/2+o_C(1)}.",
    "source_url": "paper_C_complete_v07c.pdf#page=32",
    "verification": "manual_primary_source_check_required"
  },
  "manuscript_locator": {
    "result": "Proposition 9.9",
    "equation": "host count in the proof",
    "pages": "32"
  },
  "formalization_relation": "legacy host-count API for the literal Proposition 9.9 population: zero-mass pairs are deleted and the remaining finite geometry is reduced as stated, but the canonical kappa mass proof bypasses this fixed-shape N^(1/2+o(1)) interface through direct bounded-ratio sector estimates; it remains open and nonblocking"
}
AUDIT_BRIDGE -/
def HostCountStatement
    (C : ℝ) (A : ℕ) : Prop :=
  UniformHalfPowerSubpolynomialOn
    (CriticalRunWindow.InRunLengthWindow C)
    (orientedHostCoverCount A)

/--
Proof-independent real linear residual mass of the same population.
-/
noncomputable def linearMass
    (A N L : ℕ) : ℝ :=
  if hN : 2 ≤ N then
    (linearResidualMass A hN
      (sigmaZeroDeepCoreAtLeastThreeDefectsPairs
        N A L hN) : ℝ)
  else 0

/--
Exact real host-count times residual-weight estimate.
-/
theorem linearMass_le_hostCount_mul_residualWeightEnvelope
    {A N L : ℕ} (hN : 2 ≤ N) :
    linearMass A N L ≤
      hostCount A N L * residualWeightEnvelope A N L := by
  have hfinite :=
    sigmaZeroDeepCoreAtLeastThreeDefects_linearResidualMass_le
      (A := A) (L := L) hN
  have hcast :
      (linearResidualMass A hN
          (sigmaZeroDeepCoreAtLeastThreeDefectsPairs
            N A L hN) : ℝ) ≤
        ((activeSigmaZeroDeepCoreAtLeastThreeDefectsPairs
            N A L hN).card : ℝ) *
          ((2 ^ ((L + 1) +
            maxCanonicalCorrectedDefectCount A N L / 2) : ℕ) : ℝ) := by
    exact_mod_cast hfinite
  simpa only [linearMass, hostCount, dif_pos hN,
    residualWeightEnvelope] using hcast

/--
Conditional, fully quantified form of Proposition 9.9.

The sole premise is the missing Diophantine host count
`N^(1/2+o_C(1))`.  All residual-weight, defect-envelope and critical-window
bookkeeping is discharged internally.
-/
theorem proposition_nine_nine_uniformThreeHalves
    {C : ℝ} (hC : 0 ≤ C) (A : ℕ)
    (hhosts : HostCountStatement C A) :
    UniformThreeHalvesSubpolynomialOn
      (CriticalRunWindow.InRunLengthWindow C)
      (linearMass A) := by
  unfold HostCountStatement at hhosts
  have hactiveHosts :
      UniformHalfPowerSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C)
        (hostCount A) := by
    apply UniformHalfPower.mono hhosts
    refine ⟨2, ?_⟩
    intro N hN L _hrun
    have hhostNonneg : 0 ≤ hostCount A N L := by
      unfold hostCount
      simp only [dif_pos hN]
      positivity
    have hcoverNonneg :
        0 ≤ orientedHostCoverCount A N L := by
      unfold orientedHostCoverCount
      simp only [dif_pos hN]
      positivity
    rw [abs_of_nonneg hhostNonneg,
      abs_of_nonneg hcoverNonneg]
    exact hostCount_le_orientedHostCoverCount hN
  have hproduct :
      UniformThreeHalvesSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C)
        (fun N L =>
          hostCount A N L * residualWeightEnvelope A N L) :=
    halfPower_mul_linear hactiveHosts
      (residualWeightEnvelope_uniformLinear hC A)
  apply UniformThreeHalves.mono hproduct
  refine ⟨2, ?_⟩
  intro N hN L _hrun
  have hmassNonneg : 0 ≤ linearMass A N L := by
    simp only [linearMass, dif_pos hN]
    positivity
  have hproductNonneg :
      0 ≤ hostCount A N L * residualWeightEnvelope A N L := by
    unfold hostCount residualWeightEnvelope
    simp only [dif_pos hN]
    positivity
  rw [abs_of_nonneg hmassNonneg, abs_of_nonneg hproductNonneg]
  exact linearMass_le_hostCount_mul_residualWeightEnvelope hN

end

end PropositionNineNine
end PaperC
