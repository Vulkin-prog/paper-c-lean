import PaperC.Asymptotics.BoundedRatioComponentHosts
import PaperC.Asymptotics.BoundedRatioNonterminalClosure
import PaperC.Asymptotics.BoundedRatioSectorClosure
import PaperC.Asymptotics.DependencyEdgesCritical
import PaperC.Asymptotics.RationalPowerClosure
import PaperC.Asymptotics.RationalPowerLittleO
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option maxHeartbeats 3600000

/-!
# Fixed-shape cardinality reduction for the bounded-ratio nonterminal sector

This file narrows the effective-cardinality debt left by Lemma 17.28.
Every pair in the intrinsic sixth sector has

`3 * (L + 1) < 16 * c#`,

and therefore carries a canonical residual component on at most ten
occurrences.  Consequently the literal sixth-sector population is covered
by the finite offset-shape fibres from
`BoundedRatioComponentHosts`.

The finite summation below leaves one explicit quantity: the maximum
cardinality of a sixth-sector fibre with both component offset sets fixed.
After division by the already extracted factor
`2^(terminalRankBudget K L + 1)`, its polynomial shape envelope dominates
the effective cardinality from `BoundedRatioNonterminalClosure`.

We also formalize the sharper pigeonhole step used verbatim in the proof of
Lemma 17.28: in the branch `2 * (L + 1) < 3 * c#`, a component of support
exactly two exists.  Thus that branch is covered by the size-two host
population, rather than merely by the size-ten population.

The final part of this file now follows the two-case proof of the manuscript.
For `3c# ≤ 2B`, the residual weight itself is at most
`2^(2 + floor(2B/3))`; a linear host count therefore gives the published
`N^(5/3+o_C(1))` mass bound, without extracting the terminal-rank factor.
For `2B < 3c#`, the size-two cover is combined with that factor.  The older
fixed-size-ten criterion is retained below as a convenient sufficient
criterion, but it is deliberately stronger than the source argument.

No arithmetic bridge or opaque counting statement is introduced.
-/

namespace PaperC
namespace BoundedRatioNonterminalCardinality

open BoundedRatioCanonicalTerminalPopulation
open BoundedRatioComponentHosts
open BoundedRatioNonterminalClosure
open BoundedRatioSectorClosure
open CanonicalResidualComponents
open PropositionSixteenOne
open ResidualComponentCounts
open ShallowCorePairs
open TerminalComponentCount

noncomputable section

/-! ## Structural host covers -/

/--
The strict deep-core density in the sixth sector supplies a component on at
most ten occurrences.  The constants are exact:

`3B < 16c#` and `2 * 16 < 3 * (10 + 1)`.
-/
theorem intrinsicNonterminalPairs_subset_boundedComponentHostsTen
    {N M A L : ℕ} (hN : 2 ≤ N) (K : ℝ) :
    boundedIntrinsicNonterminalPairs N M A L hN K ⊆
      boundedComponentHosts N M A L 10 := by
  intro pair hpair
  have hcore :=
    (mem_boundedIntrinsicNonterminalPairs.mp hpair).1
  unfold boundedTerminalCoreConditions at hcore
  have hdensityNot := hcore.2.2.1
  unfold HasCoreDensityAtMostThreeSixteenths at hdensityNot
  have hdensity :
      3 * (L + 1) ≤
        16 *
          canonicalResidualComponentCount
            A pair.1.1 pair.1.2 L := by
    omega
  exact
    mem_boundedComponentHosts_of_rational_density
      hN pair (by norm_num) hdensity (by norm_num)

/--
The high-density part `c# > 2B/3` of the intrinsic sixth sector.
This is the branch in which the manuscript selects a component of size two
before applying the quantitative host count.
-/
noncomputable def highDensityIntrinsicNonterminalPairs
    (N M A L : ℕ) (hN : 2 ≤ N) (K : ℝ) :
    Finset (SeparatedBoundedRatioPair N M L) :=
  (boundedIntrinsicNonterminalPairs N M A L hN K).filter fun pair =>
    2 * (L + 1) <
      3 *
        canonicalResidualComponentCount
          A pair.1.1 pair.1.2 L

@[simp]
theorem mem_highDensityIntrinsicNonterminalPairs
    {N M A L : ℕ} {hN : 2 ≤ N} {K : ℝ}
    {pair : SeparatedBoundedRatioPair N M L} :
    pair ∈ highDensityIntrinsicNonterminalPairs
        N M A L hN K ↔
      pair ∈ boundedIntrinsicNonterminalPairs
          N M A L hN K ∧
        2 * (L + 1) <
          3 *
            canonicalResidualComponentCount
              A pair.1.1 pair.1.2 L := by
  simp [highDensityIntrinsicNonterminalPairs]

/--
The complementary branch `c# ≤ 2B/3` of the intrinsic sixth sector.
Writing the inequality without division keeps the split exact over `ℕ`.
-/
noncomputable def moderateDensityIntrinsicNonterminalPairs
    (N M A L : ℕ) (hN : 2 ≤ N) (K : ℝ) :
    Finset (SeparatedBoundedRatioPair N M L) :=
  (boundedIntrinsicNonterminalPairs N M A L hN K).filter fun pair =>
    3 *
        canonicalResidualComponentCount
          A pair.1.1 pair.1.2 L ≤
      2 * (L + 1)

@[simp]
theorem mem_moderateDensityIntrinsicNonterminalPairs
    {N M A L : ℕ} {hN : 2 ≤ N} {K : ℝ}
    {pair : SeparatedBoundedRatioPair N M L} :
    pair ∈ moderateDensityIntrinsicNonterminalPairs
        N M A L hN K ↔
      pair ∈ boundedIntrinsicNonterminalPairs
          N M A L hN K ∧
        3 *
            canonicalResidualComponentCount
              A pair.1.1 pair.1.2 L ≤
          2 * (L + 1) := by
  simp [moderateDensityIntrinsicNonterminalPairs]

/--
The two density branches partition the literal intrinsic sixth sector.
-/
theorem moderate_union_highDensityIntrinsicNonterminalPairs
    {N M A L : ℕ} (hN : 2 ≤ N) (K : ℝ) :
    moderateDensityIntrinsicNonterminalPairs N M A L hN K ∪
        highDensityIntrinsicNonterminalPairs N M A L hN K =
      boundedIntrinsicNonterminalPairs N M A L hN K := by
  classical
  ext pair
  simp only [Finset.mem_union,
    mem_moderateDensityIntrinsicNonterminalPairs,
    mem_highDensityIntrinsicNonterminalPairs]
  constructor
  · rintro (h | h) <;> exact h.1
  · intro hpair
    by_cases hdensity :
        3 *
            canonicalResidualComponentCount
              A pair.1.1 pair.1.2 L ≤
          2 * (L + 1)
    · exact Or.inl ⟨hpair, hdensity⟩
    · exact Or.inr ⟨hpair, by omega⟩

theorem moderate_disjoint_highDensityIntrinsicNonterminalPairs
    {N M A L : ℕ} (hN : 2 ≤ N) (K : ℝ) :
    Disjoint
      (moderateDensityIntrinsicNonterminalPairs N M A L hN K)
      (highDensityIntrinsicNonterminalPairs N M A L hN K) := by
  classical
  exact Finset.disjoint_left.mpr (by
    intro pair hmoderate hhigh
    have hm :=
      (mem_moderateDensityIntrinsicNonterminalPairs.mp hmoderate).2
    have hh :=
      (mem_highDensityIntrinsicNonterminalPairs.mp hhigh).2
    omega)

/--
In the branch `c# > 2B/3`, the canonical component count from the terminal
population module gives at least one component of support exactly two.
-/
theorem highDensityIntrinsicNonterminalPairs_subset_boundedComponentHostsTwo
    {N M A L : ℕ} (hN : 2 ≤ N) (K : ℝ) :
    highDensityIntrinsicNonterminalPairs N M A L hN K ⊆
      boundedComponentHosts N M A L 2 := by
  classical
  intro pair hpair
  have hdensity :=
    (mem_highDensityIntrinsicNonterminalPairs.mp hpair).2
  have hcomponentCount :=
    canonicalResidualComponentCount_le_runLength
      (A := A) hN pair
  have hpositive :
      0 <
        L + 1 -
          3 * boundedTerminalSlack A pair := by
    unfold boundedTerminalSlack
    omega
  have hpairComponents :
      0 < (boundedCanonicalPairComponents A pair).card :=
    hpositive.trans_le
      (bounded_terminal_component_count
        (A := A) hN pair).2
  obtain ⟨component, hcomponent⟩ :=
    Finset.card_pos.mp hpairComponents
  rw [boundedCanonicalPairComponents, mem_pairComponents] at hcomponent
  exact
    mem_boundedComponentHosts.mpr
      ⟨component, hcomponent.1, by omega⟩

/--
Quantitative finite form of the size-two reduction.  Once every fixed
size-two offset-shape host fibre is bounded by `Q`, the entire high-density
sixth-sector branch has the displayed explicit bound.
-/
theorem card_highDensityIntrinsicNonterminalPairs_le_of_sizeTwoShapeFibers
    {N M A L Q : ℕ} (hN : 2 ≤ N) (K : ℝ)
    (hshape :
      ∀ shape ∈ boundedOffsetShapes L 2,
        (boundedComponentHostsOfShape
          N M A L 2 shape).card ≤ Q) :
    (highDensityIntrinsicNonterminalPairs
        N M A L hN K).card ≤
      ((3 * (L + 1) ^ 2) ^ 2) * Q := by
  exact
    (Finset.card_le_card
      (highDensityIntrinsicNonterminalPairs_subset_boundedComponentHostsTwo
        hN K)).trans
      (by
        simpa only [Nat.reduceAdd] using
          card_boundedComponentHosts_le_of_shapeFibers
            (N := N) (M := M) (A := A) (L := L)
            (K := 2) hN hshape)

/-! ## The moderate-density mass (`c# ≤ 2B/3`) -/

/--
The literal natural residual mass of the moderate-density branch.
-/
noncomputable def moderateDensityIntrinsicNonterminalResidualMass
    (N M A L : ℕ) (hN : 2 ≤ N) (K : ℝ) : ℕ :=
  ∑ pair ∈
      moderateDensityIntrinsicNonterminalPairs N M A L hN K,
    residualWeight A hN pair

/--
The pointwise weight envelope in the first line of the two-case argument:
`D# ≤ 2`, `τ ≤ D# + c#`, and `3c# ≤ 2B`.
-/
def moderateDensityResidualWeightEnvelopeNat (L : ℕ) : ℕ :=
  2 ^ (2 + (2 * (L + 1)) / 3)

/-- Real cast of `moderateDensityResidualWeightEnvelopeNat`. -/
def moderateDensityResidualWeightEnvelope (_N L : ℕ) : ℝ :=
  (moderateDensityResidualWeightEnvelopeNat L : ℝ)

/--
Every moderate-density sixth-sector pair has residual weight at most
`2^(2 + floor(2B/3))`.
-/
theorem residualWeight_le_moderateDensityEnvelope
    {N M A L : ℕ} {hN : 2 ≤ N} {K : ℝ}
    {pair : SeparatedBoundedRatioPair N M L}
    (hpair :
      pair ∈ moderateDensityIntrinsicNonterminalPairs
        N M A L hN K) :
    residualWeight A hN pair ≤
      moderateDensityResidualWeightEnvelopeNat L := by
  have hsector :=
    (mem_moderateDensityIntrinsicNonterminalPairs.mp hpair).1
  have hdensity :=
    (mem_moderateDensityIntrinsicNonterminalPairs.mp hpair).2
  have htau :=
    pairTau_le_corrected_add_components
      (A := A) hN pair
  have hdata :=
    mem_boundedIntrinsicNonterminalPairs.mp hsector
  unfold boundedTerminalCoreConditions at hdata
  have hD :
      canonicalCorrectedDefectCount
          A pair.1.1 pair.1.2 L ≤ 2 :=
    hdata.1.2.2.2.2
  have hsigma :=
    pairSigma_eq_zero_of_mem_intrinsicNonterminal hsector
  have hweight :
      residualWeight A hN pair ≤
        2 ^ pairTau A hN pair := by
    unfold residualWeight
    simp only [hsigma, pow_zero, one_mul]
    exact Nat.sub_le _ _
  have hexponent :
      pairTau A hN pair ≤
        2 + (2 * (L + 1)) / 3 := by
    omega
  exact hweight.trans
    (Nat.pow_le_pow_right (by norm_num) hexponent)

/-- Finite summation of the pointwise moderate-density weight bound. -/
theorem moderateDensityIntrinsicNonterminalResidualMass_le
    {N M A L : ℕ} (hN : 2 ≤ N) (K : ℝ) :
    moderateDensityIntrinsicNonterminalResidualMass
        N M A L hN K ≤
      (moderateDensityIntrinsicNonterminalPairs
        N M A L hN K).card *
        moderateDensityResidualWeightEnvelopeNat L := by
  unfold moderateDensityIntrinsicNonterminalResidualMass
  calc
    (∑ pair ∈
        moderateDensityIntrinsicNonterminalPairs N M A L hN K,
        residualWeight A hN pair) ≤
        ∑ _pair ∈
          moderateDensityIntrinsicNonterminalPairs N M A L hN K,
          moderateDensityResidualWeightEnvelopeNat L :=
      Finset.sum_le_sum fun pair hpair =>
        residualWeight_le_moderateDensityEnvelope hpair
    _ =
        (moderateDensityIntrinsicNonterminalPairs
          N M A L hN K).card *
          moderateDensityResidualWeightEnvelopeNat L := by
      simp

/--
The moderate branch uses only the coarse size-ten structural cover.
-/
theorem moderateDensityIntrinsicNonterminalPairs_subset_hostsTen
    {N M A L : ℕ} (hN : 2 ≤ N) (K : ℝ) :
    moderateDensityIntrinsicNonterminalPairs N M A L hN K ⊆
      boundedComponentHosts N M A L 10 := by
  intro pair hpair
  exact intrinsicNonterminalPairs_subset_boundedComponentHostsTen
    hN K
    (mem_moderateDensityIntrinsicNonterminalPairs.mp hpair).1

/--
Proof-independent real mass of the moderate branch, set to zero for
`N < 2`.
-/
noncomputable def moderateDensityIntrinsicNonterminalMass
    (A : ℕ) (K : ℝ) (N M L : ℕ) : ℝ :=
  if hN : 2 ≤ N then
    (moderateDensityIntrinsicNonterminalResidualMass
      N M A L hN K : ℝ)
  else 0

theorem moderateDensityIntrinsicNonterminalMass_nonneg
    (A : ℕ) (K : ℝ) (N M L : ℕ) :
    0 ≤ moderateDensityIntrinsicNonterminalMass A K N M L := by
  unfold moderateDensityIntrinsicNonterminalMass
  split_ifs <;> positivity

/--
The moderate branch is dominated by a supplied endpoint-independent host
envelope times its explicit pointwise weight.
-/
theorem moderateDensityIntrinsicNonterminalMass_le_hostEnvelope
    {A N M L : ℕ} {K : ℝ}
    (hN : 2 ≤ N) (hostEnvelope : ℕ → ℕ → ℝ)
    (hhosts :
      ((boundedComponentHosts N M A L 10).card : ℝ) ≤
        hostEnvelope N L) :
    moderateDensityIntrinsicNonterminalMass A K N M L ≤
      hostEnvelope N L *
        moderateDensityResidualWeightEnvelope N L := by
  have hmass :=
    moderateDensityIntrinsicNonterminalResidualMass_le
      (M := M) (A := A) (L := L) hN K
  have hcardNat :
      (moderateDensityIntrinsicNonterminalPairs
          N M A L hN K).card ≤
        (boundedComponentHosts N M A L 10).card :=
    Finset.card_le_card
      (moderateDensityIntrinsicNonterminalPairs_subset_hostsTen hN K)
  have hmassReal :
      (moderateDensityIntrinsicNonterminalResidualMass
          N M A L hN K : ℝ) ≤
        ((moderateDensityIntrinsicNonterminalPairs
          N M A L hN K).card : ℝ) *
          moderateDensityResidualWeightEnvelope N L := by
    unfold moderateDensityResidualWeightEnvelope
    exact_mod_cast hmass
  rw [moderateDensityIntrinsicNonterminalMass, dif_pos hN]
  calc
    (moderateDensityIntrinsicNonterminalResidualMass
          N M A L hN K : ℝ) ≤
        ((moderateDensityIntrinsicNonterminalPairs
          N M A L hN K).card : ℝ) *
          moderateDensityResidualWeightEnvelope N L :=
      hmassReal
    _ ≤
        ((boundedComponentHosts N M A L 10).card : ℝ) *
          moderateDensityResidualWeightEnvelope N L :=
      mul_le_mul_of_nonneg_right
        (by exact_mod_cast hcardNat)
        (by
          unfold moderateDensityResidualWeightEnvelope
          positivity)
    _ ≤
        hostEnvelope N L *
          moderateDensityResidualWeightEnvelope N L :=
      mul_le_mul_of_nonneg_right hhosts
        (by
          unfold moderateDensityResidualWeightEnvelope
          positivity)

/--
The explicit moderate-density weight is
`N^(2/3+o_C(1))` in the critical window.
-/
theorem moderateDensityResidualWeightEnvelope_uniformTwoThird
    {C : ℝ} :
    UniformRationalPowerSubpolynomialOn 2 3
      (CriticalRunWindow.InRunLengthWindow C)
      moderateDensityResidualWeightEnvelope := by
  let loss : ℕ → ℕ → ℝ :=
    fun _N _L =>
      256 * CriticalRunWindow.balanceConstant C ^ 2
  have hloss :
      UniformSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C) loss := by
    simpa only [loss] using
      ExpSqrtLog.uniformSubpolynomialOn_const
        (CriticalRunWindow.InRunLengthWindow C)
        (256 * CriticalRunWindow.balanceConstant C ^ 2)
  apply UniformRationalPower.of_cube_bound hloss
  refine ⟨1, ?_⟩
  intro N hN L hrun
  have hNpos : 0 < N := by omega
  have hrunPower :=
    CriticalChannelPowers.two_pow_runLength_le_balance_mul
      hNpos hrun
  have hexponent :
      (2 + (2 * (L + 1)) / 3) * 3 ≤
        8 + 2 * L := by
    omega
  have hpowNat :
      (moderateDensityResidualWeightEnvelopeNat L) ^ 3 ≤
        256 * (2 ^ L) ^ 2 := by
    unfold moderateDensityResidualWeightEnvelopeNat
    calc
      (2 ^ (2 + (2 * (L + 1)) / 3)) ^ 3 =
          2 ^ ((2 + (2 * (L + 1)) / 3) * 3) := by
        rw [pow_mul]
      _ ≤ 2 ^ (8 + 2 * L) :=
        Nat.pow_le_pow_right (by norm_num) hexponent
      _ = 256 * (2 ^ L) ^ 2 := by
        rw [pow_add,
          show 2 * L = L * 2 by omega, ← pow_mul]
        norm_num
  have hpowReal :
      (moderateDensityResidualWeightEnvelope N L) ^ 3 ≤
        256 * ((2 : ℝ) ^ L) ^ 2 := by
    unfold moderateDensityResidualWeightEnvelope
    exact_mod_cast hpowNat
  rw [abs_of_nonneg
    (show 0 ≤ moderateDensityResidualWeightEnvelope N L by
      unfold moderateDensityResidualWeightEnvelope
      positivity)]
  calc
    moderateDensityResidualWeightEnvelope N L ^ 3 ≤
        256 * ((2 : ℝ) ^ L) ^ 2 := hpowReal
    _ ≤
        256 *
          (CriticalRunWindow.balanceConstant C * (N : ℝ)) ^ 2 :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hrunPower 2)
        (by norm_num)
    _ =
        (N : ℝ) ^ 2 * |loss N L| := by
      dsimp only [loss]
      rw [abs_of_nonneg (by positivity :
        0 ≤ 256 * CriticalRunWindow.balanceConstant C ^ 2)]
      ring

/--
A linear host count times an `N^(2/3+o(1))` weight is
`N^(5/3+o(1))`.
-/
theorem linear_mul_twoThird_uniformFiveThird
    {admissible : ℕ → ℕ → Prop}
    {hosts weight : ℕ → ℕ → ℝ}
    (hhosts : UniformLinearSubpolynomialOn admissible hosts)
    (hweight :
      UniformRationalPowerSubpolynomialOn 2 3 admissible weight) :
    UniformFiveThirdSubpolynomialOn admissible
      (fun N L => hosts N L * weight N L) := by
  intro k hk
  have hsixk : 0 < 6 * k := Nat.mul_pos (by omega) hk
  have htwok : 0 < 2 * k := Nat.mul_pos (by omega) hk
  obtain ⟨Nh, hNh⟩ := hhosts (6 * k) hsixk
  obtain ⟨Nw, hNw⟩ := hweight (2 * k) htwok
  refine ⟨max Nh Nw, ?_⟩
  intro N hN L hNL
  have hh :
      |hosts N L| ^ (6 * k) ≤
        (N : ℝ) ^ (6 * k + 1) :=
    hNh N ((le_max_left _ _).trans hN) L hNL
  have hw :
      |weight N L| ^ (6 * k) ≤
        (N : ℝ) ^ (4 * k + 1) := by
    simpa only [
      show 3 * (2 * k) = 6 * k by omega,
      show 2 * (2 * k) = 4 * k by omega] using
      hNw N ((le_max_right _ _).trans hN) L hNL
  have hsquare :
      (|hosts N L * weight N L| ^ (3 * k)) ^ 2 ≤
        ((N : ℝ) ^ (5 * k + 1)) ^ 2 := by
    calc
      (|hosts N L * weight N L| ^ (3 * k)) ^ 2 =
          |hosts N L| ^ (6 * k) *
            |weight N L| ^ (6 * k) := by
        rw [abs_mul, mul_pow, mul_pow]
        simp only [← pow_mul]
        congr 2 <;> omega
      _ ≤
          (N : ℝ) ^ (6 * k + 1) *
            (N : ℝ) ^ (4 * k + 1) :=
        mul_le_mul hh hw (by positivity) (by positivity)
      _ =
          ((N : ℝ) ^ (5 * k + 1)) ^ 2 := by
        rw [← pow_add, ← pow_mul]
        congr 1
        omega
  exact
    (sq_le_sq₀ (by positivity)
      (show 0 ≤ (N : ℝ) ^ (5 * k + 1) by positivity)).mp
      hsquare

/--
Source-faithful closure of the moderate-density line of Lemma 17.28.
The only counting input is the direct endpoint-uniform domination of the
size-ten host population by a linear-subpolynomial envelope.
-/
theorem moderateDensityIntrinsicNonterminalMass_uniformLittleO
    {C : ℝ} {κ₀ A : ℕ} {K : ℝ}
    (hostEnvelope : ℕ → ℕ → ℝ)
    (hhostRate :
      UniformLinearSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C) hostEnvelope)
    (hhostNonneg : ∀ N L, 0 ≤ hostEnvelope N L)
    (hhosts :
      ∃ N₁ : ℕ, ∀ N ≥ N₁, ∀ M L,
        2 * N ≤ M →
        M ≤ κ₀ * N →
        CriticalRunWindow.InRunLengthWindow C N L →
        ((boundedComponentHosts N M A L 10).card : ℝ) ≤
          hostEnvelope N L) :
    UniformLittleOInBoundedRatioWindow C κ₀
      (moderateDensityIntrinsicNonterminalMass A K) := by
  let envelope : ℕ → ℕ → ℝ :=
    fun N L =>
      hostEnvelope N L *
        moderateDensityResidualWeightEnvelope N L
  have henvelopeRate :
      UniformFiveThirdSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C) envelope := by
    simpa only [envelope] using
      linear_mul_twoThird_uniformFiveThird hhostRate
        (moderateDensityResidualWeightEnvelope_uniformTwoThird
          (C := C))
  have henvelopeLittleO :
      UniformLittleOOn
        (CriticalRunWindow.InRunLengthWindow C)
        envelope (fun N _ => (N : ℝ) ^ 2) :=
    UniformRationalPower.littleO_natPower_of_lt
      (by norm_num) henvelopeRate
  apply BoundedRatioSectorClosure.uniformLittleOInBoundedRatioWindow_of_nonnegative_envelope
      henvelopeLittleO
      (moderateDensityIntrinsicNonterminalMass_nonneg A K)
      (by
        intro N L
        dsimp only [envelope]
        exact mul_nonneg (hhostNonneg N L)
          (by
            unfold moderateDensityResidualWeightEnvelope
            positivity))
  obtain ⟨N₁, hN₁⟩ := hhosts
  refine ⟨max N₁ 2, ?_⟩
  intro N hN M L hNM hMκ hrun
  have hNtwo : 2 ≤ N :=
    (le_max_right N₁ 2).trans hN
  exact
    moderateDensityIntrinsicNonterminalMass_le_hostEnvelope
      hNtwo hostEnvelope
      (hN₁ N ((le_max_left N₁ 2).trans hN)
        M L hNM hMκ hrun)

/-! ## The high-density mass (`c# > 2B/3`) -/

/-- Literal natural residual mass of the high-density branch. -/
noncomputable def highDensityIntrinsicNonterminalResidualMass
    (N M A L : ℕ) (hN : 2 ≤ N) (K : ℝ) : ℕ :=
  ∑ pair ∈
      highDensityIntrinsicNonterminalPairs N M A L hN K,
    residualWeight A hN pair

/--
The pointwise rank saving summed only over the high-density branch.
-/
theorem highDensityIntrinsicNonterminalResidualMass_mul_rankFactor_le
    {N M A L : ℕ} (hN : 2 ≤ N) (K : ℝ) :
    highDensityIntrinsicNonterminalResidualMass N M A L hN K *
        2 ^ (terminalRankBudget K L + 1) ≤
      (highDensityIntrinsicNonterminalPairs
        N M A L hN K).card *
        (4 * 2 ^ (L + 1)) := by
  unfold highDensityIntrinsicNonterminalResidualMass
  rw [Finset.sum_mul]
  calc
    (∑ pair ∈
        highDensityIntrinsicNonterminalPairs N M A L hN K,
        residualWeight A hN pair *
          2 ^ (terminalRankBudget K L + 1)) ≤
        ∑ _pair ∈
          highDensityIntrinsicNonterminalPairs N M A L hN K,
          4 * 2 ^ (L + 1) := by
      exact Finset.sum_le_sum fun pair hpair =>
        residualWeight_mul_two_pow_budget_succ_le
          (mem_highDensityIntrinsicNonterminalPairs.mp hpair).1
    _ =
        (highDensityIntrinsicNonterminalPairs
          N M A L hN K).card *
          (4 * 2 ^ (L + 1)) := by
      simp

/-- Proof-independent real mass of the high-density branch. -/
noncomputable def highDensityIntrinsicNonterminalMass
    (A : ℕ) (K : ℝ) (N M L : ℕ) : ℝ :=
  if hN : 2 ≤ N then
    (highDensityIntrinsicNonterminalResidualMass
      N M A L hN K : ℝ)
  else 0

theorem highDensityIntrinsicNonterminalMass_nonneg
    (A : ℕ) (K : ℝ) (N M L : ℕ) :
    0 ≤ highDensityIntrinsicNonterminalMass A K N M L := by
  unfold highDensityIntrinsicNonterminalMass
  split_ifs <;> positivity

/--
The direct quantitative host envelope from the size-two line of Lemma
17.23:

`N exp(Cterm sqrt(B) / log(B))`.

The theorem below accepts domination by this expression directly; no named
bridge statement is introduced.
-/
noncomputable def sizeTwoComponentHostEnvelope
    (Cterm : ℝ) (N L : ℕ) : ℝ :=
  (N : ℝ) *
    Real.exp
      (Cterm * Real.sqrt ((L + 1 : ℕ) : ℝ) /
        Real.log ((L + 1 : ℕ) : ℝ))

/--
The exact exponential loss left after the terminal-rank factor is divided
out.
-/
noncomputable def terminalRankGapFactor
    (Cterm K : ℝ) (_N L : ℕ) : ℝ :=
  Real.exp
      (Cterm * Real.sqrt ((L + 1 : ℕ) : ℝ) /
        Real.log ((L + 1 : ℕ) : ℝ)) /
    ((2 ^ (terminalRankBudget K L + 1) : ℕ) : ℝ)

/--
Minimal high-density mass envelope after the critical estimate
`4·2^B ≤ 8 exp(C log 2) N`:

`8 exp(C log 2) N² · exp(Cterm sqrt(B)/log B) / 2^(R_K(B)+1)`.
-/
noncomputable def highDensityIntrinsicNonterminalMassEnvelope
    (C Cterm K : ℝ) (N L : ℕ) : ℝ :=
  (8 * CriticalRunWindow.balanceConstant C) *
    (N : ℝ) ^ 2 * terminalRankGapFactor Cterm K N L

theorem terminalRankGapFactor_nonneg
    (Cterm K : ℝ) (N L : ℕ) :
    0 ≤ terminalRankGapFactor Cterm K N L := by
  unfold terminalRankGapFactor
  positivity

theorem highDensityIntrinsicNonterminalMassEnvelope_nonneg
    (C Cterm K : ℝ) (N L : ℕ) :
    0 ≤ highDensityIntrinsicNonterminalMassEnvelope
      C Cterm K N L := by
  unfold highDensityIntrinsicNonterminalMassEnvelope
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (by norm_num)
        (CriticalRunWindow.balanceConstant_nonneg C))
      (sq_nonneg (N : ℝ)))
    (terminalRankGapFactor_nonneg Cterm K N L)

/--
The finite high-density mass is dominated by the minimal envelope whenever
the direct size-two host count is available.
-/
theorem highDensityIntrinsicNonterminalMass_le_envelope
    {C Cterm K : ℝ} {A N M L : ℕ}
    (hN : 2 ≤ N)
    (hrun : CriticalRunWindow.InRunLengthWindow C N L)
    (hhosts :
      ((boundedComponentHosts N M A L 2).card : ℝ) ≤
        sizeTwoComponentHostEnvelope Cterm N L) :
    highDensityIntrinsicNonterminalMass A K N M L ≤
      highDensityIntrinsicNonterminalMassEnvelope
        C Cterm K N L := by
  have hfinite :=
    highDensityIntrinsicNonterminalResidualMass_mul_rankFactor_le
      (M := M) (A := A) (L := L) hN K
  have hfiniteReal :
      (highDensityIntrinsicNonterminalResidualMass
          N M A L hN K : ℝ) *
          ((2 ^ (terminalRankBudget K L + 1) : ℕ) : ℝ) ≤
        ((highDensityIntrinsicNonterminalPairs
          N M A L hN K).card : ℝ) *
          ((4 * 2 ^ (L + 1) : ℕ) : ℝ) := by
    exact_mod_cast hfinite
  have hdenom :
      0 < ((2 ^ (terminalRankBudget K L + 1) : ℕ) : ℝ) := by
    positivity
  have hcard :
      ((highDensityIntrinsicNonterminalPairs
          N M A L hN K).card : ℝ) ≤
        ((boundedComponentHosts N M A L 2).card : ℝ) := by
    exact_mod_cast
      Finset.card_le_card
        (highDensityIntrinsicNonterminalPairs_subset_boundedComponentHostsTwo
          hN K)
  have hpower :=
    CriticalChannelPowers.two_pow_runLength_le_balance_mul
      (show 0 < N by omega) hrun
  have hcritical :
      ((4 * 2 ^ (L + 1) : ℕ) : ℝ) ≤
        (8 * CriticalRunWindow.balanceConstant C) * (N : ℝ) := by
    calc
      ((4 * 2 ^ (L + 1) : ℕ) : ℝ) =
          8 * (2 : ℝ) ^ L := by
        push_cast
        rw [pow_succ]
        ring
      _ ≤
          8 *
            (CriticalRunWindow.balanceConstant C * (N : ℝ)) :=
        mul_le_mul_of_nonneg_left hpower (by norm_num)
      _ =
          (8 * CriticalRunWindow.balanceConstant C) * (N : ℝ) := by
        ring
  rw [highDensityIntrinsicNonterminalMass, dif_pos hN]
  have hfiniteDiv :=
    (le_div_iff₀ hdenom).2 hfiniteReal
  calc
    (highDensityIntrinsicNonterminalResidualMass
        N M A L hN K : ℝ) ≤
        (((highDensityIntrinsicNonterminalPairs
          N M A L hN K).card : ℝ) *
            ((4 * 2 ^ (L + 1) : ℕ) : ℝ)) /
          ((2 ^ (terminalRankBudget K L + 1) : ℕ) : ℝ) :=
      hfiniteDiv
    _ ≤
        (sizeTwoComponentHostEnvelope Cterm N L *
            ((8 * CriticalRunWindow.balanceConstant C) * (N : ℝ))) /
          ((2 ^ (terminalRankBudget K L + 1) : ℕ) : ℝ) := by
      apply div_le_div_of_nonneg_right _ hdenom.le
      exact mul_le_mul (hcard.trans hhosts) hcritical
        (by positivity)
        (by
          unfold sizeTwoComponentHostEnvelope
          positivity)
    _ =
        highDensityIntrinsicNonterminalMassEnvelope
          C Cterm K N L := by
      unfold sizeTwoComponentHostEnvelope
        highDensityIntrinsicNonterminalMassEnvelope
        terminalRankGapFactor
      ring

/--
The floor in `R_K(B)` loses less than one: for `B ≥ 2`, the exact rank-gap
factor is bounded by the manuscript exponential

`exp((Cterm - K log 2) sqrt(B)/log(B))`.
-/
theorem terminalRankGapFactor_le_exp_gap
    {Cterm K : ℝ} {N L : ℕ} (_hB : 2 ≤ L + 1) :
    terminalRankGapFactor Cterm K N L ≤
      Real.exp
        (-(K * Real.log 2 - Cterm) *
          (Real.sqrt ((L + 1 : ℕ) : ℝ) /
            Real.log ((L + 1 : ℕ) : ℝ))) := by
  let B : ℝ := ((L + 1 : ℕ) : ℝ)
  let x : ℝ := Real.sqrt B / Real.log B
  have hlogTwo : 0 < Real.log (2 : ℝ) :=
    Real.log_pos (by norm_num)
  have hfloor :=
    Nat.lt_floor_add_one (terminalRankScale K L)
  have hfloor' :
      terminalRankScale K L <
        (terminalRankBudget K L : ℝ) + 1 := by
    simpa only [terminalRankBudget] using hfloor
  have hexponent :
      K * Real.log 2 * x ≤
        ((terminalRankBudget K L + 1 : ℕ) : ℝ) *
          Real.log 2 := by
    have hscaled :=
      (mul_lt_mul_of_pos_right hfloor' hlogTwo).le
    calc
      K * Real.log 2 * x =
          terminalRankScale K L * Real.log 2 := by
        unfold terminalRankScale
        dsimp only [B, x]
        push_cast
        ring
      _ ≤
          ((terminalRankBudget K L : ℝ) + 1) *
            Real.log 2 := hscaled
      _ =
          ((terminalRankBudget K L + 1 : ℕ) : ℝ) *
            Real.log 2 := by
        push_cast
        ring
  have hdenomExp :
      ((2 ^ (terminalRankBudget K L + 1) : ℕ) : ℝ) =
        Real.exp
          (((terminalRankBudget K L + 1 : ℕ) : ℝ) *
            Real.log 2) := by
    calc
      ((2 ^ (terminalRankBudget K L + 1) : ℕ) : ℝ) =
          (2 : ℝ) ^ (terminalRankBudget K L + 1) := by
        norm_num
      _ =
          (Real.exp (Real.log 2)) ^
            (terminalRankBudget K L + 1) := by
        rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      _ =
          Real.exp
            (((terminalRankBudget K L + 1 : ℕ) : ℝ) *
              Real.log 2) :=
        (Real.exp_nat_mul _ _).symm
  have hdenomLower :
      Real.exp (K * Real.log 2 * x) ≤
        ((2 ^ (terminalRankBudget K L + 1) : ℕ) : ℝ) := by
    rw [hdenomExp]
    exact Real.exp_le_exp.mpr hexponent
  have hdenomPos :
      0 < ((2 ^ (terminalRankBudget K L + 1) : ℕ) : ℝ) := by
    positivity
  unfold terminalRankGapFactor
  dsimp only [B, x] at hdenomLower ⊢
  apply (div_le_iff₀ hdenomPos).2
  calc
    Real.exp
          (Cterm * Real.sqrt ↑(L + 1) /
            Real.log ↑(L + 1)) =
        Real.exp
            (-(K * Real.log 2 - Cterm) *
              (Real.sqrt ↑(L + 1) / Real.log ↑(L + 1))) *
          Real.exp
            (K * Real.log 2 *
              (Real.sqrt ↑(L + 1) / Real.log ↑(L + 1))) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤
        Real.exp
            (-(K * Real.log 2 - Cterm) *
              (Real.sqrt ↑(L + 1) / Real.log ↑(L + 1))) *
          ((2 ^ (terminalRankBudget K L + 1) : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hdenomLower (Real.exp_nonneg _)

/--
The manuscript threshold `K log 2 > 2 Cterm` makes the exact terminal-rank
gap tend uniformly to zero.  The proof uses only
`log B = o(sqrt B)` and the fact that `B=L+1` tends uniformly to infinity
in the critical window.
-/
theorem terminalRankGapFactor_uniformLittleOOne
    {C Cterm K : ℝ} (hC : 0 ≤ C) (hCterm : 0 ≤ Cterm)
    (hthreshold : 2 * Cterm < K * Real.log 2) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (terminalRankGapFactor Cterm K)
      (fun _ _ => 1) := by
  let δ : ℝ := K * Real.log 2 - Cterm
  have hδ : 0 < δ := by
    dsimp only [δ]
    nlinarith
  intro ε hε
  let T : ℝ := 1 / (ε * δ)
  have hT : 0 < T := by
    dsimp only [T]
    positivity
  have hhalf : 0 < (1 / 2 : ℝ) := by norm_num
  have hcoeff : 0 < 1 / T := by positivity
  have hraw :
      ∀ᶠ B : ℕ in Filter.atTop,
        ‖Real.log (B : ℝ)‖ ≤
          (1 / T) * ‖(B : ℝ) ^ (1 / 2 : ℝ)‖ :=
    tendsto_natCast_atTop_atTop.eventually
      ((isLittleO_log_rpow_atTop hhalf).bound hcoeff)
  obtain ⟨B₀, hB₀⟩ :=
    Filter.eventually_atTop.mp
      (hraw.and (Filter.eventually_ge_atTop 2))
  obtain ⟨N₀, hN₀⟩ :=
    DependencyEdgesCritical.runLengthAddOne_tends_to_infinity
      hC B₀
  refine ⟨N₀, ?_⟩
  intro N hN L hrun
  have hB₀L : B₀ ≤ L + 1 :=
    hN₀ N hN L hrun
  have hlarge := hB₀ (L + 1) hB₀L
  have hBtwo : 2 ≤ L + 1 := hlarge.2
  have hBlog : 0 < Real.log ((L + 1 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast hBtwo)
  have hBnonneg : 0 ≤ ((L + 1 : ℕ) : ℝ) := by positivity
  have hlogBound :
      Real.log ((L + 1 : ℕ) : ℝ) ≤
        (1 / T) * Real.sqrt ((L + 1 : ℕ) : ℝ) := by
    have h := hlarge.1
    rw [Real.norm_eq_abs,
      abs_of_pos hBlog,
      Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hBnonneg _),
      ← Real.sqrt_eq_rpow] at h
    exact h
  have hscaled :
      T * Real.log ((L + 1 : ℕ) : ℝ) ≤
        Real.sqrt ((L + 1 : ℕ) : ℝ) := by
    calc
      T * Real.log ((L + 1 : ℕ) : ℝ) ≤
          T * ((1 / T) *
            Real.sqrt ((L + 1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hlogBound hT.le
      _ = Real.sqrt ((L + 1 : ℕ) : ℝ) := by
        field_simp
  have hratio :
      T ≤
        Real.sqrt ((L + 1 : ℕ) : ℝ) /
          Real.log ((L + 1 : ℕ) : ℝ) :=
    (le_div_iff₀ hBlog).2 hscaled
  let y : ℝ :=
    δ * (Real.sqrt ((L + 1 : ℕ) : ℝ) /
      Real.log ((L + 1 : ℕ) : ℝ))
  have hy : 0 ≤ y := by
    dsimp only [y]
    positivity
  have hyLower : 1 ≤ ε * y := by
    have hmul := mul_le_mul_of_nonneg_left hratio hδ.le
    have hcancel : δ * T = 1 / ε := by
      dsimp only [T]
      field_simp
      ring
    rw [hcancel] at hmul
    have hdiv := (div_le_iff₀ hε).mp hmul
    simpa only [y, one_mul, mul_comm] using hdiv
  have hyExp : y ≤ Real.exp y :=
    le_trans (by linarith) (Real.add_one_le_exp y)
  have honeExp : 1 ≤ ε * Real.exp y :=
    hyLower.trans
      (mul_le_mul_of_nonneg_left hyExp hε.le)
  have hdecay : Real.exp (-y) ≤ ε := by
    have hmultiply :=
      mul_le_mul_of_nonneg_right honeExp (Real.exp_nonneg (-y))
    rw [mul_assoc, ← Real.exp_add] at hmultiply
    simpa using hmultiply
  have hgap :=
    terminalRankGapFactor_le_exp_gap
      (Cterm := Cterm) (K := K) (N := N) hBtwo
  rw [abs_of_nonneg
    (terminalRankGapFactor_nonneg Cterm K N L), abs_one, mul_one]
  exact hgap.trans (by
    convert hdecay using 1
    · simp only [δ, y]
      ring)

/--
Consequently the minimal high-density envelope is uniformly `o(N²)`.
-/
theorem highDensityIntrinsicNonterminalMassEnvelope_uniformLittleO
    {C Cterm K : ℝ} (hC : 0 ≤ C) (hCterm : 0 ≤ Cterm)
    (hthreshold : 2 * Cterm < K * Real.log 2) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (highDensityIntrinsicNonterminalMassEnvelope C Cterm K)
      (fun N _ => (N : ℝ) ^ 2) := by
  have hgap :=
    terminalRankGapFactor_uniformLittleOOne
      hC hCterm hthreshold
  let a : ℝ := 8 * CriticalRunWindow.balanceConstant C
  have ha : 0 < a := by
    dsimp only [a, CriticalRunWindow.balanceConstant]
    positivity
  intro ε hε
  obtain ⟨N₀, hN₀⟩ :=
    hgap (ε / a) (div_pos hε ha)
  refine ⟨N₀, ?_⟩
  intro N hN L hrun
  have hfactor := hN₀ N hN L hrun
  rw [abs_of_nonneg
      (terminalRankGapFactor_nonneg Cterm K N L),
    abs_one, mul_one] at hfactor
  rw [abs_of_nonneg
      (highDensityIntrinsicNonterminalMassEnvelope_nonneg
        C Cterm K N L),
    abs_of_nonneg (sq_nonneg (N : ℝ))]
  have hcoef :
      a * terminalRankGapFactor Cterm K N L ≤ ε := by
    calc
      a * terminalRankGapFactor Cterm K N L ≤
          a * (ε / a) :=
        mul_le_mul_of_nonneg_left hfactor ha.le
      _ = ε := by field_simp
  unfold highDensityIntrinsicNonterminalMassEnvelope
  dsimp only [a] at hcoef
  calc
    (8 * CriticalRunWindow.balanceConstant C) *
          (N : ℝ) ^ 2 *
          terminalRankGapFactor Cterm K N L =
        ((8 * CriticalRunWindow.balanceConstant C) *
          terminalRankGapFactor Cterm K N L) *
            (N : ℝ) ^ 2 := by ring
    _ ≤ ε * (N : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right hcoef (sq_nonneg (N : ℝ))

/--
Source-faithful closure of the high-density line.  Its sole arithmetic
input is the displayed direct bound for the concrete size-two host
population.
-/
theorem highDensityIntrinsicNonterminalMass_uniformLittleO
    {C Cterm K : ℝ} {κ₀ A : ℕ}
    (hC : 0 ≤ C) (hCterm : 0 ≤ Cterm)
    (hthreshold : 2 * Cterm < K * Real.log 2)
    (hhosts :
      ∃ N₁ : ℕ, ∀ N ≥ N₁, ∀ M L,
        2 * N ≤ M →
        M ≤ κ₀ * N →
        CriticalRunWindow.InRunLengthWindow C N L →
        ((boundedComponentHosts N M A L 2).card : ℝ) ≤
          sizeTwoComponentHostEnvelope Cterm N L) :
    UniformLittleOInBoundedRatioWindow C κ₀
      (highDensityIntrinsicNonterminalMass A K) := by
  apply BoundedRatioSectorClosure.uniformLittleOInBoundedRatioWindow_of_nonnegative_envelope
    (highDensityIntrinsicNonterminalMassEnvelope_uniformLittleO
      hC hCterm hthreshold)
    (highDensityIntrinsicNonterminalMass_nonneg A K)
    (highDensityIntrinsicNonterminalMassEnvelope_nonneg C Cterm K)
  obtain ⟨N₁, hN₁⟩ := hhosts
  refine ⟨max N₁ 2, ?_⟩
  intro N hN M L hNM hMκ hrun
  have hNtwo : 2 ≤ N :=
    (le_max_right N₁ 2).trans hN
  exact
    highDensityIntrinsicNonterminalMass_le_envelope
      hNtwo hrun
      (hN₁ N ((le_max_left N₁ 2).trans hN)
        M L hNM hMκ hrun)

/-! ## Assembly of the two manuscript branches -/

/-- Exact finite decomposition of the sixth-sector residual mass. -/
theorem boundedIntrinsicNonterminalResidualMass_eq_densitySplit
    {N M A L : ℕ} (hN : 2 ≤ N) (K : ℝ) :
    boundedIntrinsicNonterminalResidualMass N M A L hN K =
      moderateDensityIntrinsicNonterminalResidualMass N M A L hN K +
        highDensityIntrinsicNonterminalResidualMass N M A L hN K := by
  classical
  unfold boundedIntrinsicNonterminalResidualMass
    moderateDensityIntrinsicNonterminalResidualMass
    highDensityIntrinsicNonterminalResidualMass
  calc
    (∑ pair ∈ boundedIntrinsicNonterminalPairs N M A L hN K,
        residualWeight A hN pair) =
        ∑ pair ∈
          (moderateDensityIntrinsicNonterminalPairs N M A L hN K ∪
            highDensityIntrinsicNonterminalPairs N M A L hN K),
          residualWeight A hN pair := by
      rw [moderate_union_highDensityIntrinsicNonterminalPairs hN K]
    _ =
        (∑ pair ∈
          moderateDensityIntrinsicNonterminalPairs N M A L hN K,
          residualWeight A hN pair) +
        ∑ pair ∈
          highDensityIntrinsicNonterminalPairs N M A L hN K,
          residualWeight A hN pair :=
      Finset.sum_union
        (moderate_disjoint_highDensityIntrinsicNonterminalPairs hN K)

/--
The public sixth-sector mass is exactly the sum of the two density
branches.
-/
theorem intrinsicNonterminalSectorResidualMass_eq_densitySplit
    (A : ℕ) (K : ℝ) (N M L : ℕ) :
    sectorResidualMass A
        (boundedIntrinsicTerminalPredicate A K)
        .nonterminal N M L =
      moderateDensityIntrinsicNonterminalMass A K N M L +
        highDensityIntrinsicNonterminalMass A K N M L := by
  by_cases hN : 2 ≤ N
  · rw [sectorResidualMass, dif_pos hN,
      ← boundedIntrinsicNonterminalResidualMass_eq_sectorResidualMassNat
        hN K,
      moderateDensityIntrinsicNonterminalMass, dif_pos hN,
      highDensityIntrinsicNonterminalMass, dif_pos hN]
    exact_mod_cast
      boundedIntrinsicNonterminalResidualMass_eq_densitySplit
        (M := M) (A := A) (L := L) hN K
  · rw [sectorResidualMass, dif_neg hN,
      moderateDensityIntrinsicNonterminalMass, dif_neg hN,
      highDensityIntrinsicNonterminalMass, dif_neg hN]
    norm_num

/--
Lemma 17.28 in the two cases used by the source.

* the moderate branch consumes a direct size-ten host count with
  `N^(1+o_C(1))` envelope;
* the high branch consumes the direct size-two count
  `N exp(Cterm sqrt(B)/log B)`;
* `2 Cterm < K log 2` supplies the strict exponential saving.

No global cardinality premise and no named arithmetic bridge is required.
-/
theorem intrinsicNonterminalSector_uniformLittleO_of_densitySplit
    {C Cterm K : ℝ} {κ₀ A : ℕ}
    (hC : 0 ≤ C) (hCterm : 0 ≤ Cterm)
    (hthreshold : 2 * Cterm < K * Real.log 2)
    (hostEnvelope : ℕ → ℕ → ℝ)
    (hhostRate :
      UniformLinearSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C) hostEnvelope)
    (hhostNonneg : ∀ N L, 0 ≤ hostEnvelope N L)
    (hhostsTen :
      ∃ N₁ : ℕ, ∀ N ≥ N₁, ∀ M L,
        2 * N ≤ M →
        M ≤ κ₀ * N →
        CriticalRunWindow.InRunLengthWindow C N L →
        ((boundedComponentHosts N M A L 10).card : ℝ) ≤
          hostEnvelope N L)
    (hhostsTwo :
      ∃ N₁ : ℕ, ∀ N ≥ N₁, ∀ M L,
        2 * N ≤ M →
        M ≤ κ₀ * N →
        CriticalRunWindow.InRunLengthWindow C N L →
        ((boundedComponentHosts N M A L 2).card : ℝ) ≤
          sizeTwoComponentHostEnvelope Cterm N L) :
    UniformLittleOInBoundedRatioWindow C κ₀
      (sectorResidualMass A
        (boundedIntrinsicTerminalPredicate A K) .nonterminal) := by
  have hmoderate :=
    moderateDensityIntrinsicNonterminalMass_uniformLittleO
      (K := K) hostEnvelope hhostRate hhostNonneg hhostsTen
  have hhigh :=
    highDensityIntrinsicNonterminalMass_uniformLittleO
      hC hCterm hthreshold hhostsTwo
  have hsum :=
    uniformLittleOInBoundedRatioWindow_add hmoderate hhigh
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := hsum ε hε
  refine ⟨N₀, ?_⟩
  intro N hN M L hNM hMκ hrun
  rw [intrinsicNonterminalSectorResidualMass_eq_densitySplit]
  exact hN₀ N hN M L hNM hMκ hrun

/--
Registered-interface version of the source-faithful density split.
The historical bridge arguments in `NonterminalSectorStabilityStatement`
remain explicit at the outer interface but are not needed for this
mass-level implication once the two concrete host bounds are supplied.
-/
theorem nonterminalSectorStability_of_densitySplit
    {C Cterm K : ℝ} {κ₀ A : ℕ}
    (hC : 0 ≤ C) (hCterm : 0 ≤ Cterm)
    (hthreshold : 2 * Cterm < K * Real.log 2)
    (hostEnvelope : ℕ → ℕ → ℝ)
    (hhostRate :
      UniformLinearSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C) hostEnvelope)
    (hhostNonneg : ∀ N L, 0 ≤ hostEnvelope N L)
    (hhostsTen :
      ∃ N₁ : ℕ, ∀ N ≥ N₁, ∀ M L,
        2 * N ≤ M →
        M ≤ κ₀ * N →
        CriticalRunWindow.InRunLengthWindow C N L →
        ((boundedComponentHosts N M A L 10).card : ℝ) ≤
          hostEnvelope N L)
    (hhostsTwo :
      ∃ N₁ : ℕ, ∀ N ≥ N₁, ∀ M L,
        2 * N ≤ M →
        M ≤ κ₀ * N →
        CriticalRunWindow.InRunLengthWindow C N L →
        ((boundedComponentHosts N M A L 2).card : ℝ) ≤
          sizeTwoComponentHostEnvelope Cterm N L) :
    NonterminalSectorStabilityStatement C κ₀ A
      (boundedIntrinsicTerminalPredicate A K) := by
  intro _hES _hPell
  exact
    intrinsicNonterminalSector_uniformLittleO_of_densitySplit
      hC hCterm hthreshold hostEnvelope hhostRate hhostNonneg
      hhostsTen hhostsTwo

/-! ## Sixth-sector fibres with one component shape fixed -/

/--
The intrinsic sixth-sector pairs carrying a bounded component with one
specified ordered pair of offset sets.
-/
noncomputable def intrinsicNonterminalShapeFiber
    (N M A L : ℕ) (hN : 2 ≤ N) (K : ℝ)
    (shape :
      Finset (Fin (L + 1)) × Finset (Fin (L + 1))) :
    Finset (SeparatedBoundedRatioPair N M L) :=
  (boundedIntrinsicNonterminalPairs N M A L hN K).filter fun pair =>
    pair ∈ boundedComponentHostsOfShape
      N M A L 10 shape

@[simp]
theorem mem_intrinsicNonterminalShapeFiber
    {N M A L : ℕ} {hN : 2 ≤ N} {K : ℝ}
    {shape :
      Finset (Fin (L + 1)) × Finset (Fin (L + 1))}
    {pair : SeparatedBoundedRatioPair N M L} :
    pair ∈ intrinsicNonterminalShapeFiber
        N M A L hN K shape ↔
      pair ∈ boundedIntrinsicNonterminalPairs
          N M A L hN K ∧
        pair ∈ boundedComponentHostsOfShape
          N M A L 10 shape := by
  simp [intrinsicNonterminalShapeFiber]

/-- A sixth-sector fixed-shape fibre is contained in its ambient host fibre. -/
theorem intrinsicNonterminalShapeFiber_subset_boundedComponentHostsOfShape
    {N M A L : ℕ} {hN : 2 ≤ N} {K : ℝ}
    {shape :
      Finset (Fin (L + 1)) × Finset (Fin (L + 1))} :
    intrinsicNonterminalShapeFiber
        N M A L hN K shape ⊆
      boundedComponentHostsOfShape
        N M A L 10 shape := by
  intro pair hpair
  exact (mem_intrinsicNonterminalShapeFiber.mp hpair).2

/-- The fixed offset-shape fibres cover the literal intrinsic sixth sector. -/
theorem intrinsicNonterminalPairs_subset_shapeFibers
    {N M A L : ℕ} (hN : 2 ≤ N) (K : ℝ) :
    boundedIntrinsicNonterminalPairs N M A L hN K ⊆
      (boundedOffsetShapes L 10).biUnion fun shape =>
        intrinsicNonterminalShapeFiber
          N M A L hN K shape := by
  classical
  intro pair hpair
  have hhost :
      pair ∈ boundedComponentHosts N M A L 10 :=
    intrinsicNonterminalPairs_subset_boundedComponentHostsTen
      hN K hpair
  have hshapeUnion :=
    boundedComponentHosts_subset_shapeUnion
      (N := N) (M := M) (A := A) (L := L) (K := 10)
      hN hhost
  obtain ⟨shape, hshape, hpairShape⟩ :=
    Finset.mem_biUnion.mp hshapeUnion
  apply Finset.mem_biUnion.mpr
  exact
    ⟨shape, hshape,
      mem_intrinsicNonterminalShapeFiber.mpr
        ⟨hpair, hpairShape⟩⟩

/--
Maximum cardinality of a sixth-sector fibre with both component offset sets
fixed.  This finite maximum is the single unsummed counting quantity in the
reduction.
-/
noncomputable def intrinsicNonterminalShapeFiberMaximum
    (N M A L : ℕ) (hN : 2 ≤ N) (K : ℝ) : ℕ :=
  (boundedOffsetShapes L 10).sup fun shape =>
    (intrinsicNonterminalShapeFiber
      N M A L hN K shape).card

/-- Every admissible fixed-shape fibre is bounded by the finite maximum. -/
theorem card_intrinsicNonterminalShapeFiber_le_maximum
    {N M A L : ℕ} {hN : 2 ≤ N} {K : ℝ}
    {shape :
      Finset (Fin (L + 1)) × Finset (Fin (L + 1))}
    (hshape : shape ∈ boundedOffsetShapes L 10) :
    (intrinsicNonterminalShapeFiber
        N M A L hN K shape).card ≤
      intrinsicNonterminalShapeFiberMaximum
        N M A L hN K := by
  exact Finset.le_sup (f := fun shape =>
    (intrinsicNonterminalShapeFiber
      N M A L hN K shape).card) hshape

/--
An ambient fixed-shape host bound controls the actual sixth-sector maximum.
This is the direct attachment point for the degree-one, Pell, and
Evertse--Silverman counts already developed in the host module.
-/
theorem intrinsicNonterminalShapeFiberMaximum_le_of_hostShapeFibers
    {N M A L Q : ℕ} {hN : 2 ≤ N} {K : ℝ}
    (hshape :
      ∀ shape ∈ boundedOffsetShapes L 10,
        (boundedComponentHostsOfShape
          N M A L 10 shape).card ≤ Q) :
    intrinsicNonterminalShapeFiberMaximum
        N M A L hN K ≤ Q := by
  unfold intrinsicNonterminalShapeFiberMaximum
  apply Finset.sup_le
  intro shape hshapeMem
  exact
    (Finset.card_le_card
      (intrinsicNonterminalShapeFiber_subset_boundedComponentHostsOfShape
        (N := N) (M := M) (A := A) (L := L)
        (hN := hN) (K := K) (shape := shape))).trans
      (hshape shape hshapeMem)

/--
Exact finite summation over component shapes.  All shape multiplicity is
absorbed into the explicit polynomial `((11)(L+1)^10)^2`.
-/
theorem card_intrinsicNonterminalPairs_le_shapeFiberMaximum
    {N M A L : ℕ} (hN : 2 ≤ N) (K : ℝ) :
    (boundedIntrinsicNonterminalPairs
        N M A L hN K).card ≤
      ((11 * (L + 1) ^ 10) ^ 2) *
        intrinsicNonterminalShapeFiberMaximum
          N M A L hN K := by
  classical
  calc
    (boundedIntrinsicNonterminalPairs
        N M A L hN K).card ≤
        ((boundedOffsetShapes L 10).biUnion fun shape =>
          intrinsicNonterminalShapeFiber
            N M A L hN K shape).card :=
      Finset.card_le_card
        (intrinsicNonterminalPairs_subset_shapeFibers hN K)
    _ ≤
        ∑ shape ∈ boundedOffsetShapes L 10,
          (intrinsicNonterminalShapeFiber
            N M A L hN K shape).card :=
      Finset.card_biUnion_le
    _ ≤
        ∑ _shape ∈ boundedOffsetShapes L 10,
          intrinsicNonterminalShapeFiberMaximum
            N M A L hN K :=
      Finset.sum_le_sum fun shape hshape =>
        card_intrinsicNonterminalShapeFiber_le_maximum hshape
    _ =
        (boundedOffsetShapes L 10).card *
          intrinsicNonterminalShapeFiberMaximum
            N M A L hN K := by
      simp
    _ ≤
        ((11 * (L + 1) ^ 10) ^ 2) *
          intrinsicNonterminalShapeFiberMaximum
            N M A L hN K := by
      exact
        Nat.mul_le_mul_right
          (intrinsicNonterminalShapeFiberMaximum
            N M A L hN K)
          (by
            simpa only [Nat.reduceAdd] using
              card_boundedOffsetShapes_le L 10)

/-!
## A proof-independent global envelope (stronger sufficient criterion)

The rest of the file is kept for compatibility with earlier versions.  It
bounds the whole sixth sector through size-ten fixed-shape fibres before
splitting by density.  This is a valid sufficient criterion, but it is
strictly stronger than the two-case argument in Lemma 17.28 and should not
be read as the remaining source-level obligation.
-/

/--
The preceding finite maximum, set to zero below `N=2`, so that it has the
same proof-independent parameter list as the effective cardinality.
-/
noncomputable def intrinsicNonterminalShapeFiberMaximumCardinality
    (A : ℕ) (K : ℝ) (N M L : ℕ) : ℕ :=
  if hN : 2 ≤ N then
    intrinsicNonterminalShapeFiberMaximum
      N M A L hN K
  else 0

/--
The fixed-shape cardinality envelope after division by the full extracted
rank factor.
-/
noncomputable def intrinsicNonterminalShapeFiberEnvelope
    (A : ℕ) (K : ℝ) (N M L : ℕ) : ℝ :=
  (((11 * (L + 1) ^ 10) ^ 2 *
      intrinsicNonterminalShapeFiberMaximumCardinality
        A K N M L : ℕ) : ℝ) /
    ((2 ^ (terminalRankBudget K L + 1) : ℕ) : ℝ)

/--
Critical normalization of the fixed-shape envelope.  A uniform little-oh
bound for this one explicit function closes the effective-cardinality debt.
-/
noncomputable def intrinsicNonterminalNormalizedShapeFiberEnvelope
    (A : ℕ) (K : ℝ) (N M L : ℕ) : ℝ :=
  (N : ℝ) *
    intrinsicNonterminalShapeFiberEnvelope A K N M L

theorem intrinsicNonterminalShapeFiberEnvelope_nonneg
    (A : ℕ) (K : ℝ) (N M L : ℕ) :
    0 ≤ intrinsicNonterminalShapeFiberEnvelope A K N M L := by
  unfold intrinsicNonterminalShapeFiberEnvelope
  positivity

theorem intrinsicNonterminalNormalizedShapeFiberEnvelope_nonneg
    (A : ℕ) (K : ℝ) (N M L : ℕ) :
    0 ≤
      intrinsicNonterminalNormalizedShapeFiberEnvelope
        A K N M L := by
  unfold intrinsicNonterminalNormalizedShapeFiberEnvelope
  exact mul_nonneg (by positivity)
    (intrinsicNonterminalShapeFiberEnvelope_nonneg
      A K N M L)

/-- Global natural-cardinality form of the finite fixed-shape reduction. -/
theorem intrinsicNonterminalCardinality_le_shapeFiberMaximum
    (A : ℕ) (K : ℝ) (N M L : ℕ) :
    intrinsicNonterminalCardinality A K N M L ≤
      ((11 * (L + 1) ^ 10) ^ 2) *
        intrinsicNonterminalShapeFiberMaximumCardinality
          A K N M L := by
  by_cases hN : 2 ≤ N
  · simpa only [intrinsicNonterminalCardinality,
      intrinsicNonterminalShapeFiberMaximumCardinality,
      dif_pos hN] using
      card_intrinsicNonterminalPairs_le_shapeFiberMaximum
        (M := M) (A := A) (L := L) hN K
  · simp [intrinsicNonterminalCardinality,
      intrinsicNonterminalShapeFiberMaximumCardinality,
      hN]

/-- The fixed-shape envelope dominates the effective sixth-sector count. -/
theorem intrinsicNonterminalEffectiveCardinality_le_shapeFiberEnvelope
    (A : ℕ) (K : ℝ) (N M L : ℕ) :
    intrinsicNonterminalEffectiveCardinality A K N M L ≤
      intrinsicNonterminalShapeFiberEnvelope A K N M L := by
  have hdenominator :
      0 <
        ((2 ^ (terminalRankBudget K L + 1) : ℕ) : ℝ) := by
    positivity
  have hcard :
      (intrinsicNonterminalCardinality A K N M L : ℝ) ≤
        (((11 * (L + 1) ^ 10) ^ 2 *
          intrinsicNonterminalShapeFiberMaximumCardinality
            A K N M L : ℕ) : ℝ) := by
    exact_mod_cast
      intrinsicNonterminalCardinality_le_shapeFiberMaximum
        A K N M L
  unfold intrinsicNonterminalEffectiveCardinality
    intrinsicNonterminalShapeFiberEnvelope
  exact (div_le_div_iff_of_pos_right hdenominator).2 hcard

/-- The same domination after multiplication by the critical factor `N`. -/
theorem intrinsicNonterminalNormalizedCardinality_le_shapeFiberEnvelope
    (A : ℕ) (K : ℝ) (N M L : ℕ) :
    intrinsicNonterminalNormalizedCardinality A K N M L ≤
      intrinsicNonterminalNormalizedShapeFiberEnvelope
        A K N M L := by
  unfold intrinsicNonterminalNormalizedCardinality
    intrinsicNonterminalNormalizedShapeFiberEnvelope
  exact
    mul_le_mul_of_nonneg_left
      (intrinsicNonterminalEffectiveCardinality_le_shapeFiberEnvelope
        A K N M L)
      (by positivity)

/-! ## Uniform closure from the one fixed-shape invariant -/

/--
Uniform little-oh for the normalized fixed-shape envelope implies the
effective-cardinality invariant isolated in
`BoundedRatioNonterminalClosure`.
-/
theorem intrinsicNonterminalNormalizedCardinality_uniformLittleO_of_shapeFiberEnvelope
    {C : ℝ} {κ₀ A : ℕ} {K : ℝ}
    (henvelope :
      UniformLittleOInBoundedRatioWindow C κ₀
        (intrinsicNonterminalNormalizedShapeFiberEnvelope A K)) :
    UniformLittleOInBoundedRatioWindow C κ₀
      (intrinsicNonterminalNormalizedCardinality A K) := by
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := henvelope ε hε
  refine ⟨N₀, ?_⟩
  intro N hN M L hNM hMκ hrun
  have hbound :=
    intrinsicNonterminalNormalizedCardinality_le_shapeFiberEnvelope
      A K N M L
  have henvelopeBound :=
    hN₀ N hN M L hNM hMκ hrun
  rw [abs_of_nonneg
    (intrinsicNonterminalNormalizedShapeFiberEnvelope_nonneg
      A K N M L)] at henvelopeBound
  rw [abs_of_nonneg
    (intrinsicNonterminalNormalizedCardinality_nonneg
      A K N M L)]
  exact hbound.trans henvelopeBound

/--
Historical fixed-shape sufficient criterion for Lemma 17.28.  Every finite
and critical-window transfer has been discharged, but its global premise is
stronger than the density-split criterion proved above.
-/
theorem intrinsicNonterminalSector_uniformLittleO_of_shapeFiberEnvelope
    {C : ℝ} {κ₀ A : ℕ} {K : ℝ}
    (henvelope :
      UniformLittleOInBoundedRatioWindow C κ₀
        (intrinsicNonterminalNormalizedShapeFiberEnvelope A K)) :
    UniformLittleOInBoundedRatioWindow C κ₀
      (sectorResidualMass A
        (boundedIntrinsicTerminalPredicate A K) .nonterminal) := by
  exact
    intrinsicNonterminalSector_uniformLittleO_of_normalizedCardinality
      (intrinsicNonterminalNormalizedCardinality_uniformLittleO_of_shapeFiberEnvelope
        henvelope)

/--
Registered-interface form of the same reduction.  The historical
Evertse--Silverman and generalized-Pell antecedents remain visible in the
target interface, but no additional hypothesis besides the fixed-shape
envelope is manufactured here.
-/
theorem nonterminalSectorStability_of_shapeFiberEnvelope
    {C : ℝ} {κ₀ A : ℕ} {K : ℝ}
    (henvelope :
      UniformLittleOInBoundedRatioWindow C κ₀
        (intrinsicNonterminalNormalizedShapeFiberEnvelope A K)) :
    NonterminalSectorStabilityStatement C κ₀ A
      (boundedIntrinsicTerminalPredicate A K) := by
  intro _hES _hPell
  exact
    intrinsicNonterminalSector_uniformLittleO_of_shapeFiberEnvelope
      henvelope

end

end BoundedRatioNonterminalCardinality
end PaperC
