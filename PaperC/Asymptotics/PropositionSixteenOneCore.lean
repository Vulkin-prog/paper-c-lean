import PaperC.Asymptotics.PropositionElevenTwo
import PaperC.Asymptotics.BoundedRatioRationalMass
import PaperC.Asymptotics.BoundedRatioSectorAligned
import PaperC.Diophantine.EvertseSilvermanInput
import PaperC.Diophantine.PellInput

set_option maxHeartbeats 1800000

/-!
# Proposition 16.1: finite core on an interval of bounded ratio

The manuscript writes `U_{N,κ} = [N, κN) ∩ ℤ`.  For the application in
Theorem 16.2 the quotient `κ = M / N` need not be an integer, so this file
uses the equivalent and more literal integral parametrization

`U(N,M) = [N,M)`, with `2N ≤ M ≤ κ₀N`.

The relation exponent is computed in the finite cylinder with cutoff
`M + L`, which contains both complete start windows.  The definition
`R2κ` is therefore the exact finite sum

`∑_{x,y∈U(N,M), |x-y|>L} (2^ρ(x,y)-1)`.

The algebraic decomposition, the ordered seven-sector partition and the
finite summation are proved here without asymptotic assumptions.  The
bounded-ratio stability estimates of Section 17 are exposed separately,
one conclusion at a time.  In particular, the three deep-sector interfaces
correspond exactly to the bounded-ratio analogues of Proposition 9.9,
Proposition 9.11 and Theorem 10.1.  The first two explicitly take the
Evertse--Silverman and generalized-Pell inputs; the terminal interface takes
only generalized Pell, so the actual hypothesis flow remains visible in the
final theorem.
-/

namespace PaperC
namespace PropositionSixteenOne

open scoped BigOperators
open Affine
open Affine.CanonicalRationalCode
open CanonicalResidualComponents
open RationalMassFinite
open ResidualComponentCounts
open SectionElevenPartition

noncomputable section

/-! ## The literal bounded-ratio population -/

/-- The integral form of `U_{N,κ}` used in Proposition 16.1. -/
def boundedRatioBlock (N M : ℕ) : Finset ℕ :=
  BoundedRatioGeometry.boundedRatioBlock N M

@[simp]
theorem mem_boundedRatioBlock
    {N M x : ℕ} :
    x ∈ boundedRatioBlock N M ↔ N ≤ x ∧ x < M := by
  exact BoundedRatioGeometry.mem_boundedRatioBlock

/--
The finite prime cutoff sufficient for every vertex in a length-`L` window
whose start lies in `[N,M)`.
-/
def boundedRatioCutoff (M L : ℕ) : ℕ :=
  M + L

/-- Every occurrence in a retained window lies below the chosen cutoff. -/
theorem startWindow_le_boundedRatioCutoff
    {N M L x j : ℕ}
    (hx : x ∈ boundedRatioBlock N M) (hj : j ≤ L) :
    x + j ≤ boundedRatioCutoff M L := by
  have hx' := mem_boundedRatioBlock.mp hx
  unfold boundedRatioCutoff
  omega

/-- Ordered separated pairs of starts in `[N,M)`. -/
def separatedBoundedRatioPairs
    (N M L : ℕ) : Finset (ℕ × ℕ) :=
  BoundedRatioGeometry.separatedBoundedRatioPairs N M L

@[simp]
theorem mem_separatedBoundedRatioPairs
    {N M L x y : ℕ} :
    (x, y) ∈ separatedBoundedRatioPairs N M L ↔
      x ∈ boundedRatioBlock N M ∧
      y ∈ boundedRatioBlock N M ∧
      L < Nat.dist x y := by
  exact BoundedRatioGeometry.mem_separatedBoundedRatioPairs

/-- A separated bounded-ratio pair bundled with its range proof. -/
abbrev SeparatedBoundedRatioPair
    (N M L : ℕ) :=
  {pair : ℕ × ℕ // pair ∈ separatedBoundedRatioPairs N M L}

/-- Both coordinates are at least two once the base scale is at least two. -/
theorem pair_coordinates_two_le
    {N M L : ℕ} (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L) :
    2 ≤ pair.1.1 ∧ 2 ≤ pair.1.2 := by
  have hp := mem_separatedBoundedRatioPairs.mp pair.2
  exact
    ⟨hN.trans (mem_boundedRatioBlock.mp hp.1).1,
      hN.trans (mem_boundedRatioBlock.mp hp.2.1).1⟩

/-! ## Exact exponents and weights -/

/-- The systematic rational-channel exponent on a bounded-ratio pair. -/
noncomputable def pairSigma
    {N M L : ℕ} (A : ℕ)
    (pair : SeparatedBoundedRatioPair N M L) : ℕ :=
  canonicalPairSigma A L pair.1.1 pair.1.2

/-- The residual exponent `τ = ρ - σ`. -/
noncomputable def pairTau
    {N M L : ℕ} (A : ℕ) (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L) : ℕ :=
  residualTau (boundedRatioCutoff M L) A
    pair.1.1 pair.1.2 L
    (pair_coordinates_two_le hN pair).1
    (pair_coordinates_two_le hN pair).2

/-- The full relation exponent in the adequate finite cylinder. -/
noncomputable def pairRho
    {N M L : ℕ}
    (pair : SeparatedBoundedRatioPair N M L) : ℕ :=
  relationRho
    (twoStartSystem (boundedRatioCutoff M L)
      pair.1.1 pair.1.2 L)

/-- The exact rank identity `ρ = σ + τ` on `[N,M)`. -/
theorem pairRho_eq_pairSigma_add_pairTau
    {N M A L : ℕ} (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L) :
    pairRho pair = pairSigma A pair + pairTau A hN pair := by
  unfold pairRho pairSigma pairTau
  rw [canonicalPairSigma_eq_rationalSigma]
  exact
    relationRho_eq_rationalSigma_add_residualTau
      (boundedRatioCutoff M L) A
      pair.1.1 pair.1.2 L
      (pair_coordinates_two_le hN pair).1
      (pair_coordinates_two_le hN pair).2

/-- Full homogeneous weight `2^ρ-1`. -/
noncomputable def homogeneousWeight
    {N M L : ℕ}
    (pair : SeparatedBoundedRatioPair N M L) : ℕ :=
  2 ^ pairRho pair - 1

/-- Systematic weight `2^σ-1`. -/
noncomputable def systematicWeight
    {N M L : ℕ} (A : ℕ)
    (pair : SeparatedBoundedRatioPair N M L) : ℕ :=
  2 ^ pairSigma A pair - 1

/-- Residual weight `2^σ(2^τ-1)`. -/
noncomputable def residualWeight
    {N M L : ℕ} (A : ℕ) (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L) : ℕ :=
  2 ^ pairSigma A pair * (2 ^ pairTau A hN pair - 1)

/-- Pointwise form of equation (11.1), valid unchanged on `[N,M)`. -/
theorem homogeneousWeight_eq_systematic_add_residual
    {N M A L : ℕ} (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L) :
    homogeneousWeight pair =
      systematicWeight A pair + residualWeight A hN pair := by
  unfold homogeneousWeight systematicWeight residualWeight
  rw [pairRho_eq_pairSigma_add_pairTau (A := A) hN pair]
  exact PropositionElevenTwo.two_pow_add_sub_one
    (pairSigma A pair) (pairTau A hN pair)

/-! ## Literal finite masses -/

/-- The natural-valued homogeneous mass in Proposition 16.1. -/
noncomputable def homogeneousMassNat
    (N M L : ℕ) : ℕ :=
  ∑ pair : SeparatedBoundedRatioPair N M L,
    homogeneousWeight pair

/--
The public real-valued quantity `R_{2,κ}(N,L)`.  The endpoint `M` records
the exact integral interval `[N,M)` and is not rounded from a real quotient.
-/
noncomputable def R2κ
    (N M L : ℕ) : ℝ :=
  (homogeneousMassNat N M L : ℝ)

/-- Expansion of `R2κ` as the manuscript's literal filtered double sum. -/
theorem R2κ_eq_filtered_sum
    (N M L : ℕ) :
    R2κ N M L =
      ∑ pair ∈ separatedBoundedRatioPairs N M L,
        ((2 ^ relationRho
          (twoStartSystem (boundedRatioCutoff M L)
            pair.1 pair.2 L) - 1 : ℕ) : ℝ) := by
  classical
  unfold R2κ homogeneousMassNat homogeneousWeight pairRho
  rw [Nat.cast_sum]
  symm
  exact
    Finset.sum_subtype
      (separatedBoundedRatioPairs N M L)
      (fun _pair ↦ Iff.rfl)
      (fun pair ↦
        ((2 ^ relationRho
          (twoStartSystem (boundedRatioCutoff M L)
            pair.1 pair.2 L) - 1 : ℕ) : ℝ))

/-- Finite systematic mass. -/
noncomputable def systematicMassNat
    {N M L : ℕ} (A : ℕ) :
    ℕ :=
  ∑ pair : SeparatedBoundedRatioPair N M L,
    systematicWeight A pair

/--
The systematic subtype sum is exactly the bounded-ratio rational mass
constructed by the finite geometry module.
-/
theorem systematicMassNat_eq_boundedRationalMass
    (N M A L : ℕ) :
    systematicMassNat (N := N) (M := M) (L := L) A =
      BoundedRatioGeometry.boundedRationalMass N M A L 2 := by
  classical
  unfold systematicMassNat systematicWeight pairSigma
    BoundedRatioGeometry.boundedRationalMass
  exact
    (Finset.sum_subtype
      (separatedBoundedRatioPairs N M L)
      (fun _pair ↦ Iff.rfl)
      (fun pair ↦
        2 ^ canonicalPairSigma A L pair.1 pair.2 - 1)).symm

/--
Finite form of the new height-two computation in Lemma 17.5.  This is an
unconditional theorem; only its uniform asymptotic conversion is analytic.
-/
theorem systematicMassNat_le_boundedRatioEnvelope
    (N M A L : ℕ)
    (hNM : N ≤ M) (hA : 1 ≤ A) :
    systematicMassNat (N := N) (M := M) (L := L) A ≤
      2 * ((3 * L + 1) * (1 + (M - N) / 2)) *
          2 ^ (L / 2) +
        L * (2 * L) * ((2 * L) * L + 1) *
          (1 + (M - N) / 3) * 2 ^ (L / 3) := by
  rw [systematicMassNat_eq_boundedRationalMass]
  exact
    BoundedRatioGeometry.boundedRationalMass_le
      N M A L 2 hNM hA (by norm_num)

/-- Finite residual mass. -/
noncomputable def residualMassNat
    {N M L : ℕ} (A : ℕ) (hN : 2 ≤ N) :
    ℕ :=
  ∑ pair : SeparatedBoundedRatioPair N M L,
    residualWeight A hN pair

/-- Exact finite systematic/residual decomposition on `[N,M)`. -/
theorem homogeneousMassNat_eq_systematic_add_residual
    {N M A L : ℕ} (hN : 2 ≤ N) :
    homogeneousMassNat N M L =
      systematicMassNat (N := N) (M := M) (L := L) A +
        residualMassNat (N := N) (M := M) (L := L) A hN := by
  unfold homogeneousMassNat systematicMassNat residualMassNat
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro pair _hpair
  exact homogeneousWeight_eq_systematic_add_residual hN pair

/-- Proof-independent real systematic mass. -/
noncomputable def systematicMass
    (A N M L : ℕ) : ℝ :=
  if hN : 2 ≤ N then
    (systematicMassNat (N := N) (M := M) (L := L) A : ℝ)
  else 0

/-- Public identification with the finite bounded-ratio rational mass. -/
theorem systematicMass_eq_boundedRationalMass
    {A N M L : ℕ} (hN : 2 ≤ N) :
    systematicMass A N M L =
      (BoundedRatioGeometry.boundedRationalMass N M A L 2 : ℝ) := by
  simp only [systematicMass, dif_pos hN]
  exact_mod_cast
    systematicMassNat_eq_boundedRationalMass N M A L

/-- Proof-independent real residual mass. -/
noncomputable def residualMass
    (A N M L : ℕ) : ℝ :=
  if hN : 2 ≤ N then
    (residualMassNat (N := N) (M := M) (L := L) A hN : ℝ)
  else 0

/-- Real-valued exact decomposition, beyond the harmless threshold `N=2`. -/
theorem R2κ_eq_systematic_add_residual
    {N M A L : ℕ} (hN : 2 ≤ N) :
    R2κ N M L =
      systematicMass A N M L + residualMass A N M L := by
  simp only [R2κ, systematicMass, residualMass, dif_pos hN]
  exact_mod_cast
    homogeneousMassNat_eq_systematic_add_residual
      (M := M) (A := A) (L := L) hN

/-! ## A concrete ordered Section 17 partition -/

/--
The last test in Section 17 depends on the future literal construction of
the bounded-ratio terminal population.  Its type is fixed here so that such
a construction can be plugged in without changing Proposition 16.1.
-/
abbrev TerminalPredicateFamily :=
  ∀ (N M L : ℕ), SeparatedBoundedRatioPair N M L → Prop

/-- Literal bounded-ratio version of the test `P# ≤ N`. -/
def HasSmallCanonicalPrimeProduct
    {N M L : ℕ} (A : ℕ) (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L) : Prop :=
  CanonicalResidualPrimeProductAtMost
    (A := A) (L := L)
    (show 1 ≤ pair.1.1 by
      exact (by omega : 1 ≤ 2).trans
        (pair_coordinates_two_le hN pair).1)
    (show 1 ≤ pair.1.2 by
      exact (by omega : 1 ≤ 2).trans
        (pair_coordinates_two_le hN pair).2)
    N

/-- The six manuscript tests, in their exact order. -/
noncomputable def boundedRatioSectorTests
    (N M A L : ℕ) (hN : 2 ≤ N)
    (terminal : TerminalPredicateFamily) :
    OrderedSectorTests (SeparatedBoundedRatioPair N M L) where
  smallPrimeProduct :=
    HasSmallCanonicalPrimeProduct A hN
  smallCanonicalHeight := fun pair ↦
    SmallHeightLargeProductPairs.HasSmallCanonicalHeight
      A L pair.1.1 pair.1.2
  shallowCore := fun pair ↦
    ShallowCorePairs.HasCoreDensityAtMostThreeSixteenths
      A L pair.1.1 pair.1.2
  aligned := fun pair ↦
    SectionElevenPartition.IsCanonicallyAligned
      A L pair.1.1 pair.1.2
  manyDefects := fun pair ↦
    SectionElevenPartition.HasAtLeastThreeCorrectedDefects
      A L pair.1.1 pair.1.2
  terminal := terminal N M L

/-- The selected Section 17 sector of one bounded-ratio pair. -/
noncomputable def boundedRatioSectorOf
    {N M L : ℕ} (A : ℕ) (hN : 2 ≤ N)
    (terminal : TerminalPredicateFamily)
    (pair : SeparatedBoundedRatioPair N M L) :
    ResidualSector :=
  sectorOf
    (boundedRatioSectorTests N M A L hN terminal)
    pair

/-- The finite population in one of the seven bounded-ratio sectors. -/
noncomputable def boundedRatioSectorPairs
    (N M A L : ℕ) (hN : 2 ≤ N)
    (terminal : TerminalPredicateFamily)
    (sector : ResidualSector) :
    Finset (SeparatedBoundedRatioPair N M L) :=
  sectorPopulation
    (boundedRatioSectorTests N M A L hN terminal)
    sector

@[simp]
theorem mem_boundedRatioSectorPairs
    {N M A L : ℕ} {hN : 2 ≤ N}
    {terminal : TerminalPredicateFamily}
    {sector : ResidualSector}
    {pair : SeparatedBoundedRatioPair N M L} :
    pair ∈ boundedRatioSectorPairs
        N M A L hN terminal sector ↔
      boundedRatioSectorOf A hN terminal pair = sector := by
  exact mem_sectorPopulation

/-- The seven bounded-ratio sector populations are pairwise disjoint. -/
theorem boundedRatioSectorPairs_disjoint
    {N M A L : ℕ} (hN : 2 ≤ N)
    (terminal : TerminalPredicateFamily)
    {s t : ResidualSector} (hst : s ≠ t) :
    Disjoint
      (boundedRatioSectorPairs N M A L hN terminal s)
      (boundedRatioSectorPairs N M A L hN terminal t) :=
  sectorPopulations_disjoint
    (boundedRatioSectorTests N M A L hN terminal) hst

/-- Exact exhaustive and unique sector assignment. -/
theorem boundedRatio_existsUnique_sector
    {N M A L : ℕ} (hN : 2 ≤ N)
    (terminal : TerminalPredicateFamily)
    (pair : SeparatedBoundedRatioPair N M L) :
    ∃! sector : ResidualSector,
      pair ∈ boundedRatioSectorPairs
        N M A L hN terminal sector :=
  existsUnique_sector
    (boundedRatioSectorTests N M A L hN terminal)
    pair

/-- Finite residual mass carried by one Section 17 sector. -/
noncomputable def sectorResidualMassNat
    {N M L : ℕ} (A : ℕ) (hN : 2 ≤ N)
    (terminal : TerminalPredicateFamily)
    (sector : ResidualSector) : ℕ :=
  ∑ pair ∈ boundedRatioSectorPairs
      N M A L hN terminal sector,
    residualWeight A hN pair

/-- Exact finite disintegration of the residual mass over seven sectors. -/
theorem residualMassNat_eq_sum_sectors
    {N M A L : ℕ} (hN : 2 ≤ N)
    (terminal : TerminalPredicateFamily) :
    residualMassNat (N := N) (M := M) (L := L) A hN =
      ∑ sector : ResidualSector,
        sectorResidualMassNat
          (M := M) (L := L) A hN terminal sector := by
  classical
  let tests :=
    boundedRatioSectorTests N M A L hN terminal
  let weight : SeparatedBoundedRatioPair N M L → ℕ :=
    residualWeight A hN
  have hfiber :=
    Finset.sum_fiberwise
      (Finset.univ : Finset (SeparatedBoundedRatioPair N M L))
      (sectorOf tests) weight
  unfold residualMassNat
  simpa only [tests, weight, sectorResidualMassNat,
    boundedRatioSectorPairs, sectorPopulation] using hfiber.symm

/-- Proof-independent real mass of one bounded-ratio sector. -/
noncomputable def sectorResidualMass
    (A : ℕ) (terminal : TerminalPredicateFamily)
    (sector : ResidualSector)
    (N M L : ℕ) : ℝ :=
  if hN : 2 ≤ N then
    (sectorResidualMassNat
      (M := M) (L := L) A hN terminal sector : ℝ)
  else 0

/-- Real exact disintegration beyond `N=2`. -/
theorem residualMass_eq_sum_sectorResidualMass
    {N M A L : ℕ} (hN : 2 ≤ N)
    (terminal : TerminalPredicateFamily) :
    residualMass A N M L =
      ∑ sector : ResidualSector,
        sectorResidualMass A terminal sector N M L := by
  simp only [residualMass, sectorResidualMass, dif_pos hN]
  exact_mod_cast
    residualMassNat_eq_sum_sectors
      (M := M) (A := A) (L := L) hN terminal

/-- Complete exact finite assembly underlying Lemmas 17.31 and 17.32. -/
theorem R2κ_eq_systematic_add_sum_sectors
    {N M A L : ℕ} (hN : 2 ≤ N)
    (terminal : TerminalPredicateFamily) :
    R2κ N M L =
      systematicMass A N M L +
        ∑ sector : ResidualSector,
          sectorResidualMass A terminal sector N M L := by
  rw [R2κ_eq_systematic_add_residual hN,
    residualMass_eq_sum_sectorResidualMass hN terminal]

/-! ## Uniformity in `2 ≤ M/N ≤ κ₀` -/

/--
Uniform reciprocal-power formulation of
`|f(N,M,L)| ≤ N^(p/q+o_{C,κ₀}(1))` on bounded-ratio intervals.

The threshold is independent of both the endpoint `M` and the run length
`L`.  This is the three-variable analogue of
`UniformRationalPowerSubpolynomialOn`.
-/
def UniformRationalPowerInBoundedRatioWindow
    (p q : ℕ) (C : ℝ) (κ₀ : ℕ)
    (f : ℕ → ℕ → ℕ → ℝ) : Prop :=
  ∀ k : ℕ, 0 < k →
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ M L,
      2 * N ≤ M →
      M ≤ κ₀ * N →
      CriticalRunWindow.InRunLengthWindow C N L →
      |f N M L| ^ (q * k) ≤
        (N : ℝ) ^ (p * k + 1)

/--
Uniform little-oh on bounded-ratio intervals.  The threshold is independent
of both the endpoint `M` and the run length `L`.
-/
def UniformLittleOInBoundedRatioWindow
    (C : ℝ) (κ₀ : ℕ)
    (f : ℕ → ℕ → ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ M L,
      2 * N ≤ M →
      M ≤ κ₀ * N →
      CriticalRunWindow.InRunLengthWindow C N L →
      |f N M L| ≤ ε * |(N : ℝ) ^ 2|

/-- Uniform little-oh is stable under pointwise addition. -/
theorem uniformLittleOInBoundedRatioWindow_add
    {C : ℝ} {κ₀ : ℕ}
    {f g : ℕ → ℕ → ℕ → ℝ}
    (hf : UniformLittleOInBoundedRatioWindow C κ₀ f)
    (hg : UniformLittleOInBoundedRatioWindow C κ₀ g) :
    UniformLittleOInBoundedRatioWindow C κ₀
      (fun N M L ↦ f N M L + g N M L) := by
  intro ε hε
  have hhalf : 0 < ε / 2 := by positivity
  obtain ⟨Nf, hNf⟩ := hf (ε / 2) hhalf
  obtain ⟨Ng, hNg⟩ := hg (ε / 2) hhalf
  refine ⟨max Nf Ng, ?_⟩
  intro N hN M L hNM hMκ hrun
  calc
    |f N M L + g N M L| ≤
        |f N M L| + |g N M L| := abs_add_le _ _
    _ ≤
        (ε / 2) * |(N : ℝ) ^ 2| +
          (ε / 2) * |(N : ℝ) ^ 2| :=
      add_le_add
        (hNf N ((le_max_left _ _).trans hN)
          M L hNM hMκ hrun)
        (hNg N ((le_max_right _ _).trans hN)
          M L hNM hMκ hrun)
    _ = ε * |(N : ℝ) ^ 2| := by ring

/-- A finite sum of bounded-ratio little-oh families is little-oh. -/
theorem uniformLittleOInBoundedRatioWindow_finset_sum
    {ι : Type*} {C : ℝ} {κ₀ : ℕ}
    {F : ι → ℕ → ℕ → ℕ → ℝ}
    (s : Finset ι)
    (hF :
      ∀ i ∈ s,
        UniformLittleOInBoundedRatioWindow C κ₀ (F i)) :
    UniformLittleOInBoundedRatioWindow C κ₀
      (fun N M L ↦ ∑ i ∈ s, F i N M L) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro ε hε
      refine ⟨0, ?_⟩
      intro N _ M L _hNM _hMκ _hrun
      simp only [Finset.sum_empty, abs_zero]
      exact mul_nonneg hε.le (abs_nonneg _)
  | @insert i s hi ih =>
      have hhead := hF i (Finset.mem_insert_self i s)
      have htail :
          ∀ j ∈ s,
            UniformLittleOInBoundedRatioWindow C κ₀ (F j) := by
        intro j hj
        exact hF j (Finset.mem_insert_of_mem hj)
      have hsum :=
        uniformLittleOInBoundedRatioWindow_add hhead (ih htail)
      simpa only [Finset.sum_insert hi] using hsum

/-- Fintype-indexed specialization used by the seven sectors. -/
theorem uniformLittleOInBoundedRatioWindow_fintype_sum
    {ι : Type*} [Fintype ι]
    {C : ℝ} {κ₀ : ℕ}
    {F : ι → ℕ → ℕ → ℕ → ℝ}
    (hF :
      ∀ i,
        UniformLittleOInBoundedRatioWindow C κ₀ (F i)) :
    UniformLittleOInBoundedRatioWindow C κ₀
      (fun N M L ↦ ∑ i, F i N M L) := by
  classical
  apply uniformLittleOInBoundedRatioWindow_finset_sum Finset.univ
  intro i _hi
  exact hF i

/--
Generic sectorial assembly.  This theorem contains the whole finite
reasoning of Lemmas 17.31--17.32; only the individual analytic estimates
remain as premises.
-/
theorem proposition_sixteen_one_of_sector_estimates
    {C : ℝ} {κ₀ A : ℕ}
    (terminal : TerminalPredicateFamily)
    (hsystematic :
      UniformLittleOInBoundedRatioWindow C κ₀
        (systematicMass A))
    (hsector :
      ∀ sector : ResidualSector,
        UniformLittleOInBoundedRatioWindow C κ₀
          (sectorResidualMass A terminal sector)) :
    UniformLittleOInBoundedRatioWindow C κ₀ R2κ := by
  have hsectors :
      UniformLittleOInBoundedRatioWindow C κ₀
        (fun N M L ↦
          ∑ sector : ResidualSector,
            sectorResidualMass A terminal sector N M L) :=
    uniformLittleOInBoundedRatioWindow_fintype_sum hsector
  have htotal :=
    uniformLittleOInBoundedRatioWindow_add
      hsystematic hsectors
  intro ε hε
  obtain ⟨Ntotal, hNtotal⟩ := htotal ε hε
  refine ⟨max 2 Ntotal, ?_⟩
  intro N hN M L hNM hMκ hrun
  have hNtwo : 2 ≤ N := (le_max_left _ _).trans hN
  have hNlarge : Ntotal ≤ N := (le_max_right _ _).trans hN
  rw [R2κ_eq_systematic_add_sum_sectors hNtwo terminal]
  exact hNtotal N hNlarge M L hNM hMκ hrun

/-! ## The target statement -/

/--
Literal fully quantified form of Proposition 16.1:

`R_{2,κ}(N,L) = o_{C,κ₀}(N²)`, uniformly for
`2N ≤ M ≤ κ₀N` and `|L-log₂N| ≤ C`.
-/
def PropositionSixteenOneStatement
    (C : ℝ) (κ₀ : ℕ) : Prop :=
  UniformLittleOInBoundedRatioWindow C κ₀ R2κ

/-! ## Closed bounded-ratio rational mass -/

/--
Lemma 17.5's systematic mass is already closed from the finite geometry:
the new height-two contribution is `N·2^(L/2)` times a fixed polynomial in
`L`, hence `o(N²)` uniformly in every fixed ratio range.
-/
theorem systematicMass_uniformLittleOInBoundedRatioWindow
    {C : ℝ} (hC : 0 ≤ C)
    (κ₀ A : ℕ) (hA : 1 ≤ A) :
    UniformLittleOInBoundedRatioWindow C κ₀
      (systematicMass A) := by
  intro ε hε
  obtain ⟨Nmass, hNmass⟩ :=
    BoundedRatioRationalMass.boundedRationalMass_uniformLittleO_square
      hC κ₀ A hA ε hε
  refine ⟨max 2 Nmass, ?_⟩
  intro N hN M L hNM hMκ hrun
  have hNtwo : 2 ≤ N :=
    (le_max_left 2 Nmass).trans hN
  have hNmassN : Nmass ≤ N :=
    (le_max_right 2 Nmass).trans hN
  rw [systematicMass_eq_boundedRationalMass hNtwo]
  exact hNmass N hNmassN M L hNM hMκ hrun

/-! ## Narrow bounded-ratio stability interfaces -/

/-- Bounded-ratio stability of the first residual sector only. -/
def SmallPrimeProductSectorStabilityStatement
    (C : ℝ) (κ₀ A : ℕ)
    (terminal : TerminalPredicateFamily) : Prop :=
  UniformLittleOInBoundedRatioWindow C κ₀
    (sectorResidualMass A terminal .smallPrimeProduct)

/-- Bounded-ratio stability of the second residual sector only. -/
def SmallCanonicalHeightSectorStabilityStatement
    (C : ℝ) (κ₀ A : ℕ)
    (terminal : TerminalPredicateFamily) : Prop :=
  UniformLittleOInBoundedRatioWindow C κ₀
    (sectorResidualMass A terminal .smallCanonicalHeight)

/-- Bounded-ratio stability of the third residual sector only. -/
def ShallowCoreSectorStabilityStatement
    (C : ℝ) (κ₀ A : ℕ)
    (terminal : TerminalPredicateFamily) : Prop :=
  UniformLittleOInBoundedRatioWindow C κ₀
    (sectorResidualMass A terminal .shallowCore)

/--
The fourth bounded-ratio sector is eventually empty.  The strengthened
aligned exclusion only needs the common lower bound `N`, so it also handles
pairs crossing dyadic subblocks.
-/
theorem alignedDeepCoreSector_eventually_empty
    {C : ℝ} (hC : 0 ≤ C) (A : ℕ)
    (terminal : TerminalPredicateFamily) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧
      ∀ N ≥ N₀, ∀ M L,
        CriticalRunWindow.InRunLengthWindow C N L →
        ∀ hNtwo : 2 ≤ N,
          boundedRatioSectorPairs
              N M A L hNtwo terminal .alignedDeepCore =
            ∅ := by
  obtain ⟨Nalign, hNalign⟩ :=
    BoundedRatioSectorAligned.no_aligned_deep_core_of_lower_bounds_eventually
      hC A
  refine ⟨max 2 Nalign, le_max_left _ _, ?_⟩
  intro N hN M L hrun hNtwo
  have hNlarge : Nalign ≤ N :=
    (le_max_right _ _).trans hN
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro pair hpair
  have hsector :
      boundedRatioSectorOf A hNtwo terminal pair =
        .alignedDeepCore :=
    mem_boundedRatioSectorPairs.mp hpair
  have h :
      ¬HasSmallCanonicalPrimeProduct A hNtwo pair ∧
        ¬SmallHeightLargeProductPairs.HasSmallCanonicalHeight
          A L pair.1.1 pair.1.2 ∧
        ¬ShallowCorePairs.HasCoreDensityAtMostThreeSixteenths
          A L pair.1.1 pair.1.2 ∧
        SectionElevenPartition.IsCanonicallyAligned
          A L pair.1.1 pair.1.2 := by
    simpa only [boundedRatioSectorOf, boundedRatioSectorTests] using
      (sectorOf_eq_alignedDeepCore_iff.mp hsector)
  rcases h.2.2.2 with ⟨candidate, hchoice⟩
  have hpairData :=
    mem_separatedBoundedRatioPairs.mp pair.2
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
            A pair.1.1 pair.1.2 L := by
      omega
    simpa only [canonicalResidualComponentCount, hchoice] using hcount
  exact
    hNalign N hNlarge L hrun
      ((L + 1) ^ A)
      (Nat.one_le_pow _ _ (by omega))
      le_rfl
      pair.1.1 (mem_boundedRatioBlock.mp hpairData.1).1
      pair.1.2 (mem_boundedRatioBlock.mp hpairData.2.1).1
      candidate hdensity

/-- Lemma 17.17: the aligned sector has zero eventual mass. -/
theorem alignedDeepCoreSector_uniformLittleOInBoundedRatioWindow
    {C : ℝ} (hC : 0 ≤ C) (κ₀ A : ℕ)
    (terminal : TerminalPredicateFamily) :
    UniformLittleOInBoundedRatioWindow C κ₀
      (sectorResidualMass A terminal .alignedDeepCore) := by
  obtain ⟨Nempty, hNemptyTwo, hNempty⟩ :=
    alignedDeepCoreSector_eventually_empty hC A terminal
  intro ε hε
  refine ⟨Nempty, ?_⟩
  intro N hN M L _hNM _hMκ hrun
  have hNtwo : 2 ≤ N := hNemptyTwo.trans hN
  have hempty := hNempty N hN M L hrun hNtwo
  have hmass :
      sectorResidualMass A terminal .alignedDeepCore N M L = 0 := by
    simp only [sectorResidualMass, dif_pos hNtwo,
      sectorResidualMassNat, hempty, Finset.sum_empty,
      Nat.cast_zero]
  rw [hmass, abs_zero]
  exact mul_nonneg hε.le (abs_nonneg _)

/--
Bounded-ratio analogue of Proposition 9.9.  The external and internal
Diophantine inputs are explicit antecedents rather than hidden in the mass
statement.
-/
/- AUDIT_BRIDGE
{
  "id": "PCv07c-L17.26-bounded-ratio-many-defects",
  "kind": "internal",
  "status": "discharged",
  "discharged_by": [
    "PaperC.BoundedRatioManyDefectsAssembly.manyDefectsSectorStability",
    "PaperC.PropositionSixteenOne.proposition_sixteen_one_canonical",
    "PaperC.TheoremSixteenTwo.theorem_sixteen_two_canonical"
  ],
  "lean_name": "PaperC.PropositionSixteenOne.ManyDefectsSectorStabilityStatement",
  "citation": {
    "authors": ["Brice Pouly"],
    "title": "Loi de Poisson critique dans un bloc dyadique — Débuts de longues plages constantes d’une fonction aléatoire complètement multiplicative de Rademacher étendue",
    "version": "7c, juillet 2026",
    "target_pdf_sha256": "23a5db3c8d024cab3fb8ca9f8f1443f40cf9502b1fb6682a331f5948f57a3336",
    "locator": "Lemmes 17.18–17.26, pp. 60–62"
  },
  "source_statement": {
    "verbatim": "Lemme 17.26 (Élimination des défauts multiples sur U). La masse linéaire des couples du coeur profond non aligné tels que D# ≥ 3 est N^{3/2+o_{C,κ₀}(1)}.",
    "source_url": "paper_C_complete_v07c.pdf#page=62",
    "verification": "manual_primary_source_check_required"
  },
  "manuscript_locator": {
    "result": "Lemma 17.26",
    "equation": "fifth residual sector",
    "pages": "60–62"
  },
  "formalization_relation": "discharged historical interface retained for compatibility: Lean covers every literal active host by a two-defect window base and a finite component shape, disintegrates each fixed fibre by a smooth squarefree coefficient, closes degree one with an N^(1/2+o(1)) envelope, closes degree two from generalized Pell or an exact signed-divisor factorization, and closes degree at least three from Evertse–Silverman together with an unconditional factorial bound for the number of prime factors. The signed-divisor and Evertse–Silverman sums are uniformly N^o(1), the degree-by-degree fixed-fibre assembly is complete, and the resulting N^(3/2+o(1)) estimate is transported to little-oh of N^2. Evertse–Silverman and generalized Pell remain explicit lower-level antecedents; there is no remaining Lemma 17.26-specific formalization debt"
}
AUDIT_BRIDGE -/
def ManyDefectsSectorStabilityStatement
    (C : ℝ) (κ₀ A : ℕ)
    (terminal : TerminalPredicateFamily) : Prop :=
  EvertseSilvermanInput.EvertseSilvermanAbscissaStatement →
  PellInput.GeneralizedPellPolynomialBoxStatement →
  UniformLittleOInBoundedRatioWindow C κ₀
    (sectorResidualMass A terminal .manyDefects)

/--
Bounded-ratio analogue of Proposition 9.11, restricted to the sixth sector.
-/
/- AUDIT_BRIDGE
{
  "id": "PCv07c-L17.28-bounded-ratio-nonterminal-sector",
  "kind": "internal",
  "status": "discharged",
  "discharged_by": [
    "PaperC.BoundedRatioNonterminalAssembly.exists_nonterminalSectorStability",
    "PaperC.PropositionSixteenOne.proposition_sixteen_one_canonical",
    "PaperC.TheoremSixteenTwo.theorem_sixteen_two_canonical"
  ],
  "lean_name": "PaperC.PropositionSixteenOne.NonterminalSectorStabilityStatement",
  "citation": {
    "authors": ["Brice Pouly"],
    "title": "Loi de Poisson critique dans un bloc dyadique — Débuts de longues plages constantes d’une fonction aléatoire complètement multiplicative de Rademacher étendue",
    "version": "7c, juillet 2026",
    "target_pdf_sha256": "23a5db3c8d024cab3fb8ca9f8f1443f40cf9502b1fb6682a331f5948f57a3336",
    "locator": "Lemme 17.28, p. 63"
  },
  "source_statement": {
    "verbatim": "La masse du coeur profond non aligné à D# ≤ 2 — les couples à D# ≥ 3 étant éliminés par le lemme 17.26 — est o_{C,κ₀}(N²) en dehors de l’ensemble T_K.",
    "source_url": "paper_C_complete_v07c.pdf#page=63",
    "verification": "manual_primary_source_check_required"
  },
  "manuscript_locator": {
    "result": "Lemma 17.28",
    "equation": "sixth residual sector",
    "pages": "63"
  },
  "formalization_relation": "discharged historical interface retained for compatibility: Lean follows the manuscript split 3c# <= 2B versus 2B < 3c# exactly. In the first branch, the size-at-most-ten host population is reduced to fixed shapes and mobile fibres; the two-singleton shapes have an elementary N^(1+o(1)) envelope, degree two is closed from generalized Pell, and degree at least three is closed from Evertse–Silverman, giving N^(5/3+o(1)) mass. In the second branch, Lean extracts a size-two component, the exact factor 2^(R_K(B)+1), and an elementary Euler-product bound N exp(Cterm sqrt(B)/log B); it then chooses K with 2 Cterm < K log 2. The finite mass decomposition, floor handling, both host counts and both little-oh transports are complete. Evertse–Silverman and generalized Pell remain explicit lower-level antecedents; there is no remaining Lemma 17.28-specific formalization debt"
}
AUDIT_BRIDGE -/
def NonterminalSectorStabilityStatement
    (C : ℝ) (κ₀ A : ℕ)
    (terminal : TerminalPredicateFamily) : Prop :=
  EvertseSilvermanInput.EvertseSilvermanAbscissaStatement →
  PellInput.GeneralizedPellPolynomialBoxStatement →
  UniformLittleOInBoundedRatioWindow C κ₀
    (sectorResidualMass A terminal .nonterminal)

/--
Historical generic bounded-ratio interface for the seventh sector.
Only the generalized-Pell input occurs in this interface;
Evertse--Silverman is absent from Lemma 17.30.  For the canonical intrinsic
classifier, `BoundedRatioTerminalSummation` now proves the complete
conclusion from generalized Pell and the proved source-scoped Lemma 9.10
arithmetic equivalence, so the principal canonical assembly no longer takes
this coarse bridge as a premise.
-/
/- AUDIT_BRIDGE
{
  "id": "PCv07c-L17.30-bounded-ratio-terminal-sector",
  "kind": "internal",
  "status": "discharged",
  "discharged_by": [
    "PaperC.BoundedRatioTerminalSummation.intrinsicTerminalSectorStability",
    "PaperC.PropositionSixteenOne.proposition_sixteen_one_canonical",
    "PaperC.TheoremSixteenTwo.theorem_sixteen_two_canonical"
  ],
  "lean_name": "PaperC.PropositionSixteenOne.TerminalSectorStabilityStatement",
  "citation": {
    "authors": ["Brice Pouly"],
    "title": "Loi de Poisson critique dans un bloc dyadique — Débuts de longues plages constantes d’une fonction aléatoire complètement multiplicative de Rademacher étendue",
    "version": "7c, juillet 2026",
    "target_pdf_sha256": "23a5db3c8d024cab3fb8ca9f8f1443f40cf9502b1fb6682a331f5948f57a3336",
    "locator": "Lemme 17.30, pp. 63–64"
  },
  "source_statement": {
    "verbatim": "Lemme 17.30 (Fermeture terminale sur U). Avec T = (C_det(κ₀)NB)^{1/2}, la population terminale satisfait #T_K ≤ N^{3/4+o_{C,κ₀}(1)} et ∑_{(x,y)∈T_K}(2^{τ(x,y)}−1) ≤ N^{7/4+o_{C,κ₀}(1)}.",
    "source_url": "paper_C_complete_v07c.pdf#page=64",
    "verification": "manual_primary_source_check_required"
  },
  "manuscript_locator": {
    "result": "Lemma 17.30",
    "equation": "seventh residual sector",
    "pages": "63–64"
  },
  "formalization_relation": "discharged historical generic terminal-sector interface retained for compatibility with arbitrary terminal classifiers; for the canonical intrinsic classifier, Lean proves the complete first-start and partner summation under generalized Pell, the uniform N^(3/4+o(1)) cardinal bound, the N^(7/4+o(1)) = o(N^2) mass bound, and the exact transport through the proved source-scoped Lemma 9.10 arithmetic equivalence. Consequently the principal canonical Proposition 16.1 and Theorem 16.2 replace this coarse premise by generalized Pell alone. Evertse–Silverman is not used in Lemma 17.30, and there is no remaining Lemma 17.30-specific formalization debt"
}
AUDIT_BRIDGE -/
def TerminalSectorStabilityStatement
    (C : ℝ) (κ₀ A : ℕ)
    (terminal : TerminalPredicateFamily) : Prop :=
  PellInput.GeneralizedPellPolynomialBoxStatement →
  UniformLittleOInBoundedRatioWindow C κ₀
    (sectorResidualMass A terminal .terminal)

end

end PropositionSixteenOne
end PaperC
