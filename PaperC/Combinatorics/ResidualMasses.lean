import PaperC.Arithmetic.RationalMassFinite
import PaperC.Combinatorics.CanonicalResidualPrimeProduct
import PaperC.Combinatorics.RelationalHosts
import PaperC.Analysis.RelationalInterpolation

/-!
# Finite residual masses and the small-product population

Section 6 of Paper C introduces, for a population of separated pairs,

`Q_res = ∑ 4^σ (4^τ - 1)` and
`R_res = ∑ 2^σ (2^τ - 1)`.

This file makes those two masses literal finite sums.  It also defines the
active part of the branch `P# ≤ N`; pairs with `τ=0` may be discarded because
both residual weights vanish.

The pointwise inequality

`[2^σ (2^τ - 1)]² ≤ 4^σ (4^τ - 1)`

is proved over `ℕ`, then combined with finite Cauchy--Schwarz.  Finally, the
active small-product population is injected into the already formalized
relational-host population.  These are the exact structural ingredients of
equation (6.6) used after Proposition 7.3.
-/

namespace PaperC
namespace ResidualMasses

open scoped BigOperators
open Affine
open Affine.CanonicalRationalCode
open CanonicalResidualComponents
open RationalMassFinite

noncomputable section

/-- A separated ordered pair, carrying its membership proof in the dyadic block. -/
abbrev SeparatedDyadicPair (N L : ℕ) :=
  {pair : ℕ × ℕ // pair ∈ separatedDyadicPairs N L}

/-- The systematic exponent `σ` attached to a separated pair. -/
noncomputable def pairSigma
    {N L : ℕ} (A : ℕ) (pair : SeparatedDyadicPair N L) : ℕ :=
  canonicalPairSigma A L pair.1.1 pair.1.2

/-- Every coordinate of a separated dyadic pair is at least two when `N ≥ 2`. -/
theorem pair_coordinates_two_le
    {N L : ℕ} (hN : 2 ≤ N) (pair : SeparatedDyadicPair N L) :
    2 ≤ pair.1.1 ∧ 2 ≤ pair.1.2 := by
  have hpair := mem_separatedDyadicPairs.mp pair.2
  exact ⟨
    two_le_of_mem_dyadicBlock hN hpair.1,
    two_le_of_mem_dyadicBlock hN hpair.2.1⟩

/-- The residual exponent `τ = ρ-σ` attached to a separated pair. -/
noncomputable def pairTau
    {N L : ℕ} (A : ℕ) (hN : 2 ≤ N)
    (pair : SeparatedDyadicPair N L) : ℕ :=
  residualTau (dyadicCutoff N L) A pair.1.1 pair.1.2 L
    (pair_coordinates_two_le hN pair).1
    (pair_coordinates_two_le hN pair).2

/-- The full relation exponent `ρ` attached to a separated pair. -/
noncomputable def pairRho
    {N L : ℕ} (pair : SeparatedDyadicPair N L) : ℕ :=
  relationRho
    (twoStartSystem (dyadicCutoff N L) pair.1.1 pair.1.2 L)

/-- Literal identity `ρ=σ+τ` for a separated dyadic pair. -/
theorem pairRho_eq_pairSigma_add_pairTau
    {N A L : ℕ} (hN : 2 ≤ N)
    (pair : SeparatedDyadicPair N L) :
    pairRho pair = pairSigma A pair + pairTau A hN pair := by
  unfold pairRho pairSigma pairTau
  rw [canonicalPairSigma_eq_rationalSigma]
  exact
    relationRho_eq_rationalSigma_add_residualTau
      (dyadicCutoff N L) A pair.1.1 pair.1.2 L
      (pair_coordinates_two_le hN pair).1
      (pair_coordinates_two_le hN pair).2

/--
Canonical form of (6.3) for a separated pair in the dyadic block:
`τ ≤ D# + c#`.
-/
theorem pairTau_le_canonicalCorrected_add_residual
    {N A L : ℕ} (hN : 2 ≤ N)
    (pair : SeparatedDyadicPair N L) :
    pairTau A hN pair ≤
      ResidualComponentCounts.canonicalCorrectedDefectCount
          A pair.1.1 pair.1.2 L +
        ResidualComponentCounts.canonicalResidualComponentCount
          A pair.1.1 pair.1.2 L := by
  rcases pair with ⟨⟨x, y⟩, hpair⟩
  have hsep := mem_separatedDyadicPairs.mp hpair
  unfold pairTau
  apply
    ResidualComponentCounts.residualTau_le_canonicalCorrected_add_residual
      (two_le_of_mem_dyadicBlock hN hsep.1)
      (two_le_of_mem_dyadicBlock hN hsep.2.1)
  · have hx := Finset.mem_Ico.mp
      (by simpa [dyadicBlock] using hsep.1)
    unfold dyadicCutoff
    omega
  · have hy := Finset.mem_Ico.mp
      (by simpa [dyadicBlock] using hsep.2.1)
    unfold dyadicCutoff
    omega

/-- The linear residual weight `2^σ(2^τ-1)`. -/
noncomputable def linearResidualWeight
    {N L : ℕ} (A : ℕ) (hN : 2 ≤ N)
    (pair : SeparatedDyadicPair N L) : ℕ :=
  2 ^ pairSigma A pair * (2 ^ pairTau A hN pair - 1)

/-- The quadratic residual weight `4^σ(4^τ-1)`. -/
noncomputable def quadraticResidualWeight
    {N L : ℕ} (A : ℕ) (hN : 2 ≤ N)
    (pair : SeparatedDyadicPair N L) : ℕ :=
  4 ^ pairSigma A pair * (4 ^ pairTau A hN pair - 1)

@[simp]
theorem linearResidualWeight_eq_zero_of_pairTau_eq_zero
    {N A L : ℕ} {hN : 2 ≤ N}
    {pair : SeparatedDyadicPair N L}
    (htau : pairTau A hN pair = 0) :
    linearResidualWeight A hN pair = 0 := by
  simp [linearResidualWeight, htau]

@[simp]
theorem quadraticResidualWeight_eq_zero_of_pairTau_eq_zero
    {N A L : ℕ} {hN : 2 ≤ N}
    {pair : SeparatedDyadicPair N L}
    (htau : pairTau A hN pair = 0) :
    quadraticResidualWeight A hN pair = 0 := by
  simp [quadraticResidualWeight, htau]

/-- Elementary one-variable inequality behind the residual interpolation. -/
private theorem two_pow_sub_one_sq_le_four_pow_sub_one (t : ℕ) :
    (2 ^ t - 1) ^ 2 ≤ 4 ^ t - 1 := by
  let u := 2 ^ t
  have hu : 1 ≤ u := by
    dsimp [u]
    exact Nat.one_le_two_pow
  have hsub : u - 1 + 1 = u := Nat.sub_add_cancel hu
  have hfour : 4 ^ t = u ^ 2 := by
    dsimp [u]
    rw [show 4 = 2 * 2 by norm_num, mul_pow]
    ring
  rw [hfour]
  apply Nat.le_sub_of_add_le
  nlinarith

/--
The square of the linear residual weight is bounded pointwise by the
quadratic residual weight.
-/
theorem linearResidualWeight_sq_le_quadraticResidualWeight
    {N A L : ℕ} (hN : 2 ≤ N)
    (pair : SeparatedDyadicPair N L) :
    (linearResidualWeight A hN pair) ^ 2 ≤
      quadraticResidualWeight A hN pair := by
  let σ := pairSigma A pair
  let τ := pairTau A hN pair
  have htau :=
    two_pow_sub_one_sq_le_four_pow_sub_one τ
  have hsigma : (2 ^ σ) ^ 2 = 4 ^ σ := by
    rw [show 4 = 2 * 2 by norm_num, mul_pow]
    ring
  unfold linearResidualWeight quadraticResidualWeight
  change (2 ^ σ * (2 ^ τ - 1)) ^ 2 ≤
    4 ^ σ * (4 ^ τ - 1)
  rw [mul_pow, hsigma]
  exact Nat.mul_le_mul_left (4 ^ σ) htau

/--
Pointwise extraction of the corrected-defect and residual-certificate
factors:

`4^σ(4^τ-1) ≤ 4^σ · 4^D# · 4^c#`.
-/
theorem quadraticResidualWeight_le_systematic_mul_corrected_mul_certificate
    {N A L : ℕ} (hN : 2 ≤ N)
    (pair : SeparatedDyadicPair N L) :
    quadraticResidualWeight A hN pair ≤
      4 ^ pairSigma A pair *
        4 ^ ResidualComponentCounts.canonicalCorrectedDefectCount
            A pair.1.1 pair.1.2 L *
          4 ^ ResidualComponentCounts.canonicalResidualComponentCount
            A pair.1.1 pair.1.2 L := by
  have htau :=
    pairTau_le_canonicalCorrected_add_residual
      (A := A) hN pair
  unfold quadraticResidualWeight
  calc
    4 ^ pairSigma A pair *
          (4 ^ pairTau A hN pair - 1) ≤
        4 ^ pairSigma A pair *
          4 ^ pairTau A hN pair :=
      Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    _ ≤
        4 ^ pairSigma A pair *
          4 ^
            (ResidualComponentCounts.canonicalCorrectedDefectCount
                A pair.1.1 pair.1.2 L +
              ResidualComponentCounts.canonicalResidualComponentCount
                A pair.1.1 pair.1.2 L) :=
      Nat.mul_le_mul_left _
        (Nat.pow_le_pow_right (by norm_num) htau)
    _ =
        4 ^ pairSigma A pair *
          4 ^ ResidualComponentCounts.canonicalCorrectedDefectCount
              A pair.1.1 pair.1.2 L *
            4 ^ ResidualComponentCounts.canonicalResidualComponentCount
              A pair.1.1 pair.1.2 L := by
      rw [pow_add]
      ring

/-- The preceding weight extraction specialized to the branch `σ=0`. -/
theorem quadraticResidualWeight_le_corrected_mul_certificate_of_sigma_eq_zero
    {N A L : ℕ} (hN : 2 ≤ N)
    (pair : SeparatedDyadicPair N L)
    (hsigma : pairSigma A pair = 0) :
    quadraticResidualWeight A hN pair ≤
      4 ^ ResidualComponentCounts.canonicalCorrectedDefectCount
          A pair.1.1 pair.1.2 L *
        4 ^ ResidualComponentCounts.canonicalResidualComponentCount
          A pair.1.1 pair.1.2 L := by
  simpa [hsigma] using
    quadraticResidualWeight_le_systematic_mul_corrected_mul_certificate
      (A := A) hN pair

/-- Linear residual mass of an arbitrary finite population. -/
noncomputable def linearResidualMass
    {N L : ℕ} (A : ℕ) (hN : 2 ≤ N)
    (population : Finset (SeparatedDyadicPair N L)) : ℕ :=
  ∑ pair ∈ population, linearResidualWeight A hN pair

/-- Quadratic residual mass of an arbitrary finite population. -/
noncomputable def quadraticResidualMass
    {N L : ℕ} (A : ℕ) (hN : 2 ≤ N)
    (population : Finset (SeparatedDyadicPair N L)) : ℕ :=
  ∑ pair ∈ population, quadraticResidualWeight A hN pair

/-- Sum of squared linear weights is bounded by the quadratic residual mass. -/
theorem sum_linearResidualWeight_sq_le_quadraticResidualMass
    {N A L : ℕ} (hN : 2 ≤ N)
    (population : Finset (SeparatedDyadicPair N L)) :
    (∑ pair ∈ population,
        (linearResidualWeight A hN pair) ^ 2) ≤
      quadraticResidualMass A hN population := by
  unfold quadraticResidualMass
  exact Finset.sum_le_sum fun pair _hpair ↦
    linearResidualWeight_sq_le_quadraticResidualWeight hN pair

/--
Finite form of (6.6), before replacing the population cardinality by the
relational-host bound.
-/
theorem linearResidualMass_cast_le_sqrt_card_mul_sqrt_quadratic
    {N A L : ℕ} (hN : 2 ≤ N)
    (population : Finset (SeparatedDyadicPair N L)) :
    (linearResidualMass A hN population : ℝ) ≤
      Real.sqrt (population.card : ℝ) *
        Real.sqrt (quadraticResidualMass A hN population : ℝ) := by
  have hcs :=
    RelationalInterpolation.sum_le_sqrt_card_mul_sqrt_sum_sq
      population
      (fun pair : SeparatedDyadicPair N L ↦
        (linearResidualWeight A hN pair : ℝ))
  have hsq :
      (∑ pair ∈ population,
          (linearResidualWeight A hN pair : ℝ) ^ 2) ≤
        (quadraticResidualMass A hN population : ℝ) := by
    exact_mod_cast
      sum_linearResidualWeight_sq_le_quadraticResidualMass
        hN population
  calc
    (linearResidualMass A hN population : ℝ) =
        ∑ pair ∈ population,
          (linearResidualWeight A hN pair : ℝ) := by
      simp [linearResidualMass]
    _ ≤ Real.sqrt (population.card : ℝ) *
          Real.sqrt
            (∑ pair ∈ population,
              (linearResidualWeight A hN pair : ℝ) ^ 2) :=
      hcs
    _ ≤ Real.sqrt (population.card : ℝ) *
          Real.sqrt (quadraticResidualMass A hN population : ℝ) :=
      mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt hsq) (Real.sqrt_nonneg _)

/-! ## The branch `P# ≤ N` -/

/-- All separated pairs in the small canonical-prime-product branch. -/
noncomputable def smallProductPairs
    (N A L : ℕ) (hN : 2 ≤ N) :
    Finset (SeparatedDyadicPair N L) := by
  classical
  exact Finset.univ.filter fun pair ↦
    CanonicalResidualPrimeProductAtMost
      (A := A) (L := L)
      (show 1 ≤ pair.1.1 by
        exact le_trans (by omega : 1 ≤ 2)
          (pair_coordinates_two_le hN pair).1)
      (show 1 ≤ pair.1.2 by
        exact le_trans (by omega : 1 ≤ 2)
          (pair_coordinates_two_le hN pair).2)
      N

@[simp]
theorem mem_smallProductPairs
    {N A L : ℕ} {hN : 2 ≤ N}
    {pair : SeparatedDyadicPair N L} :
    pair ∈ smallProductPairs N A L hN ↔
      CanonicalResidualPrimeProductAtMost
        (A := A) (L := L)
        (show 1 ≤ pair.1.1 by
          exact le_trans (by omega : 1 ≤ 2)
            (pair_coordinates_two_le hN pair).1)
        (show 1 ≤ pair.1.2 by
          exact le_trans (by omega : 1 ≤ 2)
            (pair_coordinates_two_le hN pair).2)
        N := by
  simp [smallProductPairs]

/--
The active small-product population.  Requiring `τ>0` removes precisely the
pairs whose residual weights are both zero.
-/
noncomputable def activeSmallProductPairs
    (N A L : ℕ) (hN : 2 ≤ N) :
    Finset (SeparatedDyadicPair N L) := by
  classical
  exact (smallProductPairs N A L hN).filter fun pair ↦
    0 < pairTau A hN pair

@[simp]
theorem mem_activeSmallProductPairs
    {N A L : ℕ} {hN : 2 ≤ N}
    {pair : SeparatedDyadicPair N L} :
    pair ∈ activeSmallProductPairs N A L hN ↔
      CanonicalResidualPrimeProductAtMost
          (A := A) (L := L)
          (show 1 ≤ pair.1.1 by
            exact le_trans (by omega : 1 ≤ 2)
              (pair_coordinates_two_le hN pair).1)
          (show 1 ≤ pair.1.2 by
            exact le_trans (by omega : 1 ≤ 2)
              (pair_coordinates_two_le hN pair).2)
          N ∧
        0 < pairTau A hN pair := by
  simp [activeSmallProductPairs]

theorem activeSmallProductPairs_subset_smallProductPairs
    {N A L : ℕ} (hN : 2 ≤ N) :
    activeSmallProductPairs N A L hN ⊆
      smallProductPairs N A L hN := by
  exact Finset.filter_subset _ _

/-! ### The two populations in Proposition 7.3 -/

/-- Active pairs in the exceptional branch `σ=0`. -/
noncomputable def sigmaZeroSmallProductPairs
    (N A L : ℕ) (hN : 2 ≤ N) :
    Finset (SeparatedDyadicPair N L) := by
  classical
  exact (activeSmallProductPairs N A L hN).filter fun pair ↦
    pairSigma A pair = 0

/-- Active pairs carried by a nontrivial rational channel, i.e. `σ>0`. -/
noncomputable def positiveSigmaSmallProductPairs
    (N A L : ℕ) (hN : 2 ≤ N) :
    Finset (SeparatedDyadicPair N L) := by
  classical
  exact (activeSmallProductPairs N A L hN).filter fun pair ↦
    0 < pairSigma A pair

@[simp]
theorem mem_sigmaZeroSmallProductPairs
    {N A L : ℕ} {hN : 2 ≤ N}
    {pair : SeparatedDyadicPair N L} :
    pair ∈ sigmaZeroSmallProductPairs N A L hN ↔
      pair ∈ activeSmallProductPairs N A L hN ∧
        pairSigma A pair = 0 := by
  simp [sigmaZeroSmallProductPairs]

@[simp]
theorem mem_positiveSigmaSmallProductPairs
    {N A L : ℕ} {hN : 2 ≤ N}
    {pair : SeparatedDyadicPair N L} :
    pair ∈ positiveSigmaSmallProductPairs N A L hN ↔
      pair ∈ activeSmallProductPairs N A L hN ∧
        0 < pairSigma A pair := by
  simp [positiveSigmaSmallProductPairs]

theorem disjoint_sigmaZero_positiveSigmaSmallProductPairs
    {N A L : ℕ} (hN : 2 ≤ N) :
    Disjoint
      (sigmaZeroSmallProductPairs N A L hN)
      (positiveSigmaSmallProductPairs N A L hN) := by
  rw [Finset.disjoint_left]
  intro pair hzero hpositive
  rw [mem_sigmaZeroSmallProductPairs] at hzero
  rw [mem_positiveSigmaSmallProductPairs] at hpositive
  omega

theorem sigmaZero_union_positiveSigma_eq_activeSmallProductPairs
    {N A L : ℕ} (hN : 2 ≤ N) :
    sigmaZeroSmallProductPairs N A L hN ∪
        positiveSigmaSmallProductPairs N A L hN =
      activeSmallProductPairs N A L hN := by
  ext pair
  simp only [Finset.mem_union, mem_sigmaZeroSmallProductPairs,
    mem_positiveSigmaSmallProductPairs]
  constructor
  · rintro (hzero | hpositive)
    · exact hzero.1
    · exact hpositive.1
  · intro hactive
    by_cases hzero : pairSigma A pair = 0
    · exact Or.inl ⟨hactive, hzero⟩
    · exact Or.inr ⟨hactive, Nat.pos_of_ne_zero hzero⟩

/-- The active branch viewed as an ordinary finset of ordered pairs. -/
noncomputable def activeSmallProductPairValues
    (N A L : ℕ) (hN : 2 ≤ N) : Finset (ℕ × ℕ) :=
  (activeSmallProductPairs N A L hN).image Subtype.val

theorem card_activeSmallProductPairValues
    (N A L : ℕ) (hN : 2 ≤ N) :
    (activeSmallProductPairValues N A L hN).card =
      (activeSmallProductPairs N A L hN).card := by
  unfold activeSmallProductPairValues
  exact Finset.card_image_of_injective
    (activeSmallProductPairs N A L hN) Subtype.val_injective

/-- Every active small-product pair is a relational host. -/
theorem activeSmallProductPairValues_subset_relationalHosts
    {N A L : ℕ} (hN : 2 ≤ N) :
    activeSmallProductPairValues N A L hN ⊆
      RelationalHosts.relationalHosts N L := by
  intro pair hpair
  rw [activeSmallProductPairValues, Finset.mem_image] at hpair
  obtain ⟨z, hz, rfl⟩ := hpair
  have hzActive := mem_activeSmallProductPairs.mp hz
  have hzSep := mem_separatedDyadicPairs.mp z.2
  rw [RelationalHosts.mem_relationalHosts]
  refine ⟨hzSep.1, hzSep.2.1, hzSep.2.2, ?_⟩
  have hrho :=
    pairRho_eq_pairSigma_add_pairTau
      (A := A) hN z
  unfold pairRho at hrho
  calc
    0 < pairSigma A z + pairTau A hN z := by omega
    _ = relationRho
        (twoStartSystem (dyadicCutoff N L) z.1.1 z.1.2 L) :=
      hrho.symm

/-- Host-cardinality bound for the active small-product population. -/
theorem card_activeSmallProductPairs_le_relationalHosts
    {N A L : ℕ} (hN : 2 ≤ N) :
    (activeSmallProductPairs N A L hN).card ≤
      (RelationalHosts.relationalHosts N L).card := by
  rw [← card_activeSmallProductPairValues N A L hN]
  exact Finset.card_le_card
    (activeSmallProductPairValues_subset_relationalHosts hN)

/-- Quadratic mass after deleting the zero-weight pairs with `τ=0`. -/
noncomputable def activeSmallProductQuadraticResidualMass
    (N A L : ℕ) (hN : 2 ≤ N) : ℕ :=
  quadraticResidualMass A hN
    (activeSmallProductPairs N A L hN)

/-- Linear mass after deleting the zero-weight pairs with `τ=0`. -/
noncomputable def activeSmallProductLinearResidualMass
    (N A L : ℕ) (hN : 2 ≤ N) : ℕ :=
  linearResidualMass A hN
    (activeSmallProductPairs N A L hN)

/-- Quadratic contribution of the exceptional `σ=0` population. -/
noncomputable def sigmaZeroQuadraticResidualMass
    (N A L : ℕ) (hN : 2 ≤ N) : ℕ :=
  quadraticResidualMass A hN
    (sigmaZeroSmallProductPairs N A L hN)

/-- Quadratic contribution of the nontrivial rational-channel population. -/
noncomputable def positiveSigmaQuadraticResidualMass
    (N A L : ℕ) (hN : 2 ≤ N) : ℕ :=
  quadraticResidualMass A hN
    (positiveSigmaSmallProductPairs N A L hN)

/-- Linear contribution of the exceptional `σ=0` population. -/
noncomputable def sigmaZeroLinearResidualMass
    (N A L : ℕ) (hN : 2 ≤ N) : ℕ :=
  linearResidualMass A hN
    (sigmaZeroSmallProductPairs N A L hN)

/-- Linear contribution of the nontrivial rational-channel population. -/
noncomputable def positiveSigmaLinearResidualMass
    (N A L : ℕ) (hN : 2 ≤ N) : ℕ :=
  linearResidualMass A hN
    (positiveSigmaSmallProductPairs N A L hN)

/-- Exact finite decomposition of the active quadratic residual mass. -/
theorem activeSmallProductQuadraticResidualMass_eq_sigmaZero_add_positiveSigma
    {N A L : ℕ} (hN : 2 ≤ N) :
    activeSmallProductQuadraticResidualMass N A L hN =
      sigmaZeroQuadraticResidualMass N A L hN +
        positiveSigmaQuadraticResidualMass N A L hN := by
  rw [activeSmallProductQuadraticResidualMass]
  rw [← sigmaZero_union_positiveSigma_eq_activeSmallProductPairs
    (A := A) hN]
  unfold sigmaZeroQuadraticResidualMass
  unfold positiveSigmaQuadraticResidualMass
  unfold quadraticResidualMass
  exact Finset.sum_union
    (disjoint_sigmaZero_positiveSigmaSmallProductPairs
      (A := A) hN)

/-- Exact finite decomposition of the active linear residual mass. -/
theorem activeSmallProductLinearResidualMass_eq_sigmaZero_add_positiveSigma
    {N A L : ℕ} (hN : 2 ≤ N) :
    activeSmallProductLinearResidualMass N A L hN =
      sigmaZeroLinearResidualMass N A L hN +
        positiveSigmaLinearResidualMass N A L hN := by
  rw [activeSmallProductLinearResidualMass]
  rw [← sigmaZero_union_positiveSigma_eq_activeSmallProductPairs
    (A := A) hN]
  unfold sigmaZeroLinearResidualMass
  unfold positiveSigmaLinearResidualMass
  unfold linearResidualMass
  exact Finset.sum_union
    (disjoint_sigmaZero_positiveSigmaSmallProductPairs
      (A := A) hN)

/-- The paper's literal `Q_res` on all separated pairs with `P# ≤ N`. -/
noncomputable def smallProductQuadraticResidualMass
    (N A L : ℕ) (hN : 2 ≤ N) : ℕ :=
  quadraticResidualMass A hN
    (smallProductPairs N A L hN)

/-- The paper's literal `R_res` on all separated pairs with `P# ≤ N`. -/
noncomputable def smallProductLinearResidualMass
    (N A L : ℕ) (hN : 2 ≤ N) : ℕ :=
  linearResidualMass A hN
    (smallProductPairs N A L hN)

/-- Deleting the pairs with `τ=0` does not change `Q_res`. -/
theorem smallProductQuadraticResidualMass_eq_active
    {N A L : ℕ} (hN : 2 ≤ N) :
    smallProductQuadraticResidualMass N A L hN =
      activeSmallProductQuadraticResidualMass N A L hN := by
  classical
  unfold smallProductQuadraticResidualMass
  unfold activeSmallProductQuadraticResidualMass
  unfold quadraticResidualMass
  symm
  apply Finset.sum_subset
    (activeSmallProductPairs_subset_smallProductPairs
      (A := A) hN)
  intro pair hpairSmall hpairNotActive
  have htau : pairTau A hN pair = 0 := by
    have hnotPos : ¬ 0 < pairTau A hN pair := by
      intro hpos
      exact hpairNotActive
        (mem_activeSmallProductPairs.mpr
          ⟨mem_smallProductPairs.mp hpairSmall, hpos⟩)
    omega
  exact quadraticResidualWeight_eq_zero_of_pairTau_eq_zero htau

/-- Deleting the pairs with `τ=0` does not change `R_res`. -/
theorem smallProductLinearResidualMass_eq_active
    {N A L : ℕ} (hN : 2 ≤ N) :
    smallProductLinearResidualMass N A L hN =
      activeSmallProductLinearResidualMass N A L hN := by
  classical
  unfold smallProductLinearResidualMass
  unfold activeSmallProductLinearResidualMass
  unfold linearResidualMass
  symm
  apply Finset.sum_subset
    (activeSmallProductPairs_subset_smallProductPairs
      (A := A) hN)
  intro pair hpairSmall hpairNotActive
  have htau : pairTau A hN pair = 0 := by
    have hnotPos : ¬ 0 < pairTau A hN pair := by
      intro hpos
      exact hpairNotActive
        (mem_activeSmallProductPairs.mpr
          ⟨mem_smallProductPairs.mp hpairSmall, hpos⟩)
    omega
  exact linearResidualWeight_eq_zero_of_pairTau_eq_zero htau

/-- Proposition 7.3's exact split of the full quadratic mass. -/
theorem smallProductQuadraticResidualMass_eq_sigmaZero_add_positiveSigma
    {N A L : ℕ} (hN : 2 ≤ N) :
    smallProductQuadraticResidualMass N A L hN =
      sigmaZeroQuadraticResidualMass N A L hN +
        positiveSigmaQuadraticResidualMass N A L hN := by
  rw [smallProductQuadraticResidualMass_eq_active hN]
  exact
    activeSmallProductQuadraticResidualMass_eq_sigmaZero_add_positiveSigma
      (A := A) hN

/-- The analogous exact split of the full linear mass. -/
theorem smallProductLinearResidualMass_eq_sigmaZero_add_positiveSigma
    {N A L : ℕ} (hN : 2 ≤ N) :
    smallProductLinearResidualMass N A L hN =
      sigmaZeroLinearResidualMass N A L hN +
        positiveSigmaLinearResidualMass N A L hN := by
  rw [smallProductLinearResidualMass_eq_active hN]
  exact
    activeSmallProductLinearResidualMass_eq_sigmaZero_add_positiveSigma
      (A := A) hN

/--
Equation (6.6) on the small-product branch, with the total relational-host
cardinality exposed for the later asymptotic substitution.
-/
theorem smallProductLinearResidualMass_cast_le
    {N A L : ℕ} (hN : 2 ≤ N) :
    (smallProductLinearResidualMass N A L hN : ℝ) ≤
      Real.sqrt ((RelationalHosts.relationalHosts N L).card : ℝ) *
        Real.sqrt (smallProductQuadraticResidualMass N A L hN : ℝ) := by
  have hinterp :=
    linearResidualMass_cast_le_sqrt_card_mul_sqrt_quadratic
      (A := A) hN (activeSmallProductPairs N A L hN)
  have hcard :
      ((activeSmallProductPairs N A L hN).card : ℝ) ≤
        ((RelationalHosts.relationalHosts N L).card : ℝ) := by
    exact_mod_cast card_activeSmallProductPairs_le_relationalHosts
      (A := A) hN
  rw [smallProductLinearResidualMass_eq_active hN]
  rw [smallProductQuadraticResidualMass_eq_active hN]
  unfold activeSmallProductLinearResidualMass
  unfold activeSmallProductQuadraticResidualMass
  exact hinterp.trans
    (mul_le_mul_of_nonneg_right
      (Real.sqrt_le_sqrt hcard)
      (Real.sqrt_nonneg _))

end
end ResidualMasses
end PaperC
