import PaperC.Combinatorics.ResidualMasses

set_option maxHeartbeats 1800000

/-!
# The small-height large-product population

This file defines the finite population occurring in Proposition 7.4 of
Paper C.  Its members are separated ordered pairs in the dyadic block such
that

* the canonical residual prime product satisfies `N < P#`;
* a canonical reduced candidate `(a,b)` has been selected; and
* its height `q = max(a,b)` satisfies the manuscript's literal condition
  `q ≤ √(log B)`, where `B = L+1`.

The real inequality is retained verbatim rather than replacing it by a
rounded natural logarithm.  We then delete the pairs with `τ=0`, split the
active population exactly into `σ=0` and `σ>0`, and define its linear and
quadratic residual masses using the generic infrastructure from
`ResidualMasses`.

Finally, every active `σ=0` pair is placed in the relational-host population.
This is the cardinality input used in the Cauchy--Schwarz step of Proposition
7.4.
-/

namespace PaperC
namespace SmallHeightLargeProductPairs

open Affine
open Affine.CanonicalRationalCode
open CanonicalResidualComponents
open RationalMassFinite
open ResidualMasses

noncomputable section

/--
A canonical reduced candidate exists and has manuscript height
`q = max(a,b) ≤ √(log (L+1))`.

The existential witness retains both the selected candidate and the proof
that it is the canonical choice.  This avoids treating the default value
`canonicalPairHeight = 0` as if it represented an actual channel.
-/
def HasSmallCanonicalHeight
    (A L x y : ℕ) : Prop :=
  ∃ c : ReducedCandidate x y (L + 1) ((L + 1) ^ A),
    canonicalReducedCandidate?
        x y (L + 1) ((L + 1) ^ A) = some c ∧
      ((Nat.max c.1.1 c.1.2 : ℕ) : ℝ) ≤
        Real.sqrt (Real.log ((L + 1 : ℕ) : ℝ))

/--
All separated pairs in the large-product, small-canonical-height sector of
Proposition 7.4.
-/
noncomputable def smallHeightLargeProductPairs
    (N A L : ℕ) (hN : 2 ≤ N) :
    Finset (SeparatedDyadicPair N L) := by
  classical
  exact Finset.univ.filter fun pair ↦
    CanonicalResidualPrimeProductExceeds
        (A := A) (L := L)
        (show 1 ≤ pair.1.1 by
          exact le_trans (by omega : 1 ≤ 2)
            (pair_coordinates_two_le hN pair).1)
        (show 1 ≤ pair.1.2 by
          exact le_trans (by omega : 1 ≤ 2)
            (pair_coordinates_two_le hN pair).2)
        N ∧
      HasSmallCanonicalHeight A L pair.1.1 pair.1.2

@[simp]
theorem mem_smallHeightLargeProductPairs
    {N A L : ℕ} {hN : 2 ≤ N}
    {pair : SeparatedDyadicPair N L} :
    pair ∈ smallHeightLargeProductPairs N A L hN ↔
      CanonicalResidualPrimeProductExceeds
          (A := A) (L := L)
          (show 1 ≤ pair.1.1 by
            exact le_trans (by omega : 1 ≤ 2)
              (pair_coordinates_two_le hN pair).1)
          (show 1 ≤ pair.1.2 by
            exact le_trans (by omega : 1 ≤ 2)
              (pair_coordinates_two_le hN pair).2)
          N ∧
        HasSmallCanonicalHeight A L pair.1.1 pair.1.2 := by
  simp [smallHeightLargeProductPairs]

/-- Every member exposes its selected small-height canonical candidate. -/
theorem exists_smallHeight_candidate_of_mem
    {N A L : ℕ} {hN : 2 ≤ N}
    {pair : SeparatedDyadicPair N L}
    (hpair : pair ∈ smallHeightLargeProductPairs N A L hN) :
    ∃ c :
        ReducedCandidate pair.1.1 pair.1.2
          (L + 1) ((L + 1) ^ A),
      canonicalReducedCandidate?
          pair.1.1 pair.1.2 (L + 1) ((L + 1) ^ A) =
        some c ∧
      ((Nat.max c.1.1 c.1.2 : ℕ) : ℝ) ≤
        Real.sqrt (Real.log ((L + 1 : ℕ) : ℝ)) :=
  (mem_smallHeightLargeProductPairs.mp hpair).2

/--
The active part of the sector.  Removing `τ=0` does not change either
residual mass.
-/
noncomputable def activeSmallHeightLargeProductPairs
    (N A L : ℕ) (hN : 2 ≤ N) :
    Finset (SeparatedDyadicPair N L) := by
  classical
  exact (smallHeightLargeProductPairs N A L hN).filter fun pair ↦
    0 < pairTau A hN pair

@[simp]
theorem mem_activeSmallHeightLargeProductPairs
    {N A L : ℕ} {hN : 2 ≤ N}
    {pair : SeparatedDyadicPair N L} :
    pair ∈ activeSmallHeightLargeProductPairs N A L hN ↔
      pair ∈ smallHeightLargeProductPairs N A L hN ∧
        0 < pairTau A hN pair := by
  simp [activeSmallHeightLargeProductPairs]

theorem activeSmallHeightLargeProductPairs_subset
    {N A L : ℕ} (hN : 2 ≤ N) :
    activeSmallHeightLargeProductPairs N A L hN ⊆
      smallHeightLargeProductPairs N A L hN :=
  Finset.filter_subset _ _

/-! ## The `σ=0` and `σ>0` branches -/

/-- Active pairs in the exceptional branch `σ=0`. -/
noncomputable def sigmaZeroSmallHeightLargeProductPairs
    (N A L : ℕ) (hN : 2 ≤ N) :
    Finset (SeparatedDyadicPair N L) := by
  classical
  exact
    (activeSmallHeightLargeProductPairs N A L hN).filter fun pair ↦
      pairSigma A pair = 0

/-- Active pairs carried by a positive systematic rational code. -/
noncomputable def positiveSigmaSmallHeightLargeProductPairs
    (N A L : ℕ) (hN : 2 ≤ N) :
    Finset (SeparatedDyadicPair N L) := by
  classical
  exact
    (activeSmallHeightLargeProductPairs N A L hN).filter fun pair ↦
      0 < pairSigma A pair

@[simp]
theorem mem_sigmaZeroSmallHeightLargeProductPairs
    {N A L : ℕ} {hN : 2 ≤ N}
    {pair : SeparatedDyadicPair N L} :
    pair ∈ sigmaZeroSmallHeightLargeProductPairs N A L hN ↔
      pair ∈ activeSmallHeightLargeProductPairs N A L hN ∧
        pairSigma A pair = 0 := by
  simp [sigmaZeroSmallHeightLargeProductPairs]

@[simp]
theorem mem_positiveSigmaSmallHeightLargeProductPairs
    {N A L : ℕ} {hN : 2 ≤ N}
    {pair : SeparatedDyadicPair N L} :
    pair ∈ positiveSigmaSmallHeightLargeProductPairs N A L hN ↔
      pair ∈ activeSmallHeightLargeProductPairs N A L hN ∧
        0 < pairSigma A pair := by
  simp [positiveSigmaSmallHeightLargeProductPairs]

theorem disjoint_sigmaZero_positiveSigmaSmallHeightLargeProductPairs
    {N A L : ℕ} (hN : 2 ≤ N) :
    Disjoint
      (sigmaZeroSmallHeightLargeProductPairs N A L hN)
      (positiveSigmaSmallHeightLargeProductPairs N A L hN) := by
  rw [Finset.disjoint_left]
  intro pair hzero hpositive
  rw [mem_sigmaZeroSmallHeightLargeProductPairs] at hzero
  rw [mem_positiveSigmaSmallHeightLargeProductPairs] at hpositive
  omega

theorem sigmaZero_union_positiveSigma_eq_activeSmallHeightLargeProductPairs
    {N A L : ℕ} (hN : 2 ≤ N) :
    sigmaZeroSmallHeightLargeProductPairs N A L hN ∪
        positiveSigmaSmallHeightLargeProductPairs N A L hN =
      activeSmallHeightLargeProductPairs N A L hN := by
  ext pair
  simp only [Finset.mem_union,
    mem_sigmaZeroSmallHeightLargeProductPairs,
    mem_positiveSigmaSmallHeightLargeProductPairs]
  constructor
  · rintro (hzero | hpositive)
    · exact hzero.1
    · exact hpositive.1
  · intro hactive
    by_cases hzero : pairSigma A pair = 0
    · exact Or.inl ⟨hactive, hzero⟩
    · exact Or.inr ⟨hactive, Nat.pos_of_ne_zero hzero⟩

/-! ## Literal residual masses of the sector -/

/-- Quadratic residual mass on the full Proposition 7.4 population. -/
noncomputable def smallHeightLargeProductQuadraticResidualMass
    (N A L : ℕ) (hN : 2 ≤ N) : ℕ :=
  quadraticResidualMass A hN
    (smallHeightLargeProductPairs N A L hN)

/-- Linear residual mass on the full Proposition 7.4 population. -/
noncomputable def smallHeightLargeProductLinearResidualMass
    (N A L : ℕ) (hN : 2 ≤ N) : ℕ :=
  linearResidualMass A hN
    (smallHeightLargeProductPairs N A L hN)

/-- Quadratic residual mass after deleting the zero-weight pairs. -/
noncomputable def activeSmallHeightLargeProductQuadraticResidualMass
    (N A L : ℕ) (hN : 2 ≤ N) : ℕ :=
  quadraticResidualMass A hN
    (activeSmallHeightLargeProductPairs N A L hN)

/-- Linear residual mass after deleting the zero-weight pairs. -/
noncomputable def activeSmallHeightLargeProductLinearResidualMass
    (N A L : ℕ) (hN : 2 ≤ N) : ℕ :=
  linearResidualMass A hN
    (activeSmallHeightLargeProductPairs N A L hN)

/-- Quadratic contribution of the `σ=0` branch. -/
noncomputable def sigmaZeroSmallHeightLargeProductQuadraticResidualMass
    (N A L : ℕ) (hN : 2 ≤ N) : ℕ :=
  quadraticResidualMass A hN
    (sigmaZeroSmallHeightLargeProductPairs N A L hN)

/-- Linear contribution of the `σ=0` branch. -/
noncomputable def sigmaZeroSmallHeightLargeProductLinearResidualMass
    (N A L : ℕ) (hN : 2 ≤ N) : ℕ :=
  linearResidualMass A hN
    (sigmaZeroSmallHeightLargeProductPairs N A L hN)

/-- Quadratic contribution of the `σ>0` branch. -/
noncomputable def positiveSigmaSmallHeightLargeProductQuadraticResidualMass
    (N A L : ℕ) (hN : 2 ≤ N) : ℕ :=
  quadraticResidualMass A hN
    (positiveSigmaSmallHeightLargeProductPairs N A L hN)

/-- Linear contribution of the `σ>0` branch. -/
noncomputable def positiveSigmaSmallHeightLargeProductLinearResidualMass
    (N A L : ℕ) (hN : 2 ≤ N) : ℕ :=
  linearResidualMass A hN
    (positiveSigmaSmallHeightLargeProductPairs N A L hN)

/-- Deleting `τ=0` does not change the quadratic residual mass. -/
theorem smallHeightLargeProductQuadraticResidualMass_eq_active
    {N A L : ℕ} (hN : 2 ≤ N) :
    smallHeightLargeProductQuadraticResidualMass N A L hN =
      activeSmallHeightLargeProductQuadraticResidualMass N A L hN := by
  classical
  unfold smallHeightLargeProductQuadraticResidualMass
  unfold activeSmallHeightLargeProductQuadraticResidualMass
  unfold quadraticResidualMass
  symm
  apply Finset.sum_subset
    (activeSmallHeightLargeProductPairs_subset (A := A) hN)
  intro pair hpair hpairNotActive
  have htau : pairTau A hN pair = 0 := by
    have hnotPos : ¬ 0 < pairTau A hN pair := by
      intro hpos
      exact hpairNotActive
        (mem_activeSmallHeightLargeProductPairs.mpr
          ⟨hpair, hpos⟩)
    omega
  exact quadraticResidualWeight_eq_zero_of_pairTau_eq_zero htau

/-- Deleting `τ=0` does not change the linear residual mass. -/
theorem smallHeightLargeProductLinearResidualMass_eq_active
    {N A L : ℕ} (hN : 2 ≤ N) :
    smallHeightLargeProductLinearResidualMass N A L hN =
      activeSmallHeightLargeProductLinearResidualMass N A L hN := by
  classical
  unfold smallHeightLargeProductLinearResidualMass
  unfold activeSmallHeightLargeProductLinearResidualMass
  unfold linearResidualMass
  symm
  apply Finset.sum_subset
    (activeSmallHeightLargeProductPairs_subset (A := A) hN)
  intro pair hpair hpairNotActive
  have htau : pairTau A hN pair = 0 := by
    have hnotPos : ¬ 0 < pairTau A hN pair := by
      intro hpos
      exact hpairNotActive
        (mem_activeSmallHeightLargeProductPairs.mpr
          ⟨hpair, hpos⟩)
    omega
  exact linearResidualWeight_eq_zero_of_pairTau_eq_zero htau

/-- Exact decomposition of the active quadratic mass. -/
theorem activeSmallHeightLargeProductQuadraticResidualMass_eq_branches
    {N A L : ℕ} (hN : 2 ≤ N) :
    activeSmallHeightLargeProductQuadraticResidualMass N A L hN =
      sigmaZeroSmallHeightLargeProductQuadraticResidualMass N A L hN +
        positiveSigmaSmallHeightLargeProductQuadraticResidualMass
          N A L hN := by
  rw [activeSmallHeightLargeProductQuadraticResidualMass]
  rw [← sigmaZero_union_positiveSigma_eq_activeSmallHeightLargeProductPairs
    (A := A) hN]
  unfold sigmaZeroSmallHeightLargeProductQuadraticResidualMass
  unfold positiveSigmaSmallHeightLargeProductQuadraticResidualMass
  unfold quadraticResidualMass
  exact Finset.sum_union
    (disjoint_sigmaZero_positiveSigmaSmallHeightLargeProductPairs
      (A := A) hN)

/-- Exact decomposition of the active linear mass. -/
theorem activeSmallHeightLargeProductLinearResidualMass_eq_branches
    {N A L : ℕ} (hN : 2 ≤ N) :
    activeSmallHeightLargeProductLinearResidualMass N A L hN =
      sigmaZeroSmallHeightLargeProductLinearResidualMass N A L hN +
        positiveSigmaSmallHeightLargeProductLinearResidualMass
          N A L hN := by
  rw [activeSmallHeightLargeProductLinearResidualMass]
  rw [← sigmaZero_union_positiveSigma_eq_activeSmallHeightLargeProductPairs
    (A := A) hN]
  unfold sigmaZeroSmallHeightLargeProductLinearResidualMass
  unfold positiveSigmaSmallHeightLargeProductLinearResidualMass
  unfold linearResidualMass
  exact Finset.sum_union
    (disjoint_sigmaZero_positiveSigmaSmallHeightLargeProductPairs
      (A := A) hN)

/-- Exact decomposition of the full quadratic mass. -/
theorem smallHeightLargeProductQuadraticResidualMass_eq_branches
    {N A L : ℕ} (hN : 2 ≤ N) :
    smallHeightLargeProductQuadraticResidualMass N A L hN =
      sigmaZeroSmallHeightLargeProductQuadraticResidualMass N A L hN +
        positiveSigmaSmallHeightLargeProductQuadraticResidualMass
          N A L hN := by
  rw [smallHeightLargeProductQuadraticResidualMass_eq_active hN]
  exact
    activeSmallHeightLargeProductQuadraticResidualMass_eq_branches
      (A := A) hN

/-- Exact decomposition of the full linear mass. -/
theorem smallHeightLargeProductLinearResidualMass_eq_branches
    {N A L : ℕ} (hN : 2 ≤ N) :
    smallHeightLargeProductLinearResidualMass N A L hN =
      sigmaZeroSmallHeightLargeProductLinearResidualMass N A L hN +
        positiveSigmaSmallHeightLargeProductLinearResidualMass
          N A L hN := by
  rw [smallHeightLargeProductLinearResidualMass_eq_active hN]
  exact
    activeSmallHeightLargeProductLinearResidualMass_eq_branches
      (A := A) hN

/-! ## Relational-host inclusion of the active `σ=0` branch -/

/-- The `σ=0` branch viewed as ordinary ordered pairs. -/
noncomputable def sigmaZeroSmallHeightLargeProductPairValues
    (N A L : ℕ) (hN : 2 ≤ N) : Finset (ℕ × ℕ) :=
  (sigmaZeroSmallHeightLargeProductPairs N A L hN).image Subtype.val

theorem card_sigmaZeroSmallHeightLargeProductPairValues
    (N A L : ℕ) (hN : 2 ≤ N) :
    (sigmaZeroSmallHeightLargeProductPairValues N A L hN).card =
      (sigmaZeroSmallHeightLargeProductPairs N A L hN).card := by
  unfold sigmaZeroSmallHeightLargeProductPairValues
  exact Finset.card_image_of_injective
    (sigmaZeroSmallHeightLargeProductPairs N A L hN)
    Subtype.val_injective

/-- Every active `σ=0` pair has positive relation rank. -/
theorem pair_mem_relationalHosts_of_mem_sigmaZero
    {N A L : ℕ} {hN : 2 ≤ N}
    {pair : SeparatedDyadicPair N L}
    (hpair :
      pair ∈ sigmaZeroSmallHeightLargeProductPairs N A L hN) :
    pair.1 ∈ RelationalHosts.relationalHosts N L := by
  have hbranch :=
    mem_sigmaZeroSmallHeightLargeProductPairs.mp hpair
  have hactive :=
    mem_activeSmallHeightLargeProductPairs.mp hbranch.1
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
            (dyadicCutoff N L) pair.1.1 pair.1.2 L) :=
      hrho.symm

/-- Finset-level inclusion in the relational-host population. -/
theorem sigmaZeroSmallHeightLargeProductPairValues_subset_relationalHosts
    {N A L : ℕ} (hN : 2 ≤ N) :
    sigmaZeroSmallHeightLargeProductPairValues N A L hN ⊆
      RelationalHosts.relationalHosts N L := by
  intro pair hpair
  rw [sigmaZeroSmallHeightLargeProductPairValues,
    Finset.mem_image] at hpair
  obtain ⟨z, hz, rfl⟩ := hpair
  exact pair_mem_relationalHosts_of_mem_sigmaZero hz

/-- Cardinality bound inherited from Lemma 4.2. -/
theorem card_sigmaZeroSmallHeightLargeProductPairs_le_relationalHosts
    {N A L : ℕ} (hN : 2 ≤ N) :
    (sigmaZeroSmallHeightLargeProductPairs N A L hN).card ≤
      (RelationalHosts.relationalHosts N L).card := by
  rw [← card_sigmaZeroSmallHeightLargeProductPairValues N A L hN]
  exact Finset.card_le_card
    (sigmaZeroSmallHeightLargeProductPairValues_subset_relationalHosts
      (A := A) hN)

end

end SmallHeightLargeProductPairs
end PaperC
