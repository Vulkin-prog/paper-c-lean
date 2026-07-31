import PaperC.Asymptotics.PropositionSixteenOneCore

set_option maxHeartbeats 1800000

/-!
# Finite residual masses on bounded-ratio intervals

This module is the bounded-ratio counterpart of the generic part of
`PaperC.Combinatorics.ResidualMasses`.  It deliberately stops before any
relational-host construction: every interpolation theorem is stated for an
arbitrary finite population of separated pairs.

For a pair in `[N,M)²` it defines

* the linear residual weight `2^σ (2^τ - 1)`;
* the quadratic residual weight `4^σ (4^τ - 1)`;
* the corresponding masses on an arbitrary finite population.

Pairs with `τ = 0` have zero linear and quadratic weight.  Filtering them
out therefore changes neither mass.  The pointwise estimate

`[2^σ (2^τ - 1)]² ≤ 4^σ (4^τ - 1)`

then gives the finite Cauchy--Schwarz interpolation used throughout
Section 17.  The final part specializes these definitions to each literal
sector population from Proposition 16.1 and identifies its linear mass with
`PropositionSixteenOne.sectorResidualMassNat`.

No host-counting assertion or asymptotic hypothesis is introduced here.
-/

namespace PaperC
namespace BoundedRatioResidualMasses

open scoped BigOperators
open PropositionSixteenOne
open SectionElevenPartition

noncomputable section

/-! ## Pointwise weights -/

/--
The linear residual weight on a bounded-ratio pair.  This is a named alias
for the residual weight already used in Proposition 16.1.
-/
noncomputable def linearResidualWeight
    {N M L : ℕ} (A : ℕ) (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L) : ℕ :=
  residualWeight A hN pair

/-- The quadratic residual weight `4^σ(4^τ-1)`. -/
noncomputable def quadraticResidualWeight
    {N M L : ℕ} (A : ℕ) (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L) : ℕ :=
  4 ^ pairSigma A pair * (4 ^ pairTau A hN pair - 1)

@[simp]
theorem linearResidualWeight_eq_residualWeight
    {N M A L : ℕ} (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L) :
    linearResidualWeight A hN pair = residualWeight A hN pair :=
  rfl

@[simp]
theorem linearResidualWeight_eq_zero_of_pairTau_eq_zero
    {N M A L : ℕ} {hN : 2 ≤ N}
    {pair : SeparatedBoundedRatioPair N M L}
    (htau : pairTau A hN pair = 0) :
    linearResidualWeight A hN pair = 0 := by
  simp [linearResidualWeight, residualWeight, htau]

@[simp]
theorem quadraticResidualWeight_eq_zero_of_pairTau_eq_zero
    {N M A L : ℕ} {hN : 2 ≤ N}
    {pair : SeparatedBoundedRatioPair N M L}
    (htau : pairTau A hN pair = 0) :
    quadraticResidualWeight A hN pair = 0 := by
  simp [quadraticResidualWeight, htau]

/-- Elementary one-variable inequality behind residual interpolation. -/
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
    {N M A L : ℕ} (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L) :
    (linearResidualWeight A hN pair) ^ 2 ≤
      quadraticResidualWeight A hN pair := by
  let σ := pairSigma A pair
  let τ := pairTau A hN pair
  have htau :=
    two_pow_sub_one_sq_le_four_pow_sub_one τ
  have hsigma : (2 ^ σ) ^ 2 = 4 ^ σ := by
    rw [show 4 = 2 * 2 by norm_num, mul_pow]
    ring
  unfold linearResidualWeight residualWeight quadraticResidualWeight
  change (2 ^ σ * (2 ^ τ - 1)) ^ 2 ≤
    4 ^ σ * (4 ^ τ - 1)
  rw [mul_pow, hsigma]
  exact Nat.mul_le_mul_left (4 ^ σ) htau

/-! ## Arbitrary populations and their active parts -/

/-- Linear residual mass of an arbitrary finite bounded-ratio population. -/
noncomputable def linearResidualMass
    {N M L : ℕ} (A : ℕ) (hN : 2 ≤ N)
    (population : Finset (SeparatedBoundedRatioPair N M L)) : ℕ :=
  ∑ pair ∈ population, linearResidualWeight A hN pair

/-- Quadratic residual mass of an arbitrary finite bounded-ratio population. -/
noncomputable def quadraticResidualMass
    {N M L : ℕ} (A : ℕ) (hN : 2 ≤ N)
    (population : Finset (SeparatedBoundedRatioPair N M L)) : ℕ :=
  ∑ pair ∈ population, quadraticResidualWeight A hN pair

/--
The active part of a population.  It removes exactly the pairs with
vanishing residual exponent.
-/
noncomputable def activePopulation
    {N M L : ℕ} (A : ℕ) (hN : 2 ≤ N)
    (population : Finset (SeparatedBoundedRatioPair N M L)) :
    Finset (SeparatedBoundedRatioPair N M L) := by
  classical
  exact population.filter fun pair ↦ 0 < pairTau A hN pair

@[simp]
theorem mem_activePopulation
    {N M A L : ℕ} {hN : 2 ≤ N}
    {population : Finset (SeparatedBoundedRatioPair N M L)}
    {pair : SeparatedBoundedRatioPair N M L} :
    pair ∈ activePopulation A hN population ↔
      pair ∈ population ∧ 0 < pairTau A hN pair := by
  simp [activePopulation]

theorem activePopulation_subset
    {N M A L : ℕ} (hN : 2 ≤ N)
    (population : Finset (SeparatedBoundedRatioPair N M L)) :
    activePopulation A hN population ⊆ population :=
  Finset.filter_subset _ _

/-- Removing the inactive pairs does not change the linear mass. -/
theorem linearResidualMass_eq_activePopulation
    {N M A L : ℕ} (hN : 2 ≤ N)
    (population : Finset (SeparatedBoundedRatioPair N M L)) :
    linearResidualMass A hN population =
      linearResidualMass A hN (activePopulation A hN population) := by
  classical
  unfold linearResidualMass
  symm
  apply Finset.sum_subset (activePopulation_subset (A := A) hN population)
  intro pair hpair hnotActive
  have htau : pairTau A hN pair = 0 := by
    have hnotPos : ¬ 0 < pairTau A hN pair := by
      intro hpos
      exact hnotActive (mem_activePopulation.mpr ⟨hpair, hpos⟩)
    omega
  exact linearResidualWeight_eq_zero_of_pairTau_eq_zero htau

/-- Removing the inactive pairs does not change the quadratic mass. -/
theorem quadraticResidualMass_eq_activePopulation
    {N M A L : ℕ} (hN : 2 ≤ N)
    (population : Finset (SeparatedBoundedRatioPair N M L)) :
    quadraticResidualMass A hN population =
      quadraticResidualMass A hN (activePopulation A hN population) := by
  classical
  unfold quadraticResidualMass
  symm
  apply Finset.sum_subset (activePopulation_subset (A := A) hN population)
  intro pair hpair hnotActive
  have htau : pairTau A hN pair = 0 := by
    have hnotPos : ¬ 0 < pairTau A hN pair := by
      intro hpos
      exact hnotActive (mem_activePopulation.mpr ⟨hpair, hpos⟩)
    omega
  exact quadraticResidualWeight_eq_zero_of_pairTau_eq_zero htau

/-! ## Cardinality interfaces -/

/--
The underlying ordered pairs of a bundled population.  This is the natural
interface for a future relational-host population living in `ℕ × ℕ`.
-/
noncomputable def populationPairValues
    {N M L : ℕ}
    (population : Finset (SeparatedBoundedRatioPair N M L)) :
    Finset (ℕ × ℕ) :=
  population.image Subtype.val

theorem card_populationPairValues
    {N M L : ℕ}
    (population : Finset (SeparatedBoundedRatioPair N M L)) :
    (populationPairValues population).card = population.card := by
  unfold populationPairValues
  exact Finset.card_image_of_injective population Subtype.val_injective

/-- Every underlying value still belongs to the ambient separated population. -/
theorem populationPairValues_subset_separatedBoundedRatioPairs
    {N M L : ℕ}
    (population : Finset (SeparatedBoundedRatioPair N M L)) :
    populationPairValues population ⊆
      PropositionSixteenOne.separatedBoundedRatioPairs N M L := by
  intro pair hpair
  rw [populationPairValues, Finset.mem_image] at hpair
  obtain ⟨bundledPair, _hbundledPair, rfl⟩ := hpair
  exact bundledPair.2

/-- Any bundled population is no larger than the ambient separated set. -/
theorem card_population_le_separatedBoundedRatioPairs
    {N M L : ℕ}
    (population : Finset (SeparatedBoundedRatioPair N M L)) :
    population.card ≤
      (PropositionSixteenOne.separatedBoundedRatioPairs N M L).card := by
  rw [← card_populationPairValues population]
  exact Finset.card_le_card
    (populationPairValues_subset_separatedBoundedRatioPairs population)

/-- Coarse width-squared bound, independent of any host construction. -/
theorem card_population_le_width_sq
    {N M L : ℕ}
    (population : Finset (SeparatedBoundedRatioPair N M L)) :
    population.card ≤ (M - N) ^ 2 := by
  exact
    (card_population_le_separatedBoundedRatioPairs population).trans
      (by
        simpa [PropositionSixteenOne.separatedBoundedRatioPairs] using
          BoundedRatioGeometry.card_separatedBoundedRatioPairs_le N M L)

/-- Uniform coarse bound under `M ≤ κ₀N`. -/
theorem card_population_le_ratio_sq
    {N M L κ₀ : ℕ}
    (population : Finset (SeparatedBoundedRatioPair N M L))
    (hM : M ≤ κ₀ * N) :
    population.card ≤ (κ₀ * N) ^ 2 := by
  exact (card_population_le_width_sq population).trans
    (Nat.pow_le_pow_left ((Nat.sub_le M N).trans hM) 2)

/-! ## Finite Cauchy--Schwarz interpolation -/

/-- Sum of squared linear weights is bounded by the quadratic mass. -/
theorem sum_linearResidualWeight_sq_le_quadraticResidualMass
    {N M A L : ℕ} (hN : 2 ≤ N)
    (population : Finset (SeparatedBoundedRatioPair N M L)) :
    (∑ pair ∈ population,
        (linearResidualWeight A hN pair) ^ 2) ≤
      quadraticResidualMass A hN population := by
  unfold quadraticResidualMass
  exact Finset.sum_le_sum fun pair _hpair ↦
    linearResidualWeight_sq_le_quadraticResidualWeight hN pair

/--
Finite bounded-ratio interpolation before replacing the population
cardinality by a relational-host estimate.
-/
theorem linearResidualMass_cast_le_sqrt_card_mul_sqrt_quadratic
    {N M A L : ℕ} (hN : 2 ≤ N)
    (population : Finset (SeparatedBoundedRatioPair N M L)) :
    (linearResidualMass A hN population : ℝ) ≤
      Real.sqrt (population.card : ℝ) *
        Real.sqrt (quadraticResidualMass A hN population : ℝ) := by
  have hcs :=
    RelationalInterpolation.sum_le_sqrt_card_mul_sqrt_sum_sq
      population
      (fun pair : SeparatedBoundedRatioPair N M L ↦
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

/-! ## Literal Section 17 sectors -/

/-- The active part of one literal bounded-ratio sector. -/
noncomputable def activeSectorPairs
    (N M A L : ℕ) (hN : 2 ≤ N)
    (terminal : TerminalPredicateFamily)
    (sector : ResidualSector) :
    Finset (SeparatedBoundedRatioPair N M L) :=
  activePopulation A hN
    (boundedRatioSectorPairs N M A L hN terminal sector)

@[simp]
theorem mem_activeSectorPairs
    {N M A L : ℕ} {hN : 2 ≤ N}
    {terminal : TerminalPredicateFamily}
    {sector : ResidualSector}
    {pair : SeparatedBoundedRatioPair N M L} :
    pair ∈ activeSectorPairs N M A L hN terminal sector ↔
      boundedRatioSectorOf A hN terminal pair = sector ∧
        0 < pairTau A hN pair := by
  simp [activeSectorPairs]

theorem activeSectorPairs_subset_sectorPairs
    {N M A L : ℕ} (hN : 2 ≤ N)
    (terminal : TerminalPredicateFamily)
    (sector : ResidualSector) :
    activeSectorPairs N M A L hN terminal sector ⊆
      boundedRatioSectorPairs N M A L hN terminal sector :=
  activePopulation_subset hN _

/-- Quadratic mass on the full literal sector. -/
noncomputable def sectorQuadraticResidualMass
    {N M L : ℕ} (A : ℕ) (hN : 2 ≤ N)
    (terminal : TerminalPredicateFamily)
    (sector : ResidualSector) : ℕ :=
  quadraticResidualMass A hN
    (boundedRatioSectorPairs N M A L hN terminal sector)

/-- Quadratic sector mass after deleting the zero-weight pairs. -/
noncomputable def activeSectorQuadraticResidualMass
    {N M L : ℕ} (A : ℕ) (hN : 2 ≤ N)
    (terminal : TerminalPredicateFamily)
    (sector : ResidualSector) : ℕ :=
  quadraticResidualMass A hN
    (activeSectorPairs N M A L hN terminal sector)

/--
The linear mass on the full sector is exactly the natural-valued sector
mass already exposed by Proposition 16.1.
-/
theorem sectorResidualMassNat_eq_linearResidualMass
    {N M A L : ℕ} (hN : 2 ≤ N)
    (terminal : TerminalPredicateFamily)
    (sector : ResidualSector) :
    sectorResidualMassNat
        (M := M) (L := L) A hN terminal sector =
      linearResidualMass A hN
        (boundedRatioSectorPairs N M A L hN terminal sector) := by
  rfl

/-- Deleting inactive sector pairs does not change its literal linear mass. -/
theorem sectorResidualMassNat_eq_activeLinearResidualMass
    {N M A L : ℕ} (hN : 2 ≤ N)
    (terminal : TerminalPredicateFamily)
    (sector : ResidualSector) :
    sectorResidualMassNat
        (M := M) (L := L) A hN terminal sector =
      linearResidualMass A hN
        (activeSectorPairs N M A L hN terminal sector) := by
  rw [sectorResidualMassNat_eq_linearResidualMass hN terminal sector]
  exact linearResidualMass_eq_activePopulation hN _

/-- The full and active quadratic sector masses agree exactly. -/
theorem sectorQuadraticResidualMass_eq_active
    {N M A L : ℕ} (hN : 2 ≤ N)
    (terminal : TerminalPredicateFamily)
    (sector : ResidualSector) :
    sectorQuadraticResidualMass
        (M := M) (L := L) A hN terminal sector =
      activeSectorQuadraticResidualMass
        (M := M) (L := L) A hN terminal sector := by
  unfold sectorQuadraticResidualMass activeSectorQuadraticResidualMass
    activeSectorPairs
  exact quadraticResidualMass_eq_activePopulation hN _

/-- Cauchy--Schwarz on a full literal sector. -/
theorem sectorResidualMassNat_cast_le_sqrt_card_mul_sqrt_quadratic
    {N M A L : ℕ} (hN : 2 ≤ N)
    (terminal : TerminalPredicateFamily)
    (sector : ResidualSector) :
    (sectorResidualMassNat
        (M := M) (L := L) A hN terminal sector : ℝ) ≤
      Real.sqrt
          ((boundedRatioSectorPairs
            N M A L hN terminal sector).card : ℝ) *
        Real.sqrt
          (sectorQuadraticResidualMass
            (M := M) (L := L) A hN terminal sector : ℝ) := by
  rw [sectorResidualMassNat_eq_linearResidualMass hN terminal sector]
  exact
    linearResidualMass_cast_le_sqrt_card_mul_sqrt_quadratic
      hN (boundedRatioSectorPairs N M A L hN terminal sector)

/--
Cauchy--Schwarz in its sharper active-sector form.  This is the interface
intended for a later injection into bounded relational hosts.
-/
theorem sectorResidualMassNat_cast_le_sqrt_active_card_mul_sqrt_quadratic
    {N M A L : ℕ} (hN : 2 ≤ N)
    (terminal : TerminalPredicateFamily)
    (sector : ResidualSector) :
    (sectorResidualMassNat
        (M := M) (L := L) A hN terminal sector : ℝ) ≤
      Real.sqrt
          ((activeSectorPairs
            N M A L hN terminal sector).card : ℝ) *
        Real.sqrt
          (activeSectorQuadraticResidualMass
            (M := M) (L := L) A hN terminal sector : ℝ) := by
  rw [sectorResidualMassNat_eq_activeLinearResidualMass
    hN terminal sector]
  exact
    linearResidualMass_cast_le_sqrt_card_mul_sqrt_quadratic
      hN (activeSectorPairs N M A L hN terminal sector)

/-- Active sector values as unbundled ordered pairs. -/
noncomputable def activeSectorPairValues
    (N M A L : ℕ) (hN : 2 ≤ N)
    (terminal : TerminalPredicateFamily)
    (sector : ResidualSector) :
    Finset (ℕ × ℕ) :=
  populationPairValues
    (activeSectorPairs N M A L hN terminal sector)

theorem card_activeSectorPairValues
    (N M A L : ℕ) (hN : 2 ≤ N)
    (terminal : TerminalPredicateFamily)
    (sector : ResidualSector) :
    (activeSectorPairValues N M A L hN terminal sector).card =
      (activeSectorPairs N M A L hN terminal sector).card :=
  card_populationPairValues _

/--
Every active sector pair is still an ambient separated pair.  Future host
modules can strengthen this inclusion without changing the mass API.
-/
theorem activeSectorPairValues_subset_separatedBoundedRatioPairs
    {N M A L : ℕ} (hN : 2 ≤ N)
    (terminal : TerminalPredicateFamily)
    (sector : ResidualSector) :
    activeSectorPairValues N M A L hN terminal sector ⊆
      PropositionSixteenOne.separatedBoundedRatioPairs N M L :=
  populationPairValues_subset_separatedBoundedRatioPairs _

end
end BoundedRatioResidualMasses
end PaperC
