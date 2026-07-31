import PaperC.Asymptotics.BoundedRatioDenseQuantitative
import PaperC.Asymptotics.BoundedRatioElementaryQuantitative
import PaperC.Asymptotics.BoundedRatioManyDefectsAssembly
import PaperC.Asymptotics.BoundedRatioNonterminalMobileAssembly
import PaperC.Asymptotics.BoundedRatioTwoSingletonCritical
import PaperC.Asymptotics.DyadicKappaTransport
import PaperC.Asymptotics.SectionThirteenRate
import PaperC.Diophantine.PellDivisorEnvelope

set_option maxHeartbeats 3600000

/-!
# Quantitative dyadic mother mass from the bounded-ratio `κ` proofs

The historical route to Corollary 11.3 asks separately for the generic
interfaces C11.3, P9.9, and T10.1.  The bounded-ratio theory proves the
canonical masses needed at the dyadic endpoint more directly:

* all elementary sectors keep their fixed rational-power saving;
* the many-defects sector follows from Evertse--Silverman and generalized
  Pell;
* the moderate nonterminal branch is `N^(5/3+o(1))`;
* the dense nonterminal branch has the manuscript's exponential saving;
* the canonical terminal branch is `N^(7/4+o(1))` under generalized Pell.

This module sums those literal masses at `M = 2N`, then uses the exact
transport in `DyadicKappaTransport`.  Thus its public mother-mass theorem
does not pass through any of the three historical aggregate interfaces.
-/

namespace PaperC
namespace DyadicKappaQuantitative

open BoundedRatioCanonicalTerminalPopulation
open BoundedRatioNonterminalCardinality
open BoundedRatioNonterminalMobileAssembly
open BoundedRatioTwoSingletonCritical
open PropositionSixteenOne

noncomputable section

private theorem rationalPower_uniformBigO_quadraticLogLog
    {p q : ℕ} {C : ℝ}
    {f : ℕ → ℕ → ℝ}
    (hpq : p < 2 * q)
    (hf :
      UniformRationalPowerSubpolynomialOn
        p q (CriticalRunWindow.InRunLengthWindow C) f) :
    UniformBigOOn
      (CriticalRunWindow.InRunLengthWindow C)
      f SectionThirteenRate.quadraticDivLogLogSquaredScale := by
  have h :=
    SectionThirteenRate.rationalPower_uniformBigO_natPowerDivLogLogSquared
      (p := p) (q := q) (r := 2) hpq hf
  simpa only [
    SectionThirteenRate.natPowerDivLogLogSquaredScale,
    SectionThirteenRate.quadraticDivLogLogSquaredScale] using h

/-! ## The two quantitative branches of sector six -/

/--
The moderate-density part of the intrinsic sixth sector keeps its
`N^(5/3+o(1))` rate after specializing to `M = 2N`.
-/
theorem moderateDensityMass_dyadic_uniformBigO
    {C K : ℝ} (hostEnvelope : ℕ → ℕ → ℝ)
    (hhostRate :
      UniformLinearSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C) hostEnvelope)
    (hhostNonneg : ∀ N L, 0 ≤ hostEnvelope N L)
    (hhostsTen :
      ∃ N₁ : ℕ, ∀ N ≥ N₁, ∀ M L,
        2 * N ≤ M →
        M ≤ 2 * N →
        CriticalRunWindow.InRunLengthWindow C N L →
        ((BoundedRatioComponentHosts.boundedComponentHosts
          N M 3 L 10).card : ℝ) ≤ hostEnvelope N L) :
    UniformBigOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun N L ↦
        moderateDensityIntrinsicNonterminalMass
          3 K N (2 * N) L)
      SectionThirteenRate.quadraticDivLogLogSquaredScale := by
  let envelope : ℕ → ℕ → ℝ :=
    fun N L =>
      hostEnvelope N L *
        moderateDensityResidualWeightEnvelope N L
  have henvelopeRate :
      UniformRationalPowerSubpolynomialOn 5 3
        (CriticalRunWindow.InRunLengthWindow C)
        envelope := by
    simpa only [envelope] using
      linear_mul_twoThird_uniformFiveThird hhostRate
        (moderateDensityResidualWeightEnvelope_uniformTwoThird
          (C := C))
  have henvelopeBigO :
      UniformBigOOn
        (CriticalRunWindow.InRunLengthWindow C)
        envelope
        SectionThirteenRate.quadraticDivLogLogSquaredScale :=
    rationalPower_uniformBigO_quadraticLogLog
      (by omega) henvelopeRate
  apply SectionThirteenRate.uniformBigOOn_mono henvelopeBigO
  obtain ⟨N₁, hN₁⟩ := hhostsTen
  refine ⟨max N₁ 2, ?_⟩
  intro N hN L hrun
  have hNtwo : 2 ≤ N :=
    (le_max_right N₁ 2).trans hN
  have hbound :
      moderateDensityIntrinsicNonterminalMass
          3 K N (2 * N) L ≤
        envelope N L := by
    exact
      moderateDensityIntrinsicNonterminalMass_le_hostEnvelope
        hNtwo hostEnvelope
        (hN₁ N ((le_max_left N₁ 2).trans hN)
          (2 * N) L le_rfl le_rfl hrun)
  have hleft :
      0 ≤
        moderateDensityIntrinsicNonterminalMass
          3 K N (2 * N) L :=
    moderateDensityIntrinsicNonterminalMass_nonneg
      3 K N (2 * N) L
  have hright : 0 ≤ envelope N L := by
    dsimp only [envelope]
    exact mul_nonneg (hhostNonneg N L) (by
      unfold moderateDensityResidualWeightEnvelope
      positivity)
  simpa only [abs_of_nonneg hleft, abs_of_nonneg hright] using hbound

/--
The high-density part of sector six inherits the explicit exponential
saving, and hence the displayed quadratic logarithmic rate.
-/
theorem highDensityMass_dyadic_uniformBigO
    {C Cterm K : ℝ} (hC : 0 ≤ C) (hCterm : 0 ≤ Cterm)
    (hthreshold : 2 * Cterm < K * Real.log 2)
    (hhostsTwo :
      ∃ N₁ : ℕ, ∀ N ≥ N₁, ∀ M L,
        2 * N ≤ M →
        M ≤ 2 * N →
        CriticalRunWindow.InRunLengthWindow C N L →
        ((BoundedRatioComponentHosts.boundedComponentHosts
          N M 3 L 2).card : ℝ) ≤
            sizeTwoComponentHostEnvelope Cterm N L) :
    UniformBigOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun N L ↦
        highDensityIntrinsicNonterminalMass
          3 K N (2 * N) L)
      SectionThirteenRate.quadraticDivLogLogSquaredScale := by
  have hc :
      0 <
        BoundedRatioDenseQuantitative.denseQuantitativeConstant
          Cterm K :=
    BoundedRatioDenseQuantitative.denseQuantitativeConstant_pos
      hCterm hthreshold
  have henvelopeQuantitative :=
    BoundedRatioDenseQuantitative.highDensityIntrinsicNonterminalMassEnvelope_uniformBigO_quantitative
        hC hCterm hthreshold
  have henvelopeBigO :
      UniformBigOOn
        (CriticalRunWindow.InRunLengthWindow C)
        (highDensityIntrinsicNonterminalMassEnvelope C Cterm K)
        SectionThirteenRate.quadraticDivLogLogSquaredScale :=
    SectionThirteenRate.uniformBigOOn_trans henvelopeQuantitative
      (SectionThirteenRate.quantitativeHomogeneousScale_uniformBigO_loglogSquared
        hc)
  apply SectionThirteenRate.uniformBigOOn_mono henvelopeBigO
  obtain ⟨N₁, hN₁⟩ := hhostsTwo
  refine ⟨max N₁ 2, ?_⟩
  intro N hN L hrun
  have hNtwo : 2 ≤ N :=
    (le_max_right N₁ 2).trans hN
  have hbound :
      highDensityIntrinsicNonterminalMass
          3 K N (2 * N) L ≤
        highDensityIntrinsicNonterminalMassEnvelope
          C Cterm K N L := by
    exact
      highDensityIntrinsicNonterminalMass_le_envelope
        hNtwo hrun
        (hN₁ N ((le_max_left N₁ 2).trans hN)
          (2 * N) L le_rfl le_rfl hrun)
  have hleft :
      0 ≤
        highDensityIntrinsicNonterminalMass
          3 K N (2 * N) L :=
    highDensityIntrinsicNonterminalMass_nonneg
      3 K N (2 * N) L
  have hright :
      0 ≤
        highDensityIntrinsicNonterminalMassEnvelope
          C Cterm K N L :=
    highDensityIntrinsicNonterminalMassEnvelope_nonneg
      C Cterm K N L
  simpa only [abs_of_nonneg hleft, abs_of_nonneg hright] using hbound

/--
The literal sixth sector on `[N,2N)` is quantitatively controlled by its
moderate/dense disintegration.
-/
theorem nonterminalSector_dyadic_uniformBigO
    {C Cterm K : ℝ} (hC : 0 ≤ C) (hCterm : 0 ≤ Cterm)
    (hthreshold : 2 * Cterm < K * Real.log 2)
    (hostEnvelope : ℕ → ℕ → ℝ)
    (hhostRate :
      UniformLinearSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C) hostEnvelope)
    (hhostNonneg : ∀ N L, 0 ≤ hostEnvelope N L)
    (hhostsTen :
      ∃ N₁ : ℕ, ∀ N ≥ N₁, ∀ M L,
        2 * N ≤ M →
        M ≤ 2 * N →
        CriticalRunWindow.InRunLengthWindow C N L →
        ((BoundedRatioComponentHosts.boundedComponentHosts
          N M 3 L 10).card : ℝ) ≤ hostEnvelope N L)
    (hhostsTwo :
      ∃ N₁ : ℕ, ∀ N ≥ N₁, ∀ M L,
        2 * N ≤ M →
        M ≤ 2 * N →
        CriticalRunWindow.InRunLengthWindow C N L →
        ((BoundedRatioComponentHosts.boundedComponentHosts
          N M 3 L 2).card : ℝ) ≤
            sizeTwoComponentHostEnvelope Cterm N L) :
    UniformBigOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun N L ↦
        sectorResidualMass 3
          (boundedIntrinsicTerminalPredicate 3 K)
          .nonterminal N (2 * N) L)
      SectionThirteenRate.quadraticDivLogLogSquaredScale := by
  have hmoderate :=
    moderateDensityMass_dyadic_uniformBigO
      (K := K) hostEnvelope hhostRate hhostNonneg hhostsTen
  have hhigh :=
    highDensityMass_dyadic_uniformBigO
      hC hCterm hthreshold hhostsTwo
  have hsum :=
    PropositionElevenThree.uniformBigOOn_add hmoderate hhigh
  simpa only [
    intrinsicNonterminalSectorResidualMass_eq_densitySplit] using hsum

/-! ## The seven dyadic sectors and their exact sum -/

/--
Every literal sector of the bounded-ratio partition at `M=2N` has the
rate required by the Section 13 numerator.
-/
theorem everySector_dyadic_uniformBigO
    {C Cterm K : ℝ} (hC : 0 ≤ C) (hCterm : 0 ≤ Cterm)
    (hK : 0 ≤ K)
    (hthreshold : 2 * Cterm < K * Real.log 2)
    (hES :
      EvertseSilvermanInput.EvertseSilvermanAbscissaStatement)
    (hPell :
      PellInput.GeneralizedPellPolynomialBoxStatement)
    (hostEnvelope : ℕ → ℕ → ℝ)
    (hhostRate :
      UniformLinearSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C) hostEnvelope)
    (hhostNonneg : ∀ N L, 0 ≤ hostEnvelope N L)
    (hhostsTen :
      ∃ N₁ : ℕ, ∀ N ≥ N₁, ∀ M L,
        2 * N ≤ M →
        M ≤ 2 * N →
        CriticalRunWindow.InRunLengthWindow C N L →
        ((BoundedRatioComponentHosts.boundedComponentHosts
          N M 3 L 10).card : ℝ) ≤ hostEnvelope N L)
    (hhostsTwo :
      ∃ N₁ : ℕ, ∀ N ≥ N₁, ∀ M L,
        2 * N ≤ M →
        M ≤ 2 * N →
        CriticalRunWindow.InRunLengthWindow C N L →
        ((BoundedRatioComponentHosts.boundedComponentHosts
          N M 3 L 2).card : ℝ) ≤
            sizeTwoComponentHostEnvelope Cterm N L) :
    ∀ sector : SectionElevenPartition.ResidualSector,
      UniformBigOOn
        (CriticalRunWindow.InRunLengthWindow C)
        (fun N L ↦
          sectorResidualMass 3
            (boundedIntrinsicTerminalPredicate 3 K)
            sector N (2 * N) L)
        SectionThirteenRate.quadraticDivLogLogSquaredScale := by
  intro sector
  cases sector with
  | smallPrimeProduct =>
      exact
        rationalPower_uniformBigO_quadraticLogLog (by omega)
          (BoundedRatioElementaryQuantitative.smallPrimeProduct_dyadic_uniformSevenFourths
            hC K)
  | smallCanonicalHeight =>
      exact
        rationalPower_uniformBigO_quadraticLogLog (by omega)
          (BoundedRatioElementaryQuantitative.smallCanonicalHeight_dyadic_uniformSevenFourths
            hC K)
  | shallowCore =>
      exact
        rationalPower_uniformBigO_quadraticLogLog (by omega)
          (BoundedRatioElementaryQuantitative.shallowCore_dyadic_uniformThirtyOneSixteenths
            hC K)
  | alignedDeepCore =>
      simpa only [
        SectionThirteenRate.quadraticDivLogLogSquaredScale] using
        BoundedRatioElementaryQuantitative.alignedDeepCore_dyadic_uniformBigO
          hC K
  | manyDefects =>
      have hbounded :=
        BoundedRatioManyDefectsAssembly.manyDefectsSector_uniformThreeHalves
            hC 2 3 (boundedIntrinsicTerminalPredicate 3 K)
              hES hPell
      have hdyadic :=
        BoundedRatioElementaryQuantitative.uniformRationalPowerInBoundedRatioWindow_dyadic
          hbounded
      exact
        rationalPower_uniformBigO_quadraticLogLog
          (by omega) hdyadic
  | nonterminal =>
      exact
        nonterminalSector_dyadic_uniformBigO
          hC hCterm hthreshold hostEnvelope
            hhostRate hhostNonneg hhostsTen hhostsTwo
  | terminal =>
      exact
        rationalPower_uniformBigO_quadraticLogLog (by omega)
          (BoundedRatioElementaryQuantitative.terminal_dyadic_uniformSevenFourths
              hC K hK hPell)

/--
The bounded-ratio mass at its dyadic endpoint has the exact quantitative
numerator rate, using only the concrete Evertse--Silverman and generalized
Pell inputs.
-/
theorem R2κ_dyadic_uniformBigO
    {C Cterm K : ℝ} (hC : 0 ≤ C) (hCterm : 0 ≤ Cterm)
    (hK : 0 ≤ K)
    (hthreshold : 2 * Cterm < K * Real.log 2)
    (hES :
      EvertseSilvermanInput.EvertseSilvermanAbscissaStatement)
    (hPell :
      PellInput.GeneralizedPellPolynomialBoxStatement)
    (hostEnvelope : ℕ → ℕ → ℝ)
    (hhostRate :
      UniformLinearSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C) hostEnvelope)
    (hhostNonneg : ∀ N L, 0 ≤ hostEnvelope N L)
    (hhostsTen :
      ∃ N₁ : ℕ, ∀ N ≥ N₁, ∀ M L,
        2 * N ≤ M →
        M ≤ 2 * N →
        CriticalRunWindow.InRunLengthWindow C N L →
        ((BoundedRatioComponentHosts.boundedComponentHosts
          N M 3 L 10).card : ℝ) ≤ hostEnvelope N L)
    (hhostsTwo :
      ∃ N₁ : ℕ, ∀ N ≥ N₁, ∀ M L,
        2 * N ≤ M →
        M ≤ 2 * N →
        CriticalRunWindow.InRunLengthWindow C N L →
        ((BoundedRatioComponentHosts.boundedComponentHosts
          N M 3 L 2).card : ℝ) ≤
            sizeTwoComponentHostEnvelope Cterm N L) :
    UniformBigOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun N L ↦ R2κ N (2 * N) L)
      SectionThirteenRate.quadraticDivLogLogSquaredScale := by
  have hsystematic :
      UniformBigOOn
        (CriticalRunWindow.InRunLengthWindow C)
        (fun N L ↦ systematicMass 3 N (2 * N) L)
        SectionThirteenRate.quadraticDivLogLogSquaredScale :=
    rationalPower_uniformBigO_quadraticLogLog (by omega)
      (BoundedRatioElementaryQuantitative.systematicMass_dyadic_uniformThreeHalves
        hC)
  have hsectors :
      UniformBigOOn
        (CriticalRunWindow.InRunLengthWindow C)
        (fun N L ↦
          ∑ sector : SectionElevenPartition.ResidualSector,
            sectorResidualMass 3
              (boundedIntrinsicTerminalPredicate 3 K)
              sector N (2 * N) L)
        SectionThirteenRate.quadraticDivLogLogSquaredScale :=
    PropositionElevenThree.uniformBigOOn_fintype_sum
      (everySector_dyadic_uniformBigO
        hC hCterm hK hthreshold hES hPell hostEnvelope
          hhostRate hhostNonneg hhostsTen hhostsTwo)
  have htotal :=
    PropositionElevenThree.uniformBigOOn_add
      hsystematic hsectors
  apply SectionThirteenRate.uniformBigOOn_mono htotal
  refine ⟨2, ?_⟩
  intro N hN L _hrun
  rw [R2κ_eq_systematic_add_sum_sectors
    hN (boundedIntrinsicTerminalPredicate 3 K)]

/-!
## Canonical mother-mass theorem

The envelope witnesses and the terminal threshold are now constructed
inside Lean.  Consequently the public signature contains neither C11.3,
P9.9, nor T10.1.
-/

/--
The dyadic homogeneous mother mass has the quantitative rate required by
Corollary 13.10, directly from the bounded-ratio `κ` proofs.
-/
theorem homogeneousMass_uniformBigO_of_generalizedPell
    {C : ℝ} (hC : 0 ≤ C)
    (hES :
      EvertseSilvermanInput.EvertseSilvermanAbscissaStatement)
    (hPell :
      PellInput.GeneralizedPellPolynomialBoxStatement) :
    UniformBigOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (PropositionElevenTwo.homogeneousMass 3)
      SectionThirteenRate.quadraticDivLogLogSquaredScale := by
  obtain ⟨Q₂, hQ₂Rate, hQ₂Nonneg, hQ₂Dom⟩ :=
    exists_twoSingletonShapeFiberEnvelope hC 2 3
  obtain ⟨Cterm, hCterm, hhostsTwo⟩ :=
    exists_sizeTwoComponentHostEnvelope hC 2 3
  obtain ⟨hostEnvelope, hhostRate, hhostNonneg, hhostsTen⟩ :=
    evertseSilverman_generalizedPell_imply_exists_moderateNonterminalHostEnvelope
      hC 2 3 hES hPell Q₂ hQ₂Rate hQ₂Nonneg hQ₂Dom
  have hlogTwo : 0 < Real.log 2 :=
    Real.log_pos (by norm_num)
  let K : ℝ := (2 * Cterm + 1) / Real.log 2
  have hK : 0 ≤ K := by
    dsimp only [K]
    exact div_nonneg (by linarith) hlogTwo.le
  have hthreshold : 2 * Cterm < K * Real.log 2 := by
    dsimp only [K]
    rw [div_mul_cancel₀ _ hlogTwo.ne']
    linarith
  have hR2κ :=
    R2κ_dyadic_uniformBigO
      hC hCterm hK hthreshold hES hPell hostEnvelope
        hhostRate hhostNonneg hhostsTen hhostsTwo
  have heq :
      PropositionElevenTwo.homogeneousMass 3 =
        fun N L ↦ R2κ N (2 * N) L := by
    funext N L
    exact
      DyadicKappaTransport.homogeneousMass_eq_R2κ_two_mul
        3 N L
  rw [heq]
  exact hR2κ

/--
Compatibility wrapper for the former specialized Nicolas--Robin Pell
envelope.
-/
theorem homogeneousMass_uniformBigO_of_pellEnvelope
    {C : ℝ} (hC : 0 ≤ C)
    (hES :
      EvertseSilvermanInput.EvertseSilvermanAbscissaStatement)
    (hConductor :
      PellInput.QuadraticOrderConductorFiberBoundStatement)
    (hDivisor :
      PellInput.NicolasRobinPellEnvelopeStatement) :
    UniformBigOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (PropositionElevenTwo.homogeneousMass 3)
      SectionThirteenRate.quadraticDivLogLogSquaredScale :=
  homogeneousMass_uniformBigO_of_generalizedPell
    hC hES
      (PellInput.generalizedPellPolynomialBox_of_quadraticOrder_nicolasRobin
        hConductor hDivisor)

/--
The canonical mother-mass theorem with the source-shaped Nicolas--Robin
divisor inequality.  All polynomial-height and unit-orbit postprocessing is
constructed internally.
-/
theorem homogeneousMass_uniformBigO
    {C : ℝ} (hC : 0 ≤ C)
    (hES :
      EvertseSilvermanInput.EvertseSilvermanAbscissaStatement)
    (hConductor :
      PellInput.QuadraticOrderConductorFiberBoundStatement)
    (hDivisor :
      PellInput.NicolasRobinDivisorLogBoundStatement) :
    UniformBigOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (PropositionElevenTwo.homogeneousMass 3)
      SectionThirteenRate.quadraticDivLogLogSquaredScale :=
  homogeneousMass_uniformBigO_of_generalizedPell
    hC hES
      (PellInput.generalizedPellPolynomialBox_of_quadraticOrder_divisorLogBound
        hConductor hDivisor)

end

end DyadicKappaQuantitative
end PaperC
