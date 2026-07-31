import PaperC.Analysis.CriticalWeightedDefect
import PaperC.Asymptotics.RationalPowerClosure
import PaperC.Asymptotics.RelationalHostsThreeHalves
import PaperC.Asymptotics.SmallHeightTauEnvelopeCritical
import PaperC.Combinatorics.SmallHeightLargeProductMassBound

/-!
# The small-height `σ = 0` branch in the critical window

The finite estimate for this branch is

`Q_zero ≤ 4^tauEnvelope * #relationalHosts`.

The first factor is uniformly subpolynomial by the small-height
prime-counting argument, while the host count is
`N^(3/2+o_C(1))`.  This module first compares the exact finite core maximum
used by the mass bound with the pair-independent `τ` envelope, and then
performs the uniform asymptotic closure.
-/

namespace PaperC
namespace SmallHeightSigmaZeroCritical

open ResidualComponentCounts
open ResidualMasses
open SmallHeightLargeProductMassBound
open SmallHeightLargeProductPairs
open SmallHeightResidualComponentEnvelope
open SmallHeightTauEnvelope

noncomputable section

/--
The exact finite maximum of `D# + c#` on the small-height population is
bounded by the pair-independent `τ` envelope.
-/
theorem maxSmallHeightLargeProductCoreExponent_le_tauEnvelope
    {N A L : ℕ} {hN : 2 ≤ N}
    (hB : 8 ≤ L + 1) :
    maxSmallHeightLargeProductCoreExponent N A L hN ≤
      smallHeightTauEnvelope A N L := by
  unfold maxSmallHeightLargeProductCoreExponent
  apply Finset.sup_le
  intro pair hpair
  have hcorrected :
      canonicalCorrectedDefectCount
          A pair.1.1 pair.1.2 L ≤
        CorrectedDefectEnvelope.maxCanonicalCorrectedDefectCount
          A N L :=
    CorrectedDefectEnvelope.canonicalCorrectedDefectCount_le_max
      pair.2
  have hresidual :
      canonicalResidualComponentCount
          A pair.1.1 pair.1.2 L ≤
        smallHeightResidualComponentEnvelope L := by
    simpa only [pairResidualComponentCount] using
      pairResidualComponentCount_le_envelope_of_mem
        hB hpair
  unfold smallHeightTauEnvelope
  exact Nat.add_le_add hcorrected hresidual

/-- The exact core factor is bounded by the uniform fourth-power `τ` envelope. -/
theorem smallHeightLargeProductCoreFactor_le_four_pow_tauEnvelope
    {N A L : ℕ} {hN : 2 ≤ N}
    (hB : 8 ≤ L + 1) :
    smallHeightLargeProductCoreFactor N A L hN ≤
      4 ^ smallHeightTauEnvelope A N L := by
  unfold smallHeightLargeProductCoreFactor
  exact Nat.pow_le_pow_right (by norm_num)
    (maxSmallHeightLargeProductCoreExponent_le_tauEnvelope hB)

/--
Finite exceptional-branch estimate with the pair-independent envelope
exposed in the form used by the asymptotic argument.
-/
theorem sigmaZeroQuadraticResidualMass_le_tauEnvelope_mul_hosts
    {N A L : ℕ} (hN : 2 ≤ N)
    (hB : 8 ≤ L + 1) :
    sigmaZeroSmallHeightLargeProductQuadraticResidualMass
        N A L hN ≤
      4 ^ smallHeightTauEnvelope A N L *
        (RelationalHosts.relationalHosts N L).card := by
  calc
    sigmaZeroSmallHeightLargeProductQuadraticResidualMass
          N A L hN ≤
        smallHeightLargeProductCoreFactor N A L hN *
          (RelationalHosts.relationalHosts N L).card :=
      sigmaZeroQuadraticResidualMass_le (A := A) hN
    _ ≤
        4 ^ smallHeightTauEnvelope A N L *
          (RelationalHosts.relationalHosts N L).card :=
      Nat.mul_le_mul_right _
        (smallHeightLargeProductCoreFactor_le_four_pow_tauEnvelope hB)

/--
Proof-independent real form of the small-height `σ=0` quadratic mass.
Below the harmless threshold `N=2`, it is defined to be zero.
-/
noncomputable def sigmaZeroQuadraticResidualMassTotal
    (A N L : ℕ) : ℝ :=
  if hN : 2 ≤ N then
    (sigmaZeroSmallHeightLargeProductQuadraticResidualMass
      N A L hN : ℝ)
  else 0

/--
The exceptional small-height branch satisfies

`Q_zero ≤ N^(3/2+o_C(1))`

uniformly in the literal critical run-length window.
-/
theorem sigmaZeroQuadraticResidualMass_uniformThreeHalves
    {C : ℝ} (hC : 0 ≤ C) (A : ℕ) :
    UniformThreeHalvesSubpolynomialOn
      (CriticalRunWindow.InRunLengthWindow C)
      (sigmaZeroQuadraticResidualMassTotal A) := by
  let admissible := CriticalRunWindow.InRunLengthWindow C
  let hosts : ℕ → ℕ → ℝ :=
    fun N L =>
      ((RelationalHosts.relationalHosts N L).card : ℝ)
  let tauFactor : ℕ → ℕ → ℝ :=
    fun N L =>
      (((4 ^ smallHeightTauEnvelope A N L : ℕ) : ℝ))
  have hhosts :
      UniformThreeHalvesSubpolynomialOn admissible hosts := by
    simpa only [admissible, hosts] using
      RelationalHostsThreeHalves.card_relationalHosts_uniformThreeHalves_inRunLengthWindow
        hC
  have hhostsRational :
      UniformRationalPowerSubpolynomialOn 3 2 admissible hosts := by
    simpa only [UniformThreeHalvesSubpolynomialOn,
      UniformRationalPowerSubpolynomialOn] using hhosts
  have htau :
      UniformSubpolynomialOn admissible tauFactor := by
    simpa only [admissible, tauFactor] using
      SmallHeightTauEnvelopeCritical.four_pow_smallHeightTauEnvelope_uniformSubpolynomial
        hC A
  have henvelopeRational :
      UniformRationalPowerSubpolynomialOn 3 2 admissible
        (fun N L => tauFactor N L * hosts N L) :=
    UniformRationalPower.mul_subpolynomial
      (p := 3) (q := 2) (by omega) hhostsRational htau
  have henvelope :
      UniformThreeHalvesSubpolynomialOn admissible
        (fun N L => tauFactor N L * hosts N L) := by
    simpa only [UniformThreeHalvesSubpolynomialOn,
      UniformRationalPowerSubpolynomialOn] using henvelopeRational
  obtain ⟨Nwindow, hNwindow⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  obtain ⟨Nadm, hNadm⟩ :=
    CriticalWeightedDefect.admissible_eventually
      CriticalRunWindow.lowerConstant_pos
      CriticalRunWindow.lowerConstant_lt_upperConstant
  obtain ⟨Nheight, hNheight⟩ :=
    CriticalWeightedDefect.height_tends_to_infinity
      (c₂ := CriticalRunWindow.upperConstant)
      CriticalRunWindow.lowerConstant_pos 8
  apply UniformThreeHalves.mono henvelope
  refine ⟨max 2 (max Nwindow (max Nadm Nheight)), ?_⟩
  intro N hN L hrun
  have hNtwo : 2 ≤ N :=
    (le_max_left _ _).trans hN
  have hNtail :
      max Nwindow (max Nadm Nheight) ≤ N :=
    (le_max_right _ _).trans hN
  have hNwindowN : Nwindow ≤ N :=
    (le_max_left _ _).trans hNtail
  have hNtail' : max Nadm Nheight ≤ N :=
    (le_max_right _ _).trans hNtail
  have hNadmN : Nadm ≤ N :=
    (le_max_left _ _).trans hNtail'
  have hNheightN : Nheight ≤ N :=
    (le_max_right _ _).trans hNtail'
  have hfirst :=
    hNwindow N hNwindowN L hrun
  have hadmissible :
      CriticalWeightedDefect.Admissible
        CriticalRunWindow.lowerConstant
        CriticalRunWindow.upperConstant N (L + 1) :=
    hNadm N hNadmN (L + 1) hfirst.1
  have hB : 8 ≤ L + 1 :=
    hNheight N hNheightN (L + 1) hadmissible
  have hfinite :=
    sigmaZeroQuadraticResidualMass_le_tauEnvelope_mul_hosts
      (A := A) hNtwo hB
  have hfiniteReal :
      (sigmaZeroSmallHeightLargeProductQuadraticResidualMass
          N A L hNtwo : ℝ) ≤
        (((4 ^ smallHeightTauEnvelope A N L : ℕ) : ℝ)) *
          ((RelationalHosts.relationalHosts N L).card : ℝ) := by
    exact_mod_cast hfinite
  have hleftNonneg :
      0 ≤ sigmaZeroQuadraticResidualMassTotal A N L := by
    simp [sigmaZeroQuadraticResidualMassTotal, hNtwo]
  have hrightNonneg :
      0 ≤ tauFactor N L * hosts N L := by
    dsimp only [tauFactor, hosts]
    positivity
  rw [abs_of_nonneg hleftNonneg, abs_of_nonneg hrightNonneg]
  simpa only [sigmaZeroQuadraticResidualMassTotal, dif_pos hNtwo,
    tauFactor, hosts] using hfiniteReal

end

end SmallHeightSigmaZeroCritical
end PaperC
