import PaperC.Analysis.CriticalWeightedDefect
import PaperC.Asymptotics.CriticalRationalMass
import PaperC.Asymptotics.RationalPowerClosure
import PaperC.Asymptotics.SmallHeightTauEnvelopeCritical
import PaperC.Combinatorics.SmallHeightLargeProductMassBound

/-!
# The small-height positive-`σ` branch in the critical window

The finite systematic estimate is

`Q_pos ≤ 2 * 4^tauEnvelope * rationalMass(N,A,L,4)`.

The base-four rational mass is `N^(5/3+o_C(1))` by Proposition 5.4.
The remaining factor is uniformly subpolynomial, including the harmless
constant `2`, so the rational-power multiplication closure gives the same
`5/3` exponent for the positive-`σ` residual mass.
-/

namespace PaperC
namespace SmallHeightPositiveSigmaCritical

open RationalMassFinite
open SmallHeightLargeProductMassBound
open SmallHeightLargeProductPairs
open SmallHeightTauEnvelope

noncomputable section

/--
Proof-independent real form of the positive-`σ` small-height quadratic
residual mass.  Below `N=2`, it is defined to be zero.
-/
noncomputable def positiveSigmaQuadraticResidualMassTotal
    (A N L : ℕ) : ℝ :=
  if hN : 2 ≤ N then
    (positiveSigmaSmallHeightLargeProductQuadraticResidualMass
      N A L hN : ℝ)
  else 0

/--
The positive-`σ` small-height branch is uniformly
`N^(5/3+o_C(1))` in the critical run-length window.
-/
theorem positiveSigmaQuadraticResidualMass_uniformFiveThird
    {C : ℝ} (hC : 0 ≤ C)
    (A : ℕ) (hA : 1 ≤ A) :
    UniformFiveThirdSubpolynomialOn
      (CriticalRunWindow.InRunLengthWindow C)
      (positiveSigmaQuadraticResidualMassTotal A) := by
  let admissible := CriticalRunWindow.InRunLengthWindow C
  let systematic : ℕ → ℕ → ℝ :=
    fun N L => ((rationalMass N A L 4 : ℕ) : ℝ)
  let tauFactor : ℕ → ℕ → ℝ :=
    fun N L =>
      (((4 ^ smallHeightTauEnvelope A N L : ℕ) : ℝ))
  let residualFactor : ℕ → ℕ → ℝ :=
    fun N L => 2 * tauFactor N L
  have hsystematic :
      UniformFiveThirdSubpolynomialOn admissible systematic := by
    simpa only [admissible, systematic] using
      CriticalRationalMass.rationalMass_four_uniformFiveThird
        hC A hA
  have htau :
      UniformSubpolynomialOn admissible tauFactor := by
    simpa only [admissible, tauFactor] using
      SmallHeightTauEnvelopeCritical.four_pow_smallHeightTauEnvelope_uniformSubpolynomial
        hC A
  have hresidual :
      UniformSubpolynomialOn admissible residualFactor := by
    simpa only [residualFactor] using
      ExpSqrtLog.uniformSubpolynomialOn_const_mul
        2 htau
  have henvelope :
      UniformFiveThirdSubpolynomialOn admissible
        (fun N L => residualFactor N L * systematic N L) :=
    UniformRationalPower.mul_subpolynomial
      (p := 5) (q := 3) (by omega)
      hsystematic hresidual
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
  apply UniformRationalPower.mono henvelope
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
    positiveSigmaQuadraticResidualMass_le_uniform
      (A := A) hNtwo hB
  have hfiniteReal :
      (positiveSigmaSmallHeightLargeProductQuadraticResidualMass
          N A L hNtwo : ℝ) ≤
        (2 : ℝ) *
          (((4 ^ smallHeightTauEnvelope A N L : ℕ) : ℝ)) *
          (rationalMass N A L 4 : ℝ) := by
    exact_mod_cast hfinite
  have hleftNonneg :
      0 ≤ positiveSigmaQuadraticResidualMassTotal A N L := by
    simp [positiveSigmaQuadraticResidualMassTotal, hNtwo]
  have hrightNonneg :
      0 ≤ residualFactor N L * systematic N L := by
    dsimp only [residualFactor, tauFactor, systematic]
    positivity
  rw [abs_of_nonneg hleftNonneg, abs_of_nonneg hrightNonneg]
  simpa only [positiveSigmaQuadraticResidualMassTotal, dif_pos hNtwo,
    residualFactor, tauFactor, systematic, mul_assoc] using
    hfiniteReal

end

end SmallHeightPositiveSigmaCritical
end PaperC
