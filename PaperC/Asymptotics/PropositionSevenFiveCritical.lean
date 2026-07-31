import PaperC.Asymptotics.CorrectedDefectEnvelope
import PaperC.Asymptotics.RelationalHostsThreeHalves
import PaperC.Asymptotics.ShallowCoreDensityCritical
import PaperC.Asymptotics.ShallowCoreRationalClosure
import PaperC.Asymptotics.ShallowCoreSigmaCritical
import PaperC.Combinatorics.ShallowCoreMassBound

/-!
# Proposition 7.5 in the critical window

This module assembles the three independent ingredients of the shallow-core
sector:

* the finite estimate
  `Q ≤ N² · 4^maxσ · 4^maxD# · 4^⌊3(L+1)/16⌋`;
* the subpolynomial bounds for the systematic and corrected-defect factors;
* the density rate
  `4^⌊3(L+1)/16⌋ = N^(3/8+o_C(1))`.

They give the manuscript's quadratic exponent

`Q_res ≤ N^(19/8+o_C(1))`.

The finite Cauchy--Schwarz inequality against the relational-host population
then interpolates `3/2` and `19/8`, giving

`R_res ≤ N^(31/16+o_C(1)) = o_C(N²)`.

The public totals below do not depend on a proof of `2 ≤ N`; below that
harmless finite threshold they are defined to be zero.
-/

namespace PaperC
namespace PropositionSevenFiveCritical

open ShallowCorePairs

noncomputable section

/-- Proof-independent real form of Proposition 7.5's quadratic mass. -/
noncomputable def shallowCoreQuadraticResidualMassTotal
    (A N L : ℕ) : ℝ :=
  if hN : 2 ≤ N then
    (shallowCoreQuadraticResidualMass N A L hN : ℝ)
  else 0

/-- Proof-independent real form of Proposition 7.5's linear mass. -/
noncomputable def shallowCoreLinearResidualMassTotal
    (A N L : ℕ) : ℝ :=
  if hN : 2 ≤ N then
    (shallowCoreLinearResidualMass N A L hN : ℝ)
  else 0

/--
The finite shallow-core estimate, expressed with proof-independent real
envelopes.
-/
theorem shallowCoreQuadraticResidualMassTotal_le_envelope
    {A N L : ℕ} (hN : 2 ≤ N) :
    shallowCoreQuadraticResidualMassTotal A N L ≤
      (N : ℝ) ^ 2 *
        (((4 ^
          ShallowCoreSigmaCritical.maxShallowCoreSigmaTotal A N L :
            ℕ) : ℝ)) *
        (((4 ^
          CorrectedDefectEnvelope.maxCanonicalCorrectedDefectCount
            A N L : ℕ) : ℝ)) *
        (((4 ^ shallowCoreComponentEnvelope L : ℕ) : ℝ)) := by
  have hfinite :=
    ShallowCoreMassBound.shallowCoreQuadraticResidualMass_le
      (A := A) (L := L) hN
  have hfiniteReal :
      (shallowCoreQuadraticResidualMass N A L hN : ℝ) ≤
        (N : ℝ) ^ 2 *
          (((4 ^ maxShallowCoreSigma N A L hN : ℕ) : ℝ)) *
          (((4 ^
            CorrectedDefectEnvelope.maxCanonicalCorrectedDefectCount
              A N L : ℕ) : ℝ)) *
          (((4 ^ shallowCoreComponentEnvelope L : ℕ) : ℝ)) := by
    exact_mod_cast hfinite
  simpa only [shallowCoreQuadraticResidualMassTotal, dif_pos hN,
    ShallowCoreSigmaCritical.maxShallowCoreSigmaTotal,
    dif_pos hN] using hfiniteReal

/--
The complete quadratic residual mass of Proposition 7.5 satisfies

`Q_res ≤ N^(19/8+o_C(1))`

uniformly in the literal critical run-length window.
-/
theorem shallowCoreQuadraticResidualMass_uniformNineteenEighths
    {C : ℝ} (hC : 0 ≤ C) (A : ℕ) :
    UniformRationalPowerSubpolynomialOn 19 8
      (CriticalRunWindow.InRunLengthWindow C)
      (shallowCoreQuadraticResidualMassTotal A) := by
  let admissible := CriticalRunWindow.InRunLengthWindow C
  let sigmaFactor : ℕ → ℕ → ℝ :=
    fun N L =>
      (((4 ^
        ShallowCoreSigmaCritical.maxShallowCoreSigmaTotal A N L :
          ℕ) : ℝ))
  let correctedFactor : ℕ → ℕ → ℝ :=
    fun N L =>
      (((4 ^
        CorrectedDefectEnvelope.maxCanonicalCorrectedDefectCount
          A N L : ℕ) : ℝ))
  let densityFactor : ℕ → ℕ → ℝ :=
    fun _ L =>
      (((4 ^ shallowCoreComponentEnvelope L : ℕ) : ℝ))
  have hsigma :
      UniformSubpolynomialOn admissible sigmaFactor := by
    simpa only [admissible, sigmaFactor] using
      ShallowCoreSigmaCritical.four_pow_maxShallowCoreSigma_uniformSubpolynomial
        hC A
  have hcorrected :
      UniformSubpolynomialOn admissible correctedFactor := by
    simpa only [admissible, correctedFactor] using
      CorrectedDefectEnvelope.four_pow_maxCanonicalCorrectedDefectCount_uniformSubpolynomial
        hC A
  have hdensity :
      UniformRationalPowerSubpolynomialOn
        3 8 admissible densityFactor := by
    simpa only [admissible, densityFactor] using
      ShallowCoreDensityCritical.four_pow_shallowCoreComponentEnvelope_uniformThreeEighths
        C
  have henvelope :
      UniformRationalPowerSubpolynomialOn 19 8 admissible
        (fun N L =>
          (N : ℝ) ^ 2 *
            sigmaFactor N L *
            correctedFactor N L *
            densityFactor N L) :=
    UniformRationalPower.quadratic_mul_twoSubpolynomial_threeEighths
      hsigma hcorrected hdensity
  apply UniformRationalPower.mono henvelope
  refine ⟨2, ?_⟩
  intro N hN L _hrun
  have hleftNonneg :
      0 ≤ shallowCoreQuadraticResidualMassTotal A N L := by
    simp [shallowCoreQuadraticResidualMassTotal, hN]
  have hrightNonneg :
      0 ≤
        (N : ℝ) ^ 2 *
          sigmaFactor N L *
          correctedFactor N L *
          densityFactor N L := by
    dsimp only [sigmaFactor, correctedFactor, densityFactor]
    positivity
  rw [abs_of_nonneg hleftNonneg, abs_of_nonneg hrightNonneg]
  simpa only [sigmaFactor, correctedFactor, densityFactor] using
    (shallowCoreQuadraticResidualMassTotal_le_envelope
      (A := A) hN)

/-- The finite interpolation inequality (6.6) for the public totals. -/
theorem shallowCoreLinearResidualMassTotal_le
    {A N L : ℕ} (hN : 2 ≤ N) :
    shallowCoreLinearResidualMassTotal A N L ≤
      Real.sqrt
          ((RelationalHosts.relationalHosts N L).card : ℝ) *
        Real.sqrt
          (shallowCoreQuadraticResidualMassTotal A N L) := by
  simpa only [shallowCoreLinearResidualMassTotal,
    shallowCoreQuadraticResidualMassTotal, dif_pos hN] using
    (shallowCoreLinearResidualMass_cast_le (A := A) hN)

/--
The complete linear residual mass of Proposition 7.5 satisfies

`R_res ≤ N^(31/16+o_C(1))`

uniformly in the critical run-length window.
-/
theorem shallowCoreLinearResidualMass_uniformThirtyOneSixteenths
    {C : ℝ} (hC : 0 ≤ C) (A : ℕ) :
    UniformRationalPowerSubpolynomialOn 31 16
      (CriticalRunWindow.InRunLengthWindow C)
      (shallowCoreLinearResidualMassTotal A) := by
  let hosts : ℕ → ℕ → ℝ :=
    fun N L =>
      ((RelationalHosts.relationalHosts N L).card : ℝ)
  have hhosts :
      UniformThreeHalvesSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C) hosts := by
    simpa only [hosts] using
      RelationalHostsThreeHalves.card_relationalHosts_uniformThreeHalves_inRunLengthWindow
        hC
  have hquadratic :=
    shallowCoreQuadraticResidualMass_uniformNineteenEighths hC A
  apply
    UniformRationalPower.interpolate_threeHalves_nineteenEighths
      hhosts hquadratic
  refine ⟨2, ?_⟩
  intro N hN L _hrun
  have hlinearNonneg :
      0 ≤ shallowCoreLinearResidualMassTotal A N L := by
    simp [shallowCoreLinearResidualMassTotal, hN]
  have hquadraticNonneg :
      0 ≤ shallowCoreQuadraticResidualMassTotal A N L := by
    simp [shallowCoreQuadraticResidualMassTotal, hN]
  refine ⟨by positivity, hquadraticNonneg, hlinearNonneg, ?_⟩
  simpa only [hosts] using
    (shallowCoreLinearResidualMassTotal_le (A := A) hN)

/--
The Proposition 7.5 linear mass is uniformly negligible relative to the
quadratic scale:

`R_res = o_C(N²)`.
-/
theorem shallowCoreLinearResidualMass_uniformLittleOQuadratic
    {C : ℝ} (hC : 0 ≤ C) (A : ℕ) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (shallowCoreLinearResidualMassTotal A)
      (fun N _ => (N : ℝ) ^ 2) :=
  UniformRationalPower.thirtyOneSixteenths_littleO_quadratic
    (shallowCoreLinearResidualMass_uniformThirtyOneSixteenths
      hC A)

end

end PropositionSevenFiveCritical
end PaperC
