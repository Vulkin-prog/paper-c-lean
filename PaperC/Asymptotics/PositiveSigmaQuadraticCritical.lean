import PaperC.Asymptotics.CorrectedDefectEnvelope
import PaperC.Asymptotics.LinearProduct
import PaperC.Asymptotics.ResidualCertificateMassCritical
import PaperC.Asymptotics.WeightedChannelMassCritical
import PaperC.Combinatorics.PositiveSigmaGlobalGrouping
import PaperC.Combinatorics.PositiveSigmaKeyMassBound

/-!
# The positive-systematic branch of Proposition 7.3

This file composes the finite fixed-channel CRT estimate, the systematic
channel mass, and the uniform envelope for the corrected defect.  It gives
the complete `N^(2+o_C(1))` upper bound for the active `P# ≤ N`, `σ>0`
quadratic residual population.
-/

namespace PaperC
namespace PositiveSigmaQuadraticCritical

open scoped BigOperators
open Affine
open RationalMassFinite
open ResidualComponentCounts
open ResidualMasses
open PositiveSigmaFixedChannelCover
open PositiveSigmaGlobalGrouping

noncomputable section

/--
Proof-independent real form of the positive-`σ` quadratic residual mass.
Below `N=2` it is set to zero; beyond that finite threshold it is literally
`positiveSigmaQuadraticResidualMass`.
-/
noncomputable def positiveSigmaQuadraticResidualMassTotal
    (A N L : ℕ) : ℝ :=
  if hN : 2 ≤ N then
    (positiveSigmaQuadraticResidualMass N A L hN : ℝ)
  else 0

/--
The summed fixed-channel certificate mass is bounded by the systematic
channel mass times the uniform one-channel residual envelope.
-/
theorem positiveSigmaChannelCertificateMass_cast_le
    {N A L : ℕ} (hN : 2 ≤ N) (hB : 4 ≤ L + 1) :
    (positiveSigmaChannelCertificateMass N A L hN : ℝ) ≤
      (((L + 2 : ℕ) : ℝ) * (weightedChannelMass L : ℝ)) *
        residualCertificateChannelEnvelope N L := by
  simpa only [Nat.cast_add, Nat.cast_ofNat] using
    PositiveSigmaKeyMassBound.positiveSigmaChannelCertificateMass_cast_le
      hN hB

/--
Finite global envelope for the positive-systematic quadratic mass.
-/
theorem positiveSigmaQuadraticResidualMass_cast_le_envelope
    {N A L : ℕ} (hN : 2 ≤ N) (hB : 4 ≤ L + 1) :
    (positiveSigmaQuadraticResidualMass N A L hN : ℝ) ≤
      (((4 ^ CorrectedDefectEnvelope.maxCanonicalCorrectedDefectCount
          A N L : ℕ) : ℝ)) *
        ((((L + 2 : ℕ) : ℝ) * (weightedChannelMass L : ℝ)) *
          residualCertificateChannelEnvelope N L) := by
  let D :=
    CorrectedDefectEnvelope.maxCanonicalCorrectedDefectCount A N L
  have hgroup :=
    positiveSigmaQuadraticResidualMass_le_channelCertificateMass
      (D := D) hN
      (fun pair _hpair =>
        CorrectedDefectEnvelope.canonicalCorrectedDefectCount_le_max
          pair.2)
  have hgroupCast :
      (positiveSigmaQuadraticResidualMass N A L hN : ℝ) ≤
        (((4 ^ D : ℕ) : ℝ)) *
          (positiveSigmaChannelCertificateMass N A L hN : ℝ) := by
    exact_mod_cast hgroup
  calc
    (positiveSigmaQuadraticResidualMass N A L hN : ℝ) ≤
        (((4 ^ D : ℕ) : ℝ)) *
          (positiveSigmaChannelCertificateMass N A L hN : ℝ) :=
      hgroupCast
    _ ≤
        (((4 ^ D : ℕ) : ℝ)) *
          ((((L + 2 : ℕ) : ℝ) * (weightedChannelMass L : ℝ)) *
            residualCertificateChannelEnvelope N L) :=
      mul_le_mul_of_nonneg_left
        (positiveSigmaChannelCertificateMass_cast_le hN hB)
        (by positivity)

/--
Multiplication by a uniformly subpolynomial factor preserves the quantified
`N^(2+o(1))` convention.
-/
theorem uniformQuadratic_mul_subpolynomial
    {admissible : ℕ → ℕ → Prop}
    {f s : ℕ → ℕ → ℝ}
    (hf :
      UniformRationalPowerSubpolynomialOn 2 1 admissible f)
    (hs : UniformSubpolynomialOn admissible s) :
    UniformRationalPowerSubpolynomialOn 2 1 admissible
      (fun N L => s N L * f N L) := by
  intro k hk
  have htwok : 0 < 2 * k := Nat.mul_pos (by omega) hk
  obtain ⟨Nf, hNf⟩ := hf (2 * k) htwok
  obtain ⟨Ns, hNs⟩ := hs (2 * k) htwok
  refine ⟨max Nf Ns, ?_⟩
  intro N hN L hNL
  have hfBound :=
    hNf N ((le_max_left _ _).trans hN) L hNL
  have hfBound' :
      |f N L| ^ (2 * k) ≤
        (N : ℝ) ^ (2 * (2 * k) + 1) := by
    simpa only [one_mul] using hfBound
  have hsBound :=
    hNs N ((le_max_right _ _).trans hN) L hNL
  rw [one_mul]
  have hNnonneg : 0 ≤ (N : ℝ) := by positivity
  have hsq :
      (|s N L * f N L| ^ k) ^ 2 ≤
        (((N : ℝ) ^ (2 * k + 1)) ^ 2) := by
    calc
      (|s N L * f N L| ^ k) ^ 2 =
          (|s N L| ^ k) ^ 2 * (|f N L| ^ k) ^ 2 := by
        rw [abs_mul, mul_pow, mul_pow]
      _ = |s N L| ^ (2 * k) * |f N L| ^ (2 * k) := by
        simp only [← pow_mul, Nat.mul_comm]
      _ ≤ (N : ℝ) * (N : ℝ) ^ (2 * (2 * k) + 1) :=
        mul_le_mul hsBound hfBound' (by positivity) hNnonneg
      _ = (((N : ℝ) ^ (2 * k + 1)) ^ 2) := by
        rw [← pow_mul]
        ring_nf
  exact
    (sq_le_sq₀ (by positivity)
      (show 0 ≤ (N : ℝ) ^ (2 * k + 1) by positivity)).mp hsq

/-- The elementary factor `L+2` is subpolynomial in the run-length window. -/
theorem runLengthAddTwo_uniformSubpolynomial
    {C : ℝ} (hC : 0 ≤ C) :
    UniformSubpolynomialOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun _ L => ((L + 2 : ℕ) : ℝ)) := by
  have hupperNonneg : 0 ≤ CriticalRunWindow.upperConstant :=
    (CriticalRunWindow.lowerConstant_pos.trans
      CriticalRunWindow.lowerConstant_lt_upperConstant).le
  obtain ⟨Nwindow, hwindow⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  let admissibleLarge : ℕ → ℕ → Prop :=
    fun N L =>
      CriticalRunWindow.InRunLengthWindow C N L ∧ Nwindow ≤ N
  have hlarge :
      UniformSubpolynomialOn admissibleLarge
        (fun _ L => ((L + 2 : ℕ) : ℝ)) := by
    have hheight :
        ∀ N L, admissibleLarge N L →
          ((L + 1 : ℕ) : ℝ) ≤
            CriticalRunWindow.upperConstant * Real.log N := by
      intro N L hNL
      exact (hwindow N hNL.2 L hNL.1).1.2.2.2
    have hcore :=
      ExpSqrtLog.uniformSubpolynomialOn_linear_log_add_one
        admissibleLarge (fun _ L => L + 1)
        CriticalRunWindow.upperConstant hupperNonneg hheight
    have hfun :
        (fun (_ : ℕ) L => ((L + 2 : ℕ) : ℝ)) =
          (fun (_ : ℕ) L => (((L + 1 : ℕ) : ℝ) + 1)) := by
      funext _ L
      push_cast
      ring
    rw [hfun]
    exact hcore
  intro k hk
  obtain ⟨Nlarge, hNlarge⟩ := hlarge k hk
  refine ⟨max Nwindow Nlarge, ?_⟩
  intro N hN L hrun
  exact
    hNlarge N ((le_max_right _ _).trans hN) L
      ⟨hrun, (le_max_left _ _).trans hN⟩

/--
Fully quantified positive-`σ` conclusion of Proposition 7.3:

`Q_res^(σ>0, P#≤N) ≤ N^(2+o_C(1))`.
-/
theorem positiveSigmaQuadraticResidualMass_uniformQuadratic
    {C : ℝ} (hC : 0 ≤ C) (A : ℕ) :
    UniformRationalPowerSubpolynomialOn 2 1
      (CriticalRunWindow.InRunLengthWindow C)
      (fun N L =>
        positiveSigmaQuadraticResidualMassTotal A N L) := by
  let admissible := CriticalRunWindow.InRunLengthWindow C
  let corrected : ℕ → ℕ → ℝ :=
    fun N L =>
      (((4 ^ CorrectedDefectEnvelope.maxCanonicalCorrectedDefectCount
          A N L : ℕ) : ℝ))
  let channelResidual : ℕ → ℕ → ℝ :=
    fun N L =>
      (weightedChannelMass L : ℝ) *
        residualCertificateChannelEnvelope N L
  let subfactor : ℕ → ℕ → ℝ :=
    fun N L => corrected N L * ((L + 2 : ℕ) : ℝ)
  have hcorrected :
      UniformSubpolynomialOn admissible corrected := by
    simpa only [admissible, corrected] using
      CorrectedDefectEnvelope.four_pow_maxCanonicalCorrectedDefectCount_uniformSubpolynomial
        hC A
  have hchannel :
      UniformLinearSubpolynomialOn admissible
        (fun _ L => (weightedChannelMass L : ℝ)) := by
    simpa only [admissible] using
      WeightedChannelMassCritical.weightedChannelMass_uniformLinearSubpolynomial
        hC
  have hresidual :
      UniformLinearSubpolynomialOn admissible
        residualCertificateChannelEnvelope := by
    simpa only [admissible] using
      residualCertificateChannelEnvelope_uniformLinear hC
  have hchannelResidual :
      UniformRationalPowerSubpolynomialOn 2 1
        admissible channelResidual := by
    simpa only [channelResidual] using
      UniformLinear.mul hchannel hresidual
  have hlength :
      UniformSubpolynomialOn admissible
        (fun _ L => ((L + 2 : ℕ) : ℝ)) := by
    simpa only [admissible] using
      runLengthAddTwo_uniformSubpolynomial hC
  have hsubfactor :
      UniformSubpolynomialOn admissible subfactor := by
    simpa only [subfactor] using
      ExpSqrtLog.uniformSubpolynomialOn_mul hcorrected hlength
  have henvelope :
      UniformRationalPowerSubpolynomialOn 2 1 admissible
        (fun N L => subfactor N L * channelResidual N L) :=
    uniformQuadratic_mul_subpolynomial
      hchannelResidual hsubfactor
  obtain ⟨Nwindow, hwindow⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  obtain ⟨Nadm, hadm⟩ :=
    CriticalWeightedDefect.admissible_eventually
      CriticalRunWindow.lowerConstant_pos
      CriticalRunWindow.lowerConstant_lt_upperConstant
  apply UniformRationalPower.mono henvelope
  refine ⟨max Nwindow Nadm, ?_⟩
  intro N hN L hrun
  have hfirst :=
    hwindow N ((le_max_left _ _).trans hN) L hrun
  have hadmissible :=
    hadm N ((le_max_right _ _).trans hN)
      (L + 1) hfirst.1
  have hNtwo : 2 ≤ N := hadmissible.2.1
  have hB : 4 ≤ L + 1 :=
    CriticalWindowParameters.four_le_H_of_criticalWindow
      hfirst.1 hadmissible.2.2.1
  have hfinite :=
    positiveSigmaQuadraticResidualMass_cast_le_envelope
      (A := A) hNtwo hB
  have hleftNonneg :
      0 ≤ positiveSigmaQuadraticResidualMassTotal A N L := by
    simp [positiveSigmaQuadraticResidualMassTotal, hNtwo]
  have hrightNonneg :
      0 ≤ subfactor N L * channelResidual N L := by
    dsimp only [subfactor, corrected, channelResidual]
    unfold residualCertificateChannelEnvelope
    positivity
  rw [abs_of_nonneg hleftNonneg, abs_of_nonneg hrightNonneg]
  simp only [positiveSigmaQuadraticResidualMassTotal, hNtwo,
    subfactor, corrected, channelResidual]
  calc
    (positiveSigmaQuadraticResidualMass N A L hNtwo : ℝ) ≤
        (((4 ^ CorrectedDefectEnvelope.maxCanonicalCorrectedDefectCount
            A N L : ℕ) : ℝ)) *
          ((((L + 2 : ℕ) : ℝ) * (weightedChannelMass L : ℝ)) *
            residualCertificateChannelEnvelope N L) :=
      hfinite
    _ =
        ((((4 ^ CorrectedDefectEnvelope.maxCanonicalCorrectedDefectCount
              A N L : ℕ) : ℝ)) *
            ((L + 2 : ℕ) : ℝ)) *
          ((weightedChannelMass L : ℝ) *
            residualCertificateChannelEnvelope N L) := by
      ring

end

end PositiveSigmaQuadraticCritical
end PaperC
