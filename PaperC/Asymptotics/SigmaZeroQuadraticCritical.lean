import PaperC.Analysis.CriticalWeightedDefect
import PaperC.Analysis.ExponentialSeriesMajorant
import PaperC.Arithmetic.DyadicPrimeReciprocalSums
import PaperC.Asymptotics.CorrectedDefectEnvelope
import PaperC.Asymptotics.ExpLogDivLogLog
import PaperC.Asymptotics.LinearProduct
import PaperC.Combinatorics.PropositionSevenThreeSigmaZeroCover

set_option maxHeartbeats 1800000

/-!
# The `σ = 0` branch of Proposition 7.3

This module links the literal quadratic residual mass to the ambient
certificate cover.  It then inserts the reciprocal-prime-square tail and
the corrected-defect envelope, obtaining an explicit real majorant and the
uniform `N^(2+o_C(1))` conclusion in the critical run-length window.
-/

namespace PaperC
namespace SigmaZeroQuadraticCritical

open scoped BigOperators
open CanonicalResidualComponents
open RationalMassFinite
open ResidualComponentCounts
open ResidualMasses
open SigmaZeroAmbientCertificate

noncomputable section

/-- The literal active `σ=0` population, restricted to component count `r`. -/
noncomputable def literalSigmaZeroPairsOfCount
    (N A L r : ℕ) (hN : 2 ≤ N) :
    Finset (SeparatedDyadicPair N L) :=
  (ResidualMasses.sigmaZeroSmallProductPairs N A L hN).filter fun pair ↦
    canonicalResidualComponentCount A pair.1.1 pair.1.2 L = r

@[simp]
theorem mem_literalSigmaZeroPairsOfCount
    {N A L r : ℕ} {hN : 2 ≤ N}
    {pair : SeparatedDyadicPair N L} :
    pair ∈ literalSigmaZeroPairsOfCount N A L r hN ↔
      pair ∈ ResidualMasses.sigmaZeroSmallProductPairs N A L hN ∧
        canonicalResidualComponentCount A pair.1.1 pair.1.2 L = r := by
  simp [literalSigmaZeroPairsOfCount]

/--
The literal fixed-size population injects into the value-level population
covered by the ambient certificates.
-/
theorem card_literalSigmaZeroPairsOfCount_le_cover
    {N A L r : ℕ} (hN : 2 ≤ N) :
    (literalSigmaZeroPairsOfCount N A L r hN).card ≤
      (PropositionSevenThreeSigmaZeroCover.sigmaZeroSmallProductPairs
        N A L r hN).card := by
  let sourceValues : Finset (ℕ × ℕ) :=
    (literalSigmaZeroPairsOfCount N A L r hN).image Subtype.val
  have hsourceCard :
      sourceValues.card =
        (literalSigmaZeroPairsOfCount N A L r hN).card := by
    exact Finset.card_image_of_injective _ Subtype.val_injective
  have hsubset :
      sourceValues ⊆
        PropositionSevenThreeSigmaZeroCover.sigmaZeroSmallProductPairs
          N A L r hN := by
    intro pair hpair
    rw [show sourceValues =
      (literalSigmaZeroPairsOfCount N A L r hN).image Subtype.val by rfl,
      Finset.mem_image] at hpair
    obtain ⟨z, hz, rfl⟩ := hpair
    rw [PropositionSevenThreeSigmaZeroCover.sigmaZeroSmallProductPairs,
      Finset.mem_image]
    refine ⟨z, ?_, rfl⟩
    rw [PropositionSevenThreeSigmaZeroCover.mem_sigmaZeroSmallProductSubtypePairs]
    have hzData := mem_literalSigmaZeroPairsOfCount.mp hz
    have hzero :=
      (ResidualMasses.mem_sigmaZeroSmallProductPairs.mp hzData.1)
    have hactive :=
      ResidualMasses.mem_activeSmallProductPairs.mp hzero.1
    exact ⟨hzero.2, hactive.1, hzData.2⟩
  rw [← hsourceCard]
  exact Finset.card_le_card hsubset

/-- The canonical residual-component count fits the range `r < L+2`. -/
theorem componentCount_mem_range
    {N A L : ℕ} (hN : 2 ≤ N)
    (pair : SeparatedDyadicPair N L) :
    canonicalResidualComponentCount A pair.1.1 pair.1.2 L ∈
      Finset.range (L + 2) := by
  have hxy := pair_coordinates_two_le hN pair
  have hbudget :=
    canonicalCorrected_add_twice_residual_le
      A pair.1.1 pair.1.2 L (by omega) (by omega)
  rw [Finset.mem_range]
  omega

/--
Fiber decomposition of the certificate weight over the literal `σ=0`
population.
-/
theorem sum_four_pow_componentCount_eq_fibers
    {N A L : ℕ} (hN : 2 ≤ N) :
    (∑ pair ∈ ResidualMasses.sigmaZeroSmallProductPairs N A L hN,
        4 ^ canonicalResidualComponentCount
          A pair.1.1 pair.1.2 L) =
      ∑ r ∈ Finset.range (L + 2),
        4 ^ r * (literalSigmaZeroPairsOfCount N A L r hN).card := by
  classical
  let population :=
    ResidualMasses.sigmaZeroSmallProductPairs N A L hN
  let count : SeparatedDyadicPair N L → ℕ :=
    fun pair ↦
      canonicalResidualComponentCount A pair.1.1 pair.1.2 L
  have hmaps :
      ∀ pair ∈ population, count pair ∈ Finset.range (L + 2) :=
    fun pair _hpair ↦ componentCount_mem_range hN pair
  have hfiber :=
    Finset.sum_fiberwise_of_maps_to'
      hmaps (fun r : ℕ ↦ 4 ^ r)
  have hfiber_eq (r : ℕ) :
      population.filter (fun pair ↦ count pair = r) =
        literalSigmaZeroPairsOfCount N A L r hN := by
    ext pair
    simp only [Finset.mem_filter, literalSigmaZeroPairsOfCount,
      population, count]
  simp_rw [hfiber_eq] at hfiber
  convert hfiber.symm using 1
  simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, mul_comm]

/--
The literal certificate-weight sum is bounded by the ambient-cover
fixed-size populations.
-/
theorem sum_four_pow_componentCount_le_cover
    {N A L : ℕ} (hN : 2 ≤ N) :
    (∑ pair ∈ ResidualMasses.sigmaZeroSmallProductPairs N A L hN,
        4 ^ canonicalResidualComponentCount
          A pair.1.1 pair.1.2 L) ≤
      ∑ r ∈ Finset.range (L + 2),
        4 ^ r *
          (PropositionSevenThreeSigmaZeroCover.sigmaZeroSmallProductPairs
            N A L r hN).card := by
  rw [sum_four_pow_componentCount_eq_fibers hN]
  apply Finset.sum_le_sum
  intro r _hr
  exact Nat.mul_le_mul_left _
    (card_literalSigmaZeroPairsOfCount_le_cover
      (N := N) (A := A) (L := L) (r := r) hN)

/--
Exact finite bridge from the literal `σ=0` quadratic residual mass to the
summed ambient populations, with the manuscript's factor `4^Dmax`.
-/
theorem sigmaZeroQuadraticResidualMass_le_corrected_mul_cover
    {N A L : ℕ} (hN : 2 ≤ N) :
    sigmaZeroQuadraticResidualMass N A L hN ≤
      4 ^ CorrectedDefectEnvelope.maxCanonicalCorrectedDefectCount A N L *
        ∑ r ∈ Finset.range (L + 2),
          4 ^ r *
            (PropositionSevenThreeSigmaZeroCover.sigmaZeroSmallProductPairs
              N A L r hN).card := by
  let D :=
    CorrectedDefectEnvelope.maxCanonicalCorrectedDefectCount A N L
  have hpoint :
      ∀ pair ∈ ResidualMasses.sigmaZeroSmallProductPairs N A L hN,
        quadraticResidualWeight A hN pair ≤
          4 ^ D *
            4 ^ canonicalResidualComponentCount
              A pair.1.1 pair.1.2 L := by
    intro pair hpair
    have hzero :=
      (ResidualMasses.mem_sigmaZeroSmallProductPairs.mp hpair).2
    refine
      (quadraticResidualWeight_le_corrected_mul_certificate_of_sigma_eq_zero
        hN pair hzero).trans ?_
    exact Nat.mul_le_mul_right _
      (Nat.pow_le_pow_right (by norm_num)
        (CorrectedDefectEnvelope.canonicalCorrectedDefectCount_le_max
          pair.2))
  unfold sigmaZeroQuadraticResidualMass quadraticResidualMass
  calc
    (∑ pair ∈ ResidualMasses.sigmaZeroSmallProductPairs N A L hN,
        quadraticResidualWeight A hN pair) ≤
        ∑ pair ∈ ResidualMasses.sigmaZeroSmallProductPairs N A L hN,
          4 ^ D *
            4 ^ canonicalResidualComponentCount
              A pair.1.1 pair.1.2 L :=
      Finset.sum_le_sum hpoint
    _ =
        4 ^ D *
          ∑ pair ∈ ResidualMasses.sigmaZeroSmallProductPairs N A L hN,
            4 ^ canonicalResidualComponentCount
              A pair.1.1 pair.1.2 L := by
      rw [Finset.mul_sum]
    _ ≤
        4 ^ D *
          ∑ r ∈ Finset.range (L + 2),
            4 ^ r *
              (PropositionSevenThreeSigmaZeroCover.sigmaZeroSmallProductPairs
                N A L r hN).card := by
      simpa only [D] using
        Nat.mul_le_mul_left _
          (sum_four_pow_componentCount_le_cover hN)

/--
The ambient prime family inherits the uniform reciprocal-square tail above
the boundary scale `B=L+1`.
-/
theorem sum_ambientPrime_inv_sq_le
    {N L : ℕ} (hB : 4 ≤ L + 1) :
    (∑ p : AmbientPrime N L,
        1 / (ambientPrimeModulus p : ℚ) ^ 2) ≤
      28 / (((L + 1 : ℕ) : ℚ) *
        (Nat.log 2 (L + 1) : ℚ)) := by
  have hsubset :
      ambientPrimes N L ⊆
        DyadicPrimeReciprocalSums.dyadicPrimes
          (L + 1) (dyadicCutoff N L) := by
    intro p hp
    rw [DyadicPrimeReciprocalSums.mem_dyadicPrimes]
    have hpData := mem_ambientPrimes.mp hp
    refine ⟨hpData.1, hpData.2.1, ?_⟩
    have hBpos : 1 ≤ L + 1 := by omega
    have hpow :
        dyadicCutoff N L < 2 ^ dyadicCutoff N L :=
      Nat.lt_two_pow_self
    have hmul :
        2 ^ dyadicCutoff N L ≤
          (L + 1) * 2 ^ dyadicCutoff N L := by
      simpa only [one_mul] using
        Nat.mul_le_mul_right (2 ^ dyadicCutoff N L) hBpos
    exact hpData.2.2.trans (hpow.le.trans hmul)
  have htail :=
    DyadicPrimeReciprocalSums.sum_inv_sq_subset_dyadicPrimes_le
      (L + 1) (dyadicCutoff N L) (ambientPrimes N L) hB hsubset
  change
    (∑ p : {p : ℕ // p ∈ ambientPrimes N L},
        1 / (p.1 : ℚ) ^ 2) ≤ _
  rw [← Finset.sum_subtype
    (ambientPrimes N L) (fun _p ↦ Iff.rfl)
    (fun p ↦ 1 / (p : ℚ) ^ 2)]
  exact htail

/--
The summed ambient population cover after the prime-square estimate and
the finite exponential-series majorant.
-/
theorem sum_four_pow_mul_card_cover_cast_le_exp
    {N A L : ℕ} (hN : 2 ≤ N) (hB : 4 ≤ L + 1) :
    ((∑ r ∈ Finset.range (L + 2),
        (4 : ℚ) ^ r *
          ((PropositionSevenThreeSigmaZeroCover.sigmaZeroSmallProductPairs
            N A L r hN).card : ℚ) : ℚ) : ℝ) ≤
      ((((2 * N : ℕ) : ℚ) : ℝ) ^ 2) *
        Real.exp
          (112 * (L + 1 : ℕ) /
            (Nat.log 2 (L + 1) : ℝ)) := by
  let primeSum : ℚ :=
    ∑ p : AmbientPrime N L,
      1 / (ambientPrimeModulus p : ℚ) ^ 2
  let base : ℚ :=
    4 * (((L + 1) ^ 2 : ℕ) : ℚ) * primeSum
  have hfinite :=
    PropositionSevenThreeSigmaZeroCover.sum_four_pow_mul_card_sigmaZeroSmallProductPairs_le
      (A := A) (L := L) hN
  have hfiniteCast :
      ((∑ r ∈ Finset.range (L + 2),
          (4 : ℚ) ^ r *
            ((PropositionSevenThreeSigmaZeroCover.sigmaZeroSmallProductPairs
              N A L r hN).card : ℚ) : ℚ) : ℝ) ≤
        ((((2 * N : ℕ) : ℚ) : ℝ) ^ 2) *
          ((∑ r ∈ Finset.range (L + 2),
              base ^ r / (r.factorial : ℚ) : ℚ) : ℝ) := by
    dsimp only [base, primeSum]
    exact_mod_cast hfinite
  have hbase : 0 ≤ base := by
    dsimp only [base, primeSum]
    positivity
  have hseries :=
    ratCast_sum_range_pow_div_factorial_le_exp
      base hbase (L + 2)
  have htail :
      primeSum ≤
        28 / (((L + 1 : ℕ) : ℚ) *
          (Nat.log 2 (L + 1) : ℚ)) := by
    simpa only [primeSum] using
      sum_ambientPrime_inv_sq_le (N := N) hB
  have hBposQ : (0 : ℚ) < (L + 1 : ℕ) := by
    exact_mod_cast (show 0 < L + 1 by omega)
  have hlogPosQ : (0 : ℚ) < Nat.log 2 (L + 1) := by
    exact_mod_cast
      (show 0 < Nat.log 2 (L + 1) by
        have hlog :
            2 ≤ Nat.log 2 (L + 1) := by
          apply Nat.le_log_of_pow_le (by norm_num)
          simpa using hB
        omega)
  have hbaseTail :
      base ≤
        112 * (L + 1 : ℕ) /
          (Nat.log 2 (L + 1) : ℚ) := by
    calc
      base ≤
          4 * (((L + 1) ^ 2 : ℕ) : ℚ) *
            (28 / (((L + 1 : ℕ) : ℚ) *
              (Nat.log 2 (L + 1) : ℚ))) := by
        exact mul_le_mul_of_nonneg_left htail (by positivity)
      _ =
          112 * (L + 1 : ℕ) /
            (Nat.log 2 (L + 1) : ℚ) := by
        push_cast
        field_simp
        ring
  have hbaseTailReal :
      (base : ℝ) ≤
        112 * (L + 1 : ℕ) /
          (Nat.log 2 (L + 1) : ℝ) := by
    have hcast :
        (base : ℝ) ≤
          ((112 * (L + 1 : ℕ) /
            (Nat.log 2 (L + 1) : ℚ) : ℚ) : ℝ) :=
      (Rat.cast_le (K := ℝ)).2 hbaseTail
    push_cast at hcast
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_mul,
      Nat.cast_ofNat] using hcast
  calc
    ((∑ r ∈ Finset.range (L + 2),
        (4 : ℚ) ^ r *
          ((PropositionSevenThreeSigmaZeroCover.sigmaZeroSmallProductPairs
            N A L r hN).card : ℚ) : ℚ) : ℝ) ≤
        ((((2 * N : ℕ) : ℚ) : ℝ) ^ 2) *
          ((∑ r ∈ Finset.range (L + 2),
              base ^ r / (r.factorial : ℚ) : ℚ) : ℝ) :=
      hfiniteCast
    _ ≤
        ((((2 * N : ℕ) : ℚ) : ℝ) ^ 2) *
          Real.exp (base : ℝ) :=
      mul_le_mul_of_nonneg_left hseries (by positivity)
    _ ≤
        ((((2 * N : ℕ) : ℚ) : ℝ) ^ 2) *
          Real.exp
            (112 * (L + 1 : ℕ) /
              (Nat.log 2 (L + 1) : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr hbaseTailReal) (by positivity)

/--
Explicit real envelope for the exceptional quadratic branch:

`N² · 4 · 4^Dmax · exp(112 (L+1)/log₂(L+1))`.
-/
noncomputable def sigmaZeroQuadraticEnvelope
    (A N L : ℕ) : ℝ :=
  (N : ℝ) *
    ((N : ℝ) *
      (4 *
        (((4 ^ CorrectedDefectEnvelope.maxCanonicalCorrectedDefectCount
          A N L : ℕ) : ℝ)) *
        Real.exp
          (112 * (L + 1 : ℕ) /
            (Nat.log 2 (L + 1) : ℝ))))

/-- The explicit envelope in the factorization produced by Lemma 7.1. -/
theorem sigmaZeroQuadraticEnvelope_eq_corrected_mul_certificate
    (A N L : ℕ) :
    sigmaZeroQuadraticEnvelope A N L =
      (((4 ^ CorrectedDefectEnvelope.maxCanonicalCorrectedDefectCount
          A N L : ℕ) : ℝ)) *
        (((2 * N : ℕ) : ℝ) ^ 2 *
          Real.exp
            (112 * (L + 1 : ℕ) /
              (Nat.log 2 (L + 1) : ℝ))) := by
  unfold sigmaZeroQuadraticEnvelope
  push_cast
  ring

/--
Finite explicit estimate for the literal `σ=0` quadratic residual mass.
-/
theorem sigmaZeroQuadraticResidualMass_cast_le_envelope
    {N A L : ℕ} (hN : 2 ≤ N) (hB : 4 ≤ L + 1) :
    (sigmaZeroQuadraticResidualMass N A L hN : ℝ) ≤
      sigmaZeroQuadraticEnvelope A N L := by
  let D :=
    CorrectedDefectEnvelope.maxCanonicalCorrectedDefectCount A N L
  have hbridgeNat :=
    sigmaZeroQuadraticResidualMass_le_corrected_mul_cover
      (A := A) (L := L) hN
  have hbridgeRat :
      (sigmaZeroQuadraticResidualMass N A L hN : ℚ) ≤
        (4 ^ D : ℚ) *
          ∑ r ∈ Finset.range (L + 2),
            (4 : ℚ) ^ r *
              ((PropositionSevenThreeSigmaZeroCover.sigmaZeroSmallProductPairs
                N A L r hN).card : ℚ) := by
    exact_mod_cast hbridgeNat
  have hbridgeReal :
      (sigmaZeroQuadraticResidualMass N A L hN : ℝ) ≤
        (((4 ^ D : ℕ) : ℝ)) *
          ((∑ r ∈ Finset.range (L + 2),
              (4 : ℚ) ^ r *
                ((PropositionSevenThreeSigmaZeroCover.sigmaZeroSmallProductPairs
                  N A L r hN).card : ℚ) : ℚ) : ℝ) := by
    exact_mod_cast hbridgeRat
  have hcover :=
    sum_four_pow_mul_card_cover_cast_le_exp
      (N := N) (A := A) (L := L) hN hB
  calc
    (sigmaZeroQuadraticResidualMass N A L hN : ℝ) ≤
        (((4 ^ D : ℕ) : ℝ)) *
          ((∑ r ∈ Finset.range (L + 2),
              (4 : ℚ) ^ r *
                ((PropositionSevenThreeSigmaZeroCover.sigmaZeroSmallProductPairs
                  N A L r hN).card : ℚ) : ℚ) : ℝ) :=
      hbridgeReal
    _ ≤
        (((4 ^ D : ℕ) : ℝ)) *
          ((((2 * N : ℕ) : ℚ) : ℝ) ^ 2 *
            Real.exp
              (112 * (L + 1 : ℕ) /
                (Nat.log 2 (L + 1) : ℝ))) :=
      mul_le_mul_of_nonneg_left hcover (by positivity)
    _ = sigmaZeroQuadraticEnvelope A N L := by
      rw [sigmaZeroQuadraticEnvelope_eq_corrected_mul_certificate]
      simp only [D]
      push_cast
      ring

/--
Proof-independent real form of the literal exceptional mass.
-/
noncomputable def sigmaZeroQuadraticResidualMassTotal
    (A N L : ℕ) : ℝ :=
  if hN : 2 ≤ N then
    (sigmaZeroQuadraticResidualMass N A L hN : ℝ)
  else 0

/-- The explicit exceptional envelope is uniformly `N^(2+o_C(1))`. -/
theorem sigmaZeroQuadraticEnvelope_uniformQuadratic
    {C : ℝ} (hC : 0 ≤ C) (A : ℕ) :
    UniformRationalPowerSubpolynomialOn 2 1
      (CriticalRunWindow.InRunLengthWindow C)
      (sigmaZeroQuadraticEnvelope A) := by
  let admissible := CriticalRunWindow.InRunLengthWindow C
  let corrected : ℕ → ℕ → ℝ :=
    fun N L =>
      (((4 ^ CorrectedDefectEnvelope.maxCanonicalCorrectedDefectCount
          A N L : ℕ) : ℝ))
  let exponential : ℕ → ℕ → ℝ :=
    fun _ L =>
      Real.exp
        (112 * (L + 1 : ℕ) /
          (Nat.log 2 (L + 1) : ℝ))
  let loss : ℕ → ℕ → ℝ :=
    fun N L => 4 * (corrected N L * exponential N L)
  have hcorrected :
      UniformSubpolynomialOn admissible corrected := by
    simpa only [admissible, corrected] using
      CorrectedDefectEnvelope.four_pow_maxCanonicalCorrectedDefectCount_uniformSubpolynomial
        hC A
  have hexponential :
      UniformSubpolynomialOn admissible exponential := by
    simpa only [admissible, exponential] using
      ExpLogDivLogLog.criticalRunWindow_exp_height_div_natLog_uniformSubpolynomial
        hC (by norm_num : (0 : ℝ) ≤ 112)
  have hloss :
      UniformSubpolynomialOn admissible loss := by
    simpa only [loss] using
      ExpSqrtLog.uniformSubpolynomialOn_const_mul 4
        (ExpSqrtLog.uniformSubpolynomialOn_mul
          hcorrected hexponential)
  have hlinearN :
      UniformLinearSubpolynomialOn admissible
        (fun N _L => (N : ℝ)) := by
    apply UniformLinear.of_linear_mul_subpolynomial
      (ExpSqrtLog.uniformSubpolynomialOn_const admissible 1)
    refine ⟨0, ?_⟩
    intro N _hN L _hNL
    simp
  have hlinearLoss :
      UniformLinearSubpolynomialOn admissible
        (fun N L => (N : ℝ) * loss N L) := by
    apply UniformLinear.of_linear_mul_subpolynomial hloss
    refine ⟨0, ?_⟩
    intro N _hN L _hNL
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg N)]
  have hquadratic :=
    UniformLinear.mul hlinearN hlinearLoss
  have hfun :
      sigmaZeroQuadraticEnvelope A =
        fun (N L : ℕ) =>
          (N : ℝ) *
            ((N : ℝ) *
              (4 * (corrected N L * exponential N L))) := by
    funext N L
    dsimp only [sigmaZeroQuadraticEnvelope, corrected, exponential]
    ring
  rw [hfun]
  simpa only [admissible, mul_assoc] using hquadratic

/--
Fully quantified exceptional-branch conclusion of Proposition 7.3:

`Q_res^(σ=0, P#≤N) ≤ N^(2+o_C(1))`.
-/
theorem sigmaZeroQuadraticResidualMass_uniformQuadratic
    {C : ℝ} (hC : 0 ≤ C) (A : ℕ) :
    UniformRationalPowerSubpolynomialOn 2 1
      (CriticalRunWindow.InRunLengthWindow C)
      (sigmaZeroQuadraticResidualMassTotal A) := by
  have henvelope :=
    sigmaZeroQuadraticEnvelope_uniformQuadratic hC A
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
    sigmaZeroQuadraticResidualMass_cast_le_envelope
      (A := A) hNtwo hB
  have hleftNonneg :
      0 ≤ sigmaZeroQuadraticResidualMassTotal A N L := by
    simp [sigmaZeroQuadraticResidualMassTotal, hNtwo]
  have hrightNonneg :
      0 ≤ sigmaZeroQuadraticEnvelope A N L := by
    unfold sigmaZeroQuadraticEnvelope
    positivity
  rw [abs_of_nonneg hleftNonneg, abs_of_nonneg hrightNonneg]
  unfold sigmaZeroQuadraticResidualMassTotal
  rw [dif_pos hNtwo]
  exact hfinite

end

end SigmaZeroQuadraticCritical
end PaperC
