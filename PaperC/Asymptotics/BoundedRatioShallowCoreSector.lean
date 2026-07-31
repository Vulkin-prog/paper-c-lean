import PaperC.Asymptotics.BoundedRatioCorrectedDefectEnvelope
import PaperC.Asymptotics.BoundedRatioRelationalHostsCritical
import PaperC.Asymptotics.BoundedRatioSectorClosure
import PaperC.Asymptotics.BoundedRatioShallowCoreSigmaCritical
import PaperC.Asymptotics.ShallowCoreDensityCritical
import PaperC.Asymptotics.ShallowCoreRationalClosure
import PaperC.Combinatorics.BoundedRatioResidualMasses

set_option maxHeartbeats 2400000

/-!
# Closure of the bounded-ratio shallow-core sector

This module proves the bounded-ratio analogue of Proposition 7.5 and closes
the internal interface for Lemma 17.16.

For every endpoint `M ≤ κ₀N`, the quadratic mass of the literal third
sector is dominated by the common envelope

`(κ₀N)² · 4^maxσ · 4^maxD# · 4^⌊3(L+1)/16⌋`.

The first two exponential factors are uniformly subpolynomial, while the
density factor has rate `N^(3/8+o(1))`; hence the quadratic envelope has
rate `N^(19/8+o(1))`.  Cauchy--Schwarz against the common bounded-ratio
relational-host envelope then gives a linear envelope of rate
`N^(31/16+o(1))`, which is uniformly `o(N²)`.

All endpoint dependence is discharged by finite inclusions.  No new
asymptotic or arithmetic interface is introduced.
-/

namespace PaperC
namespace BoundedRatioShallowCoreSector

open BoundedRatioResidualMasses
open BoundedRatioShallowCoreSigmaCritical
open PropositionSixteenOne
open ResidualComponentCounts
open SectionElevenPartition
open ShallowCorePairs

noncomputable section

/-! ## Pointwise residual-exponent control -/

/--
The canonical inequality `τ ≤ D# + c#` on an arbitrary bounded-ratio
pair.  Its proof only uses that both retained windows lie below the cutoff
`M+L`.
-/
theorem pairTau_le_canonicalCorrected_add_residual
    {N M A L : ℕ} (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L) :
    PropositionSixteenOne.pairTau A hN pair ≤
      canonicalCorrectedDefectCount
          A pair.1.1 pair.1.2 L +
        canonicalResidualComponentCount
          A pair.1.1 pair.1.2 L := by
  have hp := mem_separatedBoundedRatioPairs.mp pair.2
  unfold PropositionSixteenOne.pairTau
  apply
    ResidualComponentCounts.residualTau_le_canonicalCorrected_add_residual
      (pair_coordinates_two_le hN pair).1
      (pair_coordinates_two_le hN pair).2
  · exact
      startWindow_le_boundedRatioCutoff
        hp.1 (le_refl L)
  · exact
      startWindow_le_boundedRatioCutoff
        hp.2.1 (le_refl L)

/--
Pointwise extraction of the systematic, corrected-defect and residual-core
factors for a bounded-ratio pair.
-/
theorem quadraticResidualWeight_le_systematic_mul_corrected_mul_component
    {N M A L : ℕ} (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L) :
    BoundedRatioResidualMasses.quadraticResidualWeight
        A hN pair ≤
      4 ^ PropositionSixteenOne.pairSigma A pair *
        4 ^ canonicalCorrectedDefectCount
            A pair.1.1 pair.1.2 L *
          4 ^ canonicalResidualComponentCount
            A pair.1.1 pair.1.2 L := by
  have htau :=
    pairTau_le_canonicalCorrected_add_residual
      (A := A) hN pair
  unfold BoundedRatioResidualMasses.quadraticResidualWeight
  calc
    4 ^ PropositionSixteenOne.pairSigma A pair *
          (4 ^ PropositionSixteenOne.pairTau A hN pair - 1) ≤
        4 ^ PropositionSixteenOne.pairSigma A pair *
          4 ^ PropositionSixteenOne.pairTau A hN pair :=
      Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    _ ≤
        4 ^ PropositionSixteenOne.pairSigma A pair *
          4 ^
            (canonicalCorrectedDefectCount
                A pair.1.1 pair.1.2 L +
              canonicalResidualComponentCount
                A pair.1.1 pair.1.2 L) :=
      Nat.mul_le_mul_left _
        (Nat.pow_le_pow_right (by norm_num) htau)
    _ =
        4 ^ PropositionSixteenOne.pairSigma A pair *
          4 ^ canonicalCorrectedDefectCount
              A pair.1.1 pair.1.2 L *
            4 ^ canonicalResidualComponentCount
              A pair.1.1 pair.1.2 L := by
      rw [pow_add]
      ring

/--
The density test in the literal third sector bounds its residual component
count by `⌊3(L+1)/16⌋`.
-/
theorem canonicalResidualComponentCount_le_envelope_of_mem_shallowCoreSector
    {κ₀ N M A L : ℕ} {hN : 2 ≤ N}
    {terminal : TerminalPredicateFamily}
    {pair : SeparatedBoundedRatioPair N M L}
    (hMκ : M ≤ κ₀ * N)
    (hpair :
      pair ∈ boundedRatioSectorPairs
        N M A L hN terminal .shallowCore) :
    canonicalResidualComponentCount
        A pair.1.1 pair.1.2 L ≤
      shallowCoreComponentEnvelope L := by
  have hbounding :=
    embedInBoundingBlock_mem_of_mem_shallowCoreSector
      hMκ hpair
  have hdensity :=
    (mem_boundedRatioShallowCorePairs.mp hbounding).2
  change
    HasCoreDensityAtMostThreeSixteenths
      A L pair.1.1 pair.1.2 at hdensity
  unfold HasCoreDensityAtMostThreeSixteenths at hdensity
  unfold shallowCoreComponentEnvelope
  apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 16)).2
  simpa only [Nat.mul_comm] using hdensity

/--
Each quadratic weight in the third sector is bounded by the three common
exponential factors.
-/
theorem quadraticResidualWeight_le_shallowCore_envelopes_of_mem
    {κ₀ N M A L : ℕ} {hN : 2 ≤ N}
    {terminal : TerminalPredicateFamily}
    {pair : SeparatedBoundedRatioPair N M L}
    (hMκ : M ≤ κ₀ * N)
    (hpair :
      pair ∈ boundedRatioSectorPairs
        N M A L hN terminal .shallowCore) :
    BoundedRatioResidualMasses.quadraticResidualWeight
        A hN pair ≤
      4 ^ maxBoundedRatioShallowCoreSigma κ₀ A N L *
        4 ^
          BoundedRatioCorrectedDefectEnvelope.maxCanonicalCorrectedDefectCount
            κ₀ A N L *
          4 ^ shallowCoreComponentEnvelope L := by
  have hraw :=
    quadraticResidualWeight_le_systematic_mul_corrected_mul_component
      (A := A) hN pair
  have hsigma :
      4 ^ PropositionSixteenOne.pairSigma A pair ≤
        4 ^ maxBoundedRatioShallowCoreSigma κ₀ A N L := by
    apply Nat.pow_le_pow_right (by norm_num)
    simpa only [PropositionSixteenOne.pairSigma] using
      canonicalPairSigma_le_max_of_mem_shallowCoreSector
        hMκ hpair
  have hcorrected :
      4 ^ canonicalCorrectedDefectCount
            A pair.1.1 pair.1.2 L ≤
        4 ^
          BoundedRatioCorrectedDefectEnvelope.maxCanonicalCorrectedDefectCount
            κ₀ A N L := by
    apply Nat.pow_le_pow_right (by norm_num)
    exact
      BoundedRatioCorrectedDefectEnvelope.canonicalCorrectedDefectCount_le_max
        hMκ pair.2
  have hcomponent :
      4 ^ canonicalResidualComponentCount
            A pair.1.1 pair.1.2 L ≤
        4 ^ shallowCoreComponentEnvelope L := by
    apply Nat.pow_le_pow_right (by norm_num)
    exact
      canonicalResidualComponentCount_le_envelope_of_mem_shallowCoreSector
        hMκ hpair
  exact hraw.trans
    (Nat.mul_le_mul
      (Nat.mul_le_mul hsigma hcorrected)
      hcomponent)

/-! ## A common quadratic envelope -/

/--
Natural-valued endpoint-independent quadratic envelope:

`(κ₀N)² · 4^maxσ · 4^maxD# · 4^⌊3(L+1)/16⌋`.
-/
noncomputable def boundedRatioShallowCoreQuadraticEnvelopeNat
    (κ₀ A N L : ℕ) : ℕ :=
  (κ₀ * N) ^ 2 *
    4 ^ maxBoundedRatioShallowCoreSigma κ₀ A N L *
      4 ^
        BoundedRatioCorrectedDefectEnvelope.maxCanonicalCorrectedDefectCount
          κ₀ A N L *
        4 ^ shallowCoreComponentEnvelope L

/-- Real-valued form of the common quadratic envelope. -/
noncomputable def boundedRatioShallowCoreQuadraticEnvelope
    (κ₀ A N L : ℕ) : ℝ :=
  (boundedRatioShallowCoreQuadraticEnvelopeNat
    κ₀ A N L : ℝ)

/--
Finite domination of the full quadratic mass of the literal third sector.
-/
theorem sectorQuadraticResidualMass_le_envelopeNat
    {κ₀ N M A L : ℕ} (hN : 2 ≤ N)
    (terminal : TerminalPredicateFamily)
    (hMκ : M ≤ κ₀ * N) :
    sectorQuadraticResidualMass
        (M := M) (L := L) A hN terminal .shallowCore ≤
      boundedRatioShallowCoreQuadraticEnvelopeNat
        κ₀ A N L := by
  classical
  let population :=
    boundedRatioSectorPairs
      N M A L hN terminal .shallowCore
  let E : ℕ :=
    4 ^ maxBoundedRatioShallowCoreSigma κ₀ A N L *
      4 ^
        BoundedRatioCorrectedDefectEnvelope.maxCanonicalCorrectedDefectCount
          κ₀ A N L *
        4 ^ shallowCoreComponentEnvelope L
  have hcard :
      population.card ≤ (κ₀ * N) ^ 2 :=
    card_population_le_ratio_sq population hMκ
  unfold sectorQuadraticResidualMass quadraticResidualMass
  calc
    (∑ pair ∈
          boundedRatioSectorPairs
            N M A L hN terminal .shallowCore,
        quadraticResidualWeight A hN pair) ≤
        ∑ _pair ∈
          boundedRatioSectorPairs
            N M A L hN terminal .shallowCore,
          E := by
      apply Finset.sum_le_sum
      intro pair hpair
      exact
        quadraticResidualWeight_le_shallowCore_envelopes_of_mem
          hMκ hpair
    _ =
        (boundedRatioSectorPairs
          N M A L hN terminal .shallowCore).card * E := by
      simp
    _ ≤ (κ₀ * N) ^ 2 * E := by
      exact Nat.mul_le_mul_right E hcard
    _ =
        boundedRatioShallowCoreQuadraticEnvelopeNat
          κ₀ A N L := by
      dsimp only [E]
      unfold boundedRatioShallowCoreQuadraticEnvelopeNat
      ring

/--
The same finite envelope dominates the active quadratic mass used by the
host interpolation.
-/
theorem activeSectorQuadraticResidualMass_le_envelopeNat
    {κ₀ N M A L : ℕ} (hN : 2 ≤ N)
    (terminal : TerminalPredicateFamily)
    (hMκ : M ≤ κ₀ * N) :
    activeSectorQuadraticResidualMass
        (M := M) (L := L) A hN terminal .shallowCore ≤
      boundedRatioShallowCoreQuadraticEnvelopeNat
        κ₀ A N L := by
  rw [← sectorQuadraticResidualMass_eq_active
    hN terminal .shallowCore]
  exact
    sectorQuadraticResidualMass_le_envelopeNat
      hN terminal hMκ

/-- Real form of active quadratic-mass domination. -/
theorem activeSectorQuadraticResidualMass_cast_le_envelope
    {κ₀ N M A L : ℕ} (hN : 2 ≤ N)
    (terminal : TerminalPredicateFamily)
    (hMκ : M ≤ κ₀ * N) :
    (activeSectorQuadraticResidualMass
        (M := M) (L := L) A hN terminal .shallowCore : ℝ) ≤
      boundedRatioShallowCoreQuadraticEnvelope
        κ₀ A N L := by
  unfold boundedRatioShallowCoreQuadraticEnvelope
  exact_mod_cast
    activeSectorQuadraticResidualMass_le_envelopeNat
      hN terminal hMκ

/-! ## The `N^(19/8+o(1))` quadratic rate -/

/--
The common quadratic envelope has the rate
`N^(19/8+o_{C,κ₀}(1))`.
-/
theorem boundedRatioShallowCoreQuadraticEnvelope_uniformNineteenEighths
    {C : ℝ} (hC : 0 ≤ C) (κ₀ A : ℕ) :
    UniformRationalPowerSubpolynomialOn 19 8
      (CriticalRunWindow.InRunLengthWindow C)
      (boundedRatioShallowCoreQuadraticEnvelope κ₀ A) := by
  let admissible :=
    CriticalRunWindow.InRunLengthWindow C
  let sigmaFactor : ℕ → ℕ → ℝ :=
    fun N L ↦
      (((4 ^
        maxBoundedRatioShallowCoreSigma
          κ₀ A N L : ℕ) : ℝ))
  let ratioSigmaFactor : ℕ → ℕ → ℝ :=
    fun N L ↦ (κ₀ : ℝ) ^ 2 * sigmaFactor N L
  let correctedFactor : ℕ → ℕ → ℝ :=
    fun N L ↦
      (((4 ^
        BoundedRatioCorrectedDefectEnvelope.maxCanonicalCorrectedDefectCount
          κ₀ A N L : ℕ) : ℝ))
  let densityFactor : ℕ → ℕ → ℝ :=
    fun _ L ↦
      (((4 ^ shallowCoreComponentEnvelope L : ℕ) : ℝ))
  have hsigma :
      UniformSubpolynomialOn admissible sigmaFactor := by
    simpa only [admissible, sigmaFactor] using
      four_pow_maxBoundedRatioShallowCoreSigma_uniformSubpolynomial
        hC κ₀ A
  have hratioSigma :
      UniformSubpolynomialOn admissible ratioSigmaFactor := by
    simpa only [ratioSigmaFactor] using
      ExpSqrtLog.uniformSubpolynomialOn_const_mul
        ((κ₀ : ℝ) ^ 2) hsigma
  have hcorrected :
      UniformSubpolynomialOn admissible correctedFactor := by
    simpa only [admissible, correctedFactor] using
      BoundedRatioCorrectedDefectEnvelope.four_pow_maxCanonicalCorrectedDefectCount_uniformSubpolynomial
        hC κ₀ A
  have hdensity :
      UniformRationalPowerSubpolynomialOn
        3 8 admissible densityFactor := by
    simpa only [admissible, densityFactor] using
      ShallowCoreDensityCritical.four_pow_shallowCoreComponentEnvelope_uniformThreeEighths
        C
  have hmodel :
      UniformRationalPowerSubpolynomialOn 19 8 admissible
        (fun N L ↦
          (N : ℝ) ^ 2 *
            ratioSigmaFactor N L *
            correctedFactor N L *
            densityFactor N L) :=
    UniformRationalPower.quadratic_mul_twoSubpolynomial_threeEighths
      hratioSigma hcorrected hdensity
  apply UniformRationalPower.mono hmodel
  refine ⟨0, ?_⟩
  intro N _hN L _hrun
  have heq :
      boundedRatioShallowCoreQuadraticEnvelope
          κ₀ A N L =
        (N : ℝ) ^ 2 *
          ratioSigmaFactor N L *
          correctedFactor N L *
          densityFactor N L := by
    unfold boundedRatioShallowCoreQuadraticEnvelope
      boundedRatioShallowCoreQuadraticEnvelopeNat
    dsimp only [ratioSigmaFactor, sigmaFactor,
      correctedFactor, densityFactor]
    push_cast
    ring
  rw [heq]

/-! ## Host interpolation and the `N^(31/16+o(1))` linear rate -/

/--
Common endpoint-independent linear envelope obtained by
Cauchy--Schwarz.
-/
noncomputable def boundedRatioShallowCoreLinearEnvelope
    (κ₀ A N L : ℕ) : ℝ :=
  Real.sqrt
      (BoundedRatioRelationalHostsCritical.boundedRelationalHostEnvelope
        κ₀ N L) *
    Real.sqrt
      (boundedRatioShallowCoreQuadraticEnvelope
        κ₀ A N L)

/--
The linear envelope has rate `N^(31/16+o_{C,κ₀}(1))`.
-/
theorem boundedRatioShallowCoreLinearEnvelope_uniformThirtyOneSixteenths
    {C : ℝ} (hC : 0 ≤ C) (κ₀ A : ℕ) :
    UniformRationalPowerSubpolynomialOn 31 16
      (CriticalRunWindow.InRunLengthWindow C)
      (boundedRatioShallowCoreLinearEnvelope κ₀ A) := by
  have hhosts :=
    BoundedRatioRelationalHostsCritical.boundedRelationalHostEnvelope_uniformThreeHalves
      hC κ₀
  have hquadratic :=
    boundedRatioShallowCoreQuadraticEnvelope_uniformNineteenEighths
      hC κ₀ A
  apply
    UniformRationalPower.interpolate_threeHalves_nineteenEighths
      hhosts hquadratic
  refine ⟨0, ?_⟩
  intro N _hN L _hrun
  have hhostNonneg :
      0 ≤
        BoundedRatioRelationalHostsCritical.boundedRelationalHostEnvelope
          κ₀ N L := by
    unfold
      BoundedRatioRelationalHostsCritical.boundedRelationalHostEnvelope
      BoundedRatioRelationalHostsCritical.boundedRelationalHostResidual
    positivity
  have hquadraticNonneg :
      0 ≤
        boundedRatioShallowCoreQuadraticEnvelope
          κ₀ A N L := by
    unfold boundedRatioShallowCoreQuadraticEnvelope
    positivity
  have hlinearNonneg :
      0 ≤
        boundedRatioShallowCoreLinearEnvelope
          κ₀ A N L := by
    unfold boundedRatioShallowCoreLinearEnvelope
    positivity
  refine
    ⟨hhostNonneg, hquadraticNonneg, hlinearNonneg, ?_⟩
  rfl

/--
Since `31/16 < 2`, the common linear envelope is uniformly negligible
relative to `N²`.
-/
theorem boundedRatioShallowCoreLinearEnvelope_uniformLittleOQuadratic
    {C : ℝ} (hC : 0 ≤ C) (κ₀ A : ℕ) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (boundedRatioShallowCoreLinearEnvelope κ₀ A)
      (fun N _ ↦ (N : ℝ) ^ 2) :=
  UniformRationalPower.thirtyOneSixteenths_littleO_quadratic
    (boundedRatioShallowCoreLinearEnvelope_uniformThirtyOneSixteenths
      hC κ₀ A)

/-! ## Finite linear domination and closure of Lemma 17.16 -/

/--
Once `L ≤ N`, every literal third-sector linear mass is bounded by the
common linear envelope.
-/
theorem sectorResidualMass_le_linearEnvelope
    {κ₀ N M A L : ℕ} (hN : 2 ≤ N)
    (terminal : TerminalPredicateFamily)
    (hNM : N ≤ M)
    (hMκ : M ≤ κ₀ * N)
    (hL : L ≤ N) :
    sectorResidualMass A terminal .shallowCore N M L ≤
      boundedRatioShallowCoreLinearEnvelope
        κ₀ A N L := by
  have hinterp :=
    BoundedRatioSectorClosure.sectorResidualMassNat_cast_le_host_sqrt_mul_quadratic_sqrt
      (M := M) (A := A) (L := L)
      hN terminal .shallowCore
  have hhost :=
    BoundedRatioRelationalHostsCritical.card_boundedRelationalHosts_cast_le_common
      hN hNM hMκ hL
  have hquadratic :=
    activeSectorQuadraticResidualMass_cast_le_envelope
      (A := A) (L := L) hN terminal hMκ
  simp only [sectorResidualMass, dif_pos hN]
  calc
    (sectorResidualMassNat
        (M := M) (L := L) A hN terminal .shallowCore : ℝ) ≤
        Real.sqrt
            ((BoundedRatioRelationalHosts.boundedRelationalHosts
              N M L).card : ℝ) *
          Real.sqrt
            (activeSectorQuadraticResidualMass
              (M := M) (L := L) A hN terminal
                .shallowCore : ℝ) :=
      hinterp
    _ ≤
        Real.sqrt
            (BoundedRatioRelationalHostsCritical.boundedRelationalHostEnvelope
              κ₀ N L) *
          Real.sqrt
            (boundedRatioShallowCoreQuadraticEnvelope
              κ₀ A N L) := by
      exact
        mul_le_mul
          (Real.sqrt_le_sqrt hhost)
          (Real.sqrt_le_sqrt hquadratic)
          (Real.sqrt_nonneg _)
          (Real.sqrt_nonneg _)
    _ =
        boundedRatioShallowCoreLinearEnvelope
          κ₀ A N L := rfl

/--
Lemma 17.16 is unconditional in the formal development: the literal
bounded-ratio shallow-core sector is uniformly `o(N²)`.
-/
theorem shallowCoreSectorStability
    {C : ℝ} (hC : 0 ≤ C)
    (κ₀ A : ℕ)
    (terminal : TerminalPredicateFamily) :
    ShallowCoreSectorStabilityStatement
      C κ₀ A terminal := by
  unfold ShallowCoreSectorStabilityStatement
  apply
    BoundedRatioSectorClosure.uniformLittleOInBoundedRatioWindow_of_nonnegative_envelope
      (boundedRatioShallowCoreLinearEnvelope_uniformLittleOQuadratic
        hC κ₀ A)
  · intro N M L
    unfold sectorResidualMass
    split <;> positivity
  · intro N L
    unfold boundedRatioShallowCoreLinearEnvelope
    positivity
  · obtain ⟨Nwindow, hNwindow⟩ :=
      CriticalRunWindow.firstMomentWindow_eventually hC
    have hupperNonneg :
        0 ≤ CriticalRunWindow.upperConstant :=
      (CriticalRunWindow.lowerConstant_pos.trans
        CriticalRunWindow.lowerConstant_lt_upperConstant).le
    obtain ⟨Nlength, hNlength⟩ :=
      ExpSqrtLog.linear_log_add_one_pow_le_nat_eventually
        CriticalRunWindow.upperConstant hupperNonneg 1 (by omega)
    refine
      ⟨max 2 (max Nwindow Nlength), ?_⟩
    intro N hN M L hNM hMκ hrun
    have hNtwo : 2 ≤ N :=
      (le_max_left 2 (max Nwindow Nlength)).trans hN
    have hNtail : max Nwindow Nlength ≤ N :=
      (le_max_right 2 (max Nwindow Nlength)).trans hN
    have hNwindowN : Nwindow ≤ N :=
      (le_max_left Nwindow Nlength).trans hNtail
    have hNlengthN : Nlength ≤ N :=
      (le_max_right Nwindow Nlength).trans hNtail
    have hfirst :=
      hNwindow N hNwindowN L hrun
    have hLplusTwoReal :
        (((L + 1) + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by
      simpa using
        hNlength N hNlengthN (L + 1)
          hfirst.1.2.2.2
    have hLplusTwo : (L + 1) + 1 ≤ N := by
      exact_mod_cast hLplusTwoReal
    have hbase : N ≤ M := by omega
    exact
      sectorResidualMass_le_linearEnvelope
        hNtwo terminal hbase hMκ (by omega)

end

end BoundedRatioShallowCoreSector
end PaperC
