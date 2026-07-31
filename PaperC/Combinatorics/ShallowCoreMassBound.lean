import PaperC.Asymptotics.CorrectedDefectEnvelope
import PaperC.Combinatorics.ShallowCorePairs

set_option maxHeartbeats 1800000

/-!
# Finite mass bound for the shallow-core sector

This module isolates the finite combinatorial estimate needed for
Proposition 7.5.  On the literal shallow-core population, the three factors
in

`4^σ · 4^D# · 4^c#`

are bounded respectively by the finite maximum of `σ`, the ambient finite
maximum of the corrected defect, and the density envelope
`⌊3(L+1)/16⌋`.  Summing the resulting pointwise estimate over at most `N²`
ordered pairs gives the complete finite quadratic-mass bound.
-/

namespace PaperC
namespace ShallowCoreMassBound

open Affine
open RationalMassFinite
open ResidualComponentCounts
open ResidualMasses
open ShallowCorePairs

noncomputable section

/--
Pointwise extraction of the three uniform factors on the shallow-core
population:

`4^σ(4^τ-1) ≤ 4^maxσ · 4^maxD# · 4^⌊3(L+1)/16⌋`.
-/
theorem quadraticResidualWeight_le_shallowCoreEnvelopes_of_mem
    {N A L : ℕ} {hN : 2 ≤ N}
    {pair : SeparatedDyadicPair N L}
    (hpair : pair ∈ shallowCorePairs N A L hN) :
    quadraticResidualWeight A hN pair ≤
      4 ^ maxShallowCoreSigma N A L hN *
        4 ^ CorrectedDefectEnvelope.maxCanonicalCorrectedDefectCount
            A N L *
          4 ^ shallowCoreComponentEnvelope L := by
  have hraw :=
    quadraticResidualWeight_le_systematic_mul_corrected_mul_certificate
      (A := A) hN pair
  have hsigma :
      4 ^ pairSigma A pair ≤
        4 ^ maxShallowCoreSigma N A L hN :=
    Nat.pow_le_pow_right (by norm_num)
      (pairSigma_le_maxShallowCoreSigma hpair)
  have hcorrected :
      4 ^ canonicalCorrectedDefectCount
            A pair.1.1 pair.1.2 L ≤
        4 ^ CorrectedDefectEnvelope.maxCanonicalCorrectedDefectCount
            A N L :=
    Nat.pow_le_pow_right (by norm_num)
      (CorrectedDefectEnvelope.canonicalCorrectedDefectCount_le_max
        pair.2)
  have hcomponent :
      4 ^ canonicalResidualComponentCount
            A pair.1.1 pair.1.2 L ≤
        4 ^ shallowCoreComponentEnvelope L :=
    Nat.pow_le_pow_right (by norm_num)
      (canonicalResidualComponentCount_le_envelope_of_mem hpair)
  exact hraw.trans
    (Nat.mul_le_mul
      (Nat.mul_le_mul hsigma hcorrected)
      hcomponent)

/--
Complete finite quadratic-mass estimate for Proposition 7.5:

`Q_shallow ≤ N² · 4^maxσ · 4^maxD# · 4^⌊3(L+1)/16⌋`.

All four factors are literal natural numbers; no asymptotic hypothesis is
used in this statement.
-/
theorem shallowCoreQuadraticResidualMass_le
    {N A L : ℕ} (hN : 2 ≤ N) :
    shallowCoreQuadraticResidualMass N A L hN ≤
      N ^ 2 *
        4 ^ maxShallowCoreSigma N A L hN *
          4 ^ CorrectedDefectEnvelope.maxCanonicalCorrectedDefectCount
              A N L *
            4 ^ shallowCoreComponentEnvelope L := by
  classical
  let E :=
    4 ^ maxShallowCoreSigma N A L hN *
      4 ^ CorrectedDefectEnvelope.maxCanonicalCorrectedDefectCount
          A N L *
        4 ^ shallowCoreComponentEnvelope L
  unfold shallowCoreQuadraticResidualMass quadraticResidualMass
  calc
    (∑ pair ∈ shallowCorePairs N A L hN,
        quadraticResidualWeight A hN pair) ≤
        ∑ _pair ∈ shallowCorePairs N A L hN, E := by
      apply Finset.sum_le_sum
      intro pair hpair
      exact
        quadraticResidualWeight_le_shallowCoreEnvelopes_of_mem
          hpair
    _ =
        (shallowCorePairs N A L hN).card * E := by
      simp
    _ ≤ N ^ 2 * E :=
      Nat.mul_le_mul_right E (card_shallowCorePairs_le_sq hN)
    _ =
        N ^ 2 *
          4 ^ maxShallowCoreSigma N A L hN *
            4 ^ CorrectedDefectEnvelope.maxCanonicalCorrectedDefectCount
                A N L *
              4 ^ shallowCoreComponentEnvelope L := by
      dsimp only [E]
      ring

end

end ShallowCoreMassBound
end PaperC
