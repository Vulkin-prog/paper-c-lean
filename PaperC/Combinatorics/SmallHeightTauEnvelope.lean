import PaperC.Asymptotics.CorrectedDefectEnvelope
import PaperC.Combinatorics.SmallHeightResidualComponentEnvelope

/-!
# A finite residual-exponent envelope for the small-height population

For a separated pair, the finite quotient-core estimate gives

`τ ≤ D# + c#`.

On the small-height large-product population, the corrected defect `D#` is
bounded by its finite supremum over the dyadic block, while the residual
component count `c#` is bounded by the prime-support envelope.  Their sum is
therefore a pair-independent finite envelope for `τ`.

The final statements retain both useful forms of the resulting weight bound:
the literal factorization through the pairwise counts and the uniform
factorization through their two finite envelopes.
-/

namespace PaperC
namespace SmallHeightTauEnvelope

open Affine
open RationalMassFinite
open ResidualComponentCounts
open ResidualMasses
open SmallHeightLargeProductPairs
open SmallHeightResidualComponentEnvelope

noncomputable section

/--
Finite envelope for the residual exponent on the small-height population.

The first summand is the maximum corrected defect in the whole dyadic block;
the second is the uniform prime-support envelope for the residual components
of a small-height pair.
-/
def smallHeightTauEnvelope (A N L : ℕ) : ℕ :=
  CorrectedDefectEnvelope.maxCanonicalCorrectedDefectCount A N L +
    smallHeightResidualComponentEnvelope L

/--
Every member of the small-height large-product population has residual
exponent bounded by the finite envelope.
-/
theorem pairTau_le_smallHeightTauEnvelope_of_mem
    {N A L : ℕ} {hN : 2 ≤ N}
    (hB : 8 ≤ L + 1)
    {pair : SeparatedDyadicPair N L}
    (hpair :
      pair ∈ smallHeightLargeProductPairs N A L hN) :
    pairTau A hN pair ≤
      smallHeightTauEnvelope A N L := by
  have htau :=
    pairTau_le_canonicalCorrected_add_residual
      (A := A) hN pair
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
  exact htau.trans <| by
    unfold smallHeightTauEnvelope
    exact Nat.add_le_add hcorrected hresidual

/--
The pairwise quotient-core estimate in multiplicative weight form:
`4^τ ≤ 4^D# · 4^c#`.
-/
theorem four_pow_pairTau_le_canonicalCorrected_mul_residual
    {N A L : ℕ} (hN : 2 ≤ N)
    (pair : SeparatedDyadicPair N L) :
    4 ^ pairTau A hN pair ≤
      4 ^ canonicalCorrectedDefectCount
          A pair.1.1 pair.1.2 L *
        4 ^ canonicalResidualComponentCount
          A pair.1.1 pair.1.2 L := by
  have htau :=
    pairTau_le_canonicalCorrected_add_residual
      (A := A) hN pair
  calc
    4 ^ pairTau A hN pair ≤
        4 ^
          (canonicalCorrectedDefectCount
              A pair.1.1 pair.1.2 L +
            canonicalResidualComponentCount
              A pair.1.1 pair.1.2 L) :=
      Nat.pow_le_pow_right (by norm_num) htau
    _ =
        4 ^ canonicalCorrectedDefectCount
            A pair.1.1 pair.1.2 L *
          4 ^ canonicalResidualComponentCount
            A pair.1.1 pair.1.2 L := by
      rw [pow_add]

/-- The fourth power of the uniform exponent envelope factors as `4^D · 4^c`. -/
theorem four_pow_smallHeightTauEnvelope_eq
    (A N L : ℕ) :
    4 ^ smallHeightTauEnvelope A N L =
      4 ^ CorrectedDefectEnvelope.maxCanonicalCorrectedDefectCount
          A N L *
        4 ^ smallHeightResidualComponentEnvelope L := by
  rw [smallHeightTauEnvelope, pow_add]

/-- Uniform fourth-power bound for every small-height pair. -/
theorem four_pow_pairTau_le_four_pow_smallHeightTauEnvelope_of_mem
    {N A L : ℕ} {hN : 2 ≤ N}
    (hB : 8 ≤ L + 1)
    {pair : SeparatedDyadicPair N L}
    (hpair :
      pair ∈ smallHeightLargeProductPairs N A L hN) :
    4 ^ pairTau A hN pair ≤
      4 ^ smallHeightTauEnvelope A N L :=
  Nat.pow_le_pow_right (by norm_num)
    (pairTau_le_smallHeightTauEnvelope_of_mem hB hpair)

/--
Uniform factorized weight bound, exposing separately the corrected-defect
and residual-component envelopes.
-/
theorem four_pow_pairTau_le_maxCorrected_mul_residualEnvelope_of_mem
    {N A L : ℕ} {hN : 2 ≤ N}
    (hB : 8 ≤ L + 1)
    {pair : SeparatedDyadicPair N L}
    (hpair :
      pair ∈ smallHeightLargeProductPairs N A L hN) :
    4 ^ pairTau A hN pair ≤
      4 ^ CorrectedDefectEnvelope.maxCanonicalCorrectedDefectCount
          A N L *
        4 ^ smallHeightResidualComponentEnvelope L := by
  rw [← four_pow_smallHeightTauEnvelope_eq]
  exact
    four_pow_pairTau_le_four_pow_smallHeightTauEnvelope_of_mem
      hB hpair

end

end SmallHeightTauEnvelope
end PaperC
