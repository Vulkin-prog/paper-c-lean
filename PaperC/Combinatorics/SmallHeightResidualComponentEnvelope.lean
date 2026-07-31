import PaperC.Analysis.CriticalWindowScale
import PaperC.Combinatorics.SmallHeightLargeProductPairs
import PaperC.Combinatorics.SmallHeightResidualPrimeSupport

set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000

/-!
# A finite component envelope for the small-height population

This module converts the manuscript's real height condition

`q ≤ sqrt (log B)`

to the integral cutoff used by the finite prime-counting API.  Above the
explicit threshold `8 ≤ B`, the comparison
`log B ≤ Nat.log 2 B` gives

`q ≤ Nat.sqrt (Nat.log 2 B)`.

The prime-support estimate for a selected canonical candidate then yields a
pair-independent finite envelope for its canonical residual component count.
No asymptotic estimate is used here.
-/

namespace PaperC
namespace SmallHeightResidualComponentEnvelope

open Affine
open Affine.CanonicalRationalCode
open RationalMassFinite
open ResidualComponentCounts
open ResidualMasses
open SmallHeightLargeProductPairs
open SmallHeightResidualPrimeSupport

noncomputable section

/-- Prime cutoff obtained by replacing the channel height by its integral maximum. -/
def smallHeightPrimeCutoff (L : ℕ) : ℕ :=
  4 * Nat.sqrt (Nat.log 2 (L + 1)) * (L + 1)

/-- Uniform finite envelope for the residual component count in Proposition 7.4. -/
def smallHeightResidualComponentEnvelope (L : ℕ) : ℕ :=
  2 + PrimesUpTo.count (smallHeightPrimeCutoff L)

/--
The literal real small-height condition implies the integral square-root
condition used in `smallHeightPrimeCutoff`.
-/
theorem height_le_natSqrt_natLog_of_le_realSqrt_realLog
    {B q : ℕ}
    (hB : 8 ≤ B)
    (hq :
      (q : ℝ) ≤ Real.sqrt (Real.log (B : ℝ))) :
    q ≤ Nat.sqrt (Nat.log 2 B) := by
  let n := Nat.log 2 B
  have hlog :
      Real.log (B : ℝ) ≤ (n : ℝ) := by
    simpa only [n] using
      CriticalWindowScale.real_log_le_nat_log_two hB
  have hsqrt :
      Real.sqrt (Real.log (B : ℝ)) ≤
        Real.sqrt (n : ℝ) :=
    Real.sqrt_le_sqrt hlog
  have hqSqrt :
      (q : ℝ) ≤ Real.sqrt (n : ℝ) :=
    hq.trans hsqrt
  have hnNonneg : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hqNonneg : (0 : ℝ) ≤ (q : ℝ) := by positivity
  have hsqrtNonneg : 0 ≤ Real.sqrt (n : ℝ) :=
    Real.sqrt_nonneg _
  have hsquareReal :
      ((q : ℝ) ^ 2) ≤ (n : ℝ) := by
    have hsqrtSq :
        (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) :=
      Real.sq_sqrt hnNonneg
    nlinarith
  have hsquareNat : q ^ 2 ≤ n := by
    exact_mod_cast hsquareReal
  exact (Nat.le_sqrt').2 hsquareNat

/-- The canonical residual component count attached to a separated pair. -/
noncomputable def pairResidualComponentCount
    {N L : ℕ} (A : ℕ)
    (pair : SeparatedDyadicPair N L) : ℕ :=
  canonicalResidualComponentCount
    A pair.1.1 pair.1.2 L

/-- Monotonicity of the repository's finite prime count. -/
theorem primeCount_mono
    {X Y : ℕ} (hXY : X ≤ Y) :
    PrimesUpTo.count X ≤ PrimesUpTo.count Y := by
  calc
    PrimesUpTo.count X =
        (DefectCounting.smallPrimesUpTo X).card :=
      PrimeCountBridge.count_eq_card_smallPrimesUpTo X
    _ ≤ (DefectCounting.smallPrimesUpTo Y).card := by
      apply Finset.card_le_card
      intro p hp
      rw [DefectCounting.mem_smallPrimesUpTo] at hp ⊢
      exact ⟨hp.1, hp.2.trans hXY⟩
    _ = PrimesUpTo.count Y :=
      (PrimeCountBridge.count_eq_card_smallPrimesUpTo Y).symm

/--
Every pair in the literal small-height large-product population has residual
component count bounded by the pair-independent finite envelope.
-/
theorem pairResidualComponentCount_le_envelope_of_mem
    {N A L : ℕ} {hN : 2 ≤ N}
    (hB : 8 ≤ L + 1)
    {pair : SeparatedDyadicPair N L}
    (hpair :
      pair ∈ smallHeightLargeProductPairs N A L hN) :
    pairResidualComponentCount A pair ≤
      smallHeightResidualComponentEnvelope L := by
  obtain ⟨c, hchoice, hqReal⟩ :=
    exists_smallHeight_candidate_of_mem hpair
  have hqNat :
      Nat.max c.1.1 c.1.2 ≤
        Nat.sqrt (Nat.log 2 (L + 1)) :=
    height_le_natSqrt_natLog_of_le_realSqrt_realLog
      hB hqReal
  have hcoordinates :=
    pair_coordinates_two_le hN pair
  have hcomponent :
      canonicalResidualComponentCount
          A pair.1.1 pair.1.2 L ≤
        2 +
          PrimesUpTo.count
            (4 * Nat.max c.1.1 c.1.2 * (L + 1)) :=
    canonicalResidualComponentCount_le_two_add_primeCount_of_choice
      hcoordinates.1 hcoordinates.2 c hchoice
  have hcutoff :
      4 * Nat.max c.1.1 c.1.2 * (L + 1) ≤
        smallHeightPrimeCutoff L := by
    unfold smallHeightPrimeCutoff
    exact
      Nat.mul_le_mul_right (L + 1)
        (Nat.mul_le_mul_left 4 hqNat)
  have hcount :
      PrimesUpTo.count
          (4 * Nat.max c.1.1 c.1.2 * (L + 1)) ≤
        PrimesUpTo.count (smallHeightPrimeCutoff L) :=
    primeCount_mono hcutoff
  unfold pairResidualComponentCount
  unfold smallHeightResidualComponentEnvelope
  exact hcomponent.trans (Nat.add_le_add_left hcount 2)

end

end SmallHeightResidualComponentEnvelope
end PaperC
