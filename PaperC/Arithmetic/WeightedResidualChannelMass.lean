import PaperC.Arithmetic.WeightedChannelMass
import Mathlib.Data.Real.Basic

/-!
# Aggregating a uniform residual estimate over rational channels

Proposition 7.3 treats a fixed nontrivial rational channel by CRT and then
sums the result with the systematic weight `4^σ`.  The correct outer object
is the channel mass of Lemma 5.5, not a count of start pairs which already
contains a volume factor.

This file records that finite aggregation exactly.  The residual factor may
depend on `(a,b,h)`; a uniform upper bound `K` factors out and leaves
`weightedChannelMass L`.
-/

namespace PaperC

open Finset
open scoped BigOperators

/--
Systematically weighted residual contribution of all nontrivial primitive
channels of length `L`.
-/
noncomputable def weightedResidualChannelMass
    (L : ℕ) (residual : ℕ → ℕ → ℤ → ℝ) : ℝ :=
  ∑ q ∈ Icc 2 L,
    ∑ c ∈ reducedRatiosAtHeight q,
      ∑ h ∈ nontrivialChannelHeights L c.1 c.2,
        ((4 ^ channelSigma L c.1 c.2 h : ℕ) : ℝ) *
          residual c.1 c.2 h

/--
A channel-uniform residual estimate factors against the exact systematic
mass from Lemma 5.5.
-/
theorem weightedResidualChannelMass_le
    (L : ℕ) (residual : ℕ → ℕ → ℤ → ℝ) (K : ℝ)
    (hresidual :
      ∀ q ∈ Icc 2 L,
      ∀ c ∈ reducedRatiosAtHeight q,
      ∀ h ∈ nontrivialChannelHeights L c.1 c.2,
        residual c.1 c.2 h ≤ K) :
    weightedResidualChannelMass L residual ≤
      (weightedChannelMass L : ℝ) * K := by
  calc
    weightedResidualChannelMass L residual ≤
        ∑ q ∈ Icc 2 L,
          ∑ c ∈ reducedRatiosAtHeight q,
            ∑ h ∈ nontrivialChannelHeights L c.1 c.2,
              ((4 ^ channelSigma L c.1 c.2 h : ℕ) : ℝ) * K := by
      unfold weightedResidualChannelMass
      apply Finset.sum_le_sum
      intro q hq
      apply Finset.sum_le_sum
      intro c hc
      apply Finset.sum_le_sum
      intro h hh
      exact mul_le_mul_of_nonneg_left
        (hresidual q hq c hc h hh) (by positivity)
    _ = (weightedChannelMass L : ℝ) * K := by
      simp [weightedChannelMass, weightedChannelMassAtHeight,
        weightedChannelMassAtPair, Finset.sum_mul]

end PaperC
