import PaperC.Asymptotics.CriticalChannelPowers
import PaperC.Asymptotics.RationalPowers
import PaperC.Combinatorics.ShallowCorePairs
import Mathlib.Data.Real.Archimedean

/-!
# The shallow-core density factor in the critical window

The residual-component density condition in Proposition 7.5 gives the
literal factor

`4^⌊3(L+1)/16⌋`.

The integer inequality

`16 * ⌊3(L+1)/16⌋ ≤ 3(L+1)`

shows that its eighth power is at most `(2^(L+1))³`.  In the critical
run-length window, `2^L` is bounded by a fixed multiple of `N`; hence this
factor is uniformly `N^(3/8+o_C(1))`.
-/

namespace PaperC
namespace ShallowCoreDensityCritical

open ShallowCorePairs

noncomputable section

/--
The rounded density exponent satisfies the division-free inequality used in
the manuscript:

`16 * ⌊3(L+1)/16⌋ ≤ 3(L+1)`.
-/
theorem sixteen_mul_shallowCoreComponentEnvelope_le
    (L : ℕ) :
    16 * shallowCoreComponentEnvelope L ≤ 3 * (L + 1) := by
  unfold shallowCoreComponentEnvelope
  simpa only [Nat.mul_comm] using
    (Nat.mul_div_le (3 * (L + 1)) 16)

/--
Finite eighth-power form of the density estimate:

`(4^⌊3(L+1)/16⌋)^8 ≤ (2^(L+1))³`.
-/
theorem shallowCoreDensity_eighth_le_runLength_cube
    (L : ℕ) :
    (4 ^ shallowCoreComponentEnvelope L) ^ 8 ≤
      (2 ^ (L + 1)) ^ 3 := by
  have hexponent :=
    sixteen_mul_shallowCoreComponentEnvelope_le L
  calc
    (4 ^ shallowCoreComponentEnvelope L) ^ 8 =
        2 ^ (16 * shallowCoreComponentEnvelope L) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num,
        ← pow_mul, ← pow_mul]
      congr 1
      omega
    _ ≤ 2 ^ (3 * (L + 1)) :=
      Nat.pow_le_pow_right (by norm_num) hexponent
    _ = (2 ^ (L + 1)) ^ 3 := by
      rw [show 3 * (L + 1) = (L + 1) * 3 by omega,
        pow_mul]

/--
In the critical window the eighth power of the density factor is bounded by
a fixed multiple of `N³`.
-/
theorem shallowCoreDensity_eighth_cast_le
    {C : ℝ} {N L : ℕ}
    (hN : 0 < N)
    (hrun : CriticalRunWindow.InRunLengthWindow C N L) :
    (((4 ^ shallowCoreComponentEnvelope L : ℕ) : ℝ)) ^ 8 ≤
      (8 * (CriticalRunWindow.balanceConstant C) ^ 3) *
        (N : ℝ) ^ 3 := by
  have hfinite :=
    shallowCoreDensity_eighth_le_runLength_cube L
  have hfiniteCast :
      (((4 ^ shallowCoreComponentEnvelope L : ℕ) : ℝ)) ^ 8 ≤
        (((2 ^ (L + 1) : ℕ) : ℝ)) ^ 3 := by
    exact_mod_cast hfinite
  have hcritical :=
    CriticalChannelPowers.two_pow_runLength_le_balance_mul hN hrun
  have htwoSucc :
      (((2 ^ (L + 1) : ℕ) : ℝ)) ≤
        2 * (CriticalRunWindow.balanceConstant C * (N : ℝ)) := by
    calc
      (((2 ^ (L + 1) : ℕ) : ℝ)) =
          2 * (2 : ℝ) ^ L := by
        push_cast
        rw [pow_succ]
        ring
      _ ≤ 2 * (CriticalRunWindow.balanceConstant C * (N : ℝ)) :=
        mul_le_mul_of_nonneg_left hcritical (by norm_num)
  calc
    (((4 ^ shallowCoreComponentEnvelope L : ℕ) : ℝ)) ^ 8 ≤
        (((2 ^ (L + 1) : ℕ) : ℝ)) ^ 3 :=
      hfiniteCast
    _ ≤
        (2 * (CriticalRunWindow.balanceConstant C * (N : ℝ))) ^ 3 :=
      pow_le_pow_left₀ (by positivity) htwoSucc 3
    _ =
        (8 * (CriticalRunWindow.balanceConstant C) ^ 3) *
          (N : ℝ) ^ 3 := by
      ring

/--
The shallow-core residual-component factor has the uniform rational-power
rate

`4^⌊3(L+1)/16⌋ = N^(3/8+o_C(1))`.

No sign assumption on `C` is required: its only contribution is the fixed
positive constant `exp(C log 2)`.
-/
theorem four_pow_shallowCoreComponentEnvelope_uniformThreeEighths
    (C : ℝ) :
    UniformRationalPowerSubpolynomialOn 3 8
      (CriticalRunWindow.InRunLengthWindow C)
      (fun _ L =>
        (((4 ^ shallowCoreComponentEnvelope L : ℕ) : ℝ))) := by
  intro k hk
  let D : ℝ :=
    8 * (CriticalRunWindow.balanceConstant C) ^ 3
  have hDnonneg : 0 ≤ D := by
    dsimp only [D]
    exact mul_nonneg (by norm_num)
      (pow_nonneg
        (CriticalRunWindow.balanceConstant_nonneg C) 3)
  obtain ⟨ND : ℕ, hND⟩ :=
    exists_nat_gt (D ^ k)
  refine ⟨max ND 1, ?_⟩
  intro N hN L hrun
  have hNDN : ND ≤ N :=
    (le_max_left ND 1).trans hN
  have hNone : 1 ≤ N :=
    (le_max_right ND 1).trans hN
  have hNpos : 0 < N := by omega
  have hDpow :
      D ^ k ≤ (N : ℝ) :=
    hND.le.trans (by exact_mod_cast hNDN)
  have heighth :
      (((4 ^ shallowCoreComponentEnvelope L : ℕ) : ℝ)) ^ 8 ≤
        D * (N : ℝ) ^ 3 := by
    simpa only [D] using
      shallowCoreDensity_eighth_cast_le hNpos hrun
  rw [abs_of_nonneg
      (show 0 ≤
        (((4 ^ shallowCoreComponentEnvelope L : ℕ) : ℝ)) by
          positivity)]
  calc
    (((4 ^ shallowCoreComponentEnvelope L : ℕ) : ℝ)) ^ (8 * k) =
        ((((4 ^ shallowCoreComponentEnvelope L : ℕ) : ℝ)) ^ 8) ^ k := by
      rw [pow_mul]
    _ ≤ (D * (N : ℝ) ^ 3) ^ k :=
      pow_le_pow_left₀ (by positivity) heighth k
    _ = D ^ k * (N : ℝ) ^ (3 * k) := by
      rw [mul_pow, ← pow_mul]
    _ ≤ (N : ℝ) * (N : ℝ) ^ (3 * k) :=
      mul_le_mul hDpow (le_refl _)
        (by positivity) (Nat.cast_nonneg N)
    _ = (N : ℝ) ^ (3 * k + 1) := by
      rw [pow_succ, mul_comm]

end

end ShallowCoreDensityCritical
end PaperC
