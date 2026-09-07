import PaperCV282.BadStartRankin
import PaperCV282.PrimeEulerCutoff
import PaperCV282.PrimeEulerPNT
import PaperCV282.SaddleParameters

/-!
# From the source-form PNT remainder to actual saddle-cost deletion bounds

The remainder here is an explicit expression retaining the fixed lower
split point. It is not asserted to be o(nu). The only prime-distribution
hypothesis is on pi(t)-Ei(log t); the weighted prime sum and every actual
bad-start count are proved consequences.
-/

namespace PaperC.V282.BadStartRankinSaddle

open DefectiveRankinCount PrimeEulerRankin PrimeEulerCutoff PrimeEulerPNT
open BadStartRankin MaskedArithmeticGeometry ExponentialIntegral SaddleBranch SaddleParameters

noncomputable section

/-- The explicit split-point remainder, before proving uniform little-oh estimates. -/
def primeSplitRemainder (A w zeta eta : ℝ) : ℝ :=
  rankinPrimeSum ⌊A⌋₊ zeta - exponentialIntegral (zeta * Real.log A) +
    eta * ((Real.exp w) ^ zeta / w + A ^ zeta / Real.log A +
      (1 - zeta) * (exponentialIntegral (zeta * w) - exponentialIntegral (zeta * Real.log A)))

/-- The exact logarithmic Euler sum is controlled by Ei with an explicit, proved remainder. -/
theorem logSum_floor_exp_le_Ei_add_remainder {A w zeta eta : ℝ}
    (hA : 1 < A) (hAw : A ≤ Real.exp w) (hzeta : 0 < zeta) (hzetaOne : zeta ≤ 1)
    (hR : ∀ t ∈ Set.Icc A (Real.exp w), |primeCountingRemainder t| ≤ eta * t / Real.log t) :
    rankinLogSum ⌊Real.exp w⌋₊ zeta ≤ exponentialIntegral (zeta * w) + primeSplitRemainder A w zeta eta := by
  have he := weighted_prime_error_le hA hAw hzeta hzetaOne hR
  simp only [Real.log_exp] at he
  have hup := (le_abs_self _).trans he
  have hlog := rankinLogSum_le_primeSum ⌊Real.exp w⌋₊ zeta
  unfold primeSplitRemainder
  linarith

/-- An unconditional explicit cutoff bound, using only the proved prime-harmonic envelope. -/
theorem normalized_fullBadMask_floor_exp_le_loglog {N L : ℕ} (hN : 2 ≤ N) (hL : L ≤ N)
    (mask : Finset ℕ) {w zeta : ℝ} (hw : Real.log 4 ≤ w)
    (hzeta : 0 ≤ zeta) (hzetaHalf : zeta ≤ 1 / 2) :
    ((fullBadMask N L ⌊Real.exp w⌋₊ mask).card : ℝ) / N ≤
      3 * (L + 1 : ℝ) * Real.exp (-zeta * Real.log (3 * N : ℕ) +
        120 * Real.exp (w * zeta) * Real.log (w + Real.log 3)) := by
  have hNr : (0 : ℝ) < (3 * N : ℕ) := by exact_mod_cast (show 0 < 3 * N by omega)
  calc
    _ ≤ 3 * (L + 1 : ℝ) * ((3 * N : ℕ) : ℝ) ^ (-zeta) * rankinEulerProduct ⌊Real.exp w⌋₊ zeta :=
      normalized_fullBadMask_le_rankin hN hL mask hzetaHalf
    _ ≤ 3 * (L + 1 : ℝ) * ((3 * N : ℕ) : ℝ) ^ (-zeta) *
        Real.exp (120 * Real.exp (w * zeta) * Real.log (w + Real.log 3)) :=
      mul_le_mul_of_nonneg_left (rankinEulerProduct_floor_exp_le hw hzeta) (by positivity)
    _ = _ := by rw [Real.rpow_def_of_pos hNr, mul_assoc, ← Real.exp_add]; congr 2; ring

/-- Actual masked deletion counts at the genuine saddle branch, from a finite pi(t) bound. -/
theorem normalized_fullBadMask_le_saddleCost {N L : ℕ} (hN : 2 ≤ N) (hL : L ≤ N)
    (mask : Finset ℕ) {A w eta : ℝ} (hA : 1 < A) (hw : 0 < w) (hAw : A ≤ Real.exp w)
    (hnu : Real.exp 1 ≤ Real.log N / w)
    (hzetaHalf : upperSaddleBranch (Real.log N / w) / w ≤ 1 / 2)
    (hR : ∀ t ∈ Set.Icc A (Real.exp w), |primeCountingRemainder t| ≤ eta * t / Real.log t) :
    ((fullBadMask N L ⌊Real.exp w⌋₊ mask).card : ℝ) / N ≤
      Real.exp (-saddleCost (Real.log N / w) + Real.log (3 * (L + 1 : ℝ)) +
        primeSplitRemainder A w (upperSaddleBranch (Real.log N / w) / w) eta) := by
  let u := upperSaddleBranch (Real.log N / w)
  let zeta := u / w
  have hu : 1 ≤ u := (upperSaddleBranch_spec hnu).1
  have hzeta : 0 < zeta := div_pos (by linarith) hw
  have hzetaHalf' : zeta ≤ 1 / 2 := hzetaHalf
  have hlog := logSum_floor_exp_le_Ei_add_remainder hA hAw hzeta (by linarith) hR
  have hbad := normalized_fullBadMask_le_exp (Y := ⌊Real.exp w⌋₊) hN hL mask hzetaHalf'
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog3N : Real.log (3 * N : ℕ) = Real.log 3 + Real.log N := by
    push_cast
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hNpos.ne']
  have hzw : zeta * w = u := by dsimp [zeta]; field_simp
  have hmain : zeta * Real.log N = (Real.log N / w) * u := by dsimp [zeta]; ring
  have hlogthree : 0 ≤ zeta * Real.log 3 := mul_nonneg hzeta.le (Real.log_nonneg (by norm_num))
  change _ ≤ Real.exp (-saddleCost (Real.log N / w) + Real.log (3 * (L + 1 : ℝ)) + primeSplitRemainder A w zeta eta)
  apply hbad.trans
  apply Real.exp_le_exp.mpr
  rw [hlog3N]
  simp only [mul_add]
  rw [hmain]
  rw [hzw] at hlog
  unfold saddleCost
  dsimp only [u] at *
  linarith

/-- Under the source-form PNT, the split point is selected before N, L, w and every mask.
The explicit remainder is retained, so this does not claim the final o(nu) estimate. -/
theorem normalized_fullBadMask_saddleCost_uniform_of_pnt (hPNT : PrimeNumberTheoremRemainder)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ A : ℝ, 2 ≤ A ∧ ∀ N : ℕ, 2 ≤ N → ∀ L : ℕ, L ≤ N →
      ∀ w : ℝ, 0 < w → A ≤ Real.exp w → Real.exp 1 ≤ Real.log N / w →
      upperSaddleBranch (Real.log N / w) / w ≤ 1 / 2 → ∀ mask : Finset ℕ,
      ((fullBadMask N L ⌊Real.exp w⌋₊ mask).card : ℝ) / N ≤
        Real.exp (-saddleCost (Real.log N / w) + Real.log (3 * (L + 1 : ℝ)) +
          primeSplitRemainder A w (upperSaddleBranch (Real.log N / w) / w) eta) := by
  obtain ⟨A, hA, hR⟩ := hPNT eta heta
  refine ⟨A, hA, ?_⟩
  intro N hN L hL w hw hAw hnu hzeta mask
  exact normalized_fullBadMask_le_saddleCost hN hL mask (by linarith) hw hAw hnu hzeta (fun t ht => hR t ht.1)

end
end PaperC.V282.BadStartRankinSaddle
