import PaperCV282.PrecisePellSquareclasses
import PaperCV282.PolynomialSplitProducts

/-!
# The precise split-product start count

The same actual squareclass localization and positive-root injection as in
`PolynomialSplitProducts` are retained. Each divisor count and each Pell
fibre is bounded at the logarithmic exponential scale; multiplication merely
adds their constants. No solution or shift-dependent threshold is used.
-/

namespace PaperC.V282.PreciseSplitProducts

open ComponentNormalization DefectivePredicate PellInput
open SplitProductLocalization PositiveSquareclassPairs PolynomialSplitProducts
open PrecisePellDivisors PrecisePellSquareclasses
open scoped BigOperators

noncomputable section

/-- One divisor set contains all squareclasses, uniformly over the shift tuple. -/
theorem card_squareclass_divisors_le_expLogLog_eventually
    (hNR : NicolasRobinDivisorLogBoundStatement) (K d : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ e : ℕ, ∀ h : Fin d → ℤ,
      e ≤ M ^ K → (∀ i, (h i).natAbs ≤ M ^ K) →
      ((e * shiftDifferenceProduct h).divisors.card : ℝ) ≤ expLogLogBound c M := by
  obtain ⟨c, hc, Mdiv, hdiv⟩ := card_divisors_le_expLogLog_eventually
    hNR (K + (K + 1) * (d * d))
  refine ⟨c, hc, max Mdiv 2, ?_⟩
  intro M hM e h he hh
  apply hdiv M ((le_max_left _ _).trans hM)
  calc
    e * shiftDifferenceProduct h ≤ M ^ K * M ^ ((K + 1) * (d * d)) :=
      Nat.mul_le_mul he (shiftDifferenceProduct_le_polynomial ((le_max_right _ _).trans hM) h hh)
    _ = _ := (pow_add _ _ _).symm

/-- Precise fixed-degree bound for all integer starts in the positive-factor box.
The constant and threshold precede every shift and coefficient. -/
theorem splitProductStart_atMost_expLogLog_eventually
    (hNR : NicolasRobinDivisorLogBoundStatement) (K d : ℕ) (hd : 2 ≤ d) :
    ∃ c : ℝ, 0 ≤ c ∧ ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ h : Fin d → ℤ, ∀ e : ℕ,
      Function.Injective h → 0 < e → e ≤ M ^ K →
      (∀ i, (h i).natAbs ≤ M ^ K) →
      HasAtMostSolutionsReal (splitProductStart h e (M ^ K)) (expLogLogBound c M) := by
  classical
  obtain ⟨cd, hcd, Md, hdiv⟩ := card_squareclass_divisors_le_expLogLog_eventually hNR K d
  obtain ⟨cp, hcp, Mp, hpell⟩ := positiveSquareclassBox_atMost_expLogLog_eventually hNR (K + 1)
  refine ⟨cd + cd + cp, by positivity, max Md (max Mp 2), ?_⟩
  intro M hM h e hh he heM hshift s hs
  have htail : max Mp 2 ≤ M := (le_max_right _ _).trans hM
  have hMtwo : 2 ≤ M := (le_max_right _ _).trans htail
  let i : Fin d := ⟨0, by omega⟩
  let j : Fin d := ⟨1, by omega⟩
  have hij : i ≠ j := by intro hij; have := congrArg Fin.val hij; dsimp [i, j] at this; omega
  have hdiff : h i - h j ≠ 0 := sub_ne_zero.mpr (fun hEq => hij (hh hEq))
  let S : Finset ℕ := (e * shiftDifferenceProduct h).divisors
  let color : ℤ → ℕ × ℕ := fun X =>
    (squarefreeKernel (X + h i).toNat, squarefreeKernel (X + h j).toNat)
  have htarget : e * shiftDifferenceProduct h ≠ 0 := (Nat.mul_pos he (shiftDifferenceProduct_pos hh)).ne'
  have hcolors : ∀ X ∈ s, color X ∈ S ×ˢ S := by
    intro X hX
    obtain ⟨hheight, hpositive, Y, heq⟩ := hs X hX
    exact Finset.mem_product.mpr
      ⟨Nat.mem_divisors.mpr ⟨squarefreeKernel_shift_dvd hh he hpositive heq i, htarget⟩,
       Nat.mem_divisors.mpr ⟨squarefreeKernel_shift_dvd hh he hpositive heq j, htarget⟩⟩
  have hshiftDiff : (h i - h j).natAbs ≤ M ^ (K + 1) := by
    calc
      _ ≤ (h i).natAbs + (h j).natAbs := Int.natAbs_sub_le _ _
      _ ≤ M ^ K + M ^ K := Nat.add_le_add (hshift i) (hshift j)
      _ ≤ M * M ^ K := by simpa only [two_mul] using Nat.mul_le_mul_right (M ^ K) hMtwo
      _ = _ := (pow_succ' _ _).symm
  have hfibers : ∀ c ∈ S ×ˢ S,
      ((s.filter (fun X => color X = c)).card : ℝ) ≤ expLogLogBound cp M := by
    intro c hc
    let fiber := s.filter (fun X => color X = c)
    by_cases hempty : fiber = ∅
    · change (fiber.card : ℝ) ≤ _
      rw [hempty]
      simp only [Finset.card_empty, Nat.cast_zero]
      exact (expLogLogBound_pos cp M).le
    · obtain ⟨X, hX⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
      have hXmem := Finset.mem_filter.mp hX
      have hXprop := hs X hXmem.1
      have hXcolor := hXmem.2
      have hiEq : squarefreeKernel (X + h i).toNat = c.1 := congrArg Prod.fst hXcolor
      have hjEq : squarefreeKernel (X + h j).toNat = c.2 := congrArg Prod.snd hXcolor
      have hiPos : 0 < (X + h i).toNat := by have := hXprop.2.1 i; omega
      have hjPos : 0 < (X + h j).toNat := by have := hXprop.2.1 j; omega
      have hA : 0 < c.1 := hiEq ▸ squarefreeKernel_pos _
      have hC : 0 < c.2 := hjEq ▸ squarefreeKernel_pos _
      have hAsq : Squarefree c.1 := hiEq ▸ squarefreeKernel_squarefree _
      have hCsq : Squarefree c.2 := hjEq ▸ squarefreeKernel_squarefree _
      have hAH : c.1 ≤ M ^ (K + 1) := by
        rw [← hiEq]
        exact (squarefreeKernel_le hiPos).trans (shifted_factor_le_polynomial hMtwo hXprop.1 (hshift i))
      have hCH : c.2 ≤ M ^ (K + 1) := by
        rw [← hjEq]
        exact (squarefreeKernel_le hjPos).trans (shifted_factor_le_polynomial hMtwo hXprop.1 (hshift j))
      apply card_fixed_squareclasses_le _ _
        (hpell M ((le_max_left _ _).trans htail) c.1 c.2 (M ^ (K + 1)) (h i - h j)
          hA hC hAsq hCsq hdiff hAH hCH le_rfl hshiftDiff)
      intro Z hZ
      have hz := Finset.mem_filter.mp hZ
      have hzprop := hs Z hz.1
      exact ⟨hzprop.2.1 i, hzprop.2.1 j, congrArg Prod.fst hz.2, congrArg Prod.snd hz.2,
        shifted_factor_le_polynomial hMtwo hzprop.1 (hshift i),
        shifted_factor_le_polynomial hMtwo hzprop.1 (hshift j)⟩
  have hsum : (s.card : ℝ) ≤ (S.card : ℝ) ^ 2 * expLogLogBound cp M := by
    rw [Finset.card_eq_sum_card_fiberwise hcolors, Nat.cast_sum]
    calc
      _ ≤ ∑ _c ∈ S ×ˢ S, expLogLogBound cp M := Finset.sum_le_sum hfibers
      _ = _ := by simp [pow_two]
  have hS : (S.card : ℝ) ≤ expLogLogBound cd M :=
    hdiv M ((le_max_left _ _).trans hM) e h heM hshift
  calc
    (s.card : ℝ) ≤ (S.card : ℝ) ^ 2 * expLogLogBound cp M := hsum
    _ ≤ (expLogLogBound cd M) ^ 2 * expLogLogBound cp M := by
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hS 2)
        (expLogLogBound_pos cp M).le
    _ = expLogLogBound (cd + cd + cp) M := by
      simp only [expLogLogBound_add, pow_two]

end
end PaperC.V282.PreciseSplitProducts
