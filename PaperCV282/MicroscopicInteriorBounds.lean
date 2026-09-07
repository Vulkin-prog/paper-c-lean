import PaperCV282.MicroscopicQuadraticAsymptotics
import PaperCV282.TransitionPrimeAsymptotics
import PaperCV282.MicroscopicBorderEvents
import PaperCV282.PostQuadraticGap
import PaperCV282.MicroscopicExponentialScale

/-! # The microscopic interior sum in Theorem 7.1

The early, transition, quadratic and post-quadratic regimes exhaust every
interior start. Their common prime-scale bound can therefore be summed
without imposing a new rank hypothesis on any window.
-/

namespace PaperC.V282.MicroscopicInteriorBounds

open Filter Finset MicroscopicQuadraticAsymptotics TransitionPrimeAsymptotics
open MicroscopicBorderEvents PostQuadraticGap PostQuadraticLiterature
open LaishramUniformInput PrimeEulerPNT HarmonicIncidenceSurplus
open MediumIncidenceAsymptotics PostQuadraticPrimeBounds MicroscopicExponentialScale
open InfiniteStartProbabilityTransfer PointwiseStartBounds
open scoped Topology BigOperators

noncomputable section

/-- A fixed strict surplus below the optimal constant works for every interior position. -/
theorem all_interior_probability_eventually (hLS : UniformPrimeDivisorStatement)
    (hShorey : ShoreySquareProductStatement) (hPNT : PrimeNumberTheoremRemainder)
    {delta : ℝ} (hdelta : 0 < delta) (hstar : delta < (surplus 11 : ℝ)) :
    ∃ Lzero : ℕ, ∀ L : ℕ, Lzero ≤ L → ∀ x : ℕ, 2 ≤ x →
      infiniteStartProbability x L ≤ (2 : ℝ) ^ (-(1 + delta) * Nat.primeCounting L) := by
  have hstarone : (surplus 11 : ℝ) < 1 := by rw [surplus_eleven_eq]; norm_num
  obtain ⟨T,hT⟩ := lemma_e_one hPNT (show 0 < 1 - delta by linarith)
  obtain ⟨Q,hQ⟩ := quadratic_affine_probability_eventually hLS hPNT hstar
  obtain ⟨theta,hg,P,hP⟩ := lemma_e_three hShorey hPNT
  obtain ⟨G,hG⟩ := eventually_atTop.mp (hg.eventually_ge_atTop (1 + delta))
  have hpos : ∀ᶠ B : ℕ in atTop, (0 : ℝ) < Nat.primeCounting B := by
    simpa only [prime_count_eq_nat] using prime_count_tendsto_atTop.eventually_gt_atTop 0
  obtain ⟨C,hC⟩ := eventually_atTop.mp hpos
  refine ⟨max 2 (max T (max Q (max P (max G C)))),fun L hL x hx => ?_⟩
  have hLpos : 0 < L := by omega
  have hcompare : (2 : ℝ) ^ (-(1 + delta) * Nat.primeCounting (L + 1)) ≤
      (2 : ℝ) ^ (-(1 + delta) * Nat.primeCounting L) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hm : (Nat.primeCounting L : ℝ) ≤ Nat.primeCounting (L + 1) := by
      exact_mod_cast Nat.monotone_primeCounting (Nat.le_succ L)
    nlinarith
  by_cases hearly : x ≤ L - 1
  · rw [early_start_probability_zero hx hearly]
    positivity
  · have hxL : L ≤ x := by omega
    by_cases htransition : x ≤ L + 2
    · have ht := hT L (by omega) x hxL htransition (Affine.startRhs L)
      rw [infiniteAffineStartProbability_startRhs_eq hLpos] at ht
      have he : -(2 - (1 - delta)) = -(1 + delta) := by ring
      rw [he] at ht
      exact ht.trans hcompare
    · by_cases hquadratic : x ≤ (L + 1) ^ 2 + 2
      · have hq := hQ L (by omega) x (by omega) hquadratic (Affine.startRhs L)
        rw [infiniteAffineStartProbability_startRhs_eq hLpos,prime_count_eq_nat] at hq
        exact hq.trans hcompare
      · have hp := (hP L (by omega) x (by omega)).2
        have hgr := hG (L + 1) (by omega)
        have hgap : (1 + delta) * Nat.primeCounting (L + 1) ≤
            BalasubramanianShoreyInput.gap (L + 1) theta :=
          (le_div_iff₀ (hC (L + 1) (by omega))).mp hgr
        exact hp.trans ((Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)).trans hcompare)

/-- Every strict exponent below delta_star bounds the full interior sum in (7.2). -/
theorem theorem_seven_one_interior_sum (hLS : UniformPrimeDivisorStatement)
    (hShorey : ShoreySquareProductStatement) (hPNT : PrimeNumberTheoremRemainder)
    {delta : ℝ} (hdelta : 0 < delta) (hstar : delta < (surplus 11 : ℝ)) :
    ∃ Lzero : ℕ, ∀ L : ℕ, Lzero ≤ L →
      ∑ x ∈ Icc 2 (2 * L ^ 2), infiniteStartProbability x L ≤
        (2 : ℝ) ^ (-(1 + delta) * Nat.primeCounting L) := by
  let d : ℝ := (delta + (surplus 11 : ℝ)) / 2
  have hd : 0 < d := by dsimp [d]; linarith
  have hdstar : d < (surplus 11 : ℝ) := by dsimp [d]; linarith
  have hmargin : 0 < d - delta := by dsimp [d]; linarith
  obtain ⟨N,hN⟩ := all_interior_probability_eventually hLS hShorey hPNT hd hdstar
  obtain ⟨P,hP⟩ := eventually_atTop.mp (microscopic_prefactor_le_eventually hPNT hmargin)
  refine ⟨max N P,fun L hL => ?_⟩
  calc
    _ ≤ ∑ _x ∈ Icc 2 (2 * L ^ 2), (2 : ℝ) ^ (-(1 + d) * Nat.primeCounting L) :=
      sum_le_sum (fun x hx => hN L (by omega) x (mem_Icc.mp hx).1)
    _ = ((Icc 2 (2 * L ^ 2)).card : ℝ) * (2 : ℝ) ^ (-(1 + d) * Nat.primeCounting L) := by
      rw [sum_const,nsmul_eq_mul]
    _ ≤ (2 * (L : ℝ) ^ 2) * (2 : ℝ) ^ (-(1 + d) * Nat.primeCounting L) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have hc : (Icc 2 (2 * L ^ 2)).card ≤ 2 * L ^ 2 := by simp only [Nat.card_Icc]; omega
      exact_mod_cast hc
    _ ≤ (2 : ℝ) ^ ((d - delta) * Nat.primeCounting L) *
        (2 : ℝ) ^ (-(1 + d) * Nat.primeCounting L) :=
      mul_le_mul_of_nonneg_right (hP L (by omega)) (by positivity)
    _ = _ := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring

end
end PaperC.V282.MicroscopicInteriorBounds
