import PaperCV282.TransitionPrimeScales
import PaperCV282.TransitionPrimeMinor

/-! # Companion E.1, including its asymptotic conclusion

All three transition starts are covered by the same lower gap, before any
choice of right-hand side. Endpoint losses are bounded explicitly by four.
-/

namespace PaperC.V282.TransitionPrimeAsymptotics

open Filter TransitionPrimeScales TransitionPrimeMinor MicroscopicValuationMatrix
open MediumIncidenceAsymptotics PostQuadraticPrimeBounds PrimeEulerPNT
open PointwiseStartBounds
open scoped Topology

noncomputable section

/-- The common real lower bound for transition-start rank. -/
def transitionGap (B : ℕ) : ℝ :=
  Nat.primeCounting (2 * B) - (Nat.primeCounting (transitionCutoff B) : ℝ) - 4

theorem transitionCutoff_le {B : ℕ} (hB : 16 ≤ B) : transitionCutoff B ≤ B := by
  have hs : 4 ≤ Nat.sqrt B := Nat.le_sqrt.mpr hB
  have hsq := Nat.sqrt_le' B
  dsimp [transitionCutoff]
  nlinarith

/-- A three-integer endpoint displacement loses at most three prime species. -/
theorem transition_top_count {a B : ℕ} (hB : 2 ≤ B) (ha : B - 2 ≤ a) :
    Nat.primeCounting (2 * B) ≤ Nat.primeCounting (a + B - 1) + 3 := by
  have hn : 2 * B ≤ (a + B - 1) + 3 := by omega
  exact (Nat.monotone_primeCounting hn).trans (primeCounting_add_le _ _)

/-- The literal identity minor bounds the complete-value rank uniformly over the transition. -/
theorem transition_value_rank_gap {M a B : ℕ} (hB : 16 ≤ B)
    (halo : B - 2 ≤ a) (hahi : a ≤ B) (hM : a + B ≤ M + 1) :
    transitionGap B + 1 ≤ ((valuationMatrix M (a + 1) B).rank : ℝ) := by
  have ha : 0 < a := by omega
  have hY : transitionCutoff B ≤ a + B - 1 := (transitionCutoff_le hB).trans (by omega)
  have hr := transition_value_rank_lower ha hahi (transitionCutoff_square_ge B) hM
  rw [card_transitionPrimes hY] at hr
  have htop := transition_top_count (by omega : 2 ≤ B) halo
  have hnat : Nat.primeCounting (2 * B) ≤
      (valuationMatrix M (a + 1) B).rank + Nat.primeCounting (transitionCutoff B) + 3 := by omega
  have hreal : (Nat.primeCounting (2 * B) : ℝ) ≤
      (valuationMatrix M (a + 1) B).rank + (Nat.primeCounting (transitionCutoff B) : ℝ) + 3 := by
    exact_mod_cast hnat
  dsimp [transitionGap]
  linarith

/-- The shared rank gap is (2-o(1)) pi(B). -/
theorem transition_gap_ratio_tendsto_two (hPNT : PrimeNumberTheoremRemainder) :
    Tendsto (fun B : ℕ => transitionGap B / Nat.primeCounting B) atTop (𝓝 2) := by
  have hz : Tendsto (fun B : ℕ => 4 / (Nat.primeCounting B : ℝ)) atTop (𝓝 0) := by
    simpa only [prime_count_eq_nat] using (tendsto_const_nhds (x := (4 : ℝ))).div_atTop prime_count_tendsto_atTop
  simpa only [transitionGap,sub_div,sub_zero] using
    ((doubled_prime_count_ratio hPNT).sub (transition_cutoff_prime_ratio hPNT)).sub hz

/-- The exact finite gap already bounds every transition affine probability. -/
theorem transition_affine_probability_le_gap {L x : ℕ} (hL : 16 ≤ L + 1)
    (hxlo : L ≤ x) (hxhi : x ≤ L + 2) (b : Fin L → F₂) :
    infiniteAffineStartProbability x L b ≤ (2 : ℝ) ^ (-transitionGap (L + 1)) := by
  have hr := transition_value_rank_gap (M := x + L) (a := x - 1) hL
    (by omega) (by omega) (by omega)
  have hx : 1 ≤ x := by omega
  rw [Nat.sub_add_cancel hx] at hr
  exact infinite_probability_le_real_value_rank hx (le_refl _) hr b

/-- The full source E.1 conclusion, uniformly for all three starts and every affine word. -/
theorem lemma_e_one (hPNT : PrimeNumberTheoremRemainder) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    ∃ Lzero : ℕ, ∀ L : ℕ, Lzero ≤ L → ∀ x : ℕ, L ≤ x → x ≤ L + 2 →
      ∀ b : Fin L → F₂,
      infiniteAffineStartProbability x L b ≤
        (2 : ℝ) ^ (-(2 - epsilon) * Nat.primeCounting (L + 1)) := by
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp (transition_gap_ratio_tendsto_two hPNT) epsilon hepsilon
  have hpos : ∀ᶠ B : ℕ in atTop, (0 : ℝ) < Nat.primeCounting B := by
    simpa only [prime_count_eq_nat] using prime_count_tendsto_atTop.eventually_gt_atTop 0
  obtain ⟨P,hP⟩ := eventually_atTop.mp hpos
  refine ⟨max 16 (max N P),fun L hL x hxlo hxhi b => ?_⟩
  have hsmall : 16 ≤ L + 1 := by omega
  have hBN : N ≤ L + 1 := by omega
  have hBP : P ≤ L + 1 := by omega
  have hd := hN (L + 1) hBN
  rw [Real.dist_eq] at hd
  have hlow := (abs_lt.mp hd).1
  have hr : (2 - epsilon) * Nat.primeCounting (L + 1) ≤ transitionGap (L + 1) := by
    have hh : 2 - epsilon < transitionGap (L + 1) / Nat.primeCounting (L + 1) := by linarith
    exact ((lt_div_iff₀ (hP (L + 1) hBP)).mp hh).le
  exact (transition_affine_probability_le_gap hsmall hxlo hxhi b).trans
    (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith))

end
end PaperC.V282.TransitionPrimeAsymptotics
