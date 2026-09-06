import PaperCV282.MediumPrimeScaling
import PaperCV282.MediumPrimeLayers
import PaperCV282.HarmonicIncidenceSurplus

/-! # The uniform lower bound for odd medium-prime incidences

The finite floor-sum and the fixed bound on square exceptions imply
E >= (H_11-1-epsilon) pi(B), uniformly over all positive quadratic windows.
-/

namespace PaperC.V282.MediumIncidenceAsymptotics

open Filter Finset MediumPrimeScaling MediumPrimeLayers MediumMultipleCounts
open PostQuadraticPrimeBounds PrimeEulerPNT HarmonicIncidenceSurplus
open scoped Topology BigOperators

noncomputable section

/-- The prime-count normalization diverges, so every fixed loss is negligible. -/
theorem prime_count_tendsto_atTop :
    Tendsto (fun B : ℕ => (PrimesUpTo.count B : ℝ)) atTop atTop := by
  simpa only [prime_count_eq_nat,Function.comp_def] using tendsto_natCast_atTop_atTop.comp Nat.tendsto_primeCounting

/-- A single exact prime-count layer has its expected PNT limit. -/
theorem layer_ratio_tendsto (hPNT : PrimeNumberTheoremRemainder) {j : ℕ}
    (hj : j ∈ Icc 1 10) :
    Tendsto (fun B : ℕ => ((PrimesUpTo.count (B / j) - PrimesUpTo.count (B / 11) : ℕ) : ℝ) /
      PrimesUpTo.count B) atTop (𝓝 (1 / (j : ℝ) - 1 / 11)) := by
  have h := (prime_count_div_ratio hPNT (mem_Icc.mp hj).1).sub
    (prime_count_div_ratio hPNT (by decide : 0 < 11))
  apply h.congr
  intro B
  have hd : B / 11 ≤ B / j :=
    Nat.div_le_div_left (by have := (mem_Icc.mp hj).2; omega) (mem_Icc.mp hj).1
  have hc : PrimesUpTo.count (B / 11) ≤ PrimesUpTo.count (B / j) := by
    simpa only [prime_count_eq_nat] using Nat.monotone_primeCounting hd
  rw [Nat.cast_sub hc,sub_div]

/-- The normalized floor-sum converges to H_11-1, with no untracked rounding loss. -/
theorem floor_sum_ratio_tendsto (hPNT : PrimeNumberTheoremRemainder) :
    Tendsto (fun B : ℕ => ((∑ p ∈ mediumPrimes B, B / p : ℕ) : ℝ) / PrimesUpTo.count B)
      atTop (𝓝 ((harmonic 11 : ℝ) - 1)) := by
  have hs := tendsto_finsetSum (Icc 1 10) (fun j hj => layer_ratio_tendsto hPNT hj)
  have hconstant : (∑ j ∈ Icc (1 : ℕ) 10, (1 / (j : ℝ) - 1 / 11)) = (harmonic 11 : ℝ) - 1 := by
    rw [harmonic_eleven_eq]
    norm_num [Finset.sum_Icc_succ_top]
  rw [hconstant] at hs
  apply hs.congr
  intro B
  rw [floor_sum_eq_prime_layers,Nat.cast_sum,Finset.sum_div]

/-- The global 854 square incidences vanish under normalization by pi(B). -/
theorem floor_sum_sub_square_loss_ratio (hPNT : PrimeNumberTheoremRemainder) :
    Tendsto (fun B : ℕ => (((∑ p ∈ mediumPrimes B, B / p : ℕ) : ℝ) - 854) /
      PrimesUpTo.count B) atTop (𝓝 ((harmonic 11 : ℝ) - 1)) := by
  have hz : Tendsto (fun B : ℕ => 854 / (PrimesUpTo.count B : ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero,Function.comp_def] using
      (tendsto_inv_atTop_zero.comp prime_count_tendsto_atTop).const_mul (854 : ℝ)
  simpa only [sub_div,sub_zero] using (floor_sum_ratio_tendsto hPNT).sub hz

/-- Companion E.3's lower bound for the true odd-incidence count, uniformly in lo. -/
theorem odd_incidence_lower_eventually (hPNT : PrimeNumberTheoremRemainder)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ Bzero : ℕ, 1332 ≤ Bzero ∧ ∀ B : ℕ, Bzero ≤ B → ∀ lo : ℕ,
      0 < lo → lo + B ≤ B ^ 2 + B + 1 →
      ((harmonic 11 : ℝ) - 1 - epsilon) * PrimesUpTo.count B ≤
        ((oddIncidences lo B (mediumPrimes B)).card : ℝ) := by
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp (floor_sum_sub_square_loss_ratio hPNT) epsilon hepsilon
  have hpos : ∀ᶠ B : ℕ in atTop, (0 : ℝ) < PrimesUpTo.count B :=
    prime_count_tendsto_atTop.eventually_gt_atTop 0
  obtain ⟨P,hP⟩ := eventually_atTop.mp hpos
  refine ⟨max 1332 (max N P),le_max_left _ _,fun B hB lo hlo htop => ?_⟩
  have hBmin : 1332 ≤ B := (le_max_left _ _).trans hB
  have hBN : N ≤ B := (le_max_left N P).trans ((le_max_right _ _).trans hB)
  have hBP : P ≤ B := (le_max_right N P).trans ((le_max_right _ _).trans hB)
  have hd := hN B hBN
  rw [Real.dist_eq] at hd
  have hlower := (abs_lt.mp hd).1
  have hl : ((harmonic 11 : ℝ) - 1 - epsilon) * PrimesUpTo.count B ≤
      ((∑ p ∈ mediumPrimes B, B / p : ℕ) : ℝ) - 854 := by
    have hh : (harmonic 11 : ℝ) - 1 - epsilon <
        (((∑ p ∈ mediumPrimes B, B / p : ℕ) : ℝ) - 854) / PrimesUpTo.count B := by linarith
    exact ((lt_div_iff₀ (hP B hBP)).mp hh).le
  have hf := floor_sum_le_odd_incidence_add hlo hBmin htop (fun p hp => mem_mediumPrimes.mp hp)
  have hfr : ((∑ p ∈ mediumPrimes B, B / p : ℕ) : ℝ) ≤
      ((oddIncidences lo B (mediumPrimes B)).card : ℝ) + 854 := by exact_mod_cast hf
  linarith

end
end PaperC.V282.MediumIncidenceAsymptotics
