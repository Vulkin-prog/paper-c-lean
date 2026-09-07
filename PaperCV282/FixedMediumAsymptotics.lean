import PaperCV282.FixedMediumLayers
import PaperCV282.MediumIncidenceAsymptotics

/-! # Companion E.3 for every fixed K, uniformly over quadratic windows -/
namespace PaperC.V282.FixedMediumAsymptotics

open Filter Finset FixedMediumLayers FixedMediumSquares MediumMultipleCounts
open MediumPrimeScaling PostQuadraticPrimeBounds PrimeEulerPNT
open scoped Topology BigOperators

noncomputable section

theorem harmonic_eq_Icc (K : ℕ) : (harmonic K : ℝ)=∑ j∈Icc 1 K, 1/(j : ℝ) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [harmonic_succ]
    push_cast
    rw [ih,sum_Icc_succ_top (by omega : 1≤K+1)]
    simp only [one_div,Nat.cast_add,Nat.cast_one]

theorem layer_constant_sum {K : ℕ} (hK : 0<K) :
    (∑ j∈Icc (1 : ℕ) (K-1), (1/(j : ℝ)-1/(K : ℝ)))=(harmonic K : ℝ)-1 := by
  have he : K-1+1=K := by omega
  have hh := congrArg (fun q : ℚ => (q : ℝ)) (harmonic_succ (K-1))
  rw [he] at hh
  push_cast at hh
  rw [sum_sub_distrib,← harmonic_eq_Icc]
  simp only [sum_const,Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul]
  rw [Nat.cast_sub (by omega : 1≤K),Nat.cast_one]
  have hKR : (K : ℝ)≠0 := by positivity
  rw [hh]
  field_simp
  ring

theorem layer_ratio_tendsto (hPNT : PrimeNumberTheoremRemainder) {K j : ℕ}
    (hK : 0<K) (hj : j∈Icc 1 (K-1)) :
    Tendsto (fun B : ℕ => ((PrimesUpTo.count (B/j)-PrimesUpTo.count (B/K) : ℕ) : ℝ)/
      PrimesUpTo.count B) atTop (𝓝 (1/(j : ℝ)-1/(K : ℝ))) := by
  have h := (prime_count_div_ratio hPNT (mem_Icc.mp hj).1).sub (prime_count_div_ratio hPNT hK)
  apply h.congr
  intro B
  have hd : B/K≤B/j := Nat.div_le_div_left (by have := (mem_Icc.mp hj).2; omega) (mem_Icc.mp hj).1
  have hc : PrimesUpTo.count (B/K)≤PrimesUpTo.count (B/j) := by
    simpa only [prime_count_eq_nat] using Nat.monotone_primeCounting hd
  rw [Nat.cast_sub hc,sub_div]

theorem floor_sum_ratio_tendsto (hPNT : PrimeNumberTheoremRemainder) (K : ℕ) (hK : 0<K) :
    Tendsto (fun B : ℕ => ((∑ p∈mediumPrimes K B, B/p : ℕ) : ℝ)/PrimesUpTo.count B)
      atTop (𝓝 ((harmonic K : ℝ)-1)) := by
  have hs := tendsto_finsetSum (Icc 1 (K-1)) (fun j hj => layer_ratio_tendsto hPNT hK hj)
  rw [layer_constant_sum hK] at hs
  apply hs.congr
  intro B
  rw [floor_sum_eq_prime_layers K B hK,Nat.cast_sum,Finset.sum_div]

theorem floor_sum_sub_square_loss_ratio (hPNT : PrimeNumberTheoremRemainder) (K : ℕ) (hK : 0<K) :
    Tendsto (fun B : ℕ => (((∑ p∈mediumPrimes K B, B/p : ℕ) : ℝ)-((2*K^2)*K : ℕ))/
      PrimesUpTo.count B) atTop (𝓝 ((harmonic K : ℝ)-1)) := by
  have hz : Tendsto (fun B : ℕ => (((2*K^2)*K : ℕ) : ℝ)/(PrimesUpTo.count B : ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero,Function.comp_def] using
      (tendsto_inv_atTop_zero.comp MediumIncidenceAsymptotics.prime_count_tendsto_atTop).const_mul
        ((((2*K^2)*K : ℕ) : ℝ))
  simpa only [sub_div,sub_zero] using (floor_sum_ratio_tendsto hPNT K hK).sub hz

/-- K is fixed before the asymptotic threshold; the threshold precedes the
location of every actual B-integer window. -/
theorem equation_E_three (hPNT : PrimeNumberTheoremRemainder) (K : ℕ) (hK : 2≤K)
    {epsilon : ℝ} (hepsilon : 0<epsilon) :
    ∃ Bzero : ℕ, 1≤Bzero ∧ ∀ B : ℕ, Bzero≤B → ∀ lo : ℕ,
      0<lo → lo+B≤B^2+B+1 →
      ((harmonic K : ℝ)-1-epsilon)*PrimesUpTo.count B≤
        ((oddIncidences lo B (mediumPrimes K B)).card : ℝ) := by
  have hKpos : 0<K := by omega
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp (floor_sum_sub_square_loss_ratio hPNT K hKpos) epsilon hepsilon
  have hpos : ∀ᶠ B : ℕ in atTop, (0 : ℝ)<PrimesUpTo.count B :=
    MediumIncidenceAsymptotics.prime_count_tendsto_atTop.eventually_gt_atTop 0
  obtain ⟨P,hP⟩ := eventually_atTop.mp hpos
  refine ⟨max 1 (max N P),le_max_left _ _,fun B hB lo hlo htop => ?_⟩
  have hBpos : 0<B := by omega
  have hBN : N≤B := by omega
  have hBP : P≤B := by omega
  have hd := hN B hBN
  rw [Real.dist_eq] at hd
  have hlower := (abs_lt.mp hd).1
  have hl : ((harmonic K : ℝ)-1-epsilon)*PrimesUpTo.count B≤
      ((∑ p∈mediumPrimes K B, B/p : ℕ) : ℝ)-((2*K^2)*K : ℕ) := by
    have hh : (harmonic K : ℝ)-1-epsilon <
        (((∑ p∈mediumPrimes K B, B/p : ℕ) : ℝ)-((2*K^2)*K : ℕ))/PrimesUpTo.count B := by linarith
    exact ((lt_div_iff₀ (hP B hBP)).mp hh).le
  have hf := FixedMediumSquares.floor_sum_le_odd_incidence_add hKpos hBpos hlo htop
    (fun p hp => (mem_mediumPrimes hKpos).mp hp)
  have hfr : ((∑ p∈mediumPrimes K B, B/p : ℕ) : ℝ)≤
      ((oddIncidences lo B (mediumPrimes K B)).card : ℝ)+((2*K^2)*K : ℕ) := by exact_mod_cast hf
  linarith

end
end PaperC.V282.FixedMediumAsymptotics
