import PaperCV282.PoissonResolutionBudget
import PaperCV282.RareConditioningRates

/-! # The printed soft local information budget in companion D.1 -/
namespace PaperC.V282.SoftLocalClosureBudget

open Real Filter Topology PoissonResolutionBudget PoissonStirlingBounds
open SaddleParameters SaddleScales SaddleCutoffAdmissibility SaddleRateConvergence

noncomputable section

def softLocalCost (I rate : ℝ) (n : ℕ) : ℝ :=
  2*I + max 0 (log rate) + log n + 2*rate*poissonEntropy (n/rate)

def softLocalRemainder (N : ℕ) (c : ℝ) : ℝ :=
  6*(poissonStirlingConstant*exp (-(c/4)*saddleNu 2 (log N)) +
    (N : ℝ)^(-(1/6 : ℝ)))

theorem softLocalRemainder_tendsto_zero {c : ℝ} (hc : 0<c) :
    Tendsto (fun N : ℕ => softLocalRemainder N c) atTop (𝓝 0) := by
  have he := margin_exponential_nat_tendsto_zero 2 c (c/4) (by norm_num) (by linarith)
  have hp := polynomial_error_nat_tendsto_zero (1/6) (by norm_num)
  have hh := ((he.const_mul poissonStirlingConstant).add hp).const_mul 6
  simpa only [softLocalRemainder, mul_zero, add_zero,
    show c/2-c/4=c/4 by ring, show -(1/3 : ℝ)+1/6=-(1/6 : ℝ) by ring] using hh

theorem soft_leading_div_atom_le {I rate V nu c eta : ℝ} {n : ℕ}
    (hr : 0<rate) (hn : 0<n)
    (hb : softLocalCost I rate n ≤ V-c*nu) :
    exp (-(V-(2*I+max 0 (log rate)))/2+eta*nu) /
      (exp (-rate)*rate^n/n.factorial) ≤
      poissonStirlingConstant*exp (-(c/2-eta)*nu) := by
  rw [div_eq_mul_inv]
  calc
    _ ≤ exp (-(V-(2*I+max 0 (log rate)))/2+eta*nu)*
        (poissonStirlingConstant*exp (poissonLocalCost rate n)) :=
      mul_le_mul_of_nonneg_left (poisson_atom_reciprocal_le hr hn) (exp_nonneg _)
    _ = poissonStirlingConstant*exp
        (-(V-(2*I+max 0 (log rate)))/2+eta*nu+poissonLocalCost rate n) := by
      rw [exp_add (-(V-(2*I+max 0 (log rate)))/2+eta*nu) (poissonLocalCost rate n)]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by
      unfold softLocalCost at hb
      unfold poissonLocalCost
      linarith)) poissonStirlingConstant_pos.le

theorem constant_exp_soft_le_power_eventually (C K epsilon : ℝ)
    (hC : 0<C) (hepsilon : 0<epsilon) :
    ∀ᶠ N : ℕ in atTop,
      C*exp (K*saddleCutoff 2 (log N))≤(N : ℝ)^epsilon := by
  have hlog : Tendsto (fun N : ℕ => log N) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlim := (tendsto_const_nhds (x := log C)).div_atTop hlog |>.add
    (((tendsto_saddleCutoff_div_height (a := 2) (by norm_num)).comp hlog).const_mul K)
  have hs := hlim.eventually (gt_mem_nhds (by simpa using hepsilon))
  filter_upwards [hs,eventually_ge_atTop (2 : ℕ)] with N hs hN
  have hn : 0<log (N : ℝ) := log_pos (by exact_mod_cast (show 1<N by omega))
  have hp : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hratio : (log C+K*saddleCutoff 2 (log N))/log N<epsilon := by
    simpa only [add_div,mul_div_assoc,Function.comp_apply] using hs
  rw [rpow_def_of_pos hp,← exp_log hC,← exp_add]
  apply exp_le_exp.mpr
  simpa only [mul_comm] using ((div_lt_iff₀ hn).mp hratio).le

/-- Conditioning and the reciprocal atom together remain subpolynomial. -/
theorem soft_polynomial_div_atom_eventually (c : ℝ) (hc : 0≤c) :
    ∀ᶠ N : ℕ in atTop, ∀ I rate : ℝ, ∀ n : ℕ, 0<rate → 0<n →
      softLocalCost I rate n ≤ saddleCutoff 2 (log N)-c*saddleNu 2 (log N) →
      exp I*(N : ℝ)^(-(1/3 : ℝ)+1/12) /
        (exp (-rate)*rate^n/n.factorial) ≤ (N : ℝ)^(-(1/6 : ℝ)) := by
  have hnu := (tendsto_saddleNu_atTop (a := 2) (by norm_num)).comp
    (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [constant_exp_soft_le_power_eventually poissonStirlingConstant (1/2) (1/12)
    poissonStirlingConstant_pos (by norm_num),
    hnu.eventually (eventually_ge_atTop (0 : ℝ)), eventually_ge_atTop (2 : ℕ)] with N hp hnu hN
  intro I rate n hr hn hb
  dsimp only [Function.comp_def] at hnu
  have hcost : I+poissonLocalCost rate n ≤ saddleCutoff 2 (log N)/2 := by
    unfold softLocalCost at hb
    unfold poissonLocalCost
    linarith [le_max_left 0 (log rate), mul_nonneg hc hnu]
  have hinv : exp I*(exp (-rate)*rate^n/n.factorial)⁻¹ ≤ (N : ℝ)^(1/12 : ℝ) := by
    calc
      _ ≤ exp I*(poissonStirlingConstant*exp (poissonLocalCost rate n)) :=
        mul_le_mul_of_nonneg_left (poisson_atom_reciprocal_le hr hn) (exp_nonneg _)
      _ = poissonStirlingConstant*exp (I+poissonLocalCost rate n) := by rw [exp_add];ring
      _ ≤ poissonStirlingConstant*exp ((1/2)*saddleCutoff 2 (log N)) :=
        mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by linarith)) poissonStirlingConstant_pos.le
      _ ≤ _ := hp
  rw [div_eq_mul_inv]
  calc
    _ = (exp I*(exp (-rate)*rate^n/n.factorial)⁻¹)*(N : ℝ)^(-(1/3 : ℝ)+1/12) := by ring
    _ ≤ (N : ℝ)^(1/12 : ℝ)*(N : ℝ)^(-(1/3 : ℝ)+1/12) :=
      mul_le_mul_of_nonneg_right hinv (rpow_nonneg (Nat.cast_nonneg N) _)
    _ = _ := by rw [← rpow_add (by positivity : (0 : ℝ)<N)]; congr 1; ring

end
end PaperC.V282.SoftLocalClosureBudget
