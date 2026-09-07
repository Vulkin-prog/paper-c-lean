import PaperCV282.PoissonResolutionBudget
import PaperCV282.RareConditioningRates

/-! # The literal hard scalar local budget of companion D.1 -/
namespace PaperC.V282.HardLocalClosureBudget

open Real Filter Topology PoissonResolutionBudget PoissonStirlingBounds
open SaddleParameters SaddleScales SaddleCutoffAdmissibility SaddleRateConvergence
open AggregateCutoffRemainder

noncomputable section

def hardLocalCost (I rate : ℝ) (n : ℕ) : ℝ :=
  I+max 0 (log rate)+poissonLocalCost rate n

def hardLocalRemainder (N : ℕ) (c : ℝ) : ℝ :=
  20*(poissonStirlingConstant*exp (-(c/2)*saddleNu 1 (log N))+(N : ℝ)^(-(1/6 : ℝ)))

theorem hardLocalRemainder_tendsto_zero {c : ℝ} (hc : 0<c) :
    Tendsto (fun N : ℕ => hardLocalRemainder N c) atTop (𝓝 0) := by
  have he := margin_exponential_nat_tendsto_zero 1 (2*c) (c/2) (by norm_num) (by linarith)
  have hp := polynomial_error_nat_tendsto_zero (1/6) (by norm_num)
  have hh := ((he.const_mul poissonStirlingConstant).add hp).const_mul 20
  simpa only [hardLocalRemainder,mul_zero,add_zero,
    show 2*c/2-c/2=c/2 by ring,show -(1/3 : ℝ)+1/6= -(1/6 : ℝ) by ring] using hh

/-- Multiplication by the information and intensity costs is exact before exponentiation. -/
theorem weighted_atom_inverse_le {I rate : ℝ} {n : ℕ} (hr : 0<rate) (hn : 0<n) :
    exp I*rate*(exp (-rate)*rate^n/n.factorial)⁻¹≤
      poissonStirlingConstant*exp (hardLocalCost I rate n) := by
  have hlambda : rate≤exp (max 0 (log rate)) := by
    nth_rw 1 [← exp_log hr]
    exact exp_le_exp.mpr (le_max_right _ _)
  calc
    _ ≤ exp I*rate*(poissonStirlingConstant*exp (poissonLocalCost rate n)) :=
      mul_le_mul_of_nonneg_left (poisson_atom_reciprocal_le hr hn) (by positivity)
    _ ≤ exp I*exp (max 0 (log rate))*(poissonStirlingConstant*exp (poissonLocalCost rate n)) := by
      gcongr
      exact mul_nonneg poissonStirlingConstant_pos.le (exp_nonneg _)
    _ = _ := by rw [hardLocalCost,exp_add,exp_add];ring

theorem hard_leading_div_atom_le {I rate V nu c eta : ℝ} {n : ℕ}
    (hr : 0<rate) (hn : 0<n) (hb : hardLocalCost I rate n≤V-c*nu) :
    exp I*rate*exp (-V+eta*nu)/(exp (-rate)*rate^n/n.factorial)≤
      poissonStirlingConstant*exp (-(c-eta)*nu) := by
  have hw := (weighted_atom_inverse_le (I := I) hr hn).trans
    (mul_le_mul_of_nonneg_left (exp_le_exp.mpr hb) poissonStirlingConstant_pos.le)
  calc
    _ = (exp I*rate*(exp (-rate)*rate^n/n.factorial)⁻¹)*exp (-V+eta*nu) := by ring
    _ ≤ (poissonStirlingConstant*exp (V-c*nu))*exp (-V+eta*nu) :=
      mul_le_mul_of_nonneg_right hw (exp_nonneg _)
    _ = _ := by rw [mul_assoc,← exp_add];congr 2;ring

/-- The polynomial remainder survives division by the local mass uniformly. -/
theorem hard_polynomial_div_atom_eventually (c : ℝ) (hc : 0≤c) :
    ∀ᶠ N : ℕ in atTop, ∀ I rate : ℝ, ∀ n : ℕ, 0<rate → 0<n →
      hardLocalCost I rate n≤saddleCutoff 1 (log N)-c*saddleNu 1 (log N) →
      exp I*rate*(N : ℝ)^(-(1/3 : ℝ)+1/12)/(exp (-rate)*rate^n/n.factorial)≤
        (N : ℝ)^(-(1/6 : ℝ)) := by
  have hnu := (tendsto_saddleNu_atTop (a := 1) (by norm_num)).comp
    (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [constant_exp_saddle_le_power_eventually poissonStirlingConstant 1 (1/12)
    poissonStirlingConstant_pos (by norm_num),hnu.eventually (eventually_ge_atTop (0 : ℝ)),
    eventually_ge_atTop (2 : ℕ)] with N hp hnu hN
  intro I rate n hr hn hb
  dsimp only [Function.comp_def] at hnu
  have hb' := hb.trans (sub_le_self _ (mul_nonneg hc hnu))
  have hinv : exp I*rate*(exp (-rate)*rate^n/n.factorial)⁻¹≤(N : ℝ)^(1/12 : ℝ) := by
    refine (weighted_atom_inverse_le hr hn).trans ?_
    exact (mul_le_mul_of_nonneg_left (exp_le_exp.mpr hb') poissonStirlingConstant_pos.le).trans
      (by simpa only [one_mul] using hp)
  calc
    _ = (exp I*rate*(exp (-rate)*rate^n/n.factorial)⁻¹)*(N : ℝ)^(-(1/3 : ℝ)+1/12) := by ring
    _ ≤ (N : ℝ)^(1/12 : ℝ)*(N : ℝ)^(-(1/3 : ℝ)+1/12) :=
      mul_le_mul_of_nonneg_right hinv (rpow_nonneg (Nat.cast_nonneg N) _)
    _ = _ := by rw [← rpow_add (by positivity : (0 : ℝ)<N)];congr 1;ring

end
end PaperC.V282.HardLocalClosureBudget
