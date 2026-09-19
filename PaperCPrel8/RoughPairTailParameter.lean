import PaperCV282.PrimeEulerCutoff
import PaperCPrel8.RoughKernelThreshold
import PaperCV282.PrimeEulerLowerSplit

/-! # Exact rounding and small-argument bounds for the rough pair reciprocal sum -/
namespace PaperC.Prel8.RoughPairTailParameter
open V282.PrimeEulerCutoff V282.PrimeEulerLowerSplit V282.SaddleParameters V282.SaddleScales
open RoughKernelThreshold Filter Topology
noncomputable section

def tailParameter (w z sigma : ℝ) : ℝ :=
  z*(⌊Real.exp w⌋₊:ℝ)^(-(1-sigma))/(1-sigma)

/-- Integer cutoff rounding costs only a constant, without halving the leading exponent. -/
theorem parameter_le {w z sigma : ℝ} (hw : Real.log 4≤w) (hz : 0≤z)
    (hs : 0≤sigma) (hsh : sigma≤1/2) :
    tailParameter w z sigma≤4*z*Real.exp (-w+w*sigma) := by
  have hy : (0:ℝ)<(⌊Real.exp w⌋₊:ℝ) := by
    have hh := (floor_exp_bounds hw).1
    exact_mod_cast (show 0<⌊Real.exp w⌋₊ by omega)
  have hs1 : 0<1-sigma := by linarith
  have he : (⌊Real.exp w⌋₊:ℝ)^(-(1-sigma))=
      (⌊Real.exp w⌋₊:ℝ)^sigma*(1/(⌊Real.exp w⌋₊:ℝ)) := by
    rw [show -(1-sigma)=sigma-1 by ring,Real.rpow_sub_one hy.ne']
    ring
  have hp := mul_le_mul (floor_exp_rpow_le_exp w hs) (inv_floor_exp_le_two_exp_neg hw)
    (show (0:ℝ)≤1/(⌊Real.exp w⌋₊:ℝ) by positivity) (Real.exp_pos _).le
  have hp' : (⌊Real.exp w⌋₊:ℝ)^(-(1-sigma))≤2*Real.exp (-w+w*sigma) := by
    rw [he]
    apply hp.trans_eq
    rw [mul_left_comm,← Real.exp_add]
    congr 2
    ring
  have hi : 1/(1-sigma)≤2 := (div_le_iff₀ hs1).mpr (by linarith)
  unfold tailParameter
  have hh := mul_le_mul (mul_le_mul_of_nonneg_left hp' hz) hi
    (by positivity : (0:ℝ)≤1/(1-sigma)) (by positivity : 0≤z*(2*Real.exp (-w+w*sigma)))
  convert hh using 1 <;> ring

/-- A finite linear bound, used only after smallness has actually been proved. -/
theorem exponential_remainder_le {a : ℝ} (ha : 0≤a) (ha1 : a≤1) :
    Real.exp a-1≤3*a :=
  (exp_sub_one_le_linear ha ha1).trans (mul_le_mul_of_nonneg_right Real.exp_one_lt_three.le ha)

/-- All fixed polynomial factors, together with exp(u), are exp(o(nu)). -/
theorem prefactor_absorption (K : ℝ) (d : ℕ) (hK : 0<K) {eta : ℝ} (heta : 0<eta) :
    ∀ᶠ H : ℝ in atTop, K*H^d*Real.exp (saddleParameter 1 H)≤Real.exp (eta*saddleNu 1 H) := by
  have hc := (tendsto_const_nhds (x:=Real.log K)).div_atTop
    (tendsto_saddleNu_atTop (by norm_num : (0:ℝ)<1))
  have hl := (tendsto_log_div_saddleNu (by norm_num : (0:ℝ)<1)).const_mul (d:ℝ)
  have hu := tendsto_saddleParameter_div_nu (by norm_num : (0:ℝ)<1)
  have hh := (hc.add hl).add hu
  have he := hh.eventually (gt_mem_nhds (show 0+(d:ℝ)*0+0<eta by simpa using heta))
  filter_upwards [he,eventually_gt_atTop (0:ℝ),
    (tendsto_saddleNu_atTop (by norm_num : (0:ℝ)<1)).eventually (eventually_gt_atTop (0:ℝ))]
    with H hH hp hn
  have heq : Real.log K/saddleNu 1 H+(d:ℝ)*(Real.log H/saddleNu 1 H)+
      saddleParameter 1 H/saddleNu 1 H=
        (Real.log K+(d:ℝ)*Real.log H+saddleParameter 1 H)/saddleNu 1 H := by ring
  rw [heq] at hH
  have hx := (div_le_iff₀ hn).mp hH.le
  calc
    _ = Real.exp (Real.log K+(d:ℝ)*Real.log H+saddleParameter 1 H) := by
      rw [Real.exp_add,Real.exp_add,Real.exp_log hK,Real.exp_nat_mul,Real.exp_log hp]
    _ ≤ _ := Real.exp_le_exp.mpr hx

end
end PaperC.Prel8.RoughPairTailParameter
