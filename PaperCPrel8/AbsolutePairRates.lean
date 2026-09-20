import PaperCPrel8.MicroscopicRetainedRates

/-! # Numerical assembly of the three absolute-pair costs -/
namespace PaperC.Prel8.AbsolutePairRates
open MicroscopicRetainedRates
noncomputable section

/-- Retain the extra inverse-information gain in the quadratic intensity term. -/
theorem information_gain {I lambda V nu c eta : ℝ} (hlambda : 0<lambda)
    (hb : I+Real.log lambda≤V-c*nu) :
    Real.exp I*lambda^2*Real.exp (-2*V+eta*nu)≤Real.exp (-I-(2*c-eta)*nu) := by
  have hh := Real.exp_le_exp.mpr (show I+2*Real.log lambda-2*V+eta*nu≤-I-(2*c-eta)*nu by linarith)
  convert hh using 1
  rw [show I+2*Real.log lambda-2*V+eta*nu=I+Real.log lambda+Real.log lambda+(-2*V+eta*nu) by ring]
  simp only [Real.exp_add,Real.exp_log hlambda]
  ring

/-- Finite ledger arithmetic with one inverse conditioning mass. -/
theorem ledger_bound {p m g b R r I V nu eta : ℝ} {Q : ℕ}
    (hm : 0<m) (hgm : g≤m)
    (hbase : b≤m^2*Real.exp (-2*V+eta*nu))
    (hlocal : 8*Real.exp I*(m*p)^2*(Q+1:ℝ)^2/m≤r)
    (hrel : Real.exp I*p^2*R≤r) :
    Real.exp I*p^2*(4*g*(2*(Q:ℝ)+1)+R+4*b)≤
      4*(Real.exp I*(m*p)^2*Real.exp (-2*V+eta*nu))+2*r := by
  have hq : 0≤(Q:ℝ) := Nat.cast_nonneg Q
  have hnear : 4*g*(2*(Q:ℝ)+1)≤8*m*(Q+1:ℝ)^2 := by
    have ha := mul_le_mul_of_nonneg_right hgm (show 0≤4*(2*(Q:ℝ)+1) by positivity)
    have hb := mul_le_mul_of_nonneg_left (show 4*(2*(Q:ℝ)+1)≤8*(Q+1:ℝ)^2 by nlinarith) hm.le
    nlinarith only [ha,hb]
  have hl : Real.exp I*p^2*(8*m*(Q+1:ℝ)^2)≤r := by
    convert hlocal using 1
    field_simp
  have hn := mul_le_mul_of_nonneg_left hnear (show 0≤Real.exp I*p^2 by positivity)
  have hb := mul_le_mul_of_nonneg_left hbase (show 0≤4*Real.exp I*p^2 by positivity)
  nlinarith only [hl,hn,hb,hrel]

end
end PaperC.Prel8.AbsolutePairRates
