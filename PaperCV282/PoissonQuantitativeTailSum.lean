import PaperCV282.PoissonQuantitativeSummation

/-! # Uniform lattice summation to the right of a moving threshold -/
namespace PaperC.V282.PoissonQuantitativeTailSum

open Real PoissonQuantitativeLattice PoissonQuantitativeSummation

noncomputable section

theorem inverse_exp_gap_le {v : ℝ} (hv : 0<v) (hv1 : v≤1) :
    1/(1-exp (-v))≤2/v := by
  have hq : exp (-v)<1 := exp_lt_one_iff.mpr (by linarith)
  have he : (1+v)*exp (-v)≤1 := by
    have h := mul_le_mul_of_nonneg_right (add_one_le_exp v) (exp_pos (-v)).le
    rw [← exp_add,add_neg_cancel,exp_zero] at h
    simpa only [add_comm] using h
  have hden : v/2≤1-exp (-v) := by nlinarith [mul_nonneg (sub_nonneg.mpr hv1) (sub_nonneg.mpr hq.le)]
  have h := one_div_le_one_div_of_le (by positivity : 0<v/2) hden
  simpa only [one_div,inv_div] using h

theorem finite_shifted_geometric_sum_le (q : ℝ) (hq0 : 0≤q) (hq1 : q<1)
    (m : ℕ) (s : Finset ℕ) (hs : ∀n∈s,m≤n) :
    (∑ n∈s,q^(n-m))≤1/(1-q) := by
  classical
  have hi : Set.InjOn (fun n : ℕ => n-m) (s : Set ℕ) := by
    intro i hi j hj hij
    have h1 := hs i hi
    have h2 := hs j hj
    change i-m=j-m at hij
    omega
  rw [← Finset.sum_image hi]
  have h := Summable.sum_le_tsum (s.image fun n => n-m) (fun _ _ => pow_nonneg hq0 _)
    (summable_geometric_of_abs_lt_one (by rwa [abs_of_nonneg hq0]))
  simpa only [tsum_geometric_of_lt_one hq0 hq1,one_div] using h

theorem shifted_gaussian_sum_le {rate t : ℝ} (hr : 1≤rate) (ht : 0≤t)
    (htop : t≤sqrt rate/2) (s : Finset ℕ) (hs : ∀n∈s,t≤latticePoint rate n) :
    (1/sqrt rate)*(∑ n∈s,exp (-(latticePoint rate n-t)^2/6))≤
      2*exp (1/6)*sqrt (12*π) := by
  let a := rate+sqrt rate*t
  have hrp : 0<rate := by linarith
  have hsp : 0<sqrt rate := sqrt_pos.mpr hrp
  have ha : 1≤a := by dsimp [a];nlinarith [sqrt_nonneg rate]
  have has : sqrt a≤2*sqrt rate := by
    have hmul := mul_le_mul_of_nonneg_left htop (sqrt_nonneg rate)
    have hsq := sq_sqrt hrp.le
    have hasq := sq_sqrt (by linarith : 0≤a)
    dsimp [a] at hasq
    nlinarith [sqrt_nonneg a]
  have hcomp (n : ℕ) (hn : n∈s) : exp (-(latticePoint rate n-t)^2/6)≤exp (-(latticePoint a n)^2/6) := by
    have htz := hs n hn
    have hna : a≤(n : ℝ) := by
      have h := (le_div_iff₀ hsp).mp htz
      dsimp [a]
      nlinarith
    have hgap : latticePoint rate n-t=((n : ℝ)-a)/sqrt rate := by dsimp [a,latticePoint];field_simp;ring
    have hden : sqrt rate≤sqrt a := sqrt_le_sqrt (by dsimp [a];nlinarith [sqrt_nonneg rate])
    have hle : latticePoint a n≤latticePoint rate n-t := by
      rw [hgap]
      exact div_le_div_of_nonneg_left (sub_nonneg.mpr hna) hsp hden
    have hnonneg : 0≤latticePoint a n := by unfold latticePoint;positivity
    exact exp_le_exp.mpr (by nlinarith [pow_le_pow_left₀ hnonneg hle 2])
  have hsum := Finset.sum_le_sum hcomp
  have hgauss := gaussian_lattice_sum_le ha s
  have hapos : 0<sqrt a := by positivity
  have hgs : (∑ n∈s,exp (-(latticePoint a n)^2/6))≤(exp (1/6)*sqrt (12*π))*sqrt a := by
    apply (div_le_iff₀ hapos).mp
    simpa only [one_div,div_eq_mul_inv,mul_comm,one_mul] using hgauss
  have hbig := hsum.trans (hgs.trans (mul_le_mul_of_nonneg_left has (by positivity)))
  have h := mul_le_mul_of_nonneg_left hbig (by positivity : 0≤1/sqrt rate)
  calc
    _≤(1/sqrt rate)*((exp (1/6)*sqrt (12*π))*(2*sqrt rate)) := h
    _=2*exp (1/6)*sqrt (12*π) := by field_simp

theorem shifted_exponential_sum_le {rate t : ℝ} (hr : 1≤rate) (ht : 1≤t)
    (htop : t≤sqrt rate/2) (s : Finset ℕ) (hs : ∀n∈s,t≤latticePoint rate n) :
    (1/sqrt rate)*(∑ n∈s,exp (-(2*t*(latticePoint rate n-t))/3))≤3/t := by
  let a := rate+sqrt rate*t
  let m : ℕ := ⌈a⌉₊
  let v := 2*t/(3*sqrt rate)
  have hsp : 0<sqrt rate := by positivity
  have htp : 0<t := by linarith
  have hv : 0<v := by dsimp [v];positivity
  have hv1 : v≤1 := by dsimp [v];exact (div_le_one (by positivity)).mpr (by linarith)
  have hmem (n : ℕ) (hn : n∈s) : m≤n := by
    apply Nat.ceil_le.mpr
    have h := (le_div_iff₀ hsp).mp (hs n hn)
    dsimp [a]
    nlinarith
  have hcomp (n : ℕ) (hn : n∈s) : exp (-(2*t*(latticePoint rate n-t))/3)≤(exp (-v))^(n-m) := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    have hna : a≤m := Nat.le_ceil a
    have he : ((n-m : ℕ) : ℝ)=(n : ℝ)-m := Nat.cast_sub (hmem n hn)
    rw [he]
    dsimp [latticePoint,v,a] at *
    have hmul := mul_le_mul_of_nonneg_left hna htp.le
    field_simp
    nlinarith
  have hsum := (Finset.sum_le_sum hcomp).trans
    (finite_shifted_geometric_sum_le (exp (-v)) (exp_pos _).le (exp_lt_one_iff.mpr (by linarith)) m s hmem)
  have h := mul_le_mul_of_nonneg_left (hsum.trans (inverse_exp_gap_le hv hv1)) (by positivity : 0≤1/sqrt rate)
  calc
    _≤(1/sqrt rate)*(2/v) := h
    _=3/t := by dsimp [v];field_simp


theorem tail_polynomial_pointwise {t z : ℝ} (ht : 0≤t) (hz : t≤z) :
    (1+z^3)*exp (-(z^2-t^2)/3)≤
      580*(1+t^3)*exp (-(2*t*(z-t))/3-(z-t)^2/6) := by
  have hu : 0≤z-t := sub_nonneg.mpr hz
  have hpoly : 1+z^3≤4*(1+t^3)*(1+(z-t)^3) := by
    have hcube : z^3≤4*(t^3+(z-t)^3) := by
      nlinarith [mul_nonneg (show 0≤t+(z-t) by linarith) (sq_nonneg (t-(z-t)))]
    nlinarith [mul_nonneg (pow_nonneg ht 3) (pow_nonneg hu 3)]
  have hdom := polynomial_gaussian_domination (z-t)
  rw [abs_of_nonneg hu] at hdom
  have hid : -(z^2-t^2)/3=-(2*t*(z-t))/3-(z-t)^2/3 := by ring
  rw [hid,exp_sub]
  have hfirst := mul_le_mul_of_nonneg_right hpoly (by positivity : 0≤exp (-(2*t*(z-t))/3)/exp ((z-t)^2/3))
  have hsecond := mul_le_mul_of_nonneg_left hdom
    (by positivity : 0≤4*(1+t^3)*exp (-(2*t*(z-t))/3))
  have he :
      (4*(1+t^3)*(1+(z-t)^3))*(exp (-(2*t*(z-t))/3)/exp ((z-t)^2/3))=
      (4*(1+t^3)*exp (-(2*t*(z-t))/3))*((1+(z-t)^3)*exp (-(z-t)^2/3)) := by
    rw [show -(z-t)^2/3=-((z-t)^2/3) by ring,exp_neg]
    ring
  rw [he] at hfirst
  apply hfirst.trans
  convert hsecond using 1
  rw [exp_sub,show -(z-t)^2/6=-((z-t)^2/6) by ring,exp_neg]
  ring

def tailSummationConstant : ℝ := 580*(4*exp (1/6)*sqrt (12*π)+6)

/-- The Gaussian tail scale survives the lattice sum uniformly in its threshold. -/
theorem weighted_tail_lattice_sum_le {rate t : ℝ} (hr : 1≤rate) (ht : 0≤t)
    (htop : t≤sqrt rate/2) (s : Finset ℕ) (hs : ∀n∈s,t≤latticePoint rate n) :
    (1/sqrt rate)*(∑ n∈s,(1+(latticePoint rate n)^3)*exp (-((latticePoint rate n)^2-t^2)/3))≤
      tailSummationConstant*(1+t^3)/(1+t) := by
  have hsum := Finset.sum_le_sum (s := s) (fun n hn => tail_polynomial_pointwise ht (hs n hn))
  rw [← Finset.mul_sum] at hsum
  have hscale := mul_le_mul_of_nonneg_left hsum (by positivity : 0≤1/sqrt rate)
  have hp : 0<1+t := by linarith
  by_cases ht1 : t≤1
  · have hdrop : (∑ n∈s,exp (-(2*t*(latticePoint rate n-t))/3-(latticePoint rate n-t)^2/6))≤
        ∑ n∈s,exp (-(latticePoint rate n-t)^2/6) := by
      apply Finset.sum_le_sum
      intro n hn
      have hu := sub_nonneg.mpr (hs n hn)
      exact exp_le_exp.mpr (by nlinarith [mul_nonneg ht hu])
    have h := hscale.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hdrop (by positivity)) (by positivity))
    have hg := mul_le_mul_of_nonneg_left (shifted_gaussian_sum_le hr ht htop s hs)
      (by positivity : 0≤580*(1+t^3))
    have hh := h.trans (by simpa only [mul_assoc,mul_comm,mul_left_comm] using hg)
    have hc : 0≤exp (1/6)*sqrt (12*π) := by positivity
    have hcoef : 2*exp (1/6)*sqrt (12*π)≤(4*exp (1/6)*sqrt (12*π)+6)/(1+t) := by
      apply (le_div_iff₀ hp).mpr
      nlinarith [mul_nonneg (sub_nonneg.mpr ht1) hc]
    have hfinal := mul_le_mul_of_nonneg_left hcoef (by positivity : 0≤580*(1+t^3))
    exact hh.trans (by simpa only [tailSummationConstant,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using hfinal)
  · have ht1' : 1≤t := le_of_not_ge ht1
    have hdrop : (∑ n∈s,exp (-(2*t*(latticePoint rate n-t))/3-(latticePoint rate n-t)^2/6))≤
        ∑ n∈s,exp (-(2*t*(latticePoint rate n-t))/3) := by
      exact Finset.sum_le_sum fun n _ => exp_le_exp.mpr (by nlinarith [sq_nonneg (latticePoint rate n-t)])
    have h := hscale.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hdrop (by positivity)) (by positivity))
    have hg := mul_le_mul_of_nonneg_left (shifted_exponential_sum_le hr ht1' htop s hs)
      (by positivity : 0≤580*(1+t^3))
    have hh := h.trans (by simpa only [mul_assoc,mul_comm,mul_left_comm] using hg)
    have htp : 0<t := by linarith
    have hrat : 3/t≤6/(1+t) := (div_le_div_iff₀ htp hp).mpr (by linarith)
    have hc : 3480≤tailSummationConstant := by
      have hp0 : 0≤exp (1/6)*sqrt (12*π) := by positivity
      unfold tailSummationConstant
      linarith
    have hfinal := (mul_le_mul_of_nonneg_left hrat (by positivity : 0≤580*(1+t^3))).trans
      (show 580*(1+t^3)*(6/(1+t))≤tailSummationConstant*(1+t^3)/(1+t) from by
        have hm := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hc (by positivity : 0≤1+t^3)) hp.le
        convert hm using 1; ring)
    exact hh.trans (by simpa only [mul_assoc,mul_comm,mul_left_comm] using hfinal)

end
end PaperC.V282.PoissonQuantitativeTailSum
