import PaperCV282.PoissonQuantitativeLocal

/-! # A quadratic entropy lower bound on the whole central interval

This bound retains Gaussian decay when estimating absolute local errors;
the cubic Taylor error alone would lose that decay near the interval ends.
-/
namespace PaperC.V282.PoissonQuantitativeEntropy

open Real Set PoissonStirlingBounds

noncomputable section

theorem hasDerivAt_entropy_shifted {x : ℝ} (hx : -1<x) :
    HasDerivAt (fun y => poissonEntropy (1+y)) (log (1+x)) x := by
  have hp : 0<1+x := by linarith
  have hi := (hasDerivAt_id x).const_add 1
  have h := ((hi.mul (hi.log hp.ne')).sub hi).add_const 1
  convert h using 1 <;> first | rfl | simp [hp.ne',one_div]

theorem entropy_lower_third {x : ℝ} (hx : |x|≤1/2) :
    x^2/3≤poissonEntropy (1+x) := by
  let f : ℝ→ℝ := fun y => poissonEntropy (1+y)-y^2/3
  have hd (y : ℝ) (hy : -1<y) : HasDerivAt f (log (1+y)-2*y/3) y := by
    convert (hasDerivAt_entropy_shifted hy).sub ((hasDerivAt_pow 2 y).div_const 3) using 1 <;> first | rfl | ring
  have hzero : f 0=0 := by simp [f,poissonEntropy]
  have hnonneg : 0≤f x := by
    by_cases hxp : 0≤x
    · have hmono : MonotoneOn f (Icc 0 (1/2)) := by
        apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
        · intro y hy
          exact (hd y (by have h := hy.1;linarith)).continuousAt.continuousWithinAt
        · intro y hy
          exact (hd y (by have h := (interior_subset hy).1;linarith)).hasDerivWithinAt
        · intro y hy
          have hy' := interior_subset hy
          have hp : 0<1+y := by have h := hy'.1;linarith
          have hl := one_sub_inv_le_log_of_pos hp
          have hid : 1-(1+y)⁻¹=y/(1+y) := by field_simp;ring
          rw [hid] at hl
          have hb : 2*y/3≤y/(1+y) := by
            apply (le_div_iff₀ hp).mpr
            have h0 := hy'.1
            have h1 := hy'.2
            nlinarith
          linarith
      have h := hmono (by simp) ⟨hxp,(le_abs_self x).trans hx⟩ hxp
      simpa only [hzero] using h
    · have hxm : x≤0 := le_of_not_ge hxp
      have hanti : AntitoneOn f (Icc (-1/2) 0) := by
        apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
        · intro y hy
          exact (hd y (by have h := hy.1;linarith)).continuousAt.continuousWithinAt
        · intro y hy
          exact (hd y (by have h := (interior_subset hy).1;linarith)).hasDerivWithinAt
        · intro y hy
          have hy' := interior_subset hy
          have hp : 0<1+y := by have h := hy'.1;linarith
          have hl := log_le_sub_one_of_pos hp
          have h0 := hy'.2
          linarith
      have h := hanti ⟨by have h := neg_abs_le x;linarith,hxm⟩ (by norm_num) hxm
      simpa only [hzero] using h
  exact sub_nonneg.mp hnonneg

/-- The true entropy retains exp(-z²/3) decay throughout |n-rate|<=rate/2. -/
theorem entropy_central_lower {rate value : ℝ} (hr : 0<rate)
    (hv : |value-rate|≤rate/2) :
    (value-rate)^2/(3*rate)≤rate*poissonEntropy (value/rate) := by
  have hx : |(value-rate)/rate|≤1/2 := by
    rw [abs_div,abs_of_pos hr]
    exact (div_le_iff₀ hr).mpr (by linarith)
  have ht := mul_le_mul_of_nonneg_left (entropy_lower_third hx) hr.le
  have he : 1+(value-rate)/rate=value/rate := by field_simp;ring
  rw [he] at ht
  have hid : (value-rate)^2/(3*rate)=rate*(((value-rate)/rate)^2/3) := by
    field_simp
  rw [hid]
  exact ht

/-- A global exponential difference bound preserving the smaller exponent. -/
theorem abs_exp_neg_sub_le (a b : ℝ) :
    |exp (-a)-exp (-b)|≤exp (-min a b)*|a-b| := by
  have hd (y : ℝ) : HasDerivAt (fun z : ℝ => exp (-z)) (-exp (-y)) y := by
    simpa only [mul_neg_one,Pi.neg_apply,id_eq] using ((hasDerivAt_id y).neg.exp)
  have hb (y : ℝ) (hy : y∈Icc (min a b) (max a b)) :
      ‖-exp (-y)‖≤exp (-min a b) := by
    rw [norm_neg,Real.norm_eq_abs,abs_of_pos (exp_pos _)]
    exact exp_le_exp.mpr (neg_le_neg hy.1)
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun y _ => (hd y).hasDerivWithinAt) hb (convex_Icc _ _)
    (show a∈Icc (min a b) (max a b) from ⟨min_le_left _ _,le_max_left _ _⟩)
    (show b∈Icc (min a b) (max a b) from ⟨min_le_right _ _,le_max_right _ _⟩)
  simpa only [Real.norm_eq_abs,abs_sub_comm] using h

end
end PaperC.V282.PoissonQuantitativeEntropy
