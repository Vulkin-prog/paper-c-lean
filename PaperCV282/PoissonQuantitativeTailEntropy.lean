import PaperCV282.PoissonQuantitativeEnvelope

/-! # Entropy lower bounds anchored at a moving upper-tail threshold -/
namespace PaperC.V282.PoissonQuantitativeTailEntropy

open MeasureTheory ProbabilityTheory Real Set
open PoissonQuantitativeLocal PoissonQuantitativeEntropy PoissonQuantitativeAbsolute
open PoissonQuantitativeEnvelope PoissonQuantitativeLattice PoissonEntropyTaylor PoissonStirlingBounds

noncomputable section

theorem entropy_increment_lower {x y : ℝ} (hx : 0≤x) (hxy : x≤y) (hy : y≤1/2) :
    (y^2-x^2)/3≤poissonEntropy (1+y)-poissonEntropy (1+x) := by
  let f : ℝ→ℝ := fun z => poissonEntropy (1+z)-z^2/3
  have hd (z : ℝ) (hz : -1<z) : HasDerivAt f (log (1+z)-2*z/3) z := by
    convert (hasDerivAt_entropy_shifted hz).sub ((hasDerivAt_pow 2 z).div_const 3) using 1 <;> first | rfl | ring
  have hm : MonotoneOn f (Icc 0 (1/2)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
    · intro z hz
      exact (hd z (by have h := hz.1;linarith)).continuousAt.continuousWithinAt
    · intro z hz
      exact (hd z (by have h := (interior_subset hz).1;linarith)).hasDerivWithinAt
    · intro z hz
      have hz' := interior_subset hz
      have hp : 0<1+z := by have h := hz'.1;linarith
      have hl := one_sub_inv_le_log_of_pos hp
      have he : 1-(1+z)⁻¹=z/(1+z) := by field_simp;ring
      rw [he] at hl
      have hb : 2*z/3≤z/(1+z) := by
        apply (le_div_iff₀ hp).mpr
        nlinarith [hz'.1,hz'.2]
      linarith
  have h := hm ⟨hx,hxy.trans hy⟩ ⟨hx.trans hxy,hy⟩ hxy
  dsimp [f] at h
  linarith

/-- Preserves the full exp(-t²/2) factor while integrating to the right of t. -/
theorem entropy_from_threshold {rate t z : ℝ} (hr : 0<rate) (ht : 0≤t)
    (htz : t≤z) (hz : z≤sqrt rate/2) :
    t^2/2-2*t^3/sqrt rate+(z^2-t^2)/3≤rate*poissonEntropy (1+z/sqrt rate) := by
  have hs : 0<sqrt rate := sqrt_pos.mpr hr
  have hsq := sq_sqrt hr.le
  have hinc := entropy_increment_lower (x := t/sqrt rate) (y := z/sqrt rate)
    (by positivity) (div_le_div_of_nonneg_right htz hs.le)
    ((div_le_iff₀ hs).mpr (by linarith))
  have hx : |t/sqrt rate|≤1/2 := by
    rw [abs_of_nonneg (by positivity : 0≤t/sqrt rate)]
    exact (div_le_iff₀ hs).mpr (by linarith)
  have htay := entropy_taylor_remainder_le hx
  rw [abs_of_nonneg (by positivity : 0≤t/sqrt rate)] at htay
  have hlow := (abs_le.mp htay).1
  have h1 := mul_le_mul_of_nonneg_left hinc hr.le
  have h2 := mul_le_mul_of_nonneg_left hlow hr.le
  have he2 : rate*(-(2*(t/sqrt rate)^3))=-2*t^3/sqrt rate := by
    field_simp
    nlinarith [congrArg (fun u : ℝ => u*t^3) hsq]
  have hea : rate*((z/sqrt rate)^2-(t/sqrt rate)^2)/3=(z^2-t^2)/3 := by
    rw [div_pow,div_pow,hsq]
    field_simp
  have heb : rate*(t/sqrt rate)^2/2=t^2/2 := by
    rw [div_pow,hsq]
    field_simp
  rw [mul_sub,← mul_div_assoc,hea] at h1
  rw [he2,mul_sub,← mul_div_assoc,heb] at h2
  simp only [div_eq_mul_inv] at h1 h2 ⊢
  nlinarith only [h1,h2]

end
end PaperC.V282.PoissonQuantitativeTailEntropy
