import PaperCV282.SaddleAsymptotics

/-! # The convex saddle envelope with second-scale error

The tangent inequality is proved on the actual upper saddle branch by
monotonicity in its parameter. No inverse-function differentiability or
second derivative of the inverse branch is assumed.
-/
namespace PaperC.Prel8.SaddleEnvelope
open PaperC.V282.SaddleBranch PaperC.V282.SaddleParameters
open PaperC.V282.ExponentialIntegral PaperC.V282.SaddleAsymptotics
open Set Filter Topology
noncomputable section

/-- Derivative of the cost after subtracting a tangent of slope `v`. -/
theorem tangent_remainder_derivative (v : ℝ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun t => saddleCostParam t-v*saddleRatio t)
      (Real.exp u*(u-1)/u^2*(u-v)) u := by
  convert (hasDerivAt_saddleCostParam hu).sub
    ((hasDerivAt_saddleRatio hu.ne').const_mul v) using 1
  field_simp

/-- Tangent support proved directly in the exponential saddle parameter. -/
theorem parametric_tangent {u v : ℝ} (hu : 1 ≤ u) (hv : 1 ≤ v) :
    saddleCostParam v + v*(saddleRatio u-saddleRatio v) ≤ saddleCostParam u := by
  let f := fun t => saddleCostParam t-v*saddleRatio t
  have hc : ContinuousOn f (Ici 1) :=
    continuousOn_saddleCostParam.sub (continuousOn_const.mul continuousOn_saddleRatio)
  rcases le_total v u with hvu | huv
  · have hm : MonotoneOn f (Ici v) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici v)
        (hc.mono (fun _ ht => hv.trans ht))
      · intro t ht
        have ht' : v < t := by simpa using ht
        exact (tangent_remainder_derivative v (by linarith : 0<t)).differentiableAt.differentiableWithinAt
      · intro t ht
        have ht' : v < t := by simpa using ht
        rw [(tangent_remainder_derivative v (by linarith : 0<t)).deriv]
        exact mul_nonneg (div_nonneg (mul_nonneg (Real.exp_pos _).le (by linarith))
          (sq_nonneg _)) (by linarith)
    have h := hm (by simp) hvu hvu
    dsimp [f] at h
    linarith
  · have hm : AntitoneOn f (Icc 1 v) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc 1 v)
        (hc.mono (fun _ ht => ht.1))
      · intro t ht
        have ht' : 1<t ∧ t<v := by simpa using ht
        exact (tangent_remainder_derivative v (by linarith : 0<t)).differentiableAt.differentiableWithinAt
      · intro t ht
        have ht' : 1<t ∧ t<v := by simpa using ht
        rw [(tangent_remainder_derivative v (by linarith : 0<t)).deriv]
        exact mul_nonpos_of_nonneg_of_nonpos
          (div_nonneg (mul_nonneg (Real.exp_pos _).le (by linarith)) (sq_nonneg _)) (by linarith)
    have h := hm ⟨hu,huv⟩ ⟨hv,le_rfl⟩ huv
    dsimp [f] at h
    linarith

/-- The actual saddle cost lies above its tangent, including the branch endpoint. -/
theorem saddle_tangent {nu mu : ℝ} (hnu : Real.exp 1 ≤ nu) (hmu : Real.exp 1 ≤ mu) :
    saddleCost nu + upperSaddleBranch nu*(mu-nu) ≤ saddleCost mu := by
  have h := parametric_tangent (upperSaddleBranch_spec hmu).1 (upperSaddleBranch_spec hnu).1
  simpa only [(upperSaddleBranch_spec hmu).2, (upperSaddleBranch_spec hnu).2,
    ← saddleCost_eq_param hmu, ← saddleCost_eq_param hnu] using h

/-- The elementary minimization used in the envelope. -/
theorem two_sqrt_le_add_div {a t : ℝ} (ha : 0 ≤ a) (ht : 0<t) :
    2*Real.sqrt a ≤ t+a/t := by
  apply (mul_le_mul_iff_right₀ ht).mp
  have hs := sq_nonneg (t-Real.sqrt a)
  have hr := Real.sq_sqrt ha
  have he : t*(t+a/t)=t^2+a := by field_simp
  rw [he]
  nlinarith

/-- Exact finite envelope for any positive width in the domain of the upper branch. -/
theorem finite_envelope {H V w : ℝ} (hV : 0<V) (hw : 0<w)
    (hnu : Real.exp 1 ≤ H/V) (hmu : Real.exp 1 ≤ H/w)
    (hroot : V=saddleCost (H/V)) :
    2*V-V*(Real.sqrt ((H/V)*upperSaddleBranch (H/V)/V)-1)^2 ≤ w+saddleCost (H/w) := by
  let nu := H/V
  let u := upperSaddleBranch nu
  let a := nu*u/V
  let t := w/V
  have hnupos : 0<nu := (Real.exp_pos 1).trans_le hnu
  have hupos : 0<u := upperSaddleBranch_pos hnu
  have ha : 0≤a := (div_pos (mul_pos hnupos hupos) hV).le
  have ht : 0<t := div_pos hw hV
  have htangent := saddle_tangent hnu hmu
  have hmin := mul_le_mul_of_nonneg_left (two_sqrt_le_add_div ha ht) hV.le
  have hs := Real.sq_sqrt ha
  have halgebra : V*(1-a+t+a/t)=w+V+u*(H/w-nu) := by
    dsimp [a,t,nu]
    field_simp
    ring
  change 2*V-V*(Real.sqrt a-1)^2 ≤ _
  calc
    _ = V*(1-a+2*Real.sqrt a) := by nlinarith
    _ ≤ V*(1-a+t+a/t) := by nlinarith
    _ = _ := halgebra
    _ ≤ _ := by rw [hroot]; dsimp [nu,u] at *; linarith

/-- Rationalizing the square-root error gives a convenient uniform upper bound. -/
theorem sqrt_error_bound {A V : ℝ} (hA : 0≤A) (hV : 0<V) :
    V*(Real.sqrt (A/V)-1)^2 ≤ (A-V)^2/V := by
  have ha : 0≤A/V := div_nonneg hA hV.le
  have ht : 0≤Real.sqrt (A/V) := Real.sqrt_nonneg _
  have hsq := Real.sq_sqrt ha
  have hb : (Real.sqrt (A/V)-1)^2 ≤ (A/V-1)^2 := by
    conv_rhs => rw [← hsq]
    nlinarith [mul_nonneg (sq_nonneg (Real.sqrt (A/V)-1))
      (show 0≤(Real.sqrt (A/V))^2+2*Real.sqrt (A/V) by positivity)]
  calc
    _ ≤ V*(A/V-1)^2 := mul_le_mul_of_nonneg_left hb hV.le
    _ = _ := by field_simp

/-- Explicit error measured in units of the paper's second scale. -/
def relativeEnvelopeError (u : ℝ) : ℝ :=
  normalizedExponentialIntegral u ^ 2 / (u*saddleCostFactor u)

/-- This is little-o at the second scale, rather than only at the leading scale. -/
theorem relativeEnvelopeError_tendsto_zero :
    Tendsto relativeEnvelopeError atTop (𝓝 0) := by
  have h := ((tendsto_normalizedExponentialIntegral.pow 2).div tendsto_saddleCostFactor
    (by norm_num : (1 : ℝ) ≠ 0)).div_atTop tendsto_id
  convert h using 1
  funext u
  change normalizedExponentialIntegral u ^ 2 / (u*saddleCostFactor u) =
    (normalizedExponentialIntegral u ^ 2 / saddleCostFactor u) / u
  rw [div_div, mul_comm u]

/-- The relative loss is eventually at most 2/u, making the paper's O(nu/u) explicit. -/
theorem relativeEnvelopeError_order_bound :
    ∀ᶠ u : ℝ in atTop, relativeEnvelopeError u ≤ 2/u := by
  have h := ((tendsto_normalizedExponentialIntegral.pow 2).div tendsto_saddleCostFactor
    (by norm_num : (1 : ℝ) ≠ 0)).eventually (gt_mem_nhds (by norm_num : (1 : ℝ)^2/1<2))
  filter_upwards [h, eventually_gt_atTop (0 : ℝ)] with u hu hu0
  have hh := div_le_div_of_nonneg_right hu.le hu0.le
  change (normalizedExponentialIntegral u ^ 2 / saddleCostFactor u) / u ≤ 2/u at hh
  simpa only [relativeEnvelopeError, div_div, mul_comm u] using hh

/-- Bound the square-root envelope loss by an explicit vanishing relative error. -/
theorem parametric_error_bound {u : ℝ} (hu : saddleParameterBase ≤ u) :
    saddleCostParam u*(Real.sqrt (Real.exp u/saddleCostParam u)-1)^2 ≤
      saddleRatio u*relativeEnvelopeError u := by
  have hupos : 0<u := by linarith [saddleParameterBase_ge_two]
  have hf := saddleCostFactor_pos hu
  have hV : 0<saddleCostParam u := by
    rw [saddleCostParam_eq_exp_mul_factor]
    exact mul_pos (Real.exp_pos _) hf
  calc
    _ ≤ (exponentialIntegral u)^2/saddleCostParam u := by
      simpa only [saddleCostParam, sub_sub_cancel] using sqrt_error_bound (Real.exp_pos u).le hV
    _ = _ := by
      rw [saddleCostParam_eq_exp_mul_factor]
      unfold saddleRatio relativeEnvelopeError normalizedExponentialIntegral
      field_simp

/-- The actual hard saddle has a width-uniform envelope with an explicit remainder. -/
theorem hard_envelope {H w : ℝ} (hH : saddleThreshold 1 ≤ H) (hw : 0<w)
    (hmu : Real.exp 1 ≤ H/w) :
    2*saddleCutoff 1 H - (H/saddleCutoff 1 H)*relativeEnvelopeError (saddleParameter 1 H) ≤
      w+saddleCost (H/w) := by
  have hV := saddleCutoff_pos (by norm_num : (0 : ℝ)<1) hH
  have hdomain := saddleCutoff_domain (by norm_num : (0 : ℝ)<1) hH
  have hroot : saddleCutoff 1 H=saddleCost (H/saddleCutoff 1 H) := by
    simpa using saddleCutoff_equation (by norm_num : (0 : ℝ)<1) hH
  have he := finite_envelope hV hw hdomain hmu hroot
  have herr := parametric_error_bound (saddleParameter_spec (by norm_num : (0 : ℝ)<1) hH).1
  have hupos : 0<saddleParameter 1 H := by
    linarith [(saddleParameter_spec (by norm_num : (0 : ℝ)<1) hH).1, saddleParameterBase_ge_two]
  rw [upperSaddleBranch_div_saddleCutoff (by norm_num : (0 : ℝ)<1) hH] at he
  rw [div_saddleCutoff_eq_ratio (by norm_num : (0 : ℝ)<1) hH] at he ⊢
  simp only [saddleCutoff, one_mul] at he ⊢
  have hexp : saddleRatio (saddleParameter 1 H)*saddleParameter 1 H =
      Real.exp (saddleParameter 1 H) := div_mul_cancel₀ _ hupos.ne'
  rw [hexp] at he
  linarith

/-- The order bound in F.4 holds with constant 2 for every sufficiently large height. -/
theorem hard_envelope_order_eventually :
    ∃ Hzero : ℝ, ∀ H ≥ Hzero, ∀ w : ℝ, 0<w → Real.exp 1 ≤ H/w →
      2*saddleCutoff 1 H - 2*(H/saddleCutoff 1 H)/saddleParameter 1 H ≤
        w+saddleCost (H/w) := by
  have he := (tendsto_saddleParameter_atTop (by norm_num : (0 : ℝ)<1)).eventually
    relativeEnvelopeError_order_bound
  have hall : ∀ᶠ H : ℝ in atTop, ∀ w : ℝ, 0<w → Real.exp 1 ≤ H/w →
      2*saddleCutoff 1 H - 2*(H/saddleCutoff 1 H)/saddleParameter 1 H ≤ w+saddleCost (H/w) := by
    filter_upwards [he, eventually_ge_atTop (saddleThreshold 1)] with H herr hH
    intro w hw hmu
    have hnu : 0≤H/saddleCutoff 1 H :=
      (Real.exp_pos 1).le.trans (saddleCutoff_domain (by norm_num : (0 : ℝ)<1) hH)
    have hprod := mul_le_mul_of_nonneg_left herr hnu
    have heq : (H/saddleCutoff 1 H)*(2/saddleParameter 1 H)=
        2*(H/saddleCutoff 1 H)/saddleParameter 1 H := by ring
    rw [heq] at hprod
    linarith [hard_envelope hH hw hmu]
  exact eventually_atTop.mp hall

/-- F.4 at the required second-scale precision, uniformly over every admissible width. -/
theorem hard_envelope_eventually (epsilon : ℝ) (hepsilon : 0<epsilon) :
    ∃ Hzero : ℝ, ∀ H ≥ Hzero, ∀ w : ℝ, 0<w → Real.exp 1 ≤ H/w →
      2*saddleCutoff 1 H - epsilon*(H/saddleCutoff 1 H) ≤ w+saddleCost (H/w) := by
  have he := (relativeEnvelopeError_tendsto_zero.comp
    (tendsto_saddleParameter_atTop (by norm_num : (0 : ℝ)<1))).eventually (gt_mem_nhds hepsilon)
  have hall : ∀ᶠ H : ℝ in atTop, ∀ w : ℝ, 0<w → Real.exp 1 ≤ H/w →
      2*saddleCutoff 1 H - epsilon*(H/saddleCutoff 1 H) ≤ w+saddleCost (H/w) := by
    filter_upwards [he, eventually_ge_atTop (saddleThreshold 1)] with H herr hH
    intro w hw hmu
    have hnu : 0≤H/saddleCutoff 1 H :=
      (Real.exp_pos 1).le.trans (saddleCutoff_domain (by norm_num : (0 : ℝ)<1) hH)
    have hbound := hard_envelope hH hw hmu
    have hprod := mul_le_mul_of_nonneg_left herr.le hnu
    dsimp only [Function.comp_apply] at hprod
    nlinarith
  exact eventually_atTop.mp hall

end
end PaperC.Prel8.SaddleEnvelope
