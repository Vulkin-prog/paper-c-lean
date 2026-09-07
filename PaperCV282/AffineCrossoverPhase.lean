import PaperCV282.CrossoverLocationExtreme

/-! # Exact affine phases and the three limiting weight regimes

The integer `d` is the effective border codimension.  Its later identification
with the affine row-space calculation is separate from this exact algebra.
-/
namespace PaperC.V282.AffineCrossoverPhase

open Filter Topology BulkPopulation AllStartSoftPoisson
open scoped NNReal

noncomputable section

def affinePhase (M L d : ℕ) : ℝ :=
  (L : ℝ)-Real.log M/Real.log 2-d

theorem rate_div_border_eq {M : ℕ} (hM : 0<M) (L d : ℕ) :
    (fullRate M L : ℝ)/((2 : ℝ)⁻¹)^d =
      Real.exp (-affinePhase M L d*Real.log 2) := by
  have hMr : (0 : ℝ)<M := by exact_mod_cast hM
  have hlog : Real.log (2 : ℝ)≠0 := ne_of_gt (Real.log_pos (by norm_num))
  have he : -affinePhase M L d*Real.log 2 =
      Real.log M+((d : ℝ)*Real.log 2-(L : ℝ)*Real.log 2) := by
    unfold affinePhase
    field_simp
    ring
  rw [he,Real.exp_add,Real.exp_sub,Real.exp_log hMr,Real.exp_nat_mul,Real.exp_nat_mul,
    Real.exp_log (by norm_num : (0 : ℝ)<2)]
  change ((M : ℝ)/(2 : ℝ)^L)/((2 : ℝ)⁻¹)^d = _
  rw [inv_pow]
  field_simp

theorem rate_div_border_tendsto
    (sizes lengths dimensions : ℕ→ℕ) (hsizes : Tendsto sizes atTop atTop) (s : ℝ)
    (hphase : Tendsto (fun n => affinePhase (sizes n) (lengths n) (dimensions n)) atTop (𝓝 s)) :
    Tendsto (fun n => (fullRate (sizes n) (lengths n) : ℝ)/((2 : ℝ)⁻¹)^dimensions n)
      atTop (𝓝 ((2 : ℝ)^(-s))) := by
  have ht := Real.continuous_exp.continuousAt.tendsto.comp ((hphase.neg).mul_const (Real.log 2))
  have ht' : Tendsto (fun n => Real.exp (-affinePhase (sizes n) (lengths n) (dimensions n)*Real.log 2))
      atTop (𝓝 ((2 : ℝ)^(-s))) := by
    simpa only [Real.rpow_def_of_pos (by norm_num : (0 : ℝ)<2),mul_comm,Function.comp_def] using ht
  apply ht'.congr'
  filter_upwards [hsizes.eventually (eventually_ge_atTop 1)] with n hn
  exact (rate_div_border_eq (by omega) _ _).symm

theorem rate_div_border_tendsto_zero_of_phase_atTop
    (sizes lengths dimensions : ℕ→ℕ) (hsizes : Tendsto sizes atTop atTop)
    (hphase : Tendsto (fun n => affinePhase (sizes n) (lengths n) (dimensions n)) atTop atTop) :
    Tendsto (fun n => (fullRate (sizes n) (lengths n) : ℝ)/((2 : ℝ)⁻¹)^dimensions n)
      atTop (𝓝 0) := by
  have hlog : 0<Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have he := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (hphase.atTop_mul_const hlog))
  apply he.congr'
  filter_upwards [hsizes.eventually (eventually_ge_atTop 1)] with n hn
  simpa only [Function.comp_def,neg_mul] using (rate_div_border_eq (by omega) (lengths n) (dimensions n)).symm

theorem rate_div_border_tendsto_atTop_of_phase_atBot
    (sizes lengths dimensions : ℕ→ℕ) (hsizes : Tendsto sizes atTop atTop)
    (hphase : Tendsto (fun n => affinePhase (sizes n) (lengths n) (dimensions n)) atTop atBot) :
    Tendsto (fun n => (fullRate (sizes n) (lengths n) : ℝ)/((2 : ℝ)⁻¹)^dimensions n)
      atTop atTop := by
  have hlog : 0<Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have he := Real.tendsto_exp_atTop.comp ((tendsto_neg_atBot_atTop.comp hphase).atTop_mul_const hlog)
  apply he.congr'
  filter_upwards [hsizes.eventually (eventually_ge_atTop 1)] with n hn
  exact (rate_div_border_eq (by omega) (lengths n) (dimensions n)).symm

theorem bulk_border_ratio_factor {M : ℕ} (hM : 0<M) (L d : ℕ) (delta : ℝ) :
    ((bulkRate M L delta : ℝ)/(fullRate M L : ℝ))*
      ((fullRate M L : ℝ)/((2 : ℝ)⁻¹)^d)=
        (bulkRate M L delta : ℝ)/((2 : ℝ)⁻¹)^d := by
  have hp : (fullRate M L : ℝ)≠0 := by
    change (M : ℝ)/(2 : ℝ)^L≠0
    positivity
  field_simp

theorem bulk_div_border_tendsto
    (sizes lengths dimensions : ℕ→ℕ) (hsizes : Tendsto sizes atTop atTop)
    (beta delta : ℝ) (hdelta : 0<delta) (hdeltaOne : delta<1)
    (hupper : ∀ᶠ n in atTop,(lengths n : ℝ)≤beta*Real.log (sizes n))
    (hpositive : ∀ᶠ n in atTop,1≤lengths n)
    (s : ℝ) (hphase : Tendsto (fun n => affinePhase (sizes n) (lengths n) (dimensions n)) atTop (𝓝 s)) :
    Tendsto (fun n => (bulkRate (sizes n) (lengths n) delta : ℝ)/((2 : ℝ)⁻¹)^dimensions n)
      atTop (𝓝 ((2 : ℝ)^(-s))) := by
  have ht := (bulkRate_ratio_tendsto_one sizes lengths hsizes beta delta hdelta hdeltaOne hupper hpositive).mul
    (rate_div_border_tendsto sizes lengths dimensions hsizes s hphase)
  apply (show Tendsto _ atTop (𝓝 ((2 : ℝ)^(-s))) from by simpa only [one_mul] using ht).congr'
  filter_upwards [hsizes.eventually (eventually_ge_atTop 1)] with n hn
  exact bulk_border_ratio_factor (by omega) _ _ _

theorem mixture_weights_tendsto
    (sizes lengths dimensions : ℕ→ℕ) (hsizes : Tendsto sizes atTop atTop)
    (beta delta : ℝ) (hdelta : 0<delta) (hdeltaOne : delta<1)
    (hupper : ∀ᶠ n in atTop,(lengths n : ℝ)≤beta*Real.log (sizes n))
    (hpositive : ∀ᶠ n in atTop,1≤lengths n)
    (s : ℝ) (hphase : Tendsto (fun n => affinePhase (sizes n) (lengths n) (dimensions n)) atTop (𝓝 s)) :
    Tendsto (fun n => ((2 : ℝ)⁻¹)^dimensions n /
      (((2 : ℝ)⁻¹)^dimensions n+(bulkRate (sizes n) (lengths n) delta : ℝ)))
      atTop (𝓝 (1/(1+(2 : ℝ)^(-s)))) ∧
    Tendsto (fun n => (bulkRate (sizes n) (lengths n) delta : ℝ) /
      (((2 : ℝ)⁻¹)^dimensions n+(bulkRate (sizes n) (lengths n) delta : ℝ)))
      atTop (𝓝 ((2 : ℝ)^(-s)/(1+(2 : ℝ)^(-s)))) := by
  have ht := bulk_div_border_tendsto sizes lengths dimensions hsizes beta delta hdelta hdeltaOne hupper hpositive s hphase
  have hd : 1+(2 : ℝ)^(-s)≠0 := by positivity
  constructor
  · convert tendsto_const_nhds.div (ht.const_add 1) hd using 1
    funext n
    dsimp only [Pi.div_apply]
    have ha : ((2 : ℝ)⁻¹)^dimensions n≠0 := by positivity
    field_simp
  · convert ht.div (ht.const_add 1) hd using 1
    funext n
    dsimp only [Pi.div_apply]
    have ha : ((2 : ℝ)⁻¹)^dimensions n≠0 := by positivity
    field_simp

theorem border_weight_tendsto_one_of_phase_atTop
    (sizes lengths dimensions : ℕ→ℕ) (hsizes : Tendsto sizes atTop atTop)
    (beta delta : ℝ) (hdelta : 0<delta) (hdeltaOne : delta<1)
    (hupper : ∀ᶠ n in atTop,(lengths n : ℝ)≤beta*Real.log (sizes n))
    (hpositive : ∀ᶠ n in atTop,1≤lengths n)
    (hphase : Tendsto (fun n => affinePhase (sizes n) (lengths n) (dimensions n)) atTop atTop) :
    Tendsto (fun n => ((2 : ℝ)⁻¹)^dimensions n /
      (((2 : ℝ)⁻¹)^dimensions n+(bulkRate (sizes n) (lengths n) delta : ℝ))) atTop (𝓝 1) := by
  have hp := bulkRate_ratio_tendsto_one sizes lengths hsizes beta delta hdelta hdeltaOne hupper hpositive
  have hr := hp.mul (rate_div_border_tendsto_zero_of_phase_atTop sizes lengths dimensions hsizes hphase)
  have hb : Tendsto (fun n => (bulkRate (sizes n) (lengths n) delta : ℝ)/((2 : ℝ)⁻¹)^dimensions n)
      atTop (𝓝 0) := by
    apply (show Tendsto _ atTop (𝓝 (0 : ℝ)) from by simpa only [mul_zero] using hr).congr'
    filter_upwards [hsizes.eventually (eventually_ge_atTop 1)] with n hn
    exact bulk_border_ratio_factor (by omega) _ _ _
  convert (show Tendsto _ atTop (𝓝 (1 : ℝ)) from by
    simpa only [add_zero,div_one] using
      tendsto_const_nhds.div (hb.const_add 1) (by norm_num : (1 : ℝ)+0≠0)) using 1
  funext n
  dsimp only [Pi.div_apply]
  have ha : ((2 : ℝ)⁻¹)^dimensions n≠0 := by positivity
  field_simp

theorem border_weight_tendsto_zero_of_phase_atBot
    (sizes lengths dimensions : ℕ→ℕ) (hsizes : Tendsto sizes atTop atTop)
    (beta delta : ℝ) (hdelta : 0<delta) (hdeltaOne : delta<1)
    (hupper : ∀ᶠ n in atTop,(lengths n : ℝ)≤beta*Real.log (sizes n))
    (hpositive : ∀ᶠ n in atTop,1≤lengths n)
    (hphase : Tendsto (fun n => affinePhase (sizes n) (lengths n) (dimensions n)) atTop atBot) :
    Tendsto (fun n => ((2 : ℝ)⁻¹)^dimensions n /
      (((2 : ℝ)⁻¹)^dimensions n+(bulkRate (sizes n) (lengths n) delta : ℝ))) atTop (𝓝 0) := by
  have hp := bulkRate_ratio_tendsto_one sizes lengths hsizes beta delta hdelta hdeltaOne hupper hpositive
  have hr := hp.pos_mul_atTop (by norm_num : (0 : ℝ)<1)
    (rate_div_border_tendsto_atTop_of_phase_atBot sizes lengths dimensions hsizes hphase)
  have hb : Tendsto (fun n => (bulkRate (sizes n) (lengths n) delta : ℝ)/((2 : ℝ)⁻¹)^dimensions n)
      atTop atTop := by
    apply hr.congr'
    filter_upwards [hsizes.eventually (eventually_ge_atTop 1)] with n hn
    exact bulk_border_ratio_factor (by omega) _ _ _
  convert (show Tendsto (fun n => 1/(1+(bulkRate (sizes n) (lengths n) delta : ℝ)/
      ((2 : ℝ)⁻¹)^dimensions n)) atTop (𝓝 (0 : ℝ)) from
        tendsto_const_nhds.div_atTop (tendsto_const_nhds.add_atTop hb)) using 1
  funext n
  have ha : ((2 : ℝ)⁻¹)^dimensions n≠0 := by positivity
  field_simp

end
end PaperC.V282.AffineCrossoverPhase
