import PaperCV282.CrossoverLocationProjection

/-! # The two infinite-phase location limits -/
namespace PaperC.V282.CrossoverLocationExtreme

open MeasureTheory Filter Topology CrossoverLocationPhase CrossoverLocationMixture CrossoverLocationProjection
open CrossoverMarkedTarget BulkPopulation BulkMarkedGeometry CrossoverLocationGrid AllStartSoftPoisson
open scoped NNReal ENNReal BoundedContinuousFunction

noncomputable section

theorem rate_div_border_tendsto_zero_of_phase_atTop
    (sizes lengths : ℕ→ℕ) (hsizes : Tendsto sizes atTop atTop)
    (hphase : Tendsto (fun n => crossoverPhase (sizes n) (lengths n)) atTop atTop) :
    Tendsto (fun n => (fullRate (sizes n) (lengths n) : ℝ)/((2 : ℝ)⁻¹)^Nat.primeCounting (lengths n))
      atTop (𝓝 0) := by
  have hlog : 0<Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hn := tendsto_neg_atTop_atBot.comp (hphase.atTop_mul_const hlog)
  have he := Real.tendsto_exp_atBot.comp hn
  apply he.congr'
  filter_upwards [hsizes.eventually (eventually_ge_atTop 1)] with n hn
  simpa only [Function.comp_def,neg_mul] using (rate_div_border_eq (by omega : 0<sizes n) (lengths n)).symm

theorem rate_div_border_tendsto_atTop_of_phase_atBot
    (sizes lengths : ℕ→ℕ) (hsizes : Tendsto sizes atTop atTop)
    (hphase : Tendsto (fun n => crossoverPhase (sizes n) (lengths n)) atTop atBot) :
    Tendsto (fun n => (fullRate (sizes n) (lengths n) : ℝ)/((2 : ℝ)⁻¹)^Nat.primeCounting (lengths n))
      atTop atTop := by
  have hlog : 0<Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hn := (tendsto_neg_atBot_atTop.comp hphase).atTop_mul_const hlog
  have he := Real.tendsto_exp_atTop.comp hn
  apply he.congr'
  filter_upwards [hsizes.eventually (eventually_ge_atTop 1)] with n hn
  exact (rate_div_border_eq (by omega : 0<sizes n) (lengths n)).symm

/-- Exact algebra for the genuine finite bulk population. -/
theorem borderWeight_eq_one_div (M L : ℕ) (delta : ℝ) :
    (borderWeight (bulkStarts M L delta) L : ℝ)=
      1/(1+(bulkRate M L delta : ℝ)/((2 : ℝ)⁻¹)^Nat.primeCounting L) := by
  change ((1/(2 : ℝ)^Nat.primeCounting L)/
    (1/(2 : ℝ)^Nat.primeCounting L+(bulkRate M L delta : ℝ)))=_
  rw [inv_pow]
  field_simp

theorem bulk_border_ratio_factor {M : ℕ} (hM : 0<M) (L : ℕ) (delta : ℝ) :
    ((bulkRate M L delta : ℝ)/(fullRate M L : ℝ))*
      ((fullRate M L : ℝ)/((2 : ℝ)⁻¹)^Nat.primeCounting L)=
        (bulkRate M L delta : ℝ)/((2 : ℝ)⁻¹)^Nat.primeCounting L := by
  have hp : (fullRate M L : ℝ)≠0 := by
    change (M : ℝ)/(2 : ℝ)^L≠0
    positivity
  field_simp

theorem borderWeight_tendsto_one_of_phase_atTop
    (sizes lengths : ℕ→ℕ) (hsizes : Tendsto sizes atTop atTop)
    (beta delta : ℝ) (hdelta : 0<delta) (hdeltaOne : delta<1)
    (hupper : ∀ᶠ n in atTop,(lengths n : ℝ)≤beta*Real.log (sizes n))
    (hpositive : ∀ᶠ n in atTop,1≤lengths n)
    (hphase : Tendsto (fun n => crossoverPhase (sizes n) (lengths n)) atTop atTop) :
    Tendsto (fun n => (borderWeight (bulkStarts (sizes n) (lengths n) delta) (lengths n) : ℝ))
      atTop (𝓝 1) := by
  have hp := bulkRate_ratio_tendsto_one sizes lengths hsizes beta delta hdelta hdeltaOne hupper hpositive
  have hr := hp.mul (rate_div_border_tendsto_zero_of_phase_atTop sizes lengths hsizes hphase)
  have hb : Tendsto (fun n => (bulkRate (sizes n) (lengths n) delta : ℝ)/
      ((2 : ℝ)⁻¹)^Nat.primeCounting (lengths n)) atTop (𝓝 0) := by
    apply (show Tendsto _ atTop (𝓝 (0 : ℝ)) from by simpa only [mul_zero] using hr).congr'
    filter_upwards [hsizes.eventually (eventually_ge_atTop 1)] with n hn
    exact bulk_border_ratio_factor (by omega) _ _
  convert (show Tendsto _ atTop (𝓝 (1 : ℝ)) from by
    simpa only [add_zero,div_one] using
      tendsto_const_nhds.div (hb.const_add 1) (by norm_num : (1 : ℝ)+0≠0)) using 1
  funext n
  exact borderWeight_eq_one_div _ _ _

theorem borderWeight_tendsto_zero_of_phase_atBot
    (sizes lengths : ℕ→ℕ) (hsizes : Tendsto sizes atTop atTop)
    (beta delta : ℝ) (hdelta : 0<delta) (hdeltaOne : delta<1)
    (hupper : ∀ᶠ n in atTop,(lengths n : ℝ)≤beta*Real.log (sizes n))
    (hpositive : ∀ᶠ n in atTop,1≤lengths n)
    (hphase : Tendsto (fun n => crossoverPhase (sizes n) (lengths n)) atTop atBot) :
    Tendsto (fun n => (borderWeight (bulkStarts (sizes n) (lengths n) delta) (lengths n) : ℝ))
      atTop (𝓝 0) := by
  have hp := bulkRate_ratio_tendsto_one sizes lengths hsizes beta delta hdelta hdeltaOne hupper hpositive
  have hr := hp.pos_mul_atTop (by norm_num : (0 : ℝ)<1)
    (rate_div_border_tendsto_atTop_of_phase_atBot sizes lengths hsizes hphase)
  have hb : Tendsto (fun n => (bulkRate (sizes n) (lengths n) delta : ℝ)/
      ((2 : ℝ)⁻¹)^Nat.primeCounting (lengths n)) atTop atTop := by
    apply hr.congr'
    filter_upwards [hsizes.eventually (eventually_ge_atTop 1)] with n hn
    exact bulk_border_ratio_factor (by omega) _ _
  simpa only [borderWeight_eq_one_div,Pi.div_apply] using
    tendsto_const_nhds.div_atTop (tendsto_const_nhds.add_atTop hb)

theorem bulkWeight_tendsto_of_borderWeight
    (sites : ℕ→Finset ℕ) (lengths : ℕ→ℕ) (a : ℝ)
    (ha : Tendsto (fun n => (borderWeight (sites n) (lengths n) : ℝ)) atTop (𝓝 a)) :
    Tendsto (fun n => (bulkWeight (sites n) (lengths n) : ℝ)) atTop (𝓝 (1-a)) := by
  apply (ha.const_sub 1).congr
  intro n
  have hw := congrArg ((↑) : ℝ≥0→ℝ) (weights_sum (sites n) (lengths n))
  simp only [NNReal.coe_add,NNReal.coe_one] at hw
  linarith

/-- At positive infinite phase all conditional macroscopic mass is at the border. -/
theorem physicalLocationMixtureLaw_tendsto_border
    (sizes lengths : ℕ→ℕ) (hsizes : Tendsto sizes atTop atTop)
    (beta delta : ℝ) (hdelta : 0<delta) (hdeltaOne : delta<1)
    (hupper : ∀ᶠ n in atTop,(lengths n : ℝ)≤beta*Real.log (sizes n))
    (hpositive : ∀ᶠ n in atTop,1≤lengths n)
    (hphase : Tendsto (fun n => crossoverPhase (sizes n) (lengths n)) atTop atTop) :
    Tendsto (fun n => physicalLocationMixtureLaw (sizes n) (lengths n) delta) atTop (𝓝 zeroLocationLaw) := by
  have ha := borderWeight_tendsto_one_of_phase_atTop sizes lengths hsizes beta delta hdelta hdeltaOne hupper hpositive hphase
  have hb := bulkWeight_tendsto_of_borderWeight (fun n => bulkStarts (sizes n) (lengths n) delta) lengths 1 ha
  have ht := mixtureLaw_tendsto _ _ (fun n => weights_sum (bulkStarts (sizes n) (lengths n) delta) (lengths n))
    1 0 (by norm_num) _ _ zeroLocationLaw unitIntervalLaw ha (by simpa using hb)
    (borderLocationLaw_tendsto sizes hsizes)
    (bulkLocationLaw_tendsto sizes lengths hsizes beta delta hdelta hdeltaOne hupper hpositive)
  have he : mixtureLaw 1 0 (by norm_num) zeroLocationLaw unitIntervalLaw=zeroLocationLaw := by
    apply Subtype.ext
    simp [mixtureLaw]
  rw [he] at ht
  exact ht

/-- At negative infinite phase the conditional first position becomes uniform on [0,1]. -/
theorem physicalLocationMixtureLaw_tendsto_bulk
    (sizes lengths : ℕ→ℕ) (hsizes : Tendsto sizes atTop atTop)
    (beta delta : ℝ) (hdelta : 0<delta) (hdeltaOne : delta<1)
    (hupper : ∀ᶠ n in atTop,(lengths n : ℝ)≤beta*Real.log (sizes n))
    (hpositive : ∀ᶠ n in atTop,1≤lengths n)
    (hphase : Tendsto (fun n => crossoverPhase (sizes n) (lengths n)) atTop atBot) :
    Tendsto (fun n => physicalLocationMixtureLaw (sizes n) (lengths n) delta) atTop (𝓝 unitIntervalLaw) := by
  have ha := borderWeight_tendsto_zero_of_phase_atBot sizes lengths hsizes beta delta hdelta hdeltaOne hupper hpositive hphase
  have hb := bulkWeight_tendsto_of_borderWeight (fun n => bulkStarts (sizes n) (lengths n) delta) lengths 0 ha
  have ht := mixtureLaw_tendsto _ _ (fun n => weights_sum (bulkStarts (sizes n) (lengths n) delta) (lengths n))
    0 1 (by norm_num) _ _ zeroLocationLaw unitIntervalLaw ha (by simpa using hb)
    (borderLocationLaw_tendsto sizes hsizes)
    (bulkLocationLaw_tendsto sizes lengths hsizes beta delta hdelta hdeltaOne hupper hpositive)
  have he : mixtureLaw 0 1 (by norm_num) zeroLocationLaw unitIntervalLaw=unitIntervalLaw := by
    apply Subtype.ext
    simp [mixtureLaw]
  rw [he] at ht
  exact ht

end
end PaperC.V282.CrossoverLocationExtreme
