import PaperCV282.AffineCrossoverLocationTransfer

/-! # Weak location limits from genuine affine comparison errors

These are assembly lemmas.  Their actual capped comparison and conditioned
interior errors must be supplied by the arithmetic budget, not postulated as
new literature inputs.  No future-prime neutrality appears here.
-/
namespace PaperC.V282.AffineCrossoverLocationLimits

open MeasureTheory Filter Topology InfiniteRademacher RarePrefixGeometry
open AffineCrossoverLocationSource AffineCrossoverLocationTarget AffineCrossoverLocationTransfer
open CrossoverLocationMixture CrossoverLocationGrid CrossoverResolvedLocationTarget
open scoped NNReal ENNReal BoundedContinuousFunction

noncomputable section

theorem location_laws_tendsto_of_errors
    (sizes lengths dimensions : ℕ→ℕ) (events : ℕ→Set InfiniteSample) (delta : ℝ)
    (hA : ∀ᶠ n in atTop,MeasurableSet (events n))
    (hpos : ∀ᶠ n in atTop,0 < infiniteRademacherMeasure.real (events n∩hitEvent (sizes n) (lengths n)))
    (hpositive : ∀ᶠ n in atTop,1≤lengths n)
    (htv : Tendsto (fun n => AffineCrossoverModel.cappedDistance
      (AffineCrossoverModel.conditionedMeasure (events n)) (sizes n) (lengths n) 0 delta
        (((2 : ℝ≥0)⁻¹)^dimensions n)) atTop (𝓝 0))
    (hi : Tendsto (fun n => conditionalInteriorProbability (sizes n) (lengths n) (events n)) atTop (𝓝 0))
    (p : ProbabilityMeasure ℝ) (q : ProbabilityMeasure (Bool×ℝ))
    (hp : Tendsto (fun n => physicalTargetLaw (sizes n) (lengths n) delta (dimensions n)) atTop (𝓝 p))
    (hq : Tendsto (fun n => AffineCrossoverLocationTarget.resolvedTargetLaw
      (sizes n) (lengths n) delta (dimensions n)) atTop (𝓝 q)) :
    Tendsto (fun n => firstLocationLaw (sizes n) (lengths n) (events n)) atTop (𝓝 p) ∧
    Tendsto (fun n => resolvedSourceLaw (sizes n) (lengths n) (events n)) atTop (𝓝 q) := by
  constructor
  · rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto] at hp ⊢
    intro F
    have hb : ∀ᶠ n in atTop,
        |(∫ x,F x ∂(firstLocationLaw (sizes n) (lengths n) (events n) : Measure ℝ))-
          (∫ x,F x ∂(physicalTargetLaw (sizes n) (lengths n) delta (dimensions n) : Measure ℝ))|≤
            4*‖F‖*AffineCrossoverModel.cappedDistance (AffineCrossoverModel.conditionedMeasure (events n))
              (sizes n) (lengths n) 0 delta (((2 : ℝ≥0)⁻¹)^dimensions n) := by
      filter_upwards [hA,hpos] with n hn hpn
      exact firstLocation_integral_error_le delta (dimensions n) hn hpn F
    have hz := squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) hb
      (show Tendsto (fun n => 4*‖F‖*AffineCrossoverModel.cappedDistance
        (AffineCrossoverModel.conditionedMeasure (events n)) (sizes n) (lengths n) 0 delta
          (((2 : ℝ≥0)⁻¹)^dimensions n)) atTop (𝓝 0) by
            simpa only [mul_zero] using htv.const_mul (4*‖F‖))
    have hd : Tendsto (fun n =>
        (∫ x,F x ∂(firstLocationLaw (sizes n) (lengths n) (events n) : Measure ℝ))-
          (∫ x,F x ∂(physicalTargetLaw (sizes n) (lengths n) delta (dimensions n) : Measure ℝ))) atTop (𝓝 0) :=
      tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using hz)
    simpa only [sub_add_cancel,zero_add] using hd.add (hp F)
  · rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto] at hq ⊢
    intro F
    have hb : ∀ᶠ n in atTop,
        |(∫ x,F x ∂(resolvedSourceLaw (sizes n) (lengths n) (events n) : Measure (Bool×ℝ)))-
          (∫ x,F x ∂(AffineCrossoverLocationTarget.resolvedTargetLaw
            (sizes n) (lengths n) delta (dimensions n) : Measure (Bool×ℝ)))|≤
              2*‖F‖*(2*AffineCrossoverModel.cappedDistance (AffineCrossoverModel.conditionedMeasure (events n))
                (sizes n) (lengths n) 0 delta (((2 : ℝ≥0)⁻¹)^dimensions n)+
                  conditionalInteriorProbability (sizes n) (lengths n) (events n)) := by
      filter_upwards [hA,hpos,hpositive] with n hn hpn hln
      exact resolvedSource_integral_error_le delta (dimensions n) hn hpn hln F
    have hz := squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) hb
      (show Tendsto (fun n => 2*‖F‖*(2*AffineCrossoverModel.cappedDistance
        (AffineCrossoverModel.conditionedMeasure (events n)) (sizes n) (lengths n) 0 delta
          (((2 : ℝ≥0)⁻¹)^dimensions n)+conditionalInteriorProbability (sizes n) (lengths n) (events n)))
            atTop (𝓝 0) by
        simpa only [mul_zero,add_zero] using ((htv.const_mul 2).add hi).const_mul (2*‖F‖))
    have hd : Tendsto (fun n =>
        (∫ x,F x ∂(resolvedSourceLaw (sizes n) (lengths n) (events n) : Measure (Bool×ℝ)))-
          (∫ x,F x ∂(AffineCrossoverLocationTarget.resolvedTargetLaw
            (sizes n) (lengths n) delta (dimensions n) : Measure (Bool×ℝ)))) atTop (𝓝 0) :=
      tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using hz)
    simpa only [sub_add_cancel,zero_add] using hd.add (hq F)

theorem location_phase_limit_of_errors
    (sizes lengths dimensions : ℕ→ℕ) (events : ℕ→Set InfiniteSample)
    (hsizes : Tendsto sizes atTop atTop) (hlengths : Tendsto lengths atTop atTop)
    (beta delta : ℝ) (hdelta : 0<delta) (hdeltaOne : delta<1)
    (hupper : ∀ᶠ n in atTop,(lengths n : ℝ)≤beta*Real.log (sizes n))
    (hA : ∀ᶠ n in atTop,MeasurableSet (events n))
    (hpos : ∀ᶠ n in atTop,0 < infiniteRademacherMeasure.real (events n∩hitEvent (sizes n) (lengths n)))
    (htv : Tendsto (fun n => AffineCrossoverModel.cappedDistance
      (AffineCrossoverModel.conditionedMeasure (events n)) (sizes n) (lengths n) 0 delta
        (((2 : ℝ≥0)⁻¹)^dimensions n)) atTop (𝓝 0))
    (hi : Tendsto (fun n => conditionalInteriorProbability (sizes n) (lengths n) (events n)) atTop (𝓝 0))
    (s : ℝ) (hphase : Tendsto (fun n => AffineCrossoverPhase.affinePhase
      (sizes n) (lengths n) (dimensions n)) atTop (𝓝 s)) :
    Tendsto (fun n => firstLocationLaw (sizes n) (lengths n) (events n)) atTop (𝓝 (crossoverLimitLaw s)) ∧
    Tendsto (fun n => resolvedSourceLaw (sizes n) (lengths n) (events n)) atTop (𝓝 (resolvedLimitLaw s)) := by
  obtain ⟨hp,hq⟩ := target_laws_tendsto sizes lengths dimensions hsizes hlengths beta delta hdelta hdeltaOne hupper s hphase
  exact location_laws_tendsto_of_errors sizes lengths dimensions events delta hA hpos
    (hlengths.eventually (eventually_ge_atTop 1)) htv hi _ _ hp hq

theorem location_phase_atTop_of_errors
    (sizes lengths dimensions : ℕ→ℕ) (events : ℕ→Set InfiniteSample)
    (hsizes : Tendsto sizes atTop atTop) (hlengths : Tendsto lengths atTop atTop)
    (beta delta : ℝ) (hdelta : 0<delta) (hdeltaOne : delta<1)
    (hupper : ∀ᶠ n in atTop,(lengths n : ℝ)≤beta*Real.log (sizes n))
    (hA : ∀ᶠ n in atTop,MeasurableSet (events n))
    (hpos : ∀ᶠ n in atTop,0 < infiniteRademacherMeasure.real (events n∩hitEvent (sizes n) (lengths n)))
    (htv : Tendsto (fun n => AffineCrossoverModel.cappedDistance
      (AffineCrossoverModel.conditionedMeasure (events n)) (sizes n) (lengths n) 0 delta
        (((2 : ℝ≥0)⁻¹)^dimensions n)) atTop (𝓝 0))
    (hi : Tendsto (fun n => conditionalInteriorProbability (sizes n) (lengths n) (events n)) atTop (𝓝 0))
    (hphase : Tendsto (fun n => AffineCrossoverPhase.affinePhase
      (sizes n) (lengths n) (dimensions n)) atTop atTop) :
    Tendsto (fun n => firstLocationLaw (sizes n) (lengths n) (events n)) atTop (𝓝 zeroLocationLaw) ∧
    Tendsto (fun n => resolvedSourceLaw (sizes n) (lengths n) (events n)) atTop
      (𝓝 (labelledLaw false zeroLocationLaw)) := by
  obtain ⟨hp,hq⟩ := target_laws_tendsto_border sizes lengths dimensions hsizes hlengths beta delta hdelta hdeltaOne hupper hphase
  exact location_laws_tendsto_of_errors sizes lengths dimensions events delta hA hpos
    (hlengths.eventually (eventually_ge_atTop 1)) htv hi _ _ hp hq

theorem location_phase_atBot_of_errors
    (sizes lengths dimensions : ℕ→ℕ) (events : ℕ→Set InfiniteSample)
    (hsizes : Tendsto sizes atTop atTop) (hlengths : Tendsto lengths atTop atTop)
    (beta delta : ℝ) (hdelta : 0<delta) (hdeltaOne : delta<1)
    (hupper : ∀ᶠ n in atTop,(lengths n : ℝ)≤beta*Real.log (sizes n))
    (hA : ∀ᶠ n in atTop,MeasurableSet (events n))
    (hpos : ∀ᶠ n in atTop,0 < infiniteRademacherMeasure.real (events n∩hitEvent (sizes n) (lengths n)))
    (htv : Tendsto (fun n => AffineCrossoverModel.cappedDistance
      (AffineCrossoverModel.conditionedMeasure (events n)) (sizes n) (lengths n) 0 delta
        (((2 : ℝ≥0)⁻¹)^dimensions n)) atTop (𝓝 0))
    (hi : Tendsto (fun n => conditionalInteriorProbability (sizes n) (lengths n) (events n)) atTop (𝓝 0))
    (hphase : Tendsto (fun n => AffineCrossoverPhase.affinePhase
      (sizes n) (lengths n) (dimensions n)) atTop atBot) :
    Tendsto (fun n => firstLocationLaw (sizes n) (lengths n) (events n)) atTop (𝓝 unitIntervalLaw) ∧
    Tendsto (fun n => resolvedSourceLaw (sizes n) (lengths n) (events n)) atTop
      (𝓝 (labelledLaw true unitIntervalLaw)) := by
  obtain ⟨hp,hq⟩ := target_laws_tendsto_bulk sizes lengths dimensions hsizes hlengths beta delta hdelta hdeltaOne hupper hphase
  exact location_laws_tendsto_of_errors sizes lengths dimensions events delta hA hpos
    (hlengths.eventually (eventually_ge_atTop 1)) htv hi _ _ hp hq

end
end PaperC.V282.AffineCrossoverLocationLimits
