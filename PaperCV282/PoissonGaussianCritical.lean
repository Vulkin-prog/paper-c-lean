import PaperCV282.PoissonGaussianLimit
import PaperCV282.GaussianThresholdAR
import PaperCV282.GrowingLevelParameters

/-! # The exact target specialization of Theorem 5.10

The sizes may run along an arbitrary subsequence. The phase is the actual
fractional part of log_2 N, and critical levels are signed integers. Conversion
to natural excesses is used only after their eventual nonnegativity is proved.
-/
namespace PaperC.V282.PoissonGaussianCritical

open MeasureTheory ProbabilityTheory Filter GrowingLevelParameters AllStartSoftPoisson
open PoissonGaussianTarget PoissonGaussianLimit
open scoped Topology NNReal

noncomputable section

def criticalExcess (R : Finset ℤ) (d : ℕ) (r : R) : ℕ := ((d : ℤ) + r.val).toNat

def criticalPoissonRates (theta : ℝ) (R : Finset ℤ) (r : R) : ℝ≥0 :=
  ⟨(2 : ℝ)^(theta-(r.val : ℝ)-1), Real.rpow_nonneg (by norm_num) _⟩

theorem depths_le_base_eventually (sizes depths : ℕ → ℕ)
    (hsizes : Tendsto sizes atTop atTop)
    (hsmall : Tendsto (fun n => (depths n : ℝ)/Real.log (sizes n)) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, depths n ≤ criticalBase (sizes n) := by
  have hlog : Tendsto (fun n => Real.log (sizes n)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hsizes)
  have hplus : Tendsto (fun n => ((depths n : ℝ)+1)/Real.log (sizes n)) atTop (𝓝 0) := by
    simpa only [add_div, add_zero] using hsmall.add
      ((tendsto_const_nhds (x := (1 : ℝ))).div_atTop hlog)
  have htwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  filter_upwards [hplus.eventually_lt_const (one_div_pos.mpr htwo), hsizes.eventually_ge_atTop 2]
    with n hn hN
  have hln : 0 < Real.log (sizes n : ℝ) := Real.log_pos (by exact_mod_cast hN)
  have hbound : (depths n : ℝ) ≤ Real.log (sizes n) / Real.log 2 := by
    have hb := (div_lt_iff₀ hln).mp hn
    rw [one_div, mul_comm, ← div_eq_mul_inv] at hb
    linarith
  unfold criticalBase
  exact (Nat.le_floor_iff (div_nonneg hln.le htwo.le)).mpr hbound

theorem fullRate_phase_eventually (sizes depths : ℕ → ℕ)
    (hsizes : Tendsto sizes atTop atTop)
    (hsmall : Tendsto (fun n => (depths n : ℝ)/Real.log (sizes n)) atTop (𝓝 0)) :
    ∀ᶠ n in atTop,
      (fullRate (sizes n) (movingLength (sizes n) (depths n)) : ℝ) =
        (2 : ℝ)^(dyadicPhase (sizes n) + (depths n : ℝ)) := by
  filter_upwards [depths_le_base_eventually sizes depths hsizes hsmall,
    hsizes.eventually_ge_atTop 1] with n hd hN
  exact fullRate_eq_phase hN hd

theorem moving_fullRate_tendsto_atTop (sizes depths : ℕ → ℕ)
    (hsizes : Tendsto sizes atTop atTop) (hdepths : Tendsto depths atTop atTop)
    (hsmall : Tendsto (fun n => (depths n : ℝ)/Real.log (sizes n)) atTop (𝓝 0)) :
    Tendsto (fun n => (fullRate (sizes n) (movingLength (sizes n) (depths n)) : ℝ)) atTop atTop := by
  apply tendsto_atTop_mono' atTop _ ((tendsto_pow_atTop_atTop_of_one_lt
    (by norm_num : (1 : ℝ)<2)).comp hdepths)
  filter_upwards [depths_le_base_eventually sizes depths hsizes hsmall,
    hsizes.eventually_ge_atTop 1] with n hd hN
  exact (fullRate_depth_bounds hN hd).1

theorem criticalExcess_eventually (depths : ℕ → ℕ) (hdepths : Tendsto depths atTop atTop)
    (R : Finset ℤ) (J : ℕ) :
    ∀ᶠ n in atTop, (∀ r : R, (J : ℤ) ≤ (depths n : ℤ)+r.val) ∧
      (∀ r : R, J ≤ criticalExcess R (depths n) r) ∧
      Function.Injective (criticalExcess R (depths n)) := by
  filter_upwards [hdepths.eventually_ge_atTop (R.sup Int.natAbs + J)] with n hn
  have hl (r : R) : (J : ℤ) ≤ (depths n : ℤ)+r.val := by
    have habs : r.val.natAbs ≤ R.sup Int.natAbs := Finset.le_sup (f := Int.natAbs) r.property
    have hneg : -(r.val.natAbs : ℤ) ≤ r.val := by omega
    omega
  refine ⟨hl, ?_, ?_⟩
  · intro r
    unfold criticalExcess
    have := hl r
    omega
  · intro r s he
    have hr := hl r
    have hs := hl s
    unfold criticalExcess at he
    have he' := congrArg (fun k : ℕ => (k : ℤ)) he
    rw [Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg (by omega)] at he'
    apply Subtype.ext
    omega

theorem critical_rate_eq_phase {N d : ℕ} (R : Finset ℤ) (r : R)
    (hN : 1 ≤ N) (hd : d ≤ criticalBase N) (hr : 0 ≤ (d : ℤ)+r.val) :
    (fullRate N (movingLength N d) : ℝ)/(2 : ℝ)^(criticalExcess R d r+1) =
      (2 : ℝ)^(dyadicPhase N-(r.val : ℝ)-1) := by
  rw [fullRate_eq_phase hN hd, ← Real.rpow_natCast,
    ← Real.rpow_sub (by norm_num : (0 : ℝ)<2)]
  congr 1
  have he : (criticalExcess R d r : ℝ) = (d : ℝ)+(r.val : ℝ) := by
    unfold criticalExcess
    exact_mod_cast Int.toNat_of_nonneg hr
  push_cast
  rw [he]
  ring

theorem critical_rates_tendsto (sizes depths : ℕ → ℕ) (theta : ℝ) (R : Finset ℤ)
    (hsizes : Tendsto sizes atTop atTop) (hdepths : Tendsto depths atTop atTop)
    (hsmall : Tendsto (fun n => (depths n : ℝ)/Real.log (sizes n)) atTop (𝓝 0))
    (hphase : Tendsto (fun n => dyadicPhase (sizes n)) atTop (𝓝 theta)) (r : R) :
    Tendsto (fun n => (fullRate (sizes n) (movingLength (sizes n) (depths n)) : ℝ)/
      (2 : ℝ)^(criticalExcess R (depths n) r+1)) atTop (𝓝 (criticalPoissonRates theta R r : ℝ)) := by
  have hcont : Continuous (fun x : ℝ => (2 : ℝ)^(x-(r.val : ℝ)-1)) := by fun_prop (disch := norm_num)
  have h := hcont.continuousAt.tendsto.comp hphase
  apply h.congr'
  filter_upwards [depths_le_base_eventually sizes depths hsizes hsmall,
    hsizes.eventually_ge_atTop 1, criticalExcess_eventually depths hdepths R 0] with n hd hN he
  exact (critical_rate_eq_phase R r hN hd (he.1 r)).symm

/-- The actual target limit with the paper's moving depth, phase and signed critical levels. -/
theorem theorem_five_ten_target (sizes depths : ℕ → ℕ) (theta : ℝ) (R : Finset ℤ) (J : ℕ)
    (hsizes : Tendsto sizes atTop atTop) (hdepths : Tendsto depths atTop atTop)
    (hsmall : Tendsto (fun n => (depths n : ℝ)/Real.log (sizes n)) atTop (𝓝 0))
    (hphase : Tendsto (fun n => dyadicPhase (sizes n)) atTop (𝓝 theta)) :
    Tendsto (fun n => jointThresholdLaw
      (fullRate (sizes n) (movingLength (sizes n) (depths n))) J (criticalExcess R (depths n))) atTop
      (𝓝 (poissonGaussianTarget J (criticalPoissonRates theta R))) := by
  apply jointThresholdLaw_tendsto _ J _ (criticalPoissonRates theta R)
    (moving_fullRate_tendsto_atTop sizes depths hsizes hdepths hsmall)
  · filter_upwards [criticalExcess_eventually depths hdepths R J] with n hn
    exact hn.2.2
  · filter_upwards [criticalExcess_eventually depths hdepths R J] with n hn
    exact hn.2.1
  · exact critical_rates_tendsto sizes depths theta R hsizes hdepths hsmall hphase

end
end PaperC.V282.PoissonGaussianCritical
