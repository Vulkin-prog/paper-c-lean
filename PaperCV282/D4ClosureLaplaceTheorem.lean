import PaperCV282.D4ClosureLaplaceTarget

/-! # Companion D.4: compact Laplace tests, including the moving phase

The source is the true centered sum of exact-run Dirac masses, and the
deterministic target is the Laplace functional of the genuine two-sided
spatial Poisson measure. Only a fixed-limit replacement needs a phase limit.
-/
namespace PaperC.V282.D4ClosureLaplaceTheorem

open MeasureTheory ProbabilityTheory Filter Topology Real InfiniteRademacher InfiniteCylinderTransfer
open D4ClosureLaplaceFunctional D4ClosureLaplaceSource D4ClosureLaplaceTransfer D4ClosureLaplaceTarget
open GrowingLevelParameters AllStartSoftPoisson SpatialMarkedParameters
open ProcessAGGInput PrimeEulerPNT HardPoissonRates RareConditioningRates SaddleParameters SaddleScales
open D4ClosurePointMeasure

noncomputable section

/-- No convergent phase or assumed approximation appears in the moving-target statement. -/
theorem companion_D4_laplace_moving (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (sizes : ℕ → ℕ) (hsizes : Tendsto sizes atTop atTop)
    (g : ℝ × ℤ → ℝ) (hg : Continuous g) (hg0 : ∀ z, 0 ≤ g z) (hgc : HasCompactSupport g)
    (c : ℝ) (hc : 0 < c) (A : ℕ → Set InfiniteSample)
    (hA : ∀ᶠ n in atTop, MeasurableSet[MeasurableSpace.comap
      (restrictToFinite (hardCutoff (sizes n))) inferInstance] (A n))
    (hpos : ∀ᶠ n in atTop, 0 < infiniteRademacherMeasure.real (A n))
    (hbudget : ∀ᶠ n in atTop, eventInformation (A n) ≤
      saddleCutoff 1 (log (sizes n))-c*saddleNu 1 (log (sizes n))) :
    Tendsto (fun n =>
      (∫ omega, exp (-(∫ z, g z ∂centeredSourceMeasure (sizes n) omega))
        ∂cond infiniteRademacherMeasure (A n)) - laplaceFunctional (dyadicPhase (sizes n)) g)
      atTop (𝓝 0) := by
  obtain ⟨d,E,hlo,hhi⟩ := compact_support_level_band g hgc
  have h := compact_source_laplace_moving_error hAGG hPNT sizes hsizes d E g hg0
    (fun r => (hg.comp (continuous_id.prodMk continuous_const)).continuousOn) hlo hhi c hc A hA hpos hbudget
  apply h.congr'
  filter_upwards [hsizes.eventually (eventually_ge_atTop (1 : ℕ)),
    fixed_depth_eventually sizes hsizes d] with n hn hd
  rw [laplaceFunctional_window _ d E g hlo hhi]
  have hscale : criticalSpatialScale (sizes n) (movingLength (sizes n) d) =
      (2 : ℝ)^(dyadicPhase (sizes n)+d) := fullRate_eq_phase hn hd
  rw [hscale]

/-- The same approximation compares the two actual test expectations. -/
theorem companion_D4_laplace_actual_target (hAGG : ProcessAGGStatement)
    (hPNT : PrimeNumberTheoremRemainder) (sizes : ℕ → ℕ) (hsizes : Tendsto sizes atTop atTop)
    (g : ℝ × ℤ → ℝ) (hg : Continuous g) (hg0 : ∀ z, 0 ≤ g z) (hgc : HasCompactSupport g)
    (c : ℝ) (hc : 0 < c) (A : ℕ → Set InfiniteSample)
    (hA : ∀ᶠ n in atTop, MeasurableSet[MeasurableSpace.comap
      (restrictToFinite (hardCutoff (sizes n))) inferInstance] (A n))
    (hpos : ∀ᶠ n in atTop, 0 < infiniteRademacherMeasure.real (A n))
    (hbudget : ∀ᶠ n in atTop, eventInformation (A n) ≤
      saddleCutoff 1 (log (sizes n))-c*saddleNu 1 (log (sizes n))) :
    Tendsto (fun n =>
      (∫ omega, exp (-(∫ z, g z ∂centeredSourceMeasure (sizes n) omega))
        ∂cond infiniteRademacherMeasure (A n)) -
      (∫ sample : IntegerSpatialSample, exp (-(∫ z, g z ∂integerPointMeasure sample))
        ∂integerSpatialSampleMeasure (dyadicPhase (sizes n)))) atTop (𝓝 0) := by
  simp_rw [integer_target_laplace _ g hg hg0 hgc]
  exact companion_D4_laplace_moving hAGG hPNT sizes hsizes g hg hg0 hgc c hc A hA hpos hbudget

theorem continuous_laplaceFunctional (g : ℝ × ℤ → ℝ) (hgc : HasCompactSupport g) :
    Continuous (fun theta => laplaceFunctional theta g) := by
  obtain ⟨d,E,hlo,hhi⟩ := compact_support_level_band g hgc
  have hfun : (fun theta => laplaceFunctional theta g) = fun theta : ℝ =>
      exp (-((2 : ℝ)^(theta+d)*∫ t in Set.Ico (1 : ℝ) 2,
        markedRetentionIntegrand E (fun t e => g (t,(e : ℤ)-d)) t)) := by
    funext theta
    exact laplaceFunctional_window theta d E g hlo hhi
  rw [hfun]
  fun_prop (disch := norm_num)

/-- A phase-convergent subsequence replaces the moving deterministic target by one fixed target. -/
theorem companion_D4_laplace_phase_limit (hAGG : ProcessAGGStatement)
    (hPNT : PrimeNumberTheoremRemainder) (sizes : ℕ → ℕ) (hsizes : Tendsto sizes atTop atTop)
    (theta : ℝ) (hphase : Tendsto (fun n => dyadicPhase (sizes n)) atTop (𝓝 theta))
    (g : ℝ × ℤ → ℝ) (hg : Continuous g) (hg0 : ∀ z, 0 ≤ g z) (hgc : HasCompactSupport g)
    (c : ℝ) (hc : 0 < c) (A : ℕ → Set InfiniteSample)
    (hA : ∀ᶠ n in atTop, MeasurableSet[MeasurableSpace.comap
      (restrictToFinite (hardCutoff (sizes n))) inferInstance] (A n))
    (hpos : ∀ᶠ n in atTop, 0 < infiniteRademacherMeasure.real (A n))
    (hbudget : ∀ᶠ n in atTop, eventInformation (A n) ≤
      saddleCutoff 1 (log (sizes n))-c*saddleNu 1 (log (sizes n))) :
    Tendsto (fun n => ∫ omega, exp (-(∫ z, g z ∂centeredSourceMeasure (sizes n) omega))
      ∂cond infiniteRademacherMeasure (A n)) atTop (𝓝 (laplaceFunctional theta g)) := by
  have htarget := (continuous_laplaceFunctional g hgc).continuousAt.tendsto.comp hphase
  have hsource := companion_D4_laplace_moving hAGG hPNT sizes hsizes g hg hg0 hgc c hc A hA hpos hbudget
  simpa only [sub_add_cancel,zero_add,Function.comp_def] using hsource.add htarget

end
end PaperC.V282.D4ClosureLaplaceTheorem
