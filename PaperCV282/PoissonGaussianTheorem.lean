import PaperCV282.PoissonGaussianSource
import PaperCV282.PoissonGaussianCritical
import PaperCV282.SignedAggregateHardBudget

/-!
# Theorem 5.10 on the actual conditioned arithmetic source

The joint weak limit is derived from the proved aggregate comparison and the
proved geometric target limit. The sole external inputs are the directional
Stein solution theorem and the ordinary prime-number remainder. No CLT,
independence of the displayed vectors, or vanishing source error is assumed.
-/
namespace PaperC.V282.PoissonGaussianTheorem

open MeasureTheory Filter InfiniteRademacher InfiniteCylinderTransfer
open PoissonGaussianSource PoissonGaussianCritical PoissonGaussianTarget SignedAggregateHardBudget
open GrowingLevelParameters AllStartSoftPoisson RareConditioningRates AggregateInformationBudget
open SaddleParameters SaddleScales HardPoissonRates DirectionalSteinInput PrimeEulerPNT
open MarkedDetruncation MixedLengthAffine
open scoped Topology NNReal

noncomputable section

/-- Exact count of runs at the literal integer critical level b_N+r. -/
def criticalExactCount (N : ℕ) (r : ℤ) :=
  infiniteExactLengthCount N (((criticalBase N : ℤ)+r).toNat) 0

theorem critical_physical_length {N d : ℕ} (R : Finset ℤ) (r : R)
    (hd : d≤criticalBase N) (hr : 0≤(d : ℤ)+r.val) :
    movingLength N d+criticalExcess R d r=((criticalBase N : ℤ)+r.val).toNat := by
  unfold movingLength criticalExcess
  omega

/-- The excess coordinate used in the limit is precisely the count X_(N,r). -/
theorem criticalExactCount_eq_excess {N d : ℕ} (R : Finset ℤ) (r : R)
    (hd : d≤criticalBase N) (hr : 0≤(d : ℤ)+r.val) :
    criticalExactCount N r.val=
      infiniteExactLengthCount N (movingLength N d) (criticalExcess R d r) := by
  funext omega
  have he := critical_physical_length R r hd hr
  have he' : excessRowCount (((criticalBase N : ℤ)+r.val).toNat) 0=
      excessRowCount (movingLength N d) (criticalExcess R d r) := by
    unfold excessRowCount
    omega
  unfold criticalExactCount infiniteExactLengthCount
  apply Finset.sum_congr rfl
  intro x hx
  rw [he']

/-- Every finite set of critical observables has its literal meaning eventually. -/
theorem criticalExactCount_eq_eventually (sizes depths : ℕ → ℕ)
    (hsizes : Tendsto sizes atTop atTop) (hdepths : Tendsto depths atTop atTop)
    (hsmall : Tendsto (fun n => (depths n : ℝ)/Real.log (sizes n)) atTop (𝓝 0)) (R : Finset ℤ) :
    ∀ᶠ n in atTop, ∀ r : R, criticalExactCount (sizes n) r.val=
      infiniteExactLengthCount (sizes n) (movingLength (sizes n) (depths n)) (criticalExcess R (depths n) r) := by
  filter_upwards [depths_le_base_eventually sizes depths hsizes hsmall,
    criticalExcess_eventually depths hdepths R 0] with n hd hr
  intro r
  exact criticalExactCount_eq_excess R r hd (hr.1 r)

/-- The full actual conditional joint Poisson--Gaussian conclusion, along arbitrary size subsequences. -/
theorem theorem_five_ten (hStein : DirectionalSteinFactorsStatement)
    (hPNT : PrimeNumberTheoremRemainder) (c : ℝ) (hc : 0<c)
    (sizes depths : ℕ → ℕ) (theta : ℝ) (R : Finset ℤ) (J : ℕ)
    (hsizes : Tendsto sizes atTop atTop) (hdepths : Tendsto depths atTop atTop)
    (hsmall : Tendsto (fun n => (depths n : ℝ)/Real.log (sizes n)) atTop (𝓝 0))
    (hphase : Tendsto (fun n => dyadicPhase (sizes n)) atTop (𝓝 theta))
    (C : ℕ → Set InfiniteSample)
    (hC : ∀ᶠ n in atTop,
      MeasurableSet[MeasurableSpace.comap (restrictToFinite (hardCutoff (sizes n))) inferInstance] (C n))
    (hpos : ∀ n, 0 < infiniteRademacherMeasure.real (C n))
    (hbudget : ∀ᶠ n in atTop,
      aggregateLogCost (eventInformation (C n)) (fullRate (sizes n) (movingLength (sizes n) (depths n)))≤
        saddleCutoff 1 (Real.log (sizes n))-c*saddleNu 1 (Real.log (sizes n))) :
    Tendsto (fun n => conditionalJointLaw (sizes n) (movingLength (sizes n) (depths n)) J
      (criticalExcess R (depths n)) (C n) (hpos n)) atTop
      (𝓝 (poissonGaussianTarget J (criticalPoissonRates theta R))) := by
  have htv := (theorem_five_eight_aggregate_hard_sequences hStein hPNT c hc sizes depths hsizes hsmall C
    hC (Filter.Eventually.of_forall hpos) hbudget).2
  have htarget := theorem_five_ten_target sizes depths theta R J hsizes hdepths hsmall hphase
  exact source_joint_limit_of_aggregate_tv sizes (fun n => movingLength (sizes n) (depths n)) J
    (fun n => criticalExcess R (depths n)) (criticalPoissonRates theta R) C hpos hsizes htv htarget

end
end PaperC.V282.PoissonGaussianTheorem
