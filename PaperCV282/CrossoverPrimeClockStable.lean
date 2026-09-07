import PaperCV282.CrossoverPrimeClockCutoff
import PaperCV282.RarePrefixSubsequence

/-! # The actual truncated prime clock and the complete signed bulk law

The finite cylinder is used to invoke stable factorization. Almost-sure
equality then returns the original prime clock, including its declared default.
-/
namespace PaperC.V282.CrossoverPrimeClockStable

open Filter Topology MeasureTheory ProbabilityTheory InfiniteRademacher InfiniteCylinderTransfer
open CrossoverPrimeClockBase CrossoverPrimeClockCylinder CrossoverPrimeClockCutoff
open PrimeClockDistribution MicroscopicBorderEvents BulkMarkedTypes BulkMarkedSource BulkMarkedTarget
open BulkMarkedGeometry BulkMarkedStable BulkMarkedRates BulkMarkedComparison BulkMarkedConvergence
open HardPoissonRates AllStartSoftPoisson PrimeEulerPNT ProcessAGGInput SharpConditioning

noncomputable section
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P
local instance instProbabilityInfiniteRademacher : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

/-- The record appearing in the paper, with the original measurable clock. -/
def actualClockRecord (L K : ℕ) (omega : InfiniteSample) : Bool × ℕ :=
  (if omega ∈ borderEvent L then true else false,min (primeOvershoot L omega) K)

theorem measurable_actualClockRecord (L K : ℕ) : Measurable (actualClockRecord L K) := by
  exact (Measurable.ite (measurableSet_borderEvent L) measurable_const measurable_const).prodMk
    ((measurable_of_countable (fun n : ℕ => min n K)).comp (measurable_primeOvershoot L))

theorem borderClockRecord_ae_eq_actual (L K : ℕ) :
    borderClockRecord L K =ᵐ[infiniteRademacherMeasure] actualClockRecord L K := by
  filter_upwards [cappedPrimeClock_ae_eq_min L K] with omega h
  exact Prod.ext rfl h

def truncatedJointDistance (M L K : ℕ) (delta : ℝ) : ℝ :=
  measureTotalVariation
    (infiniteRademacherMeasure.map (fun omega =>
      (actualClockRecord L K omega,spatialMarkedSource (bulkStarts M L delta) L omega)))
    ((infiniteRademacherMeasure.map (actualClockRecord L K)).prod
      (spatialTargetMeasure (bulkStarts M L delta) L))

theorem truncatedJointDistance_nonneg (M L K : ℕ) (delta : ℝ) :
    0 ≤ truncatedJointDistance M L K delta := by
  letI instProbabilityJoint : IsProbabilityMeasure
      (infiniteRademacherMeasure.map (fun omega =>
        (actualClockRecord L K omega,spatialMarkedSource (bulkStarts M L delta) L omega))) :=
    Measure.isProbabilityMeasure_map ((measurable_actualClockRecord L K).prodMk
      (measurable_spatialMarkedSource _ _)).aemeasurable
  letI instProbabilityRecord : IsProbabilityMeasure (infiniteRademacherMeasure.map (actualClockRecord L K)) :=
    Measure.isProbabilityMeasure_map (measurable_actualClockRecord L K).aemeasurable
  exact measureTotalVariation_nonneg _ _

theorem truncated_joint_le_conditional {M L K : ℕ} (delta : ℝ)
    (hrecord : Measurable[MeasurableSpace.comap (restrictToFinite (hardCutoff M)) inferInstance]
      (borderClockRecord L K)) :
    truncatedJointDistance M L K delta ≤ bulkConditionalDistance M L delta := by
  have he := borderClockRecord_ae_eq_actual L K
  have hj : (fun omega => (borderClockRecord L K omega,spatialMarkedSource (bulkStarts M L delta) L omega))
      =ᵐ[infiniteRademacherMeasure]
      (fun omega => (actualClockRecord L K omega,spatialMarkedSource (bulkStarts M L delta) L omega)) := by
    filter_upwards [he] with omega h
    exact Prod.ext h rfl
  have h := recorded_joint_le_conditional M L delta (borderClockRecord L K) hrecord
  rw [Measure.map_congr hj,Measure.map_congr he] at h
  exact h

/-- The finite truncation level is quantified after the uniform size threshold. -/
theorem truncated_joint_rate_eventually
    (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax delta epsilon eta : ℝ) (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax)
    (hdelta : 0 < delta) (hepsilon : 0 < epsilon) (heta : 0 < eta) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L K : ℕ, 2^K ≤ L →
      betaMin*Real.log M ≤ (L+1 : ℝ) → (L+1 : ℝ) ≤ betaMax*Real.log M →
      (fullRate M L : ℝ) ≤ 1 →
      truncatedJointDistance M L K delta ≤ 67*bulkRelativeRate M L epsilon eta := by
  obtain ⟨Mone,hone⟩ := theorem_seven_seven hAGG hPNT betaMin betaMax delta epsilon eta
    hbetaMin hbeta hdelta hepsilon heta
  obtain ⟨Mtwo,htwo⟩ := measurable_borderClockRecord_hard_eventually betaMax (lt_trans hbetaMin hbeta)
  refine ⟨max Mone Mtwo,?_⟩
  intro M hM L K hL hlo hhi hr
  exact (truncated_joint_le_conditional delta (htwo M (by omega) L K hL hhi)).trans
    (hone M (by omega) L hlo hhi hr)

/-- Full signed stable factorization with the actual prime clock along arbitrary rare subsequences. -/
theorem truncated_joint_relative_along_subsequence
    (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (sizes lengths : ℕ → ℕ) (hsizes : Tendsto sizes atTop atTop)
    (hlengths : Tendsto lengths atTop atTop) (K : ℕ)
    (beta delta : ℝ) (hbeta : 0 < beta) (hdelta : 0 < delta)
    (hupper : ∀ᶠ n in atTop, (lengths n : ℝ) ≤ beta*Real.log (sizes n))
    (hrare : Tendsto (fun n => (fullRate (sizes n) (lengths n) : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => truncatedJointDistance (sizes n) (lengths n) K delta /
      (fullRate (sizes n) (lengths n) : ℝ)) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun _ =>
    div_nonneg (truncatedJointDistance_nonneg _ _ _ _) (by positivity)) ?_
    (RarePrefixSubsequence.signed_relative_along_subsequence hAGG hPNT sizes lengths hsizes
      beta delta hbeta hdelta hupper hrare)
  obtain ⟨Mzero,hzero⟩ := measurable_borderClockRecord_hard_eventually (beta+1) (by linarith)
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hsizes)
  filter_upwards [hupper,hlog.eventually (eventually_ge_atTop (1 : ℝ)),
    hsizes.eventually (eventually_ge_atTop Mzero),hlengths.eventually (eventually_ge_atTop (2^K))]
    with n hu hl hn hL
  dsimp only [Function.comp_def] at hl
  have hm := hzero (sizes n) hn (lengths n) K hL (by nlinarith)
  exact div_le_div_of_nonneg_right (truncated_joint_le_conditional delta hm) (by positivity)

end
end PaperC.V282.CrossoverPrimeClockStable
