import PaperCV282.CrossoverMarkedComparison
import PaperCV282.CrossoverRareScaleExceptions
import PaperCV282.CrossoverUncappingLimit

/-! # The complete moving two-source marked crossover, Theorem 7.9

All finite comparisons are first divided by probabilities of actual events.
The common rare scale is used only to prove that these explicit errors vanish.
No convergence of the relative border/bulk weights is required.
-/
namespace PaperC.V282.CrossoverMarkedConvergence

open Filter Topology MeasureTheory InfiniteRademacher AllStartSoftPoisson BulkMarkedGeometry
open CrossoverMovingTarget CrossoverMarkedComparison CrossoverSparseSource CrossoverSparseTarget
open CrossoverMarkedCandidate CrossoverPrimeClockStable CrossoverBulkAtoms CrossoverRareScale
open CrossoverRareScaleProbabilities CrossoverRareScaleExceptions CrossoverUncappingLimit
open RarePrefixGeometry RarePrefixEvents RarePrefixPoisson RarePrefixMass MicroscopicNonvacancy
open PrimeEulerPNT ProcessAGGInput LaishramUniformInput PostQuadraticLiterature

noncomputable section

def cappedErrorBudget (M L K : ℕ) (delta : ℝ) : ℝ :=
  (hitProbability M L-infiniteRademacherMeasure.real (sourceSparseEvent M L K delta))/hitProbability M L+
  (infiniteRademacherMeasure.real (interiorEvent L)+infiniteRademacherMeasure.real (middleEvent M L delta))/
    infiniteRademacherMeasure.real (sourceSparseEvent M L K delta)+
  truncatedJointDistance M L K delta/
    (productJoint (bulkStarts M L delta) L K).real (sparseEvent (bulkStarts M L delta))+
  (totalRate (bulkStarts M L delta) L : ℝ)

theorem ratio_rebase (x y d : ℝ) (hd : d≠0) : (x/d)/(y/d)=x/y := by
  rw [div_div_div_cancel_right₀ hd]

theorem cappedErrorBudget_tendsto_zero
    (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (hLS : UniformPrimeDivisorStatement) (hShorey : ShoreySquareProductStatement)
    (hNR : PellInput.NicolasRobinDivisorLogBoundStatement)
    (sizes lengths : ℕ → ℕ) (hsizes : Tendsto sizes atTop atTop) (hlengths : Tendsto lengths atTop atTop)
    (K : ℕ) (beta delta : ℝ) (hbeta : 0 < beta) (hdelta : 0 < delta) (hdeltaOne : delta < 1)
    (hupper : ∀ᶠ n in atTop, (lengths n : ℝ) ≤ beta*Real.log (sizes n))
    (hrare : Tendsto (fun n => (fullRate (sizes n) (lengths n) : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => cappedErrorBudget (sizes n) (lengths n) K delta) atTop (𝓝 0) := by
  have hh := hit_probability_ratio_tendsto_one hAGG hPNT hLS hShorey hNR sizes lengths hsizes hlengths
    beta delta hbeta hdelta hdeltaOne hupper hrare
  have hs := source_sparse_event_ratio_tendsto_one hAGG hPNT sizes lengths hsizes hlengths K
    beta delta hbeta hdelta hdeltaOne hupper hrare
  have hp := product_sparse_ratio_tendsto_one sizes lengths hsizes hlengths K beta delta
    hdelta hdeltaOne hupper hrare
  have he := exceptions_rare_scale_tendsto_zero hLS hShorey hPNT hNR sizes lengths hsizes hlengths
    beta delta hbeta hdelta hdeltaOne hupper hrare
  have hd := truncated_joint_rare_scale_tendsto_zero hAGG hPNT sizes lengths hsizes hlengths K
    beta delta hbeta hdelta hdeltaOne hupper hrare
  have hb := bulk_rate_tendsto_zero sizes lengths hsizes beta delta hdelta hdeltaOne hupper
    (hlengths.eventually (eventually_ge_atTop 1)) hrare
  have h1 := (hh.sub hs).div hh (by norm_num : (1 : ℝ)≠0)
  have h2 := he.div hs (by norm_num : (1 : ℝ)≠0)
  have h3 := hd.div hp (by norm_num : (1 : ℝ)≠0)
  have ht := ((h1.add h2).add h3).add hb
  simp only [sub_self,zero_div,add_zero] at ht
  convert ht using 1
  funext n
  have hr (x y : ℝ) : (x/rareScale (sizes n) (lengths n) delta)/(y/rareScale (sizes n) (lengths n) delta)=x/y :=
    ratio_rebase x y _ (rareScale_pos _ _ _).ne'
  simp only [Pi.div_apply,cappedErrorBudget,← sub_div,hr]

/-- Every fixed prime-clock cap has vanishing true conditional total variation. -/
theorem cappedDistance_tendsto_zero
    (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (hLS : UniformPrimeDivisorStatement) (hShorey : ShoreySquareProductStatement)
    (hNR : PellInput.NicolasRobinDivisorLogBoundStatement)
    (sizes lengths : ℕ → ℕ) (hsizes : Tendsto sizes atTop atTop) (hlengths : Tendsto lengths atTop atTop)
    (K : ℕ) (beta delta : ℝ) (hbeta : 0 < beta) (hdelta : 0 < delta) (hdeltaOne : delta < 1)
    (hupper : ∀ᶠ n in atTop, (lengths n : ℝ) ≤ beta*Real.log (sizes n))
    (hrare : Tendsto (fun n => (fullRate (sizes n) (lengths n) : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => cappedDistance (sizes n) (lengths n) K delta) atTop (𝓝 0) := by
  have hc := logarithmic_lengths_eventually_contained sizes lengths hsizes beta hupper
  have hn := bulk_nonempty_eventually sizes lengths hsizes beta delta hdelta hdeltaOne hupper
    (hlengths.eventually (eventually_ge_atTop 1))
  have hp := product_sparse_ratio_tendsto_one sizes lengths hsizes hlengths K beta delta
    hdelta hdeltaOne hupper hrare
  have hd := truncated_joint_rare_scale_tendsto_zero hAGG hPNT sizes lengths hsizes hlengths K
    beta delta hbeta hdelta hdeltaOne hupper hrare
  apply squeeze_zero' ?_ ?_ (cappedErrorBudget_tendsto_zero hAGG hPNT hLS hShorey hNR sizes lengths
    hsizes hlengths K beta delta hbeta hdelta hdeltaOne hupper hrare)
  · filter_upwards [hc] with n hcn
    exact cappedDistance_nonneg K delta hcn
  · filter_upwards [hc,hn,hsizes.eventually (eventually_ge_atTop 2),hlengths.eventually (eventually_ge_atTop 1),
      hp.eventually (lt_mem_nhds (by norm_num : (1/2 : ℝ)<1)),
      hd.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1/2))] with n hcn hnn hM hL hpn hdn
    have herror : truncatedJointDistance (sizes n) (lengths n) K delta <
        (productJoint (bulkStarts (sizes n) (lengths n) delta) (lengths n) K).real
          (sparseEvent (bulkStarts (sizes n) (lengths n) delta)) :=
      (div_lt_div_iff_of_pos_right (rareScale_pos _ _ _)).mp (hdn.trans hpn)
    exact capped_comparison_bound hM hL hcn hdelta hnn herror

/-- Theorem 7.9, for the actual first contained start, exact signs and the two uncensored clocks.
The target is discrete at every prefix size and its mixture weights may oscillate. -/
theorem theorem_seven_nine
    (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (hLS : UniformPrimeDivisorStatement) (hShorey : ShoreySquareProductStatement)
    (hNR : PellInput.NicolasRobinDivisorLogBoundStatement)
    (sizes lengths : ℕ → ℕ) (hsizes : Tendsto sizes atTop atTop) (hlengths : Tendsto lengths atTop atTop)
    (beta delta : ℝ) (hbeta : 0 < beta) (hdelta : 0 < delta) (hdeltaOne : delta < 1)
    (hupper : ∀ᶠ n in atTop, (lengths n : ℝ) ≤ beta*Real.log (sizes n))
    (hrare : Tendsto (fun n => (fullRate (sizes n) (lengths n) : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => actualDistance (sizes n) (lengths n) delta) atTop (𝓝 0) := by
  apply actualDistance_tendsto_of_capped sizes lengths delta
    (logarithmic_lengths_eventually_contained sizes lengths hsizes beta hupper)
  intro K
  exact cappedDistance_tendsto_zero hAGG hPNT hLS hShorey hNR sizes lengths hsizes hlengths K
    beta delta hbeta hdelta hdeltaOne hupper hrare

end
end PaperC.V282.CrossoverMarkedConvergence
