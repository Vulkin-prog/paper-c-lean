import PaperCV282.AffineCrossoverMarkedComparison
import PaperCV282.AffineCrossoverNormalization

/-! # All losses in the true rare conditioning, expressed as source probabilities -/
namespace PaperC.V282.AffineCrossoverCappedBudget

open Filter Topology MeasureTheory ProbabilityTheory InfiniteRademacher
open AffineCrossoverModel AffineCrossoverNormalization AffineCrossoverMarkedComparison
open CrossoverSparseSource CrossoverMarkedCandidate CrossoverMarkedModel
open CrossoverBulkAtoms CrossoverPrimeClockStable BulkMarkedGeometry
open RarePrefixGeometry RarePrefixEvents MicroscopicNonvacancy MicroscopicBorderEvents
open SharpConditioning
open scoped NNReal ENNReal

noncomputable section

def cappedErrorBudget (mu : Measure InfiniteSample) (M L K : ℕ) (delta : ℝ) : ℝ :=
  (hitProbability mu M L-mu.real (sourceSparseEvent M L K delta))/hitProbability mu M L+
  (mu.real (interiorEvent L)+mu.real (middleEvent M L delta))/mu.real (sourceSparseEvent M L K delta)+
  jointDistance mu M L K delta/
    (AffineCrossoverModel.productJoint mu (bulkStarts M L delta) L K).real
      (CrossoverSparseTarget.sparseEvent (bulkStarts M L delta))+
  (totalRate (bulkStarts M L delta) L : ℝ)

theorem cappedDistance_nonneg (mu : Measure InfiniteSample) [IsProbabilityMeasure mu]
    (M L K : ℕ) (delta : ℝ) (alpha : ℝ≥0) (hh : 0<hitProbability mu M L) :
    0≤cappedDistance mu M L K delta alpha := by
  letI instProbabilitySource : IsProbabilityMeasure (sourceLaw mu M L delta) :=
    sourceLaw_probability mu M L delta hh
  letI instProbabilityCappedSource : IsProbabilityMeasure ((sourceLaw mu M L delta).map (capBorder K)) :=
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
  letI instProbabilityCappedTarget : IsProbabilityMeasure
      ((AffineCrossoverTarget.targetLaw M L delta alpha).map (capBorder K)) :=
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
  exact measureTotalVariation_nonneg _ _

variable (mu : ℕ→Measure InfiniteSample) [∀ n, IsProbabilityMeasure (mu n)]
  (sizes lengths : ℕ→ℕ) (K : ℕ) (delta : ℝ) (alpha : ℕ→ℝ≥0)

omit [∀ n, IsProbabilityMeasure (mu n)] in
theorem cappedErrorBudget_tendsto_zero
    (ha : ∀ᶠ n in atTop,0<alpha n)
    (hh : Tendsto (fun n=>hitProbability (mu n) (sizes n) (lengths n)/
      rareScale (sizes n) (lengths n) delta (alpha n)) atTop (𝓝 1))
    (hs : Tendsto (fun n=>(mu n).real (sourceSparseEvent (sizes n) (lengths n) K delta)/
      rareScale (sizes n) (lengths n) delta (alpha n)) atTop (𝓝 1))
    (hp : Tendsto (fun n=>(AffineCrossoverModel.productJoint (mu n)
      (bulkStarts (sizes n) (lengths n) delta) (lengths n) K).real
      (CrossoverSparseTarget.sparseEvent (bulkStarts (sizes n) (lengths n) delta))/
      rareScale (sizes n) (lengths n) delta (alpha n)) atTop (𝓝 1))
    (he : Tendsto (fun n=>((mu n).real (interiorEvent (lengths n))+
      (mu n).real (middleEvent (sizes n) (lengths n) delta))/
      rareScale (sizes n) (lengths n) delta (alpha n)) atTop (𝓝 0))
    (hd : Tendsto (fun n=>jointDistance (mu n) (sizes n) (lengths n) K delta/
      rareScale (sizes n) (lengths n) delta (alpha n)) atTop (𝓝 0))
    (hb : Tendsto (fun n=>(totalRate (bulkStarts (sizes n) (lengths n) delta) (lengths n) : ℝ))
      atTop (𝓝 0)) :
    Tendsto (fun n=>cappedErrorBudget (mu n) (sizes n) (lengths n) K delta) atTop (𝓝 0) := by
  have h1 := (hh.sub hs).div hh (by norm_num : (1 : ℝ)≠0)
  have h2 := he.div hs (by norm_num : (1 : ℝ)≠0)
  have h3 := hd.div hp (by norm_num : (1 : ℝ)≠0)
  have ht := ((h1.add h2).add h3).add hb
  simp only [sub_self,zero_div,add_zero] at ht
  apply ht.congr'
  filter_upwards [ha] with n han
  have hr (x y : ℝ) :
      (x/rareScale (sizes n) (lengths n) delta (alpha n))/
      (y/rareScale (sizes n) (lengths n) delta (alpha n))=x/y :=
    div_div_div_cancel_right₀ (rareScale_pos _ _ _ _ han).ne' x y
  simp only [Pi.div_apply,cappedErrorBudget,← sub_div,hr]

/-- The generic comparison closes once actual rare masses and factorization have been estimated.
Every fixed clock law is required only eventually.
-/
theorem cappedDistance_tendsto_of_normalized
    (habs : ∀ n,mu n ≪ infiniteRademacherMeasure)
    (hM : ∀ᶠ n in atTop,2≤sizes n) (hL : ∀ᶠ n in atTop,1≤lengths n)
    (hLM : ∀ᶠ n in atTop,lengths n≤sizes n) (hdelta : 0<delta)
    (hne : ∀ᶠ n in atTop,(bulkStarts (sizes n) (lengths n) delta).Nonempty)
    (ha : ∀ᶠ n in atTop,0<alpha n)
    (heq : ∀ᶠ n in atTop,(mu n).real (borderEvent (lengths n))=(alpha n : ℝ))
    (hclock : ∀ᶠ n in atTop,(cond (mu n) (borderEvent (lengths n))).map
      (actualClockRecord (lengths n) K)=
      (geometricMeasure GeometricClusterTarget.halfSuccess).map (fun j => (true,min j K)))
    (hh : Tendsto (fun n=>hitProbability (mu n) (sizes n) (lengths n)/
      rareScale (sizes n) (lengths n) delta (alpha n)) atTop (𝓝 1))
    (hp : Tendsto (fun n=>(AffineCrossoverModel.productJoint (mu n)
      (bulkStarts (sizes n) (lengths n) delta) (lengths n) K).real
      (CrossoverSparseTarget.sparseEvent (bulkStarts (sizes n) (lengths n) delta))/
      rareScale (sizes n) (lengths n) delta (alpha n)) atTop (𝓝 1))
    (hd : Tendsto (fun n=>jointDistance (mu n) (sizes n) (lengths n) K delta/
      rareScale (sizes n) (lengths n) delta (alpha n)) atTop (𝓝 0))
    (hbudget : Tendsto (fun n=>cappedErrorBudget (mu n) (sizes n) (lengths n) K delta)
      atTop (𝓝 0)) :
    Tendsto (fun n=>cappedDistance (mu n) (sizes n) (lengths n) K delta (alpha n)) atTop (𝓝 0) := by
  apply squeeze_zero' ?_ ?_ hbudget
  · filter_upwards [ha,hh.eventually (lt_mem_nhds (by norm_num : (0 : ℝ)<1))] with n han hhn
    have hhit : 0<hitProbability (mu n) (sizes n) (lengths n) :=
      (div_pos_iff_of_pos_right (rareScale_pos _ _ _ _ han)).mp hhn
    exact cappedDistance_nonneg (mu n) _ _ _ _ _ hhit
  · filter_upwards [hM,hL,hLM,hne,ha,heq,hclock,
      hp.eventually (lt_mem_nhds (by norm_num : (1/2 : ℝ)<1)),
      hd.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1/2))] with n hmn hln hcn hnn han heqn hclockn hpn hdn
    have herror : jointDistance (mu n) (sizes n) (lengths n) K delta <
        (AffineCrossoverModel.productJoint (mu n) (bulkStarts (sizes n) (lengths n) delta) (lengths n) K).real
          (CrossoverSparseTarget.sparseEvent (bulkStarts (sizes n) (lengths n) delta)) :=
      (div_lt_div_iff_of_pos_right (rareScale_pos _ _ _ _ han)).mp (hdn.trans hpn)
    exact capped_comparison_bound (mu n) (habs n) hmn hln hcn hdelta hnn (alpha n) heqn han hclockn herror

end
end PaperC.V282.AffineCrossoverCappedBudget
