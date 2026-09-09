import PaperCV282.PoissonConfigurationSplit
import PaperCV282.PoissonResolvedComparison

/-! # A finite reverse immigration segment jointly with the entire resolved future -/
namespace PaperC.V282.PoissonResolvedPast

open MeasureTheory ProbabilityTheory PoissonConfigurationSplit PoissonResolvedTarget
open GeometricMarkedConfiguration GeometricConfigurationCounts ThresholdPathEquivalence
open SharpConditioningDiscrete PoissonFieldMeasure
open scoped NNReal ENNReal

noncomputable section

@[reducible]
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

def shiftEmbedding (k : ℕ) : ℕ ↪ ℕ := ⟨fun e => k+e, fun _ _ h => Nat.add_left_cancel h⟩

theorem shifted_embeds_as_filtered (k : ℕ) (c : ℕ →₀ ℕ) :
    (shiftedConfiguration k c).embDomain (shiftEmbedding k) = c.filter (fun e => k≤e) := by
  classical
  ext e
  by_cases he : k≤e
  · have hid : shiftEmbedding k (e-k)=e := by
      change k+(e-k)=e
      omega
    rw [← hid, Finsupp.embDomain_apply_self, shiftedConfiguration_apply, Finsupp.filter_apply]
    change c (k+(e-k)) = if k≤k+(e-k) then c (k+(e-k)) else 0
    rw [if_pos (by omega : k≤k+(e-k))]
  · rw [Finsupp.filter_apply, if_neg he]
    apply Finsupp.embDomain_notin_range
    rintro ⟨i,hi⟩
    have : k+i=e := hi
    omega

theorem size_shifted_eq_tail (k : ℕ) (c : ℕ →₀ ℕ) :
    configurationSize (shiftedConfiguration k c) = tailCount c k := by
  have hs := congrArg (fun z : ℕ →₀ ℕ => z.sum (fun _ a => a)) (shifted_embeds_as_filtered k c)
  rw [Finsupp.sum_embDomain] at hs
  change configurationSize (shiftedConfiguration k c) = _ at hs
  rw [hs]
  simp only [Finsupp.sum, Finsupp.support_filter, Finset.sum_filter, Finsupp.filter_apply, tailCount]
  apply Finset.sum_congr rfl
  intro e he
  split_ifs <;> rfl

def lowerConfiguration (k : ℕ) (a : Fin k → ℕ) : ℕ →₀ ℕ :=
  Finsupp.onFinset (Finset.range k) (fun e => if h : e<k then a ⟨e,h⟩ else 0)
    (by
      intro e he
      by_contra hn
      have hnot : ¬e<k := by simpa using hn
      simp [hnot] at he)

def mergeConfiguration (k : ℕ) (p : (Fin k → ℕ) × (ℕ →₀ ℕ)) : ℕ →₀ ℕ :=
  lowerConfiguration k p.1 + p.2.embDomain (shiftEmbedding k)

theorem mergeConfiguration_low (k : ℕ) (p : (Fin k → ℕ) × (ℕ →₀ ℕ))
    (i : Fin k) : mergeConfiguration k p i.val = p.1 i := by
  have hout : i.val ∉ Set.range (shiftEmbedding k) := by
    rintro ⟨e,he⟩
    have : k+e=i.val := he
    omega
  simp [mergeConfiguration, lowerConfiguration, Finsupp.embDomain_notin_range (shiftEmbedding k) p.2 i.val hout]

theorem mergeConfiguration_high (k : ℕ) (p : (Fin k → ℕ) × (ℕ →₀ ℕ))
    (e : ℕ) : mergeConfiguration k p (k+e) = p.2 e := by
  change lowerConfiguration k p.1 (k+e) + p.2.embDomain (shiftEmbedding k) (shiftEmbedding k e)=_
  rw [Finsupp.embDomain_apply_self]
  simp [lowerConfiguration]

theorem merge_splitConfiguration (k : ℕ) (c : ℕ →₀ ℕ) :
    mergeConfiguration k (splitConfiguration k c)=c := by
  ext e
  by_cases he : e<k
  · exact mergeConfiguration_low k (splitConfiguration k c) ⟨e,he⟩
  · have hke : k≤e := by omega
    rw [← Nat.add_sub_of_le hke, mergeConfiguration_high, splitConfiguration,
      shiftedConfiguration_apply]

theorem split_mergeConfiguration (k : ℕ) (p : (Fin k → ℕ) × (ℕ →₀ ℕ)) :
    splitConfiguration k (mergeConfiguration k p)=p := by
  apply Prod.ext
  · funext i
    exact mergeConfiguration_low k p i
  · ext e
    exact mergeConfiguration_high k p e

theorem cond_prod_second_eq {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [IsProbabilityMeasure μ] (ν : Measure β) [IsProbabilityMeasure ν]
    (B : Set β) : cond (μ.prod ν) (Prod.snd ⁻¹' B) = μ.prod (cond ν B) := by
  have hs : (Prod.snd ⁻¹' B : Set (α × β)) = Set.univ ×ˢ B := by ext p; simp
  rw [hs, ProbabilityTheory.cond, Measure.prod_prod, measure_univ, one_mul,
    ProbabilityTheory.cond, Measure.prod_smul_right]
  congr 1
  simpa only [Measure.restrict_univ] using
    (Measure.prod_restrict (μ := μ) (ν := ν) Set.univ B).symm

/-- Resolution at k leaves all lower Poisson coordinates independent of exactly n fresh geometric lifetimes. -/
theorem conditional_split_configuration (rate : ℝ≥0) (k n : ℕ)
    (hn : (poissonMeasure (rate / 2^k)) {n} ≠ 0) :
    (cond (configurationMeasure rate) {c | tailCount c k=n}).map (splitConfiguration k) =
      (fieldMeasure (lowerRates rate k)).prod (thinConfigurationMeasure n) := by
  have hpre : {c : ℕ →₀ ℕ | tailCount c k=n} =
      splitConfiguration k ⁻¹' (Prod.snd ⁻¹' {c | configurationSize c=n}) := by
    ext c
    simp only [Set.mem_setOf_eq, Set.mem_preimage, splitConfiguration, size_shifted_eq_tail]
  rw [hpre, map_cond_eq _ (measurable_of_countable _) _ ((Set.to_countable _).measurableSet),
    (hasLaw_split_configuration rate k).map_eq, cond_prod_second_eq,
    conditional_configuration_eq_thin _ n hn]

def resolvedPastFutureMeasure (rate : ℝ≥0) (k n : ℕ) : Measure (ℕ → ℕ) :=
  ((fieldMeasure (lowerRates rate k)).prod (thinConfigurationMeasure n)).map
    (thresholdFunction ∘ mergeConfiguration k)

instance instProbabilityResolvedPastFuture (rate : ℝ≥0) (k n : ℕ) :
    IsProbabilityMeasure (resolvedPastFutureMeasure rate k n) :=
  Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable

/-- The whole retained path, with a finite reverse part and an unlimited future, has the explicit product construction. -/
theorem conditional_retained_path_eq (rate : ℝ≥0) (k n : ℕ)
    (hn : (poissonMeasure (rate / 2^k)) {n} ≠ 0) :
    (cond (configurationMeasure rate) {c | tailCount c k=n}).map thresholdFunction =
      resolvedPastFutureMeasure rate k n := by
  rw [resolvedPastFutureMeasure, ← conditional_split_configuration rate k n hn,
    Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  congr 1
  funext c
  simp only [Function.comp_apply, merge_splitConfiguration]

end
end PaperC.V282.PoissonResolvedPast
