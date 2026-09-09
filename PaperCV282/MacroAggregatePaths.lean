import PaperCV282.MacroAggregateUnsigned
import PaperCV282.BulkMarkedAggregation

/-! # Literal whole paths of start counts for arbitrary finite populations -/
namespace PaperC.V282.MacroAggregatePaths

open MeasureTheory ProbabilityTheory MacroAggregateUnsigned BulkMarkedTypes BulkMarkedSource BulkMarkedAggregation
open ExactMarkedModel RunFiniteness ExactLengthDecomposition ThresholdPathEquivalence MixedLengthAffine
open InfiniteRademacher InfiniteCylinderTransfer InfiniteMassCoupling ConditionedCountableLaw
open FiniteFieldTotalVariation MassPushforward CountableLawTransfer MovingMarkedLevels
open scoped BigOperators

noncomputable section

/-- Summing all levels above m is exactly filtering the original complete configuration. -/
theorem aggregate_tail_eq_filtered_total (sites : Finset ℕ) (m : ℕ) (config : SpatialMarkedConfig sites) :
    tailCount (aggregateExcess sites config) m =
      (config.filter (fun j => m ≤ j.2.1)).sum (fun _ n => n) := by
  classical
  change (config.mapDomain (fun j => j.2.1)).sum (fun e n => if m≤e then n else 0) = _
  rw [Finsupp.sum_mapDomain_index]
  · simp only [Finsupp.support_filter,Finsupp.sum,Finset.sum_filter,Finsupp.filter_apply]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases h : m≤j.2.1 <;> simp [h]
  · intro e
    split_ifs <;> rfl
  · intro e a b
    split_ifs <;> simp

/-- Shifting the excess never changes a spatial position or a sign. -/
def excessShift (sites : Finset ℕ) (m : ℕ) : SpatialMarkedIndex sites ↪ SpatialMarkedIndex sites where
  toFun j := (j.1,(m+j.2.1,j.2.2))
  inj' := by
    intro j k h
    have hi := congrArg Prod.fst h
    have he := congrArg (fun z : SpatialMarkedIndex sites => z.2.1) h
    have hs := congrArg (fun z : SpatialMarkedIndex sites => z.2.2) h
    exact Prod.ext hi (Prod.ext (by dsimp at he;omega) hs)

theorem shifted_source_embeds_as_filtered (sites : Finset ℕ) (L m : ℕ) (omega : InfiniteSample) :
    (spatialMarkedSource sites (L+m) omega).embDomain (excessShift sites m) =
      (spatialMarkedSource sites L omega).filter (fun j => m≤j.2.1) := by
  classical
  ext j
  by_cases hm : m≤j.2.1
  · let k : SpatialMarkedIndex sites := (j.1,(j.2.1-m,j.2.2))
    have hk : excessShift sites m k=j := by
      change (j.1,(m+(j.2.1-m),j.2.2))=j
      exact congrArg (fun e => (j.1,(e,j.2.2))) (show m+(j.2.1-m)=j.2.1 by omega)
    rw [← hk,Finsupp.embDomain_apply_self,Finsupp.filter_apply]
    have hkm : m ≤ (excessShift sites m k).2.1 := by
      change m ≤ m + k.2.1
      omega
    rw [if_pos hkm]
    change spatialMarkedSource sites (L+m) omega k =
      spatialMarkedSource sites L omega (k.1,(m+k.2.1,k.2.2))
    simp [spatialMarkedSource_apply,spatialMarkedValue,signedMarkValue,
      SignedExactMark,excessRowCount,Nat.add_assoc]
  · rw [Finsupp.filter_apply,if_neg hm]
    apply Finsupp.embDomain_notin_range
    rintro ⟨k,hk⟩
    have he := congrArg (fun z : SpatialMarkedIndex sites => z.2.1) hk
    change m + k.2.1 = j.2.1 at he
    omega

/-- An exact finite identity holds before any almost-sure termination argument. -/
theorem source_threshold_eq_shifted_total (sites : Finset ℕ) (L m : ℕ) (omega : InfiniteSample) :
    tailCount (aggregateExcess sites (spatialMarkedSource sites L omega)) m =
      (spatialMarkedSource sites (L+m) omega).sum (fun _ n => n) := by
  rw [aggregate_tail_eq_filtered_total,← shifted_source_embeds_as_filtered,Finsupp.sum_embDomain]

/-- The same actual sites are counted at every longer threshold. -/
def startCount (sites : Finset ℕ) (L : ℕ) (omega : InfiniteSample) : ℕ :=
  ∑ x∈sites,baseStartValue (infiniteValueBit omega) x L

theorem sum_siteCounts (sites : Finset ℕ) (config : SpatialMarkedConfig sites) :
    (∑ x : sites,siteCounts sites config x)=config.sum (fun _ n => n) := by
  classical
  unfold siteCounts Finsupp.sum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  simp

theorem source_total_eq_startCount_of_tail_changes (sites : Finset ℕ) (L : ℕ)
    (omega : InfiniteSample) (hchange : ∀x∈sites,TailChangesAt (infiniteValueBit omega) x) :
    (spatialMarkedSource sites L omega).sum (fun _ n => n)=startCount sites L omega := by
  rw [← sum_siteCounts]
  calc
    _ = ∑ x : sites,startField sites L omega x := by
      apply Finset.sum_congr rfl
      intro x hx
      exact siteCounts_source_eq_of_tail_changes sites L omega x (hchange x.val x.property)
    _ = _ := (Finset.sum_subtype sites (fun _ => Iff.rfl)
      (fun x => baseStartValue (infiniteValueBit omega) x L)).symm

/-- Every level is identified simultaneously on one probability-one event. -/
theorem ae_source_thresholds_eq_startCounts (sites : Finset ℕ) (L : ℕ)
    (hsite : ∀x∈sites,2≤x) :
    ∀ᵐ omega ∂infiniteRademacherMeasure, ∀m : ℕ,
      thresholdFunction (aggregateExcess sites (spatialMarkedSource sites L omega)) m=
        startCount sites (L+m) omega := by
  filter_upwards [ae_all_runs_end] with omega homega
  intro m
  change tailCount _ m=_
  rw [source_threshold_eq_shifted_total]
  exact source_total_eq_startCount_of_tail_changes sites (L+m) omega
    (fun x hx => homega x (hsite x hx))

theorem actual_start_path_law_eq (sites : Finset ℕ) (L : ℕ) (hsite : ∀x∈sites,2≤x)
    {nu : Measure InfiniteSample} (hnu : nu≪infiniteRademacherMeasure) :
    observableLaw nu (fun omega m => startCount sites (L+m) omega)=
      observableLaw nu (fun omega => thresholdFunction (aggregateExcess sites (spatialMarkedSource sites L omega))) := by
  funext path
  unfold observableLaw Measure.real
  apply congrArg ENNReal.toReal
  apply measure_congr
  filter_upwards [(ae_source_thresholds_eq_startCounts sites L hsite).filter_mono hnu.ae_le] with omega homega
  have he : (fun m => startCount sites (L+m) omega)=
      thresholdFunction (aggregateExcess sites (spatialMarkedSource sites L omega)) := by
    funext m
    exact (homega m).symm
  change ((fun m => startCount sites (L+m) omega)=path)=
    (thresholdFunction (aggregateExcess sites (spatialMarkedSource sites L omega))=path)
  rw [he]

/-- The full path is an injective re-encoding, so its conditional TV is exactly unchanged. -/
theorem conditional_start_path_distance_eq (sites : Finset ℕ) (L : ℕ) (hsite : ∀x∈sites,2≤x)
    (A : Set InfiniteSample) :
    massTotalVariation (conditionalObservableLaw infiniteRademacherMeasure A
      (fun omega m => startCount sites (L+m) omega))
      (pushforwardMass thresholdFunction (UnsignedAggregateComparison.geometricConfigurationLaw
        (FiniteStartMaskAverages.maskRate L sites)))=
      conditionalUnsignedAggregateDistance sites L A := by
  unfold conditionalUnsignedAggregateDistance conditionalObservableLaw
  rw [actual_start_path_law_eq sites L hsite cond_absolutelyContinuous]
  have he := pushforwardMass_observableLaw (cond infiniteRademacherMeasure A)
    (measurable_unsignedAggregateSource sites L) thresholdFunction
  change pushforwardMass thresholdFunction (observableLaw (cond infiniteRademacherMeasure A)
    (unsignedAggregateSource sites L))=observableLaw (cond infiniteRademacherMeasure A)
      (fun omega => thresholdFunction (aggregateExcess sites (spatialMarkedSource sites L omega))) at he
  rw [← he]
  exact massTotalVariation_injective _ thresholdFunction_injective _ _

end
end PaperC.V282.MacroAggregatePaths
