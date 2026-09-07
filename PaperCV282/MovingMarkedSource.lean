import PaperCV282.SpatialMarkedSource
import PaperCV282.GrowingLevelParameters
import PaperCV282.ThresholdPathEquivalence
import PaperCV282.CountableLawTransfer

/-!
# Moving levels and threshold paths of the actual infinite source

Reindexing keeps every position and sign. Aggregation sums positions/signs
explicitly. The entire path of tail counts equals the actual family of shifted
start counts almost surely, simultaneously for every threshold. No aggregate
Poisson approximation is assumed or inferred from these identities.
-/
namespace PaperC.V282.MovingMarkedSource

open MeasureTheory InfiniteRademacher InfiniteCylinderTransfer InfiniteStartProbabilityTransfer
open InfiniteExactLengthProbabilityTransfer ExactLengthDecomposition MixedLengthAffine
open ExactMarkedModel SpatialMarkedTypes SpatialMarkedSource RunFiniteness
open MovingMarkedLevels GrowingLevelParameters ThresholdPathEquivalence
open InfiniteMassCoupling CountableLawTransfer FiniteFieldTotalVariation MassPushforward
open ConditionalStartProbability
open scoped BigOperators

noncomputable section

@[reducible]
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

local instance instMeasurableExcessConfiguration : MeasurableSpace (ℕ →₀ ℕ) := ⊤

local instance instMeasurableSingletonExcessConfiguration : MeasurableSingletonClass (ℕ →₀ ℕ) := by infer_instance

instance instMeasurableMovingConfiguration (N d : ℕ) :
    MeasurableSpace (Fin N × (MovingLevel d × F₂) →₀ ℕ) := ⊤

instance instMeasurableSingletonMovingConfiguration (N d : ℕ) :
    MeasurableSingletonClass (Fin N × (MovingLevel d × F₂) →₀ ℕ) := by infer_instance

local instance instProbabilityInfiniteRademacher : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

/-- The actual full spatial source in the coordinates of (5.17). -/
def movingSource (N d : ℕ) (omega : InfiniteSample) : Fin N × (MovingLevel d × F₂) →₀ ℕ :=
  configurationEquiv (Fin N) F₂ d (spatialMarkedSource N (movingLength N d) omega)

theorem moving_source_coordinate (N d : ℕ) (omega : InfiniteSample)
    (i : Fin N) (e : ℕ) (s : F₂) :
    movingSource N d omega (i,levelEquiv d e,s) =
      signedMarkValue (infiniteValueBit omega) (N+i.val) (movingLength N d) e s := by
  exact configurationEquiv_apply (Fin N) F₂ d _ i e s

/-- The integer coordinate is literally the exact length b_N+r from (5.17). -/
theorem moving_source_physical_length {N d : ℕ} (hd : d≤criticalBase N)
    (omega : InfiniteSample) (i : Fin N) (r : MovingLevel d) (s : F₂) :
    movingSource N d omega (i,r,s) =
      if ExactLengthEvent (infiniteValueBit omega) (N+i.val)
          (((criticalBase N : ℤ)+r.val).toNat+1) ∧
          infiniteValueBit omega (N+i.val)=s then 1 else 0 := by
  have hc := moving_source_coordinate N d omega i ((levelEquiv d).symm r) s
  simp only [Equiv.apply_symm_apply] at hc
  rw [hc]
  have hl := runLength_eq (criticalBase N) d ((levelEquiv d).symm r) hd
  simp only [Equiv.apply_symm_apply] at hl
  have hl' : movingLength N d+(levelEquiv d).symm r = ((criticalBase N : ℤ)+r.val).toNat := by
    simpa only [Int.toNat_natCast,movingLength] using congrArg Int.toNat hl
  simp only [signedMarkValue,SignedExactMark,excessRowCount,hl']

theorem measurable_movingSource (N d : ℕ) : Measurable (movingSource N d) :=
  (measurable_configurationEquiv (Fin N) F₂ d).comp (measurable_spatialMarkedSource N _)

/-- The law is a genuine observable law, and reindexing preserves its distance exactly. -/
theorem moving_source_law_totalVariation_eq (N d : ℕ) (q : SpatialMarkedConfig N → ℝ) :
    massTotalVariation (observableLaw infiniteRademacherMeasure (movingSource N d))
      (pushforwardMass (configurationEquiv (Fin N) F₂ d) q) =
      massTotalVariation (spatialSourceLaw N (movingLength N d)) q := by
  unfold movingSource spatialSourceLaw
  have he := pushforwardMass_observableLaw infiniteRademacherMeasure
    (measurable_spatialMarkedSource N (movingLength N d)) (configurationEquiv (Fin N) F₂ d)
  simp only [Function.comp_def] at he
  rw [← he]
  exact massTotalVariation_equiv _ _ q

/-- Forget position and sign only here, to form exact-level counts. -/
def aggregateExcess (N : ℕ) (config : SpatialMarkedConfig N) : ℕ →₀ ℕ :=
  config.mapDomain (fun j => j.2.1)

/-- Every coefficient is the actual finite sum over active sites and signs at that level. -/
theorem aggregateExcess_apply (N : ℕ) (config : SpatialMarkedConfig N) (e : ℕ) :
    aggregateExcess N config e =
      ∑ j ∈ config.support, if j.2.1=e then config j else 0 := by
  classical
  simp [aggregateExcess,Finsupp.mapDomain,Finsupp.sum,Finsupp.single_apply]

/-- Summing all levels above m is exactly filtering the original complete configuration. -/
theorem aggregate_tail_eq_filtered_total (N m : ℕ) (config : SpatialMarkedConfig N) :
    tailCount (aggregateExcess N config) m =
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
def excessShift (N m : ℕ) : SpatialMarkedIndex N ↪ SpatialMarkedIndex N where
  toFun j := (j.1,(m+j.2.1,j.2.2))
  inj' := by
    intro j k h
    have hi := congrArg Prod.fst h
    have he := congrArg (fun z : SpatialMarkedIndex N => z.2.1) h
    have hs := congrArg (fun z : SpatialMarkedIndex N => z.2.2) h
    exact Prod.ext hi (Prod.ext (by dsimp at he;omega) hs)

theorem shifted_source_embeds_as_filtered (N L m : ℕ) (omega : InfiniteSample) :
    (spatialMarkedSource N (L+m) omega).embDomain (excessShift N m) =
      (spatialMarkedSource N L omega).filter (fun j => m≤j.2.1) := by
  classical
  ext j
  by_cases hm : m≤j.2.1
  · let k : SpatialMarkedIndex N := (j.1,(j.2.1-m,j.2.2))
    have hk : excessShift N m k=j := by
      change (j.1,(m+(j.2.1-m),j.2.2))=j
      exact congrArg (fun e => (j.1,(e,j.2.2))) (show m+(j.2.1-m)=j.2.1 by omega)
    rw [← hk,Finsupp.embDomain_apply_self,Finsupp.filter_apply]
    have hkm : m ≤ (excessShift N m k).2.1 := by dsimp [excessShift];omega
    rw [if_pos hkm]
    simp [spatialMarkedSource_apply,spatialMarkedValue,excessShift,signedMarkValue,
      SignedExactMark,excessRowCount,Nat.add_assoc]
  · rw [Finsupp.filter_apply,if_neg hm]
    apply Finsupp.embDomain_notin_range
    rintro ⟨k,hk⟩
    have he := congrArg (fun z : SpatialMarkedIndex N => z.2.1) hk
    dsimp [excessShift] at he
    omega

/-- An exact finite identity holds before any almost-sure termination argument. -/
theorem source_threshold_eq_shifted_total (N L m : ℕ) (omega : InfiniteSample) :
    tailCount (aggregateExcess N (spatialMarkedSource N L omega)) m =
      (spatialMarkedSource N (L+m) omega).sum (fun _ n => n) := by
  rw [aggregate_tail_eq_filtered_total,← shifted_source_embeds_as_filtered,Finsupp.sum_embDomain]

/-- All actual threshold counts are recovered at once on the same probability-one event. -/
theorem ae_source_thresholds_eq_startCounts {N L : ℕ} (hN : 2≤N) :
    ∀ᵐ omega ∂infiniteRademacherMeasure, ∀ m : ℕ,
      thresholdFunction (aggregateExcess N (spatialMarkedSource N L omega)) m =
        infiniteDyadicStartCount N (L+m) omega := by
  filter_upwards [ae_all_runs_end] with omega homega
  intro m
  change tailCount _ m = _
  rw [source_threshold_eq_shifted_total]
  apply spatial_source_total_eq_startCount_of_tail_changes omega
  intro x hx
  exact homega x (by have hh := Finset.mem_Ico.mp hx;omega)

/-- The exact configuration law and the literal full threshold-path law have identical TV. -/
theorem actual_threshold_law_totalVariation_eq (N L : ℕ) (q : (ℕ →₀ ℕ) → ℝ) :
    massTotalVariation
      (observableLaw infiniteRademacherMeasure
        (fun omega => thresholdFunction (aggregateExcess N (spatialMarkedSource N L omega))))
      (pushforwardMass thresholdFunction q) =
      massTotalVariation
        (observableLaw infiniteRademacherMeasure (fun omega => aggregateExcess N (spatialMarkedSource N L omega))) q := by
  have hm : Measurable (fun omega => aggregateExcess N (spatialMarkedSource N L omega)) :=
    (measurable_of_countable (aggregateExcess N)).comp (measurable_spatialMarkedSource N L)
  have he := pushforwardMass_observableLaw infiniteRademacherMeasure hm thresholdFunction
  simp only [Function.comp_def] at he
  rw [← he]
  exact massTotalVariation_injective _ thresholdFunction_injective _ q


/-- The equality transfers to every measure absolutely continuous with respect to the
original source, including positive arithmetic-event restrictions. -/
theorem ae_source_thresholds_eq_startCounts_of_ac {N L : ℕ} (hN : 2≤N)
    {ν : Measure InfiniteSample} (hν : ν ≪ infiniteRademacherMeasure) :
    ∀ᵐ omega ∂ν, ∀ m : ℕ,
      thresholdFunction (aggregateExcess N (spatialMarkedSource N L omega)) m =
        infiniteDyadicStartCount N (L+m) omega :=
  (ae_source_thresholds_eq_startCounts hN).filter_mono hν.ae_le

/-- Singleton probabilities of the literal start-count path are exactly those of the
threshold transform. The target path type need not be replaced by a finite projection. -/
theorem actual_start_path_law_eq {N L : ℕ} (hN : 2≤N)
    {ν : Measure InfiniteSample} (hν : ν ≪ infiniteRademacherMeasure) :
    observableLaw ν (fun omega m => infiniteDyadicStartCount N (L+m) omega) =
      observableLaw ν (fun omega => thresholdFunction (aggregateExcess N (spatialMarkedSource N L omega))) := by
  funext path
  unfold observableLaw Measure.real
  apply congrArg ENNReal.toReal
  apply measure_congr
  filter_upwards [ae_source_thresholds_eq_startCounts_of_ac hN hν] with omega homega
  have he : (fun m => infiniteDyadicStartCount N (L+m) omega) =
      thresholdFunction (aggregateExcess N (spatialMarkedSource N L omega)) := by
    funext m
    exact (homega m).symm
  change ((fun m => infiniteDyadicStartCount N (L+m) omega)=path) =
    (thresholdFunction (aggregateExcess N (spatialMarkedSource N L omega))=path)
  rw [he]

/-- Exactly the same TV holds for the actual whole start-count path and the exact-level law. -/
theorem actual_start_path_totalVariation_eq {N L : ℕ} (hN : 2≤N)
    (q : (ℕ →₀ ℕ) → ℝ) :
    massTotalVariation
      (observableLaw infiniteRademacherMeasure (fun omega m => infiniteDyadicStartCount N (L+m) omega))
      (pushforwardMass thresholdFunction q) =
      massTotalVariation
        (observableLaw infiniteRademacherMeasure (fun omega => aggregateExcess N (spatialMarkedSource N L omega))) q := by
  rw [actual_start_path_law_eq hN (Measure.AbsolutelyContinuous.refl _)]
  exact actual_threshold_law_totalVariation_eq N L q

end
end PaperC.V282.MovingMarkedSource
