import PaperCV282.BulkMarkedComparison
import PaperCV282.PoissonFieldAggregation

/-! # Summing all signed marks gives the actual start field and its product Poisson target -/
namespace PaperC.V282.BulkMarkedAggregation

open MeasureTheory ProbabilityTheory BulkMarkedTypes BulkMarkedTarget BulkMarkedSource BulkMarkedComparison
open ExactMarkedModel RunFiniteness ExactLengthDecomposition
open SpatialMarkedSource (signed_exact_unique_all_lengths)
open SpatialMarkedTarget (signedSiteRate)
open GeometricMarkedConfiguration GeometricConfigurationCounts PoissonFieldMeasure PoissonFieldAggregation
open InfiniteRademacher InfiniteStartProbabilityTransfer MixedLengthAffine
open scoped BigOperators NNReal ENNReal

noncomputable section
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P
local instance instDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α
local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤
local instance instProbabilityInfiniteRademacher : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

def spatialRowEmbedding (sites : Finset ℕ) (i : {x : ℕ // x∈sites} × F₂) : ℕ ↪ SpatialMarkedIndex sites where
  toFun e := (i.1,(e,i.2))
  inj' := by
    intro e f h
    exact congrArg (fun j : SpatialMarkedIndex sites => j.2.1) h

theorem flattenRows_eq_sum (sites : Finset ℕ) (rows : ({x : ℕ // x∈sites} × F₂) → (ℕ →₀ ℕ)) :
    flattenRows sites rows = ∑ i : {x : ℕ // x∈sites} × F₂, (rows i).embDomain (spatialRowEmbedding sites i) := by
  classical
  ext j
  rw [flattenRows_apply,Finsupp.finsetSum_apply]
  symm
  rw [Finset.sum_eq_single (j.1,j.2.2)]
  · exact Finsupp.embDomain_apply_self _ _ _
  · intro i hi hne
    apply Finsupp.embDomain_notin_range
    rintro ⟨e,he⟩
    apply hne
    exact Prod.ext (congrArg (fun k : SpatialMarkedIndex sites => k.1) he)
      (congrArg (fun k : SpatialMarkedIndex sites => k.2.2) he)
  · intro hn
    exact (hn (Finset.mem_univ _)).elim

theorem sum_flattenRows {A : Type*} [AddCommMonoid A] (sites : Finset ℕ)
    (rows : ({x : ℕ // x∈sites} × F₂) → (ℕ →₀ ℕ)) (f : SpatialMarkedIndex sites → ℕ → A)
    (hfzero : ∀ j, f j 0=0) (hfadd : ∀ j n m, f j (n+m)=f j n+f j m) :
    (flattenRows sites rows).sum f = ∑ i : {x : ℕ // x∈sites} × F₂, (rows i).sum (fun e n => f (i.1,e,i.2) n) := by
  rw [flattenRows_eq_sum,← Finsupp.sum_finsetSum_index hfzero hfadd]
  apply Finset.sum_congr rfl
  intro i hi
  exact Finsupp.sum_embDomain

theorem hasLaw_rowCounts (sites : Finset ℕ) (L : ℕ) :
    HasLaw (fun rows : ({x : ℕ // x∈sites} × F₂) → (ℕ →₀ ℕ) => fun i => configurationSize (rows i))
      (fieldMeasure (fun _ : {x : ℕ // x∈sites} × F₂ => signedSiteRate L)) (spatialRowsMeasure sites L) := by
  refine ⟨(measurable_of_countable _).aemeasurable,?_⟩
  rw [spatialRowsMeasure,Measure.pi_map_pi
    (f := fun _ : {x : ℕ // x∈sites} × F₂ => configurationSize)
    (fun _ => (measurable_of_countable _).aemeasurable)]
  unfold fieldMeasure
  congr 1
  funext i
  exact (hasLaw_configurationSize (signedSiteRate L)).map_eq

/-- Sum every excess and both signs at each original integer position. -/
def siteCounts (sites : Finset ℕ) (config : SpatialMarkedConfig sites) (x : sites) : ℕ :=
  config.sum (fun j n => if j.1=x then n else 0)

def startField (sites : Finset ℕ) (L : ℕ) (omega : InfiniteSample) (x : sites) : ℕ :=
  baseStartValue (infiniteValueBit omega) x.val L

def startFieldRates (sites : Finset ℕ) (L : ℕ) (_x : sites) : ℝ≥0 := 1/2^L

theorem siteCounts_flattenRows (sites : Finset ℕ)
    (rows : (sites × F₂) → (ℕ →₀ ℕ)) (x : sites) :
    siteCounts sites (flattenRows sites rows) x = ∑ s : F₂, configurationSize (rows (x,s)) := by
  rw [siteCounts,sum_flattenRows sites rows _ (by intro j;simp) (by intro j n m;split_ifs <;> simp)]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single x]
  · apply Finset.sum_congr rfl
    intro s hs
    simp only [if_true]
    rfl
  · intro y hy hne
    simp [hne,Finsupp.sum]
  · simp

/-- Rearranging rows is a probability-law identity, so independence is retained. -/
theorem hasLaw_siteRows (sites : Finset ℕ) (L : ℕ) :
    HasLaw (fun k : sites × F₂ → ℕ => fun x : sites => fun s : F₂ => k (x,s))
      (Measure.pi fun _ : sites => fieldMeasure (fun _ : F₂ => signedSiteRate L))
      (fieldMeasure (fun _ : sites × F₂ => signedSiteRate L)) := by
  refine ⟨(measurable_of_countable _).aemeasurable,?_⟩
  apply Measure.ext_of_singleton
  intro k
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  have hp : (fun v : sites × F₂ → ℕ => fun x : sites => fun s : F₂ => v (x,s)) ⁻¹' {k} =
      {fun j : sites × F₂ => k j.1 j.2} := by
    ext v
    simp only [Set.mem_preimage,Set.mem_singleton_iff]
    constructor
    · intro h
      funext j
      exact congrFun (congrFun h j.1) j.2
    · intro h
      subst v
      rfl
  rw [hp]
  simp only [fieldMeasure,Measure.pi_singleton,Fintype.prod_prod_type]

theorem hasLaw_siteCounts (sites : Finset ℕ) (L : ℕ) :
    HasLaw (siteCounts sites) (fieldMeasure (startFieldRates sites L)) (spatialTargetMeasure sites L) := by
  have hr : (∑ _ : F₂, signedSiteRate L) = (1 : ℝ≥0)/2^L := by
    apply NNReal.coe_injective
    simp only [Finset.sum_const,Finset.card_univ,ZMod.card,nsmul_eq_mul]
    change 2*((1 : ℝ)/2^(L+1))=1/2^L
    rw [pow_succ]
    field_simp
  have hsum : HasLaw (fun k : sites → F₂ → ℕ => fun x => ∑ s : F₂, k x s)
      (fieldMeasure (startFieldRates sites L))
      (Measure.pi fun _ : sites => fieldMeasure (fun _ : F₂ => signedSiteRate L)) := by
    refine ⟨(measurable_of_countable _).aemeasurable,?_⟩
    rw [Measure.pi_map_pi (fun _ => (measurable_of_countable _).aemeasurable)]
    unfold fieldMeasure
    congr 1
    funext x
    exact ((hasLaw_coordinate_sum (fun _ : F₂ => signedSiteRate L) Finset.univ).map_eq).trans (by rw [hr];rfl)
  have h := hsum.fun_comp ((hasLaw_siteRows sites L).fun_comp (hasLaw_rowCounts sites L))
  refine ⟨(measurable_of_countable _).aemeasurable,?_⟩
  rw [spatialTargetMeasure,Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  have he : (siteCounts sites) ∘ (flattenRows sites) =
      fun rows : (sites × F₂) → (ℕ →₀ ℕ) => fun x => ∑ s : F₂, configurationSize (rows (x,s)) := by
    funext rows x
    exact siteCounts_flattenRows sites rows x
  rw [he]
  exact h.map_eq

/-- For a terminating run, summing exact alternatives is exactly the start indicator. -/
theorem siteCounts_source_eq_of_tail_changes (sites : Finset ℕ) (L : ℕ)
    (omega : InfiniteSample) (x : sites)
    (hc : TailChangesAt (infiniteValueBit omega) x.val) :
    siteCounts sites (spatialMarkedSource sites L omega) x = startField sites L omega x := by
  classical
  by_cases hs : StartEvent (infiniteValueBit omega) x.val L
  · obtain ⟨e,he⟩ := exists_exactLengthEvent_of_start_of_tailChangesAt hs hc
    let j : SpatialMarkedIndex sites := (x,(e,infiniteValueBit omega x.val))
    have hj : SignedExactMark (infiniteValueBit omega) x.val L e (infiniteValueBit omega x.val) := ⟨he,rfl⟩
    have hmem : j∈(spatialMarkedSource sites L omega).support :=
      Finsupp.mem_support_iff.mpr ((spatialMarkedValue_ne_zero_iff sites L omega j).mpr hj)
    change (∑ k∈(spatialMarkedSource sites L omega).support,
      if k.1=x then (spatialMarkedSource sites L omega) k else 0) = _
    rw [Finset.sum_eq_single j]
    · simp [j,spatialMarkedSource_apply,spatialMarkedValue,signedMarkValue,hj,startField,baseStartValue,hs]
    · intro k hk hkj
      by_cases hkx : k.1=x
      · have hex := (spatialMarkedValue_ne_zero_iff sites L omega k).mp (Finsupp.mem_support_iff.mp hk)
        have hu := signed_exact_unique_all_lengths hex (by simpa only [hkx] using hj)
        exact (hkj (Prod.ext hkx (Prod.ext hu.1 hu.2))).elim
      · simp [hkx]
    · exact fun hn => (hn hmem).elim
  · change (∑ k∈(spatialMarkedSource sites L omega).support,
      if k.1=x then (spatialMarkedSource sites L omega) k else 0) = _
    rw [show startField sites L omega x=0 by simp [startField,baseStartValue,hs]]
    apply Finset.sum_eq_zero
    intro k hk
    by_cases hkx : k.1=x
    · have he := (spatialMarkedValue_ne_zero_iff sites L omega k).mp (Finsupp.mem_support_iff.mp hk)
      exact (hs (by simpa only [hkx] using exactLengthEvent_start he.1)).elim
    · simp [hkx]

theorem ae_siteCounts_source_eq (sites : Finset ℕ) (L : ℕ) (hsite : ∀x∈sites,2≤x) :
    (fun omega => siteCounts sites (spatialMarkedSource sites L omega)) =ᵐ[infiniteRademacherMeasure]
      startField sites L := by
  filter_upwards [ae_all_runs_end] with omega homega
  funext x
  exact siteCounts_source_eq_of_tail_changes sites L omega x (homega x.val (hsite x.val x.property))

theorem measurable_startField (sites : Finset ℕ) (L : ℕ) : Measurable (startField sites L) := by
  apply measurable_pi_lambda
  intro x
  exact measurable_const.ite (measurableSet_infiniteStartEvent x.val L) measurable_const

end
end PaperC.V282.BulkMarkedAggregation
