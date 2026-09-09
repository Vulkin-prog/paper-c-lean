import PaperCV282.MacroTransportFunctionals
import PaperCV282.MacroTransportCoordinates
import PaperCV282.ExactMarkedSignProjection

/-! # The literal unsigned spatial target and its complete joint law

Signs are summed at each unchanged site/excess coordinate. Every finite mark
projection is the independent Poisson product, and these projections determine
the whole finite-configuration measure uniquely.
-/
namespace PaperC.V282.MacroTransportUnsigned

open MeasureTheory ProbabilityTheory BulkMarkedTypes BulkMarkedTarget BulkMarkedTargetProjection
open BulkMarkedSource BulkMarkedTransfer BulkSupportGraph ExactMarkedModel ExactMarkedSignProjection
open PoissonFieldMeasure PoissonFieldAggregation MacroTransportModel MacroTransportFunctionals
open InfiniteRademacher InfiniteCylinderTransfer InfiniteMassCoupling ConditionedCountableLaw
open FiniteFieldTotalVariation MassPushforward GrowingLevelParameters MovingMarkedLevels
open scoped BigOperators NNReal ENNReal

noncomputable section
local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤
local instance instProbabilityInfinite : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

@[reducible]
def UnsignedConfiguration (sites : Finset ℕ) := ({x : ℕ // x∈sites} × ℕ) →₀ ℕ

instance instMeasurableUnsignedConfiguration (sites : Finset ℕ) :
    MeasurableSpace (UnsignedConfiguration sites) := ⊤
instance instSingletonUnsignedConfiguration (sites : Finset ℕ) :
    MeasurableSingletonClass (UnsignedConfiguration sites) := by infer_instance

def forgetSpatialSigns (sites : Finset ℕ) (config : SpatialMarkedConfig sites) : UnsignedConfiguration sites :=
  config.mapDomain (fun j => (j.1,j.2.1))

def unsignedProjection (sites : Finset ℕ) (E : ℕ) (config : UnsignedConfiguration sites)
    (i : {x : ℕ // x∈sites} × Fin (E+1)) : ℕ := config (i.1,i.2.val)

def forgetFiniteSpatialSigns (sites : Finset ℕ) (E : ℕ)
    (k : LabelledIndex sites (Fin (E+1) × F₂) → ℕ) (i : {x : ℕ // x∈sites} × Fin (E+1)) : ℕ :=
  ∑ s : F₂,k (i.1,(i.2,s))

def signFirstEquiv (sites : Finset ℕ) (E : ℕ) :
    LabelledIndex sites (Fin (E+1) × F₂) ≃ F₂ × ({x : ℕ // x∈sites} × Fin (E+1)) where
  toFun i := (i.2.2,(i.1,i.2.1))
  invFun i := (i.2.1,(i.2.2,i.1))
  left_inv _ := rfl
  right_inv _ := rfl

def unsignedRates (sites : Finset ℕ) (L E : ℕ) (i : {x : ℕ // x∈sites} × Fin (E+1)) : ℝ≥0 :=
  exactMarkRate L i.2.val

theorem forgetSpatialSigns_apply (sites : Finset ℕ) (config : SpatialMarkedConfig sites)
    (i : {x : ℕ // x∈sites} × ℕ) :
    forgetSpatialSigns sites config i=∑ s : F₂,config (i.1,(i.2,s)) := by
  classical
  unfold forgetSpatialSigns
  induction config using Finsupp.induction_linear with
  | zero => simp
  | single j n =>
    rcases j with ⟨x,e,s⟩
    rcases i with ⟨y,f⟩
    by_cases hx : x=y
    · subst y
      by_cases he : e=f
      · subst f;simp [Finsupp.single_apply]
      · simp [he]
    · simp [hx]
  | add f g hf hg =>
    rw [Finsupp.mapDomain_add,Finsupp.add_apply,hf,hg]
    simp [Finset.sum_add_distrib]

/-- Summing signs commutes with the joint finite projection. -/
theorem unsignedProjection_forget (sites : Finset ℕ) (E : ℕ) (config : SpatialMarkedConfig sites) :
    unsignedProjection sites E (forgetSpatialSigns sites config)=
      forgetFiniteSpatialSigns sites E (projectConfiguration sites E config) := by
  funext i
  exact forgetSpatialSigns_apply sites config (i.1,i.2.val)

/-- Reindexing and column sums prove independence, not merely the marginal means. -/
theorem hasLaw_forgetFiniteSpatialSigns (sites : Finset ℕ) (L E : ℕ) :
    HasLaw (forgetFiniteSpatialSigns sites E) (fieldMeasure (unsignedRates sites L E))
      (fieldMeasure (BulkMarkedTransfer.allSignedRates sites L E sites)) := by
  have hr := hasLaw_reindexedPoisson (BulkMarkedTransfer.allSignedRates sites L E sites) (signFirstEquiv sites E)
  have hc := hasLaw_column_sums (fun i : F₂ × ({x : ℕ // x∈sites} × Fin (E+1)) =>
    BulkMarkedTransfer.allSignedRates sites L E sites ((signFirstEquiv sites E).symm i)) (fun _ => Finset.univ)
  have hh := hc.fun_comp hr
  have he : (fun i : {x : ℕ // x∈sites} × Fin (E+1) => ∑ s : F₂,
      BulkMarkedTransfer.allSignedRates sites L E sites ((signFirstEquiv sites E).symm (s,i)))=
      unsignedRates sites L E := by
    funext i
    have hrate (s : F₂) : BulkMarkedTransfer.allSignedRates sites L E sites
        ((signFirstEquiv sites E).symm (s,i))=signedMarkRate L i.2.val := if_pos i.1.property
    simp_rw [hrate]
    apply NNReal.coe_injective
    simp only [NNReal.coe_sum,unsignedRates]
    exact sum_signedMarkRate L i.2.val
  rw [he] at hh
  exact hh

def unsignedTargetMeasure (sites : Finset ℕ) (L : ℕ) : Measure (UnsignedConfiguration sites) :=
  (spatialTargetMeasure sites L).map (forgetSpatialSigns sites)

instance instProbabilityUnsignedTarget (sites : Finset ℕ) (L : ℕ) :
    IsProbabilityMeasure (unsignedTargetMeasure sites L) :=
  Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable

/-- Every joint finite projection of the complete target is the exact unsigned product. -/
theorem hasLaw_unsignedProjection (sites : Finset ℕ) (L E : ℕ) :
    HasLaw (unsignedProjection sites E) (fieldMeasure (unsignedRates sites L E)) (unsignedTargetMeasure sites L) := by
  have h := (hasLaw_forgetFiniteSpatialSigns sites L E).fun_comp (hasLaw_projectConfiguration sites L E)
  refine ⟨(measurable_of_countable _).aemeasurable,?_⟩
  rw [unsignedTargetMeasure,Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  have he : unsignedProjection sites E ∘ forgetSpatialSigns sites=
      forgetFiniteSpatialSigns sites E ∘ projectConfiguration sites E := funext (unsignedProjection_forget sites E)
  rw [he]
  exact h.map_eq

/-- The full spatial configuration law is determined by those joint finite projections. -/
theorem unsignedMeasure_ext (sites : Finset ℕ) (mu nu : Measure (UnsignedConfiguration sites))
    [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (h : ∀ E : ℕ,mu.map (unsignedProjection sites E)=nu.map (unsignedProjection sites E)) : mu=nu := by
  apply Measure.ext_of_singleton
  intro target
  let fiber : ℕ → Set (UnsignedConfiguration sites) := fun E => {config | ∀ x e,e≤E → config (x,e)=target (x,e)}
  have hanti : Antitone fiber := by
    intro E F hEF config hc x e he
    exact hc x e (he.trans hEF)
  have hinter : {target}=⋂ E : ℕ,fiber E := by
    ext config
    simp only [Set.mem_singleton_iff,Set.mem_iInter,fiber,Set.mem_setOf_eq]
    constructor
    · rintro rfl E x e he;rfl
    · intro he
      ext i
      exact he i.2 i.1 i.2 le_rfl
  rw [hinter,hanti.measure_iInter (fun E => (Set.to_countable (fiber E)).measurableSet.nullMeasurableSet)
    ⟨0,measure_ne_top _ _⟩,hanti.measure_iInter (fun E => (Set.to_countable (fiber E)).measurableSet.nullMeasurableSet)
    ⟨0,measure_ne_top _ _⟩]
  congr 1
  funext E
  have he := congrArg (fun m : Measure (({x : ℕ // x∈sites} × Fin (E+1)) → ℕ) =>
    m {unsignedProjection sites E target}) (h E)
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _),
    Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)] at he
  have hset : unsignedProjection sites E ⁻¹' {unsignedProjection sites E target}=fiber E := by
    ext config
    simp only [Set.mem_preimage,Set.mem_singleton_iff,fiber,Set.mem_setOf_eq]
    constructor
    · intro he x e heE
      exact congrFun he (x,⟨e,by omega⟩)
    · intro he
      funext i
      exact he i.1 i.2.val (Nat.le_of_lt_succ i.2.isLt)
  rw [hset] at he
  exact he

theorem unsignedTarget_unique (sites : Finset ℕ) (L : ℕ) (nu : Measure (UnsignedConfiguration sites))
    [IsFiniteMeasure nu] (h : ∀ E : ℕ,
      HasLaw (unsignedProjection sites E) (fieldMeasure (unsignedRates sites L E)) nu) :
    nu=unsignedTargetMeasure sites L := by
  apply unsignedMeasure_ext
  intro E
  rw [(h E).map_eq,(hasLaw_unsignedProjection sites L E).map_eq]

def unsignedSource (sites : Finset ℕ) (L : ℕ) := forgetSpatialSigns sites ∘ spatialMarkedSource sites L

theorem unsignedSource_apply (sites : Finset ℕ) (L : ℕ) (omega : InfiniteSample)
    (i : {x : ℕ // x∈sites} × ℕ) :
    unsignedSource sites L omega i=exactMarkValue (infiniteValueBit omega) i.1.val L i.2 := by
  rw [unsignedSource,Function.comp_apply,forgetSpatialSigns_apply]
  exact sum_signedMarkValue _ _ _ _

def unsignedDistance (M L : ℕ) (A : Set InfiniteSample) : ℝ :=
  massTotalVariation (conditionalObservableLaw infiniteRademacherMeasure A (unsignedSource (containedStarts M L) L))
    (observableLaw (unsignedTargetMeasure (containedStarts M L) L) id)

/-- The literal unsigned spatial comparison is a statistic of the true signed field. -/
theorem unsignedDistance_le (M L : ℕ) (A : Set InfiniteSample) (hpos : 0 < infiniteRademacherMeasure.real A) :
    unsignedDistance M L A≤conditionalDistance M L A := by
  have h := conditional_functional_distance_le M L A hpos (forgetSpatialSigns (containedStarts M L))
  have ht : observableLaw (unsignedTargetMeasure (containedStarts M L) L) id=
      observableLaw (targetMeasure M L) (forgetSpatialSigns (containedStarts M L)) := by
    funext a
    exact (observableLaw_eq_map _ (measurable_of_countable _) a).symm
  unfold unsignedDistance
  rw [ht]
  exact h

/-- The actual unsigned single-site intensity in the centered coordinates of 7.6. -/
theorem unsigned_centered_rate {M d : ℕ} (hd : d≤criticalBase M) (e : ℕ) :
    (exactMarkRate (movingLength M d) e : ℝ)=
      (2 : ℝ)^(-(criticalBase M : ℝ)-((e : ℤ)-d : ℤ)-1) := by
  simpa only [exactMarkRate_coe,levelEquiv_val] using exact_site_mean hd e

end
end PaperC.V282.MacroTransportUnsigned
