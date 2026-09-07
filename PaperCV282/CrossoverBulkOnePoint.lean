import PaperCV282.CrossoverBulkAtoms
import PaperCV282.SpatialDiffuseMarks

/-! # The actual uniform site, fair sign and geometric excess at a unique Poisson point -/
namespace PaperC.V282.CrossoverBulkOnePoint

open MeasureTheory ProbabilityTheory BulkMarkedTypes BulkMarkedTarget CrossoverBulkAtoms
open GeometricClusterTarget SpatialDiffuseMarks SharpConditioning ConditionedCountableLaw
open scoped BigOperators NNReal ENNReal

noncomputable section
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P
local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

instance instMeasurableOptionIndex (sites : Finset ℕ) :
    MeasurableSpace (Option (SpatialMarkedIndex sites)) := ⊤

instance instMeasurableSingletonOptionIndex (sites : Finset ℕ) :
    MeasurableSingletonClass (Option (SpatialMarkedIndex sites)) := by infer_instance

def selectPoint (sites : Finset ℕ) (c : SpatialMarkedConfig sites) : Option (SpatialMarkedIndex sites) :=
  if h : ∃ j, c=Finsupp.single j 1 then some h.choose else none

theorem selectPoint_eq_some (sites : Finset ℕ) (c : SpatialMarkedConfig sites) (j : SpatialMarkedIndex sites) :
    selectPoint sites c=some j ↔ c=Finsupp.single j 1 := by
  unfold selectPoint
  split_ifs with h
  · constructor
    · intro he
      have hj := Option.some.inj he
      exact hj ▸ h.choose_spec
    · intro hc
      congr 1
      exact Finsupp.single_left_injective (by decide : (1 : ℕ)≠0) (h.choose_spec.symm.trans hc)
  · simp only [false_iff]
    exact fun hc => h ⟨j,hc⟩

theorem selectPoint_eq_none (sites : Finset ℕ) (c : SpatialMarkedConfig sites) :
    selectPoint sites c=none ↔ totalSize sites c≠1 := by
  have he : totalSize sites c=1 ↔ ∃ j : SpatialMarkedIndex sites, c=Finsupp.single j 1 :=
    Finsupp.sum_eq_one_iff c
  change selectPoint sites c=none ↔ ¬(totalSize sites c=1)
  rw [he]
  unfold selectPoint
  split_ifs <;> simp_all

def uniformSiteMeasure (sites : Finset ℕ) (hs : sites.Nonempty) : Measure {x // x∈sites} := by
  letI instNonemptySites : Nonempty {x // x∈sites} := ⟨⟨hs.choose,hs.choose_spec⟩⟩
  exact (PMF.uniformOfFintype {x // x∈sites}).toMeasure

instance instProbabilityUniformSite (sites : Finset ℕ) (hs : sites.Nonempty) :
    IsProbabilityMeasure (uniformSiteMeasure sites hs) := by
  unfold uniformSiteMeasure
  infer_instance

def labelMeasure (sites : Finset ℕ) (hs : sites.Nonempty) : Measure (SpatialMarkedIndex sites) :=
  (uniformSiteMeasure sites hs).prod ((geometricMeasure halfSuccess).prod signMeasure)

instance instProbabilityLabel (sites : Finset ℕ) (hs : sites.Nonempty) :
    IsProbabilityMeasure (labelMeasure sites hs) := by
  unfold labelMeasure
  infer_instance

theorem uniformSiteMeasure_real_singleton (sites : Finset ℕ) (hs : sites.Nonempty) (x : sites) :
    (uniformSiteMeasure sites hs).real {x}=1/(sites.card : ℝ) := by
  simp [uniformSiteMeasure,Measure.real,PMF.uniformOfFintype_apply]

theorem geometric_half_real_singleton (e : ℕ) :
    (geometricMeasure halfSuccess).real {e}=1/(2 : ℝ)^(e+1) := by
  exact geometric_excess_real e

theorem labelMeasure_real_singleton (sites : Finset ℕ) (hs : sites.Nonempty) (j : SpatialMarkedIndex sites) :
    (labelMeasure sites hs).real {j}=(1/(sites.card : ℝ))*(1/(2 : ℝ)^(j.2.1+1))*(1/2) := by
  have he : ({j} : Set (SpatialMarkedIndex sites))={j.1} ×ˢ ({j.2.1} ×ˢ {j.2.2}) := by
    ext k
    simp [Prod.ext_iff]
  rw [he,labelMeasure,measureReal_prod_prod,measureReal_prod_prod,
    uniformSiteMeasure_real_singleton,geometric_half_real_singleton,signMeasure_real_singleton]
  ring

theorem total_size_probability (sites : Finset ℕ) (L n : ℕ) :
    (spatialTargetMeasure sites L).real {c | totalSize sites c=n}=
      Real.exp (-(totalRate sites L : ℝ))*(totalRate sites L : ℝ)^n/n.factorial := by
  exact ((hasLaw_totalSize sites L).measureReal_eq (measurableSet_singleton n)).trans
    (poissonMeasure_real_singleton _ _)

theorem unique_point_probability_pos (sites : Finset ℕ) (hs : sites.Nonempty) (L : ℕ) :
    0<(spatialTargetMeasure sites L).real {c | totalSize sites c=1} := by
  rw [total_size_probability]
  have hc : 0<sites.card := Finset.card_pos.mpr hs
  unfold totalRate
  positivity

theorem conditional_single_atom (sites : Finset ℕ) (hs : sites.Nonempty) (L : ℕ) (j : SpatialMarkedIndex sites) :
    (cond (spatialTargetMeasure sites L) {c | totalSize sites c=1}).real {Finsupp.single j 1}=
      (labelMeasure sites hs).real {j} := by
  rw [cond_real_apply _ _ ((Set.to_countable _).measurableSet)]
  have he : {c : SpatialMarkedConfig sites | totalSize sites c=1}∩{Finsupp.single j 1}={Finsupp.single j 1} := by
    apply Set.inter_eq_right.mpr
    rintro c rfl
    simp [totalSize]
  rw [he,spatial_single_mass,total_size_probability,labelMeasure_real_singleton]
  simp only [pow_one,Nat.factorial_one,Nat.cast_one,div_one]
  have hcard : (sites.card : ℝ)≠0 := by exact_mod_cast (Finset.card_pos.mpr hs).ne'
  change Real.exp (-(totalRate sites L : ℝ))/(2 : ℝ)^(L+j.2.1+2)/
    (Real.exp (-(totalRate sites L : ℝ))*((sites.card : ℝ)/(2 : ℝ)^L))=_
  rw [show L+j.2.1+2=L+(j.2.1+1)+1 by omega,pow_add,pow_add]
  field_simp

/-- Conditioning the actual complete target on one point gives the independent displayed labels. -/
theorem conditional_selectPoint (sites : Finset ℕ) (hs : sites.Nonempty) (L : ℕ) :
    (cond (spatialTargetMeasure sites L) {c | totalSize sites c=1}).map (selectPoint sites)=
      (labelMeasure sites hs).map some := by
  letI instProbabilityConditional : IsProbabilityMeasure
      (cond (spatialTargetMeasure sites L) {c | totalSize sites c=1}) :=
    cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ (unique_point_probability_pos sites hs L))
  apply Measure.ext_of_measureReal_singleton
  intro x
  rw [Measure.real,Measure.real,Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _),
    Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  cases x with
  | none =>
    have hp : (some : SpatialMarkedIndex sites → Option (SpatialMarkedIndex sites)) ⁻¹' {none}=∅ := by ext j;simp
    rw [hp,measure_empty,ENNReal.toReal_zero]
    change (cond (spatialTargetMeasure sites L) {c | totalSize sites c=1}).real _=0
    rw [cond_real_apply _ _ ((Set.to_countable _).measurableSet)]
    have he : {c : SpatialMarkedConfig sites | totalSize sites c=1}∩(selectPoint sites ⁻¹' {none})=∅ := by
      ext c
      simp only [Set.mem_inter_iff,Set.mem_setOf_eq,Set.mem_preimage,Set.mem_singleton_iff,selectPoint_eq_none,Set.mem_empty_iff_false]
      exact iff_false_intro (fun h => h.2 h.1)
    rw [he,measureReal_empty,zero_div]
  | some j =>
    have hp : (some : SpatialMarkedIndex sites → Option (SpatialMarkedIndex sites)) ⁻¹' {some j}={j} := by ext k;simp
    have hs' : selectPoint sites ⁻¹' {some j}={Finsupp.single j 1} := by
      ext c
      exact selectPoint_eq_some sites c j
    rw [hp,hs']
    exact conditional_single_atom sites hs L j

end
end PaperC.V282.CrossoverBulkOnePoint
