import PaperCPrel8.BulkCloudIdentification
import PaperCPrel8.PoissonRegularCloud

/-! # The ordered positions of the actual signed marked Poisson sample

The finite grid law used by the CRT estimates is recovered from the independent
uniform position component of each full label, then mixed over the Poisson count.
-/
namespace PaperC.Prel8.OrderedLabelCloud
open MeasureTheory ProbabilityTheory Finset
open V282.BulkMarkedTypes V282.CrossoverBulkOnePoint V282.GeneralPoissonMarking
open V282.InfiniteMassCoupling V282.ScalarSteinInput
open RoughKernelAllocation PoissonRegularCloud PoissonCloudMixture
open scoped NNReal ENNReal
noncomputable section
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- The nonempty set of interior indices, before adding the physical start offset. -/
theorem sites_nonempty {n : ℕ} (hn : 0<n) : (Icc 1 n).Nonempty := ⟨1,by simp; omega⟩

/-- Projecting a full label gives the uniform site law. -/
theorem hasLaw_label_site (sites : Finset ℕ) (hs : sites.Nonempty) :
    HasLaw (fun j : SpatialMarkedIndex sites ↦ j.1) (uniformSiteMeasure sites hs)
      (labelMeasure sites hs) := by
  exact measurePreserving_fst.hasLaw

/-- Every finite prefix of label positions has the actual independent product law. -/
theorem hasLaw_position_prefix (sites : Finset ℕ) (hs : sites.Nonempty) (k : ℕ) :
    HasLaw (fun marks : ℕ → SpatialMarkedIndex sites ↦ fun i : Fin k ↦ (marks i.val).1)
      (Measure.pi (fun _ : Fin k ↦ uniformSiteMeasure sites hs))
      (markSequenceMeasure (labelMeasure sites hs)) := by
  have hi := ((independent_marks (labelMeasure sites hs)).precomp (Fin.val_injective (n := k))).comp
    (fun _ ↦ Prod.fst) (fun _ ↦ measurable_fst)
  exact hi.hasLaw_pi (fun i ↦ (hasLaw_label_site sites hs).fun_comp
    (hasLaw_mark_coordinate (labelMeasure sites hs) i.val))

def positions (n : ℕ) (sample : ℕ × (ℕ → SpatialMarkedIndex (Icc 1 n))) : Cloud n :=
  ⟨sample.1, ⟨(fun i ↦ (sample.2 i.val).1.val), by
    simp only [grid,Fintype.mem_piFinset]
    exact fun i ↦ (sample.2 i.val).1.property⟩⟩

instance cloudMeasurable (n : ℕ) : MeasurableSpace (Cloud n) := ⊤
instance cloudSingleton (n : ℕ) : MeasurableSingletonClass (Cloud n) := by infer_instance

/-- Variable-length position extraction is measurable. -/
theorem measurable_positions (n : ℕ) : Measurable (positions n) := by
  apply measurable_from_prod_countable_right
  intro k
  let f : (Fin k → (Icc 1 n : Finset ℕ)) → Cloud n := fun v ↦
    ⟨k,⟨fun i ↦ (v i).val,by simp only [grid,Fintype.mem_piFinset]; exact fun i ↦ (v i).property⟩⟩
  change Measurable (f ∘ (fun marks : ℕ → SpatialMarkedIndex (Icc 1 n) ↦ fun i : Fin k ↦ (marks i.val).1))
  exact (measurable_of_countable f).comp
    (Measurable.of_eval (fun i ↦ measurable_fst.comp (measurable_pi_apply i.val)))

/-- A particular finite prefix has exactly the uniform Cartesian-grid mass. -/
theorem prefix_probability (n k : ℕ) (hn : 0<n) (J : grid n k) :
    (markSequenceMeasure (labelMeasure (Icc 1 n) (sites_nonempty hn))).real
      {marks | ∀ i : Fin k, (marks i.val).1.val=J.val i} = (gridLaw n k hn).prob J := by
  let v : Fin k → (Icc 1 n : Finset ℕ) := fun i ↦
    ⟨J.val i,(Fintype.mem_piFinset.mp J.property) i⟩
  have he : {marks : ℕ → SpatialMarkedIndex (Icc 1 n) | ∀ i : Fin k, (marks i.val).1.val=J.val i} =
      {marks | (fun i : Fin k ↦ (marks i.val).1)=v} := by
    ext marks
    constructor
    · intro h; funext i; exact Subtype.ext (h i)
    · intro h i; exact congrArg Subtype.val (congrFun h i)
  rw [he]
  apply ((hasLaw_position_prefix (Icc 1 n) (sites_nonempty hn) k).measureReal_eq (measurableSet_singleton v)).trans
  change (Measure.pi (fun _ : Fin k ↦ uniformSiteMeasure (Icc 1 n) (sites_nonempty hn))).real {v} = _
  rw [Measure.real,Measure.pi_singleton,ENNReal.toReal_prod]
  change (∏ i : Fin k, (uniformSiteMeasure (Icc 1 n) (sites_nonempty hn)).real {v i}) = _
  simp only [uniformSiteMeasure_real_singleton]
  simp [gridLaw,FinitePMF.uniform_prob,grid_card,Nat.card_Icc,div_eq_mul_inv]

/-- Every ordered-cloud atom agrees with the normalized Poisson mixture already bounded by CRT. -/
theorem positions_atom (n : ℕ) (hn : 0<n) (rate : ℝ≥0) (s : Cloud n) :
    observableLaw (markSampleMeasure rate (labelMeasure (Icc 1 n) (sites_nonempty hn)))
      (positions n) s = mass rate (fun k ↦ gridLaw n k hn) s := by
  rcases s with ⟨k,J⟩
  have he : {sample | positions n sample=⟨k,J⟩} =
      ({k} : Set ℕ) ×ˢ {marks : ℕ → SpatialMarkedIndex (Icc 1 n) | ∀ i : Fin k, (marks i.val).1.val=J.val i} := by
    ext sample
    rcases sample with ⟨l,marks⟩
    constructor
    · intro h
      have hk := congrArg Sigma.fst h
      change l=k at hk
      subst l
      refine ⟨rfl,?_⟩
      have hv := (Sigma.mk.inj_iff.mp h).2
      have hv' := eq_of_heq hv
      exact fun i ↦ congrFun (congrArg Subtype.val hv') i
    · rintro ⟨hl,hv⟩
      change l=k at hl
      subst l
      apply congrArg (Sigma.mk k)
      apply Subtype.ext
      funext i
      exact hv i
  rw [observableLaw,he,markSampleMeasure,measureReal_prod_prod,prefix_probability]
  rfl

/-- Every event of the actual ordered positions has the exact earlier mixture probability. -/
theorem positions_event (n : ℕ) (hn : 0<n) (rate : ℝ≥0) (P : Cloud n → Prop) :
    (markSampleMeasure rate (labelMeasure (Icc 1 n) (sites_nonempty hn))).real
      {sample | P (positions n sample)} = probability rate (fun k ↦ gridLaw n k hn) P := by
  have he := restricted_observableLaw_eq_event
    (markSampleMeasure rate (labelMeasure (Icc 1 n) (sites_nonempty hn))) (measurable_positions n) {s | P s}
  apply he.symm.trans
  simp only [Set.mem_ofPred_eq,probability]
  congr 1
  funext s
  split_ifs
  · exact positions_atom n hn rate s
  · rfl

end
end PaperC.Prel8.OrderedLabelCloud
