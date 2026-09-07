import PaperCV282.CrossoverBulkTestMass

/-! # Exact sparse-event normalization of the independent crossover product -/
namespace PaperC.V282.CrossoverSparseTarget

open MeasureTheory ProbabilityTheory BulkMarkedTypes BulkMarkedTarget CrossoverBulkAtoms
open CrossoverMarkedModel CrossoverMarkedTarget CrossoverMarkedCandidate CrossoverBulkTestMass
open CrossoverClockRecordMass SharpConditioning

noncomputable section

instance instProbabilityProductJoint (sites : Finset ℕ) (L K : ℕ) :
    IsProbabilityMeasure (productJoint sites L K) := by
  change IsProbabilityMeasure ((recordMeasure L K).prod (spatialTargetMeasure sites L))
  infer_instance

/-- Either the border alone or a unique bulk point with no border. -/
def sparseEvent (sites : Finset ℕ) : Set (CandidateSample sites) :=
  {z | (z.1.1=true ∧ totalSize sites z.2=0) ∨ (z.1.1=false ∧ totalSize sites z.2=1)}

theorem sparseEvent_subset_rareEvent (sites : Finset ℕ) : sparseEvent sites ⊆ rareEvent sites := by
  rintro z (⟨hb,_⟩|⟨_,hn⟩)
  · exact Or.inl hb
  · exact Or.inr (by rw [hn]; decide)

theorem sparse_test_decomposition (sites : Finset ℕ) (S : Set Record) :
    sparseEvent sites ∩ (candidate sites ⁻¹' S)=
      ({v : Bool × ℕ | v.1=true ∧ borderLabel v.2∈S} ×ˢ {c | totalSize sites c=0}) ∪
      ({v : Bool × ℕ | v.1=false} ×ˢ {c | totalSize sites c=1 ∧ bulkCandidate sites c∈S}) := by
  ext z
  rcases z with ⟨⟨b,G⟩,c⟩
  cases b <;> simp [sparseEvent,candidate,bulkCandidate,encodePoint,and_comm]

theorem sparse_test_mass (sites : Finset ℕ) (hs : sites.Nonempty) (L K : ℕ) (S : Set Record) :
    (productJoint sites L K).real (sparseEvent sites ∩ (candidate sites ⁻¹' S))=
      Real.exp (-(totalRate sites L : ℝ))*
        ((borderRate L : ℝ)*(cappedBorderLaw K).real S+
          (1-(borderRate L : ℝ))*(totalRate sites L : ℝ)*(bulkLaw sites hs).real S) := by
  rw [sparse_test_decomposition]
  have hd : Disjoint
      ({v : Bool × ℕ | v.1=true ∧ borderLabel v.2∈S} ×ˢ {c : SpatialMarkedConfig sites | totalSize sites c=0})
      ({v : Bool × ℕ | v.1=false} ×ˢ {c : SpatialMarkedConfig sites | totalSize sites c=1 ∧ bulkCandidate sites c∈S}) := by
    apply Set.disjoint_left.mpr
    intro z hz ht
    have h := hz.1.1.symm.trans ht.1
    contradiction
  rw [measureReal_union hd (Set.to_countable _).measurableSet]
  change ((recordMeasure L K).prod (spatialTargetMeasure sites L)).real _+
    ((recordMeasure L K).prod (spatialTargetMeasure sites L)).real _=_
  rw [measureReal_prod_prod,measureReal_prod_prod,true_test_mass,record_false_mass,
    CrossoverBulkOnePoint.total_size_probability,one_point_test_mass sites hs]
  simp only [pow_zero,Nat.factorial_zero,Nat.cast_one,div_one,mul_one]
  ring

theorem sparse_mass (sites : Finset ℕ) (hs : sites.Nonempty) (L K : ℕ) :
    (productJoint sites L K).real (sparseEvent sites)=Real.exp (-(totalRate sites L : ℝ))*
      ((borderRate L : ℝ)+(1-(borderRate L : ℝ))*(totalRate sites L : ℝ)) := by
  simpa only [Set.preimage_univ,Set.inter_univ,probReal_univ,mul_one] using sparse_test_mass sites hs L K Set.univ

theorem sparse_mass_pos (sites : Finset ℕ) (hs : sites.Nonempty) (L K : ℕ) :
    0 < (productJoint sites L K).real (sparseEvent sites) := by
  rw [sparse_mass sites hs]
  have ha : (0 : ℝ)<borderRate L := by exact_mod_cast borderRate_pos L
  have hb := borderRate_le_one L
  positivity

/-- Exact conditional test formula, before replacing its weights by the paper's weights. -/
theorem conditional_candidate_test (sites : Finset ℕ) (hs : sites.Nonempty) (L K : ℕ) (S : Set Record) :
    ((cond (productJoint sites L K) (sparseEvent sites)).map (candidate sites)).real S=
      ((borderRate L : ℝ)*(cappedBorderLaw K).real S+
        (1-(borderRate L : ℝ))*(totalRate sites L : ℝ)*(bulkLaw sites hs).real S)/
      ((borderRate L : ℝ)+(1-(borderRate L : ℝ))*(totalRate sites L : ℝ)) := by
  rw [map_measureReal_apply (measurable_of_countable _) (Set.to_countable _).measurableSet,
    cond_real_apply _ _ (Set.to_countable _).measurableSet,sparse_test_mass sites hs,sparse_mass sites hs]
  exact mul_div_mul_left _ _ (Real.exp_ne_zero _)

end
end PaperC.V282.CrossoverSparseTarget
