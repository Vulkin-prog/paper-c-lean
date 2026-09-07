import PaperCV282.CrossoverClockRecordMass

/-! # Exact one-point test masses for the complete bulk law -/
namespace PaperC.V282.CrossoverBulkTestMass

open MeasureTheory ProbabilityTheory BulkMarkedTypes BulkMarkedTarget CrossoverBulkAtoms
open CrossoverBulkOnePoint CrossoverMarkedModel CrossoverMarkedTarget CrossoverMarkedCandidate SharpConditioning

noncomputable section

def encodePoint (sites : Finset ℕ) : Option (SpatialMarkedIndex sites) → Record :=
  Option.map (fun j => Sum.inr (j.1.val,j.2))

def bulkCandidate (sites : Finset ℕ) (c : SpatialMarkedConfig sites) : Record :=
  encodePoint sites (selectPoint sites c)

theorem candidate_off_border (sites : Finset ℕ) (z : CandidateSample sites) (h : z.1.1=false) :
    candidate sites z=bulkCandidate sites z.2 := by simp [candidate,bulkCandidate,encodePoint,h]

theorem conditional_bulkCandidate (sites : Finset ℕ) (hs : sites.Nonempty) (L : ℕ) :
    (cond (spatialTargetMeasure sites L) {c | totalSize sites c=1}).map (bulkCandidate sites)=bulkLaw sites hs := by
  have he := congrArg (fun mu : Measure (Option (SpatialMarkedIndex sites)) => mu.map (encodePoint sites))
    (conditional_selectPoint sites hs L)
  rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _),
    Measure.map_map (measurable_of_countable _) (measurable_of_countable _)] at he
  exact he

theorem one_point_test_mass (sites : Finset ℕ) (hs : sites.Nonempty) (L : ℕ) (S : Set Record) :
    (spatialTargetMeasure sites L).real {c | totalSize sites c=1 ∧ bulkCandidate sites c∈S}=
      Real.exp (-(totalRate sites L : ℝ))*(totalRate sites L : ℝ)*(bulkLaw sites hs).real S := by
  have he := congrArg (fun mu : Measure Record => mu.real S) (conditional_bulkCandidate sites hs L)
  rw [map_measureReal_apply (measurable_of_countable _) (Set.to_countable _).measurableSet,
    cond_real_apply _ _ (Set.to_countable _).measurableSet] at he
  have hn := (div_eq_iff (unique_point_probability_pos sites hs L).ne').mp he
  rw [total_size_probability] at hn
  simp only [pow_one,Nat.factorial_one,Nat.cast_one,div_one] at hn
  exact hn.trans (by ring)

end
end PaperC.V282.CrossoverBulkTestMass
