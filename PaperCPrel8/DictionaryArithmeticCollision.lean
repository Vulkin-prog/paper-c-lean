import PaperCPrel8.DictionaryCollision

/-! # Collision and sampling bounds for the actual arithmetic word fields -/
namespace PaperC.Prel8.DictionaryArithmeticCollision
open PaperC.Affine PaperC.V282.PrescribedValues PaperC.V282.WindowValues
open PaperC.V282.DictionaryMarginalCap PaperC.V282.TwoWindowParity
open PaperC.Prel8.DictionaryCollision PaperC.Prel8.DictionarySamplingBounds
open PaperC.ArratiaGoldsteinGordonInput PaperC.ConditionalStartProbability
open PaperC.SectionThirteenCouplings PaperC.ConditionalAGGAverage
open PaperC.V282.RandomDictionary
noncomputable section
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- The stacked maps are precisely the joint arithmetic value system. -/
theorem stacked_values_eq (M x y B : ℕ) :
    stacked (valueSystem M (vertex x B)) (valueSystem M (vertex y B)) =
      jointValueSystem M x y B := by ext omega i; cases i <;> rfl

/-- Exact full-cylinder probability of a collision as a homogeneous affine fibre. -/
theorem word_collision_probability_eq (M x y B : ℕ) :
    eventProbability (fullUniformPMF M) (fun omega =>
      valueSystem M (vertex x B) omega=valueSystem M (vertex y B) omega) =
    (uniformSolutionProbability (valueSystem M (vertex x B)-valueSystem M (vertex y B)) 0:ℝ) := by
  rw [eventProbability_fullUniformPMF_eq,finiteUniformProbability_eq_uniformEventProbability]
  congr 1
  unfold uniformEventProbability uniformSolutionProbability
  rw [Fintype.card_subtype]
  congr 2
  apply congrArg Finset.card
  ext omega
  simp [solutionSet,LinearMap.sub_apply,sub_eq_zero]

/-- The collision estimate uses the full valuation nullity, without any goodness premise. -/
theorem word_collision_probability_le (M x y B : ℕ) :
    eventProbability (fullUniformPMF M) (fun omega =>
      valueSystem M (vertex x B) omega=valueSystem M (vertex y B) omega) ≤
      (2:ℝ)^relationRho (jointValueSystem M x y B)/(2:ℝ)^B := by
  rw [word_collision_probability_eq]
  have h := collision_probability_le (valueSystem M (vertex x B)) (valueSystem M (vertex y B))
  rw [stacked_values_eq] at h
  have hr := (Rat.cast_le (K := ℝ)).mpr h
  simpa only [Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat,Fintype.card_fin] using hr

/-- The actual dictionary pair mass obeys the averaged full-relation estimate. -/
theorem averaged_dictionary_joint_le (M x y B m : ℕ) (hB : 1 ≤ B)
    (hm : 1 ≤ m) (hmb : m ≤ 2^B) :
    dictionaryAverage B m (fun W => dictionaryJointProbability M x y B W) ≤
      ((m:ℝ)/(2:ℝ)^B)^2+((m:ℝ)/(2:ℝ)^B)*
        ((2:ℝ)^relationRho (jointValueSystem M x y B)/(2:ℝ)^B) := by
  have hs := averaged_pair_le hB hm hmb (fullUniformPMF M)
    (valueSystem M (vertex x B)) (valueSystem M (vertex y B))
  have hc := word_collision_probability_le M x y B
  have he : dictionaryAverage B m (fun W => dictionaryJointProbability M x y B W) =
      dictionaryAverage B m (fun W => eventProbability (fullUniformPMF M) (fun omega =>
        valueSystem M (vertex x B) omega ∈ W ∧ valueSystem M (vertex y B) omega ∈ W)) := by
    simp only [dictionaryJointProbability,dictionaryIndicator_eq_true]
  rw [he]
  exact hs.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hc (show 0 ≤ (m:ℝ)/(2:ℝ)^B by positivity)))

end
end PaperC.Prel8.DictionaryArithmeticCollision
