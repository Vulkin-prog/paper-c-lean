import PaperCPrel8.FiniteFieldReplacement
import PaperCPrel8.ActualSignedConditionalLaw
import PaperCPrel8.RoughKernelGoodSet

/-! # Source-faithful replacement of deleted good-site signed marks

Every original good site has its exact conditional mean. Deletion therefore
costs p per site on each side, without any inverse conditioning probability.
-/
namespace PaperC.Prel8.SignedGoodReplacement
open FiniteFieldReplacement ActualSignedPalm ActualSignedConditionalLaw
open FiniteConditioning
open ConditionalStartProbability ArratiaGoldsteinGordonInput IndependentThinning
open V282.FiniteFieldTotalVariation V282.SignedExactMarks V282.ExactMarkedModel
open scoped BigOperators NNReal
noncomputable section
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P
variable {C Y L E : ℕ} {G : Finset ℕ}

/-- Keep all low signed types at retained sites, using the original coordinate space. -/
def kept (G K : Finset ℕ) (E : ℕ) : Finset (Index G E) :=
  Finset.univ.filter (fun i ↦ i.1.val ∈ K)

/-- Independent target rates only on the deleted coordinates. -/
def fill (G K : Finset ℕ) (L E : ℕ) (i : Index G E) : ℝ≥0 :=
  if i.1.val ∈ K then 0 else rate L i

/-- Exact site/type factorization of the filling intensity. -/
theorem fill_sum (G K : Finset ℕ) (L E : ℕ) :
    (∑ i, (fill G K L E i : ℝ)) =
      ((G \ K).card : ℝ) * ∑ a : Fin (E+1) × F₂, (signedMarkRate L a.1.val : ℝ) := by
  simp only [fill, rate, Fintype.sum_prod_type, apply_ite, NNReal.coe_zero]
  have hsite (j : {j // j ∈ G}) :
      (∑ a : Fin (E+1), ∑ b : F₂,
        if j.val ∈ K then (0:ℝ) else (signedMarkRate L a.val : ℝ)) =
      if j.val ∈ K then 0 else ∑ a : Fin (E+1), ∑ b : F₂, (signedMarkRate L a.val : ℝ) := by
    by_cases h : j.val ∈ K <;> simp [h]
  simp_rw [hsite]
  rw [← Finset.sum_subtype G (fun _ ↦ Iff.rfl)
    (fun j ↦ if j ∈ K then (0:ℝ) else ∑ a : Fin (E+1), ∑ b : F₂, (signedMarkRate L a.val : ℝ))]
  have he : G.filter (fun j ↦ j ∉ K) = G \ K := by ext j; simp
  have hf : (∑ j ∈ G, if j ∈ K then (0:ℝ) else
      ∑ a : Fin (E+1), ∑ b : F₂, (signedMarkRate L a.val : ℝ)) =
      ∑ j ∈ G, if j ∉ K then (∑ a : Fin (E+1), ∑ b : F₂, (signedMarkRate L a.val : ℝ)) else 0 := by
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : j ∈ K <;> simp [h]
  rw [hf,← Finset.sum_filter,he]
  simp

/-- Total low-type filling intensity is at most one base rate per deleted site. -/
theorem fill_sum_le (G K : Finset ℕ) (L E : ℕ) :
    (∑ i, (fill G K L E i : ℝ)) ≤ (1/(2:ℝ)^L) * ((G \ K).card : ℝ) := by
  rw [fill_sum]
  have h : (∑ a : Fin (E+1) × F₂, (signedMarkRate L a.1.val : ℝ)) ≤ 1/(2:ℝ)^L := by
    simpa only [Fintype.sum_prod_type] using sum_all_signedMarkRate_le_base L E
  exact (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _)).trans_eq (mul_comm _ _)

/-- Actual conditional activity at a coordinate is exactly the corresponding filling rate. -/
theorem deleted_mass_eq_fill (h : GoodGeometry C Y L E G) (K : Finset ℕ)
    (A : SmallSample C Y → Prop)
    (hA : 0 < eventProbability (FinitePMF.uniform (SampleSpace C))
      (fun w ↦ A (restrictSmall C Y w))) :
    (∑ i ∈ badFieldSites (kept G K E), eventProbability (sourceLaw A hA)
      (fun w ↦ field C L E G w i ≠ 0)) = ∑ i, (fill G K L E i : ℝ) := by
  rw [badFieldSites,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  have he : (fun w ↦ field C L E G w i ≠ 0) =
      (fun w ↦ SignedExactMark (valueBit w) (i.1.val+1) L i.2.1.val i.2.2) := by
    funext w
    simp [field,signedMarkValue]
  rw [he,mark_probability h A hA i]
  by_cases hk : i.1.val ∈ K <;> simp [kept,fill,hk]

/-- The literal additional low-type replacement has cost at most 2p times the deleted count. -/
theorem replacement_cost (h : GoodGeometry C Y L E G) (K : Finset ℕ)
    (A : SmallSample C Y → Prop)
    (hA : 0 < eventProbability (FinitePMF.uniform (SampleSpace C))
      (fun w ↦ A (restrictSmall C Y w))) :
    massTotalVariation (finiteFieldLaw (sourceLaw A hA) (field C L E G))
      (replacementLaw (sourceLaw A hA) (field C L E G) (kept G K E) (fill G K L E)) ≤
        2 * (1/(2:ℝ)^L) * ((G \ K).card : ℝ) := by
  have hh := replacement_bound (sourceLaw A hA) (field C L E G) (kept G K E) (fill G K L E)
  rw [deleted_mass_eq_fill h K A hA] at hh
  have hf := fill_sum_le G K L E
  nlinarith

end
end PaperC.Prel8.SignedGoodReplacement
