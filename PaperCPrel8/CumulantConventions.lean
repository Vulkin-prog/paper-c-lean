import PaperCPrel8.CumulantTranslationTable
import PaperCPrel8.FiniteCumulantEnvelope

/-! # Raw and centered higher cumulants agree for the actual finite probability law -/
namespace PaperC.Prel8.CumulantConventions
open Finset FiniteCumulantPartitions FiniteCumulantEnvelope CumulantTranslationTable
open ArratiaGoldsteinGordonInput IndependentThinning V282.SteinFiniteExpectation
noncomputable section
variable {ι Ω : Type*} [DecidableEq ι] [Fintype Ω]
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

def rawMoment (mu : FinitePMF Ω) (X : ι → Ω → ℝ) (S : Finset ι) : ℝ :=
  finitePMFExpectation mu (fun w ↦ ∏ i∈S, X i w)

def rawCumulant (mu : FinitePMF Ω) (X : ι → Ω → ℝ) (S : Finset ι) : ℝ :=
  cumulant (rawMoment mu X) S

theorem rawMoment_empty (mu : FinitePMF Ω) (X : ι → Ω → ℝ) : rawMoment mu X ∅=1 := by
  simp [rawMoment,expectation_const]

theorem rawMoment_translate_one (mu : FinitePMF Ω) (X : ι → Ω → ℝ) (i : ι) (c : ℝ) :
    rawMoment mu (fun j w ↦ X j w+if j=i then c else 0)=shiftMoment (rawMoment mu X) i c := by
  funext S
  unfold rawMoment shiftMoment
  simp_rw [prod_single_shift]
  rw [expectation_add]
  by_cases hi : i∈S
  · simp only [hi,ite_true,expectation_const_mul]
  · simp only [hi,ite_false,expectation_const]

theorem rawCumulant_translate_one (mu : FinitePMF Ω) (X : ι → Ω → ℝ)
    (i : ι) (c : ℝ) (S : Finset ι) (hS : 2≤S.card) :
    rawCumulant mu (fun j w ↦ X j w+if j=i then c else 0) S=rawCumulant mu X S := by
  unfold rawCumulant
  rw [rawMoment_translate_one,cumulant_shift _ (rawMoment_empty mu X)]
  have hn : S≠{i} := by intro he; simp [he] at hS
  simp only [shiftCumulant,if_neg hn,add_zero]

theorem rawCumulant_translate_set (mu : FinitePMF Ω) (X : ι → Ω → ℝ)
    (c : ι → ℝ) (S T : Finset ι) (hS : 2≤S.card) :
    rawCumulant mu (fun j w ↦ X j w+if j∈T then c j else 0) S=rawCumulant mu X S := by
  induction T using Finset.induction_on with
  | empty => simp
  | @insert i T hi ih =>
    have he : (fun j w ↦ X j w+if j∈insert i T then c j else 0)=
        (fun j w ↦ (X j w+if j∈T then c j else 0)+if j=i then c i else 0) := by
      funext j w
      by_cases hj : j=i
      · subst j; simp [hi]
      · simp [hj]
    rw [he,rawCumulant_translate_one _ _ i (c i) S hS,ih]

/-- Deterministic translations do not affect any order >=2. -/
theorem rawCumulant_translation [Fintype ι] (mu : FinitePMF Ω) (X : ι → Ω → ℝ)
    (c : ι → ℝ) (S : Finset ι) (hS : 2≤S.card) :
    rawCumulant mu (fun j w ↦ X j w+c j) S=rawCumulant mu X S := by
  simpa only [mem_univ,ite_true] using rawCumulant_translate_set mu X c S univ hS

/-- The centered convention used in G.8 is exactly the raw cumulant in all registered orders. -/
theorem jointCumulant_eq_raw [Fintype ι] (mu : FinitePMF Ω) (X : ι → Ω → ℝ)
    (S : Finset ι) (hS : 2≤S.card) : jointCumulant mu X S=rawCumulant mu X S := by
  have hh := rawCumulant_translation mu X (fun j ↦ -finitePMFExpectation mu (X j)) S hS
  have he : rawMoment mu (fun j w ↦ X j w + -finitePMFExpectation mu (X j))=centeredMoment mu X := by
    funext T
    simp only [rawMoment,centeredMoment,sub_eq_add_neg]
  unfold rawCumulant at hh
  rw [he] at hh
  exact hh

/-- Reference centering in Palm formulas retains its nonzero singleton correction. -/
theorem reference_singleton (mu : FinitePMF Ω) (X : ι → Ω → ℝ) (p : ι → ℝ) (i : ι) :
    rawCumulant mu (fun j w ↦ X j w-p j) {i}=finitePMFExpectation mu (X i)-p i := by
  rw [rawCumulant,cumulant_singleton]
  simp only [rawMoment,prod_singleton,expectation_sub,expectation_const]

/-- At higher orders the Palm reference p has no effect on the raw cumulants. -/
theorem reference_higher [Fintype ι] (mu : FinitePMF Ω) (X : ι → Ω → ℝ)
    (p : ι → ℝ) (S : Finset ι) (hS : 2≤S.card) :
    rawCumulant mu (fun j w ↦ X j w-p j) S=rawCumulant mu X S := by
  simpa only [sub_eq_add_neg] using rawCumulant_translation mu X (fun j ↦ -p j) S hS

end
end PaperC.Prel8.CumulantConventions
