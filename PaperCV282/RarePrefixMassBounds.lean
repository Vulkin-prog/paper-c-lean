import PaperCV282.RarePrefixPoisson

/-! # Normalization of the two rare sources without assuming a limiting weight ratio -/
namespace PaperC.V282.RarePrefixMassBounds

open MeasureTheory InfiniteRademacher InfiniteStartProbabilityTransfer RarePrefixPoisson RarePrefixEvents
open BulkPopulation BulkMarkedGeometry BulkMicroscopicRecord MicroscopicNonvacancy MicroscopicBorderEvents
open AllStartSoftPoisson
open scoped NNReal BigOperators

noncomputable section
local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

/-- Neither branch is divided by its possibly vanishing mixture weight. -/
theorem normalized_mixture_error_le {p q a b lambda i m j : ℝ}
    (ha : 0 < a) (hlambda : 0 < lambda) (hb : 0 ≤ b) (hbhi : b ≤ lambda)
    (hi : 0 ≤ i) (hm : 0 ≤ m) (hj : 0 ≤ j) (haq : a ≤ q)
    (hqa : |q-a| ≤ i) (hp : |p-(a+b)| ≤ i+m+j+b^2+a*b) :
    |p/(q+lambda)-1| ≤ 2*i/a + m/(a+lambda) + j/lambda + lambda+a+|b/lambda-1| := by
  have hd : 0 < q+lambda := by linarith
  have htri : |p-(q+lambda)| ≤ 2*i+m+j+b^2+a*b+|b-lambda| := by
    have h1 := abs_sub_le p (a+b) (q+lambda)
    have h2 := abs_add_le (a-q) (b-lambda)
    rw [abs_sub_comm a q] at h2
    have he : (a+b)-(q+lambda) = (a-q)+(b-lambda) := by ring
    rw [he] at h1
    linarith
  have he : |p/(q+lambda)-1| = |p-(q+lambda)|/(q+lambda) := by
    have heq : p/(q+lambda)-1 = (p-(q+lambda))/(q+lambda) := by field_simp
    rw [heq, abs_div, abs_of_pos hd]
  rw [he]
  have hI := div_le_div_of_nonneg_left (mul_nonneg (by norm_num : (0 : ℝ)≤2) hi) ha
    (show a ≤ q+lambda by linarith)
  have hM := div_le_div_of_nonneg_left hm (show 0 < a+lambda by positivity)
    (show a+lambda ≤ q+lambda by linarith)
  have hJ := div_le_div_of_nonneg_left hj hlambda (show lambda ≤ q+lambda by linarith)
  have hB : b^2/(q+lambda) ≤ lambda := (div_le_iff₀ hd).mpr (by nlinarith)
  have hAB : a*b/(q+lambda) ≤ a := (div_le_iff₀ hd).mpr (by nlinarith)
  have hD := div_le_div_of_nonneg_left (abs_nonneg (b-lambda)) hlambda
    (show lambda ≤ q+lambda by linarith)
  have heD : |b-lambda|/lambda = |b/lambda-1| := by
    have heq : b/lambda-1 = (b-lambda)/lambda := by field_simp
    rw [heq, abs_div, abs_of_pos hlambda]
  rw [heD] at hD
  have hdiv := div_le_div_of_nonneg_right htri hd.le
  simp only [add_div] at hdiv
  linarith

/-- Every summand is an already controlled genuine error, with no assumed target comparison. -/
def rareErrorBudget (M L : ℕ) (delta : ℝ) : ℝ :=
  2*(∑ x ∈ Finset.Icc 2 (2*L^2), infiniteStartProbability x L) /
      (((2 : ℝ)⁻¹)^Nat.primeCounting L) +
    infiniteRademacherMeasure.real (middleEvent M L delta) /
      ((((2 : ℝ)⁻¹)^Nat.primeCounting L)+(fullRate M L : ℝ)) +
    microscopicJointDistance M L delta/(fullRate M L : ℝ) +
    (fullRate M L : ℝ) + (((2 : ℝ)⁻¹)^Nat.primeCounting L) +
    |(bulkRate M L delta : ℝ)/(fullRate M L : ℝ)-1|

theorem hit_relative_error_le {M L : ℕ} {delta : ℝ}
    (hM : 2 ≤ M) (hL : 1 ≤ L) (hLM : L ≤ M) (hdelta : 0 < delta) :
    |hitProbability M L/(microscopicProbability L+(fullRate M L : ℝ))-1| ≤ rareErrorBudget M L delta := by
  have ha : 0 < (((2 : ℝ)⁻¹)^Nat.primeCounting L) := by positivity
  have hlambda : 0 < (fullRate M L : ℝ) := by change 0 < (M : ℝ)/2^L; positivity
  have hbhi : (bulkRate M L delta : ℝ) ≤ (fullRate M L : ℝ) := by
    change ((bulkStarts M L delta).card : ℝ)/(2 : ℝ)^L ≤ (M : ℝ)/(2 : ℝ)^L
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast card_bulkStarts_le hM hL hdelta
  have hi : 0 ≤ ∑ x ∈ Finset.Icc 2 (2*L^2), infiniteStartProbability x L :=
    Finset.sum_nonneg fun _ _ => by exact ENNReal.toReal_nonneg
  have hq := microscopic_probability_bounds (le_refl (∑ x ∈ Finset.Icc 2 (2*L^2), infiniteStartProbability x L))
  have hqa : |microscopicProbability L-((2 : ℝ)⁻¹)^Nat.primeCounting L| ≤
      ∑ x ∈ Finset.Icc 2 (2*L^2), infiniteStartProbability x L := by
    rw [abs_of_nonneg (sub_nonneg.mpr hq.1)]
    linarith [hq.2]
  have hp := hit_probability_error_le hM hL hLM hdelta
  rw [equation_seven_one] at hp
  have hp' : |hitProbability M L-(((2 : ℝ)⁻¹)^Nat.primeCounting L+(bulkRate M L delta : ℝ))| ≤
      (∑ x ∈ Finset.Icc 2 (2*L^2), infiniteStartProbability x L) +
      infiniteRademacherMeasure.real (middleEvent M L delta) + microscopicJointDistance M L delta +
      (bulkRate M L delta : ℝ)^2 + ((2 : ℝ)⁻¹)^Nat.primeCounting L*(bulkRate M L delta : ℝ) := by
    linarith [interior_probability_le_mass L]
  exact normalized_mixture_error_le ha hlambda (by positivity) hbhi hi
    (measureReal_nonneg (μ := infiniteRademacherMeasure)) (microscopicJointDistance_nonneg M L delta)
    hq.1 hqa hp'

end
end PaperC.V282.RarePrefixMassBounds
