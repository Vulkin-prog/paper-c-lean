import PaperCV282.MicroscopicBorderEvents
import PaperCV282.DeepStartEvents
import PaperCV282.SharpConditioning

/-! # Actual microscopic non-vacancy and conditional localization -/
namespace PaperC.V282.MicroscopicNonvacancy

open MeasureTheory ProbabilityTheory Set InfiniteRademacher InfiniteStartProbabilityTransfer
open MicroscopicBorderEvents SharpConditioning
open scoped BigOperators

noncomputable section

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤
local instance instProbabilityInfiniteRademacher : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

/-- At least one actual interior start in the microscopic range. -/
def interiorEvent (L : ℕ) : Set InfiniteSample :=
  ⋃ x ∈ Finset.Icc 2 (2 * L ^ 2), infiniteStartEvent x L

/-- The event recorded by the microscopic configuration: border or interior start. -/
def microscopicEvent (L : ℕ) : Set InfiniteSample := borderEvent L ∪ interiorEvent L

/-- The actual q_L of section 7.1, distinct from the exact border probability. -/
def microscopicProbability (L : ℕ) : ℝ := infiniteRademacherMeasure.real (microscopicEvent L)

/-- The border is the only recorded start. -/
def uniqueBorderEvent (L : ℕ) : Set InfiniteSample := borderEvent L \ interiorEvent L

theorem measurableSet_interiorEvent (L : ℕ) : MeasurableSet (interiorEvent L) := by
  apply MeasurableSet.iUnion
  intro x
  apply MeasurableSet.iUnion
  intro _hx
  exact measurableSet_infiniteStartEvent x L

theorem measurableSet_microscopicEvent (L : ℕ) : MeasurableSet (microscopicEvent L) :=
  (measurableSet_borderEvent L).union (measurableSet_interiorEvent L)

theorem measurableSet_uniqueBorderEvent (L : ℕ) : MeasurableSet (uniqueBorderEvent L) :=
  (measurableSet_borderEvent L).diff (measurableSet_interiorEvent L)

/-- The exact border is always part of microscopic non-vacancy. -/
theorem border_probability_le_microscopic_probability (L : ℕ) :
    ((2 : ℝ)⁻¹) ^ Nat.primeCounting L ≤ microscopicProbability L := by
  rw [← equation_seven_one]
  exact measureReal_mono subset_union_left (measure_ne_top _ _)

theorem microscopicProbability_pos (L : ℕ) : 0 < microscopicProbability L :=
  lt_of_lt_of_le (by positivity) (border_probability_le_microscopic_probability L)

/-- A plain union bound, without independence between microscopic starts. -/
theorem interior_probability_le_mass (L : ℕ) :
    infiniteRademacherMeasure.real (interiorEvent L) ≤
      ∑ x ∈ Finset.Icc 2 (2 * L ^ 2), infiniteStartProbability x L :=
  DeepStartEvents.probability_any_start_le_mass _ L

/-- Upper and lower finite comparisons for the real non-vacancy probability. -/
theorem microscopic_probability_bounds {L : ℕ} {epsilon : ℝ}
    (h : (∑ x ∈ Finset.Icc 2 (2 * L ^ 2), infiniteStartProbability x L) ≤ epsilon) :
    ((2 : ℝ)⁻¹) ^ Nat.primeCounting L ≤ microscopicProbability L ∧
      microscopicProbability L ≤ ((2 : ℝ)⁻¹) ^ Nat.primeCounting L + epsilon := by
  refine ⟨border_probability_le_microscopic_probability L, ?_⟩
  apply (measureReal_union_le _ _).trans
  rw [equation_seven_one]
  exact add_le_add le_rfl ((interior_probability_le_mass L).trans h)

/-- Non-vacancy without the border is paid for by the interior mass. -/
theorem nonborder_probability_le_mass (L : ℕ) :
    infiniteRademacherMeasure.real (microscopicEvent L \ borderEvent L) ≤
      ∑ x ∈ Finset.Icc 2 (2 * L ^ 2), infiniteStartProbability x L := by
  apply (measureReal_mono (show microscopicEvent L \ borderEvent L ⊆ interiorEvent L by
    intro omega homega
    exact homega.1.resolve_left homega.2) (measure_ne_top _ _)).trans
  exact interior_probability_le_mass L

/-- The unique-border probability is exactly q_L minus the interior non-vacancy probability. -/
theorem unique_border_probability_eq (L : ℕ) :
    infiniteRademacherMeasure.real (uniqueBorderEvent L) = microscopicProbability L -
      infiniteRademacherMeasure.real (interiorEvent L) := by
  have he : uniqueBorderEvent L = microscopicEvent L \ interiorEvent L := by
    ext omega
    simp only [uniqueBorderEvent, microscopicEvent, mem_sdiff, mem_union]
    tauto
  rw [he]
  exact measureReal_sdiff (show interiorEvent L ⊆ microscopicEvent L from subset_union_right)
    (measurableSet_interiorEvent L) (measure_ne_top _ _)

/-- A finite lower bound on the mass with exactly the border recorded. -/
theorem unique_border_probability_ge {L : ℕ} {epsilon : ℝ}
    (h : (∑ x ∈ Finset.Icc 2 (2 * L ^ 2), infiniteStartProbability x L) ≤ epsilon) :
    microscopicProbability L - epsilon ≤ infiniteRademacherMeasure.real (uniqueBorderEvent L) := by
  rw [unique_border_probability_eq]
  linarith [(interior_probability_le_mass L).trans h]

/-- Conditional uniqueness uses the actual event probability, then the exact border lower bound. -/
theorem conditional_unique_border_probability_ge {L : ℕ} {epsilon : ℝ}
    (h : (∑ x ∈ Finset.Icc 2 (2 * L ^ 2), infiniteStartProbability x L) ≤ epsilon) :
    1 - epsilon / ((2 : ℝ)⁻¹) ^ Nat.primeCounting L ≤
      (cond infiniteRademacherMeasure (microscopicEvent L)).real (uniqueBorderEvent L) := by
  rw [cond_real_apply _ _ (measurableSet_microscopicEvent L)]
  have he : microscopicEvent L ∩ uniqueBorderEvent L = uniqueBorderEvent L := by
    apply inter_eq_right.mpr
    intro omega homega
    exact Or.inl homega.1
  rw [he]
  change _ ≤ infiniteRademacherMeasure.real (uniqueBorderEvent L) / microscopicProbability L
  have hq := microscopicProbability_pos L
  have ha : 0 < ((2 : ℝ)⁻¹) ^ Nat.primeCounting L := by positivity
  have heps : 0 ≤ epsilon := by
    apply le_trans _ h
    apply Finset.sum_nonneg
    intro x _hx
    exact ENNReal.toReal_nonneg
  have hdiv := div_le_div_of_nonneg_left heps ha (border_probability_le_microscopic_probability L)
  have hmass := div_le_div_of_nonneg_right (unique_border_probability_ge h) hq.le
  rw [sub_div, div_self hq.ne'] at hmass
  linarith

/-- Nested conditioning loses only the probability of the extra event, divided by
its true probability. This holds on arbitrary measurable probability spaces. -/
theorem nested_conditioning_le {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (E F : Set Omega) (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hEF : E ⊆ F) (hpos : 0 < mu.real E) :
    measureTotalVariation (cond mu F) (cond mu E) ≤ mu.real (F \ E) / mu.real F := by
  have hFpos : 0 < mu.real F := hpos.trans_le (measureReal_mono hEF)
  letI instProbabilityConditionalE : IsProbabilityMeasure (cond mu E) :=
    cond_isProbabilityMeasure (ConditionedCountableLaw.measure_ne_zero_of_real_pos mu hpos)
  letI instProbabilityConditionalF : IsProbabilityMeasure (cond mu F) :=
    cond_isProbabilityMeasure (ConditionedCountableLaw.measure_ne_zero_of_real_pos mu hFpos)
  rw [measureTotalVariation_comm]
  apply (measureTotalVariation_le_iff _ _ _).mpr
  intro A hA
  rw [cond_real_apply mu E hE, cond_real_apply mu F hF]
  have hdifference (A : Set Omega) (hA : MeasurableSet A) :
      mu.real (F ∩ A) - mu.real (E ∩ A) ≤ mu.real (F \ E) := by
    rw [← measureReal_sdiff (inter_subset_inter_left A hEF) (hE.inter hA)]
    apply measureReal_mono (h₂ := measure_ne_top _ _)
    intro omega homega
    exact ⟨homega.1.1, fun he => homega.2 ⟨he, homega.1.2⟩⟩
  apply normalized_difference_le (measureReal_nonneg (μ := mu) (s := E ∩ A))
    (measureReal_mono inter_subset_left) hpos hFpos (measureReal_mono hEF)
    (hdifference A hA)
  have hc := hdifference Aᶜ hA.compl
  have hm := measureReal_inter_add_sdiff (μ := mu) (s := E) hA
  have hn := measureReal_inter_add_sdiff (μ := mu) (s := F) hA
  change mu.real (F \ A) - mu.real (E \ A) ≤ mu.real (F \ E) at hc
  linarith

/-- Total variation of the two genuine conditional source measures, with no
measurability or countability restriction on the sample space beyond its actual sigma-algebra. -/
theorem microscopic_conditional_tv_le {L : ℕ} {epsilon : ℝ}
    (h : (∑ x ∈ Finset.Icc 2 (2 * L ^ 2), infiniteStartProbability x L) ≤ epsilon) :
    measureTotalVariation (cond infiniteRademacherMeasure (microscopicEvent L))
      (cond infiniteRademacherMeasure (borderEvent L)) ≤
        epsilon / ((2 : ℝ)⁻¹) ^ Nat.primeCounting L := by
  have hn := nested_conditioning_le infiniteRademacherMeasure (borderEvent L) (microscopicEvent L)
    (measurableSet_borderEvent L) (measurableSet_microscopicEvent L) subset_union_left
    (borderEvent_probability_pos L)
  have hq := microscopicProbability_pos L
  have ha : 0 < ((2 : ℝ)⁻¹) ^ Nat.primeCounting L := by positivity
  have hm := (nonborder_probability_le_mass L).trans h
  have heps : 0 ≤ epsilon := (measureReal_nonneg.trans hm)
  apply hn.trans
  exact (div_le_div_of_nonneg_right hm hq.le).trans
    (div_le_div_of_nonneg_left heps ha (border_probability_le_microscopic_probability L))

end
end PaperC.V282.MicroscopicNonvacancy
