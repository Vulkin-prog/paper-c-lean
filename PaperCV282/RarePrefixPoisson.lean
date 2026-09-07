import PaperCV282.RarePrefixEvents
import PaperCV282.RarePrefixSubsequence
import PaperCV282.PoissonRareProbabilities

/-! # A finite rare-event comparison with the genuine independent bulk target -/
namespace PaperC.V282.RarePrefixPoisson

open MeasureTheory ProbabilityTheory Set InfiniteRademacher InfiniteStartProbabilityTransfer
open RarePrefixGeometry RarePrefixEvents BulkPopulation BulkMarkedGeometry BulkMarkedAggregation
open BulkMicroscopicRecord MicroscopicBorderEvents MesoscopicStability SharpConditioning
open PoissonFieldMeasure FiniteFieldPoissonCoupling ScalarSteinInput
open scoped NNReal ENNReal BigOperators

noncomputable section
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P
local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤
local instance instProbabilityInfiniteRademacher : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

/-- True probability of the finite-prefix hit event. -/
def hitProbability (M L : ℕ) : ℝ := infiniteRademacherMeasure.real (hitEvent M L)

theorem startField_zero_iff (sites : Finset ℕ) (L : ℕ) (omega : InfiniteSample) :
    startField sites L omega = 0 ↔ ∀ x∈sites, omega∉infiniteStartEvent x L := by
  simp only [funext_iff, Pi.zero_apply, startField, ExactMarkedModel.baseStartValue,
    infiniteStartEvent, mem_setOf_eq]
  constructor
  · intro h x hx
    have hh := h ⟨x,hx⟩
    intro hs
    simp only [if_pos hs, Nat.one_ne_zero] at hh
  · intro h x
    exact if_neg (h x.val x.property)

theorem startField_zero_mass (sites : Finset ℕ) (L : ℕ) :
    (fieldMeasure (startFieldRates sites L)).real {0} =
      Real.exp (-(FiniteStartMaskAverages.maskRate L sites : ℝ)) := by
  rw [fieldMeasure_real_singleton]
  unfold poissonFieldMass poissonMass
  simp only [Pi.zero_apply, poissonMeasure_real_singleton, pow_zero, Nat.factorial_zero,
    Nat.cast_one, div_one, mul_one]
  simp only [startFieldRates]
  rw [Finset.prod_const, ← Real.exp_nat_mul]
  congr 1
  change (Fintype.card sites : ℝ)*(-(1/(2 : ℝ)^L)) = -((sites.card : ℝ)/(2 : ℝ)^L)
  simp only [Fintype.card_coe]
  ring

/-- The target keeps the true microscopic law and independently samples the original-site field. -/
theorem border_bulk_probability_error_le (M L : ℕ) (delta : ℝ) :
    |infiniteRademacherMeasure.real (borderEvent L ∪ bulkHitEvent M L delta) -
      (1-(1-infiniteRademacherMeasure.real (borderEvent L))*Real.exp (-(bulkRate M L delta : ℝ)))| ≤
      microscopicJointDistance M L delta := by
  let sites := bulkStarts M L delta
  let record := microscopicRecord L 0
  let mu : Measure ((ℕ→Bool) × (sites→ℕ)) := infiniteRademacherMeasure.map
    (fun omega => (record omega, startField sites L omega))
  let nu : Measure ((ℕ→Bool) × (sites→ℕ)) :=
    (infiniteRademacherMeasure.map record).prod (fieldMeasure (startFieldRates sites L))
  let A : Set ((ℕ→Bool) × (sites→ℕ)) := ({r : ℕ→Bool | r 1=false} ×ˢ ({0} : Set (sites→ℕ)))ᶜ
  have hr : Measurable record := measurable_microscopicRecord L 0
  have hm : Measurable (fun omega => (record omega, startField sites L omega)) :=
    hr.prodMk (measurable_startField sites L)
  letI instProbabilityMu : IsProbabilityMeasure mu := Measure.isProbabilityMeasure_map hm.aemeasurable
  letI instProbabilityRecord : IsProbabilityMeasure (infiniteRademacherMeasure.map record) :=
    Measure.isProbabilityMeasure_map hr.aemeasurable
  letI instProbabilityNu : IsProbabilityMeasure nu := by dsimp [nu]; infer_instance
  have hrecord : MeasurableSet {r : ℕ→Bool | r 1=false} :=
    (measurable_pi_apply (1 : ℕ) : Measurable (fun r : ℕ→Bool => r 1)) (measurableSet_singleton false)
  have hA : MeasurableSet A := (hrecord.prod (measurableSet_singleton _)).compl
  have hpre : (fun omega => (record omega,startField sites L omega)) ⁻¹' A =
      borderEvent L ∪ bulkHitEvent M L delta := by
    ext omega
    simp only [A, mem_preimage, mem_compl_iff, mem_prod, mem_setOf_eq, mem_singleton_iff,
      startField_zero_iff, record, microscopicRecord, if_true, mem_union, bulkHitEvent, mem_iUnion]
    by_cases hb : omega∈borderEvent L <;> simp [hb, sites]
  have hmu : mu.real A = infiniteRademacherMeasure.real (borderEvent L ∪ bulkHitEvent M L delta) := by
    change (infiniteRademacherMeasure.map (fun omega => (record omega,startField sites L omega))).real A = _
    rw [Measure.real, Measure.map_apply hm hA, hpre]
    rfl
  have hrecpre : record ⁻¹' {r : ℕ→Bool | r 1=false} = (borderEvent L)ᶜ := by
    ext omega
    simp [record, microscopicRecord]
  have hn : nu.real A = 1-(1-infiniteRademacherMeasure.real (borderEvent L))*
      Real.exp (-(bulkRate M L delta : ℝ)) := by
    rw [show A=({r : ℕ→Bool | r 1=false} ×ˢ ({0} : Set (sites→ℕ)))ᶜ from rfl,
      measureReal_compl (hrecord.prod (measurableSet_singleton _)), probReal_univ]
    rw [show nu=(infiniteRademacherMeasure.map record).prod (fieldMeasure (startFieldRates sites L)) from rfl,
      measureReal_prod_prod, startField_zero_mass]
    have he : (infiniteRademacherMeasure.map record).real {r : ℕ→Bool | r 1=false} =
        1-infiniteRademacherMeasure.real (borderEvent L) := by
      rw [Measure.real,Measure.map_apply hr hrecord,hrecpre]
      exact (measureReal_compl (measurableSet_borderEvent L)).trans (by rw [probReal_univ])
    rw [he]
    rfl
  have hd := discrepancy_le mu nu A hA
  rw [hmu,hn] at hd
  exact hd

/-- The target's deterministic error is quadratic in its bulk intensity. -/
theorem independent_union_error_le {a b : ℝ} (ha : 0 ≤ a) (haOne : a ≤ 1) (hb : 0 ≤ b) :
    |(1-(1-a)*Real.exp (-b))-(a+b)| ≤ b^2+a*b := by
  have hlow := Real.add_one_le_exp (-b)
  have hup : Real.exp (-b) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hpoly : Real.exp (-b) ≤ 1-b+b^2 := by
    have hh := mul_le_mul_of_nonneg_right (Real.add_one_le_exp b) (Real.exp_nonneg (-b))
    rw [← Real.exp_add, add_neg_cancel,Real.exp_zero] at hh
    nlinarith [mul_nonneg hb (show 0 ≤ Real.exp (-b)-(1-b) by linarith)]
  apply abs_le.mpr
  constructor
  · have hx := mul_nonneg ha (show 0 ≤ Real.exp (-b)-(1-b) by linarith)
    nlinarith
  · have hx := mul_nonneg (show 0 ≤ 1-a by linarith) (show 0 ≤ Real.exp (-b)-(1-b) by linarith)
    nlinarith [mul_nonneg ha hb]

/-- A fully finite inequality; all three error terms are actual source quantities. -/
theorem hit_probability_error_le {M L : ℕ} {delta : ℝ}
    (hM : 2 ≤ M) (hL : 1 ≤ L) (hLM : L ≤ M) (hdelta : 0 < delta) :
    |hitProbability M L - (infiniteRademacherMeasure.real (borderEvent L)+(bulkRate M L delta : ℝ))| ≤
      infiniteRademacherMeasure.real (MicroscopicNonvacancy.interiorEvent L) +
      infiniteRademacherMeasure.real (middleEvent M L delta) + microscopicJointDistance M L delta +
      (bulkRate M L delta : ℝ)^2 + infiniteRademacherMeasure.real (borderEvent L)*(bulkRate M L delta : ℝ) := by
  have h1 := hit_mass_difference_le hM hL hLM hdelta
  have h2 := border_bulk_probability_error_le M L delta
  have ha : infiniteRademacherMeasure.real (borderEvent L) ≤ 1 :=
    (measureReal_mono (μ := infiniteRademacherMeasure) (Set.subset_univ _)).trans_eq probReal_univ
  have h3 := independent_union_error_le (measureReal_nonneg (μ := infiniteRademacherMeasure)) ha
    (show (0 : ℝ) ≤ (bulkRate M L delta : ℝ) by positivity)
  dsimp [hitProbability]
  calc
    _ ≤ |infiniteRademacherMeasure.real (hitEvent M L) -
        infiniteRademacherMeasure.real (borderEvent L ∪ bulkHitEvent M L delta)| +
      |infiniteRademacherMeasure.real (borderEvent L ∪ bulkHitEvent M L delta) -
        (1-(1-infiniteRademacherMeasure.real (borderEvent L))*Real.exp (-(bulkRate M L delta : ℝ)))| +
      |(1-(1-infiniteRademacherMeasure.real (borderEvent L))*Real.exp (-(bulkRate M L delta : ℝ))) -
        (infiniteRademacherMeasure.real (borderEvent L)+(bulkRate M L delta : ℝ))| := by
      calc
        _ ≤ |infiniteRademacherMeasure.real (hitEvent M L) -
            infiniteRademacherMeasure.real (borderEvent L ∪ bulkHitEvent M L delta)| +
          |infiniteRademacherMeasure.real (borderEvent L ∪ bulkHitEvent M L delta) -
            (infiniteRademacherMeasure.real (borderEvent L)+(bulkRate M L delta : ℝ))| := abs_sub_le _ _ _
        _ ≤ _ := by
          have ht := abs_sub_le (infiniteRademacherMeasure.real (borderEvent L ∪ bulkHitEvent M L delta))
            (1-(1-infiniteRademacherMeasure.real (borderEvent L))*Real.exp (-(bulkRate M L delta : ℝ)))
            (infiniteRademacherMeasure.real (borderEvent L)+(bulkRate M L delta : ℝ))
          linarith
    _ ≤ _ := by linarith

end
end PaperC.V282.RarePrefixPoisson
