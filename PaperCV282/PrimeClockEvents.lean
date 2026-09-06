import PaperCV282.MicroscopicBorderEvents
import Mathlib.Probability.ConditionalProbability

/-! # The first negative prime on the actual infinite sample

Prime coordinates are zero based. The index is assigned zero on the null
all-positive sample set, and all exact distribution identities retain that
exception explicitly until passing to measure.
-/
namespace PaperC.V282.PrimeClockEvents

open MeasureTheory ProbabilityTheory Set InfiniteRademacher MicroscopicBorderEvents
open scoped ENNReal

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤
local instance instProbabilityInfinite : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

noncomputable section

def firstNegativeEvent (j : ℕ) : Set InfiniteSample :=
  {omega | omega j = 1 ∧ ∀ k < j, omega k = 0}

def firstNegativeIndex (omega : InfiniteSample) : ℕ := by
  classical
  exact if h : ∃ j, omega j ≠ 0 then Nat.find h else 0

/-- Two-valuedness of the prime signs, in additive coordinates. -/
theorem bit_ne_zero_iff_eq_one (b : F₂) : b ≠ 0 ↔ b = 1 := by
  classical
  have hb : b=0 ∨ b=1 := by
    fin_cases b
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hb with rfl | rfl <;> simp

/-- A first-negative event is a literal finite product cylinder. -/
theorem firstNegativeEvent_eq_pi (j : ℕ) :
    firstNegativeEvent j = Set.pi (Finset.range (j+1))
      (fun k => {(if k=j then 1 else 0 : F₂)}) := by
  ext omega
  simp only [firstNegativeEvent,Set.mem_setOf_eq,Set.mem_pi,Finset.mem_coe,
    Finset.mem_range,Set.mem_singleton_iff]
  constructor
  · rintro ⟨hj,h⟩ k hk
    split_ifs with heq
    · simpa [heq] using hj
    · exact h k (by omega)
  · intro h
    exact ⟨by simpa using h j (by omega),fun k hk => by simpa [show k≠j by omega] using h k (by omega)⟩

theorem measurableSet_firstNegativeEvent (j : ℕ) : MeasurableSet (firstNegativeEvent j) := by
  change MeasurableSet {omega : InfiniteSample | omega j=1 ∧ ∀ k<j, omega k=0}
  apply ((measurable_pi_apply j) (measurableSet_singleton 1)).inter
  convert (MeasurableSet.iInter fun k => MeasurableSet.iInter fun (_ : k<j) =>
    (show MeasurableSet {omega : InfiniteSample | omega k=0} from
      (measurable_pi_apply k) (measurableSet_singleton 0))) using 1
  ext omega
  simp only [Set.mem_iInter,Set.mem_setOf_eq]
  rfl

/-- Exact law of the first exposed negative prime bit. -/
theorem measure_firstNegativeEvent (j : ℕ) :
    infiniteRademacherMeasure (firstNegativeEvent j) = ((2 : ℝ≥0∞)⁻¹)^(j+1) := by
  rw [firstNegativeEvent_eq_pi,infiniteRademacherMeasure,Measure.infinitePi_pi]
  · simp
  · intro k hk
    exact measurableSet_singleton _

theorem probability_firstNegativeEvent (j : ℕ) :
    infiniteRademacherMeasure.real (firstNegativeEvent j) = ((2 : ℝ)⁻¹)^(j+1) := by
  rw [measureReal_def,measure_firstNegativeEvent]
  simp

/-- The exceptional all-positive prime sample set is exactly the old zero tail. -/
theorem no_negative_eq_zeroTail :
    {omega : InfiniteSample | ¬∃ j,omega j≠0} = zeroTail 0 := by
  ext omega
  simp [zeroTail]

/-- A first negative prime exists almost surely, with no number-theoretic assumption. -/
theorem ae_exists_negative :
    ∀ᵐ omega ∂infiniteRademacherMeasure, ∃ j,omega j≠0 := by
  rw [ae_iff,no_negative_eq_zeroTail]
  exact measure_zeroTail 0

/-- On its full-measure domain the chosen index has the literal first-hit property. -/
theorem firstNegativeIndex_eq_iff {omega : InfiniteSample}
    (h : ∃ j,omega j≠0) (j : ℕ) :
    firstNegativeIndex omega=j ↔ omega∈firstNegativeEvent j := by
  rw [firstNegativeIndex,dif_pos h,Nat.find_eq_iff]
  simp only [firstNegativeEvent,Set.mem_setOf_eq,not_not]
  rw [bit_ne_zero_iff_eq_one]

/-- The exceptional default does not affect any first-prime probability. -/
theorem firstNegativeIndex_event_ae (j : ℕ) :
    {omega | firstNegativeIndex omega=j} =ᵐ[infiniteRademacherMeasure] firstNegativeEvent j := by
  filter_upwards [ae_exists_negative] with omega h
  exact propext (firstNegativeIndex_eq_iff h j)

theorem measure_firstNegativeIndex (j : ℕ) :
    infiniteRademacherMeasure {omega | firstNegativeIndex omega=j} =
      ((2 : ℝ≥0∞)⁻¹)^(j+1) := by
  rw [measure_congr (firstNegativeIndex_event_ae j),measure_firstNegativeEvent]

/-- Measurability includes the declared default on the exceptional set. -/
theorem measurable_firstNegativeIndex : Measurable firstNegativeIndex := by
  classical
  apply measurable_to_countable'
  intro j
  have heq : {omega | firstNegativeIndex omega=j} = firstNegativeEvent j ∪
      (if j=0 then zeroTail 0 else ∅) := by
    ext omega
    by_cases h : ∃ k,omega k≠0
    · have hnot : omega ∉ zeroTail 0 := by
        rw [← no_negative_eq_zeroTail]
        exact not_not.mpr h
      simp only [Set.mem_union,Set.mem_setOf_eq]
      rw [firstNegativeIndex_eq_iff h]
      by_cases hj : j=0 <;> simp [hj,hnot]
    · have hz : omega∈zeroTail 0 := by simpa only [← no_negative_eq_zeroTail,Set.mem_setOf_eq] using h
      have hne : omega∉firstNegativeEvent j := by
        intro hh
        exact h ⟨j,(bit_ne_zero_iff_eq_one _).mpr hh.1⟩
      simp [firstNegativeIndex,h,hne,hz,eq_comm]
  change MeasurableSet {omega | firstNegativeIndex omega=j}
  rw [heq]
  apply (measurableSet_firstNegativeEvent j).union
  split_ifs
  · simp only [zeroTail,Set.setOf_forall]
    exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun (_ : 0≤k) =>
      (show MeasurableSet {omega : InfiniteSample | omega k=0} from
        (measurable_pi_apply k) (measurableSet_singleton 0))
  · exact MeasurableSet.empty

/-- Before the first negative prime, every observed prime coordinate is zero. -/
theorem coordinate_zero_before_first {omega : InfiniteSample}
    (h : ∃ j,omega j≠0) {k : ℕ} (hk : k<firstNegativeIndex omega) : omega k=0 := by
  exact ((firstNegativeIndex_eq_iff h _).mp rfl).2 k hk

theorem coordinate_first_negative {omega : InfiniteSample} (h : ∃ j,omega j≠0) :
    omega (firstNegativeIndex omega)=1 :=
  ((firstNegativeIndex_eq_iff h _).mp rfl).1

/-- The initial run event is exactly the first-prime survival event almost surely. -/
theorem borderEvent_iff_first_index {omega : InfiniteSample} (h : ∃ j,omega j≠0) (L : ℕ) :
    omega∈borderEvent L ↔ Nat.primeCounting L ≤ firstNegativeIndex omega := by
  rw [borderEvent_eq_zeroPrefix]
  simp only [zeroPrefix,zero_add,Set.mem_pi,Finset.mem_coe,Finset.mem_Ico,zero_le,
    true_and,Set.mem_singleton_iff]
  constructor
  · intro hall
    by_contra hlt
    have hz := hall (firstNegativeIndex omega) (by omega)
    have hn := coordinate_first_negative h
    exact zero_ne_one (hz.symm.trans hn)
  · intro hle k hk
    exact coordinate_zero_before_first h (hk.trans_le hle)

end
end PaperC.V282.PrimeClockEvents
