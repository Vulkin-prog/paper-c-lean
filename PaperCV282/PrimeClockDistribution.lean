import PaperCV282.PrimeClockEvents

/-! # The conditional geometric prime clock

The clock counts additional positive prime signs after the initial border.
Conditioning always uses the normalized restriction of the actual source law.
-/
namespace PaperC.V282.PrimeClockDistribution

open MeasureTheory ProbabilityTheory Set InfiniteRademacher MicroscopicBorderEvents PrimeClockEvents
open scoped ENNReal

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤
local instance instProbabilityInfinite : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

noncomputable section

/-- The paper's globally defined G_L: zero off the border event. -/
def primeOvershoot (L : ℕ) (omega : InfiniteSample) : ℕ := by
  classical
  exact if omega∈borderEvent L then firstNegativeIndex omega-Nat.primeCounting L else 0

/-- The overshoot is a genuine measurable source observable. -/
theorem measurable_primeOvershoot (L : ℕ) : Measurable (primeOvershoot L) := by
  classical
  exact Measurable.ite (measurableSet_borderEvent L)
    (measurable_firstNegativeIndex.sub_const _) measurable_const

/-- The first negative after pi(L)+k positives already entails the border. -/
theorem firstNegativeEvent_subset_border {L j : ℕ} (hj : Nat.primeCounting L≤j) :
    firstNegativeEvent j ⊆ borderEvent L := by
  intro omega h
  rw [borderEvent_eq_zeroPrefix]
  intro k hk
  have hkj : k<Nat.primeCounting L := by simpa only [zero_add] using (Finset.mem_Ico.mp hk).2
  exact h.2 k (hkj.trans_le hj)

/-- The true conditional clock fiber agrees almost surely with its finite cylinder. -/
theorem primeOvershoot_inter_border_ae (L k : ℕ) :
    (borderEvent L ∩ {omega | primeOvershoot L omega=k} : Set InfiniteSample) =ᵐ[infiniteRademacherMeasure]
      firstNegativeEvent (Nat.primeCounting L+k) := by
  classical
  filter_upwards [ae_exists_negative] with omega h
  apply propext
  constructor
  · rintro ⟨hb,hk⟩
    have hi := (borderEvent_iff_first_index h L).mp hb
    simp only [Set.mem_setOf_eq,primeOvershoot,if_pos hb] at hk
    exact (firstNegativeIndex_eq_iff h _).mp (by omega)
  · intro hfirst
    have hb := firstNegativeEvent_subset_border (L := L) (by omega) hfirst
    have hi := (firstNegativeIndex_eq_iff h _).mpr hfirst
    exact ⟨hb,by simp [primeOvershoot,hb,hi]⟩

/-- Exact conditional distribution in the first identity of (7.20). -/
theorem equation_seven_twenty_prime_rank (L k : ℕ) :
    (cond infiniteRademacherMeasure (borderEvent L)).real
      {omega | primeOvershoot L omega=k} = ((2 : ℝ)⁻¹)^(k+1) := by
  rw [measureReal_def,cond_apply (measurableSet_borderEvent L),
    measure_congr (primeOvershoot_inter_border_ae L k),measure_borderEvent,measure_firstNegativeEvent]
  simp only [ENNReal.toReal_mul,ENNReal.toReal_inv,ENNReal.toReal_pow,ENNReal.toReal_ofNat]
  rw [show Nat.primeCounting L+k+1=Nat.primeCounting L+(k+1) by omega,pow_add]
  field_simp

/-- The actual conditional law on the nonnegative prime-rank overshoot. -/
def conditionalPrimeClockLaw (L : ℕ) : Measure ℕ :=
  (cond infiniteRademacherMeasure (borderEvent L)).map (primeOvershoot L)

theorem conditionalPrimeClockLaw_probability (L : ℕ) :
    IsProbabilityMeasure (conditionalPrimeClockLaw L) := by
  letI instConditionalProbability : IsProbabilityMeasure
      (cond infiniteRademacherMeasure (borderEvent L)) :=
    cond_isProbabilityMeasure (by
      rw [measure_borderEvent]
      exact pow_ne_zero _ (ENNReal.inv_ne_zero.mpr (by norm_num)))
  exact Measure.isProbabilityMeasure_map (measurable_primeOvershoot L).aemeasurable

/-- Singleton masses identify the complete geometric law, not only its tail. -/
theorem conditionalPrimeClockLaw_singleton (L k : ℕ) :
    (conditionalPrimeClockLaw L).real {k} = ((2 : ℝ)⁻¹)^(k+1) := by
  rw [conditionalPrimeClockLaw,Measure.real,Measure.map_apply
    (measurable_primeOvershoot L) (measurableSet_singleton k)]
  exact equation_seven_twenty_prime_rank L k

end
end PaperC.V282.PrimeClockDistribution
