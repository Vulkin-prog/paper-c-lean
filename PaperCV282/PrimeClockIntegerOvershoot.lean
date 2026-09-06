import PaperCV282.PrimeClockDistribution

/-! # Initial-run length and the integer prime-clock overshoot

The length is exactly one less than the first negative prime, on the full
measure set where such a prime exists. The integer tail counts actual
primes in (L,L+h]; it is not replaced by a geometric integer clock.
-/
namespace PaperC.V282.PrimeClockIntegerOvershoot

open MeasureTheory ProbabilityTheory Set InfiniteRademacher MicroscopicBorderEvents
open PrimeClockEvents PrimeClockDistribution
open scoped ENNReal

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤
local instance instProbabilityInfinite : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

noncomputable section

/-- The maximal initial run length, with a harmless default on the null exceptional set. -/
def initialRunLength (omega : InfiniteSample) : ℕ :=
  Nat.nth Nat.Prime (firstNegativeIndex omega)-1

theorem measurable_initialRunLength : Measurable initialRunLength := by
  exact (measurable_from_nat (f := fun j => Nat.nth Nat.Prime j-1)).comp measurable_firstNegativeIndex

/-- Exact deterministic survival equivalence wherever the prime clock is finite. -/
theorem initialRunLength_ge_iff {omega : InfiniteSample} (h : ∃ j,omega j≠0) (n : ℕ) :
    n≤ initialRunLength omega ↔ omega∈borderEvent n := by
  rw [borderEvent_iff_first_index h n]
  have hp := Nat.add_two_le_nth_prime (firstNegativeIndex omega)
  have hcount := nth_prime_le_iff (k := firstNegativeIndex omega) (L := n)
  unfold initialRunLength
  omega

/-- Every preceding integer is positive, while the next prime value is negative. -/
theorem initialRunLength_exact {omega : InfiniteSample} (h : ∃ j,omega j≠0) :
    (∀ n : ℕ,1≤n → n≤ initialRunLength omega → infiniteValueBit omega n=0) ∧
      infiniteValueBit omega (initialRunLength omega+1)=1 := by
  constructor
  · exact (initialRunLength_ge_iff h _).mp le_rfl
  · have hp := Nat.add_two_le_nth_prime (firstNegativeIndex omega)
    rw [show initialRunLength omega+1=Nat.nth Nat.Prime (firstNegativeIndex omega) by
      unfold initialRunLength;omega,infiniteValueBit_nth_prime]
    exact coordinate_first_negative h

/-- The complete initial-run tail has the exact prime-counting mass. -/
theorem initialRunLength_tail_probability (n : ℕ) :
    infiniteRademacherMeasure.real {omega | n≤ initialRunLength omega} =
      ((2 : ℝ)⁻¹)^Nat.primeCounting n := by
  have heq : {omega | n≤ initialRunLength omega} =ᵐ[infiniteRademacherMeasure] borderEvent n := by
    filter_upwards [ae_exists_negative] with omega h
    exact propext (initialRunLength_ge_iff h n)
  rw [Measure.real,measure_congr heq]
  exact equation_seven_one n

/-- On the border, subtraction of L is honest integer subtraction. -/
theorem overshoot_inter_border_ae (L h : ℕ) :
    (borderEvent L ∩ {omega | h≤ initialRunLength omega-L} : Set InfiniteSample) =ᵐ[infiniteRademacherMeasure]
      borderEvent (L+h) := by
  filter_upwards [ae_exists_negative] with omega hex
  apply propext
  constructor
  · rintro ⟨hb,ht⟩
    change h ≤ initialRunLength omega-L at ht
    have hL := (initialRunLength_ge_iff hex L).mpr hb
    exact (initialRunLength_ge_iff hex (L+h)).mp (by omega)
  · intro hb
    have hLh := (initialRunLength_ge_iff hex (L+h)).mpr hb
    exact ⟨(initialRunLength_ge_iff hex L).mp (by omega),by change h≤ initialRunLength omega-L;omega⟩

/-- Second exact identity of article (7.20) and companion E.6. -/
theorem equation_seven_twenty_integer_tail (L h : ℕ) :
    (cond infiniteRademacherMeasure (borderEvent L)).real
      {omega | h≤ initialRunLength omega-L} =
        ((2 : ℝ)⁻¹)^(Nat.primeCounting (L+h)-Nat.primeCounting L) := by
  rw [Measure.real,cond_apply (measurableSet_borderEvent L),
    measure_congr (overshoot_inter_border_ae L h),measure_borderEvent,measure_borderEvent]
  simp only [ENNReal.toReal_mul,ENNReal.toReal_inv,ENNReal.toReal_pow,ENNReal.toReal_ofNat]
  have hmono := Nat.monotone_primeCounting (show L≤L+h by omega)
  rw [show Nat.primeCounting (L+h)=Nat.primeCounting L+
    (Nat.primeCounting (L+h)-Nat.primeCounting L) by omega,pow_add]
  field_simp
  congr 1
  omega

/-- An actual prime-free interval forces the corresponding integer overshoot. -/
theorem conditional_overshoot_one_of_primeCounting_eq {L h : ℕ}
    (heq : Nat.primeCounting (L+h)=Nat.primeCounting L) :
    (cond infiniteRademacherMeasure (borderEvent L)).real
      {omega | h≤ initialRunLength omega-L} = 1 := by
  rw [equation_seven_twenty_integer_tail,heq,Nat.sub_self,pow_zero]

end
end PaperC.V282.PrimeClockIntegerOvershoot
