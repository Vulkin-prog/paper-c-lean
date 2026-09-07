import PaperC.Asymptotics.PrefixBoundaryProbability
import PaperCV282.PointwiseStartBounds

/-! # The exact microscopic border in the infinite model

The border event fixes the prime signs up to L. Interior starts before L
are impossible by complete multiplicativity, independently of the sample.
-/
namespace PaperC.V282.MicroscopicBorderEvents

open MeasureTheory Set InfiniteRademacher InfiniteCylinderTransfer
open InfiniteStartProbabilityTransfer PrefixBoundaryProbability
open scoped ENNReal

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

noncomputable section

/-- The actual initial positive run, including the vacuous length-zero case. -/
def borderEvent (L : ℕ) : Set InfiniteSample :=
  {omega | ∀ n : ℕ, 1 ≤ n → n ≤ L → infiniteValueBit omega n = 0}

/-- The value at one is deterministic in the source infinite model. -/
theorem infiniteValueBit_one (omega : InfiniteSample) : infiniteValueBit omega 1 = 0 := by
  simp [InfiniteRademacher.infiniteValueBit]

/-- This is precisely the historical event of equal initial values. -/
theorem borderEvent_eq_prefix (L : ℕ) :
    borderEvent L = infinitePrefixBoundaryEvent L := by
  ext omega
  constructor
  · intro h j hj
    rw [infiniteValueBit_one]
    exact h (1+j) (by omega) (by omega)
  · intro h n hn hnL
    have hh := h (n-1) (by omega)
    simpa [show 1+(n-1)=n by omega,infiniteValueBit_one] using hh

/-- Each border is a measurable source event. -/
theorem measurableSet_borderEvent (L : ℕ) : MeasurableSet (borderEvent L) := by
  rw [borderEvent_eq_prefix]
  exact measurableSet_infinitePrefixBoundaryEvent L

/-- Exact ENNReal version of equation (7.1). -/
theorem measure_borderEvent (L : ℕ) :
    infiniteRademacherMeasure (borderEvent L) = ((2 : ℝ≥0∞)⁻¹)^Nat.primeCounting L := by
  rw [borderEvent_eq_prefix]
  exact measure_infinitePrefixBoundaryEvent L

/-- Equation (7.1), with the actual probability of the initial run. -/
theorem equation_seven_one (L : ℕ) :
    infiniteRademacherMeasure.real (borderEvent L) = ((2 : ℝ)⁻¹)^Nat.primeCounting L := by
  rw [measureReal_def,measure_borderEvent]
  simp

/-- The initial run has positive mass for every finite L. -/
theorem borderEvent_probability_pos (L : ℕ) :
    0 < infiniteRademacherMeasure.real (borderEvent L) := by
  rw [equation_seven_one]
  positivity

/-- The index convention for the prime enumeration is zero based. -/
theorem nth_prime_le_iff {k L : ℕ} :
    Nat.nth Nat.Prime k ≤ L ↔ k < Nat.primeCounting L := by
  simpa [Nat.primeCounting,Nat.primeCounting'] using
    (Nat.lt_nth_iff_count_lt Nat.infinite_setOf_prime (a := k) (b := L+1)).symm

/-- The border fixes exactly the first pi(L) independent prime bits. -/
theorem borderEvent_eq_zeroPrefix (L : ℕ) :
    borderEvent L = zeroPrefix 0 (Nat.primeCounting L) := by
  ext omega
  rw [borderEvent_eq_prefix,infinitePrefixBoundaryEvent_eq_preimage,
    finitePrefixBoundaryEvent_eq_singleton_zero]
  simp only [Set.mem_preimage,Set.mem_singleton_iff,zeroPrefix,zero_add,
    Set.mem_pi,Finset.mem_coe,Finset.mem_Ico,zero_le,true_and,Set.mem_singleton_iff]
  constructor
  · intro h k hk
    let p : PrimeUpTo L := ⟨⟨Nat.nth Nat.Prime k,Nat.lt_succ_of_le (nth_prime_le_iff.mpr hk)⟩,
      Nat.prime_nth_prime k⟩
    have hh := congrFun h p
    simpa [restrictToFinite,finitePrimeCoordinate,p] using hh
  · intro h
    funext p
    have hp : Nat.primeCounting' p.1.1 < Nat.primeCounting L := by
      apply nth_prime_le_iff.mp
      simpa [Nat.primeCounting',Nat.nth_count p.2] using Nat.le_of_lt_succ p.1.2
    exact h (Nat.primeCounting' p.1.1) hp

/-- Borders are nested as the required length grows. -/
theorem borderEvent_mono {L K : ℕ} (hLK : L ≤ K) : borderEvent K ⊆ borderEvent L :=
  fun _ h n hn hnL => h n hn (hnL.trans hLK)

/-- The forbidden early-start range in article 7.1 and companion E.1. -/
theorem not_start_of_early {x L : ℕ} (hx : 2 ≤ x) (hxL : x ≤ L-1)
    (omega : InfiniteSample) : ¬ StartEvent (infiniteValueBit omega) x L := by
  intro h
  have htwo := h.eq_on_run (n := 2*x) (by omega) (by omega)
  rw [infiniteValueBit_mul omega (by omega : 2≠0) (by omega : x≠0)] at htwo
  have hg2 : infiniteValueBit omega 2 = 0 := by
    apply add_right_cancel (b := infiniteValueBit omega x)
    simpa using htwo
  have hleft := h.eq_on_run (n := 2*(x-1)) (by omega) (by omega)
  rw [infiniteValueBit_mul omega (by omega : 2≠0) (by omega : x-1≠0),hg2,zero_add] at hleft
  exact h.left_ne hleft

/-- No sample realizes an early interior start. -/
theorem forbidden_early_start {x L : ℕ} (hx : 2 ≤ x) (hxL : x ≤ L-1) :
    infiniteStartEvent x L = ∅ := by
  ext omega
  simp only [infiniteStartEvent,Set.mem_setOf_eq,Set.mem_empty_iff_false,iff_false]
  exact not_start_of_early hx hxL omega

/-- The early starts have exactly zero probability. -/
theorem early_start_probability_zero {x L : ℕ} (hx : 2 ≤ x) (hxL : x ≤ L-1) :
    infiniteStartProbability x L = 0 := by
  simp [infiniteStartProbability,forbidden_early_start hx hxL]

end
end PaperC.V282.MicroscopicBorderEvents
