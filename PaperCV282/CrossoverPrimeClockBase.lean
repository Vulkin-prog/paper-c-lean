import PaperCV282.PrimeClockDistribution

/-! # A finite representative of the truncated prime clock

The default on a sample with no negative prime must be kept separate from
the finite cylinder representative. The two clocks agree almost surely.
-/
namespace PaperC.V282.CrossoverPrimeClockBase

open MeasureTheory InfiniteRademacher PrimeClockEvents PrimeClockDistribution
open MicroscopicBorderEvents

noncomputable section
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P
local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

/-- First negative coordinate among the first K coordinates; K if none occurs. -/
def cappedIndex (K : ℕ) (bits : ℕ → F₂) : ℕ :=
  if h : ∃ j, j < K ∧ bits j ≠ 0 then Nat.find h else K

theorem cappedIndex_le (K : ℕ) (bits : ℕ → F₂) : cappedIndex K bits ≤ K := by
  unfold cappedIndex
  split_ifs with h
  · exact (Nat.find_spec h).1.le
  · exact le_rfl

theorem cappedIndex_congr {K : ℕ} {bits other : ℕ → F₂}
    (h : ∀ j < K, bits j = other j) : cappedIndex K bits = cappedIndex K other := by
  have hp : (fun j => j < K ∧ bits j ≠ 0) = (fun j => j < K ∧ other j ≠ 0) := by
    funext j
    apply propext
    by_cases hj : j < K
    · simp only [hj, true_and, h j hj]
    · simp only [hj, false_and]
  unfold cappedIndex
  simp only [hp]

theorem cappedIndex_eq_min {K t : ℕ} {bits : ℕ → F₂}
    (hbefore : ∀ j < t, bits j = 0) (hat : bits t ≠ 0) :
    cappedIndex K bits = min t K := by
  by_cases ht : t < K
  · have hex : ∃ j, j < K ∧ bits j ≠ 0 := ⟨t,ht,hat⟩
    rw [cappedIndex,dif_pos hex,min_eq_left ht.le]
    rw [Nat.find_eq_iff]
    exact ⟨⟨ht,hat⟩,fun j hj hbad => hbad.2 (hbefore j hj)⟩
  · have hn : ¬∃ j, j < K ∧ bits j ≠ 0 := by
      rintro ⟨j,hj,hb⟩
      exact hb (hbefore j (by omega))
    rw [cappedIndex,dif_neg hn,min_eq_right (by omega)]

/-- A pointwise finite cylinder, with the correct cap even on a zero tail. -/
def cappedPrimeClock (L K : ℕ) (omega : InfiniteSample) : ℕ :=
  if omega ∈ borderEvent L then
    cappedIndex K (fun j => omega (Nat.primeCounting L+j)) else 0

theorem cappedPrimeClock_le (L K : ℕ) (omega : InfiniteSample) :
    cappedPrimeClock L K omega ≤ K := by
  unfold cappedPrimeClock
  split_ifs
  · exact cappedIndex_le _ _
  · exact Nat.zero_le _

theorem cappedPrimeClock_eq_min {omega : InfiniteSample}
    (h : ∃ j, omega j ≠ 0) (L K : ℕ) :
    cappedPrimeClock L K omega = min (primeOvershoot L omega) K := by
  by_cases hb : omega ∈ borderEvent L
  · have hi := (borderEvent_iff_first_index h L).mp hb
    simp only [cappedPrimeClock,primeOvershoot,if_pos hb]
    apply cappedIndex_eq_min
    · intro j hj
      exact coordinate_zero_before_first h (by omega)
    · have hn := coordinate_first_negative h
      rw [show Nat.primeCounting L+(firstNegativeIndex omega-Nat.primeCounting L)=
        firstNegativeIndex omega by omega,hn]
      exact one_ne_zero
  · simp [cappedPrimeClock,primeOvershoot,hb]

theorem cappedPrimeClock_ae_eq_min (L K : ℕ) :
    cappedPrimeClock L K =ᵐ[infiniteRademacherMeasure]
      fun omega => min (primeOvershoot L omega) K := by
  filter_upwards [ae_exists_negative] with omega h
  exact cappedPrimeClock_eq_min h L K

end
end PaperC.V282.CrossoverPrimeClockBase
