import PaperCV282.CrossoverPrimeClockBase
import PaperCV282.BulkMicroscopicRecord

/-! # The truncated prime clock is recorded in the full prime sigma algebra -/
namespace PaperC.V282.CrossoverPrimeClockCylinder

open MeasureTheory InfiniteRademacher InfiniteCylinderTransfer
open MicroscopicBorderEvents CrossoverPrimeClockBase

noncomputable section
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P
local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

/-- Read a prime-rank coordinate in a finite prime cylinder when it is available. -/
def finitePrimeBit (Y j : ℕ) (sigma : SampleSpace Y) : F₂ :=
  if h : Nat.nth Nat.Prime j ≤ Y then
    sigma ⟨⟨Nat.nth Nat.Prime j,Nat.lt_succ_of_le h⟩,Nat.prime_nth_prime j⟩ else 0

theorem finitePrimeBit_restrict {Y j : ℕ} (hj : j < Nat.primeCounting Y)
    (omega : InfiniteSample) : finitePrimeBit Y j (restrictToFinite Y omega) = omega j := by
  simp [finitePrimeBit,nth_prime_le_iff.mpr hj,restrictToFinite,finitePrimeCoordinate]

/-- This representative uses only actual finite prime signs. -/
def finiteClock (Y L K : ℕ) (sigma : SampleSpace Y) : ℕ :=
  if (∀ n : ℕ, 1 ≤ n → n ≤ L → valueBit sigma n = 0) then
    cappedIndex K (fun j => finitePrimeBit Y (Nat.primeCounting L+j) sigma) else 0

theorem finiteClock_restrict {Y L K : ℕ} (hLY : L ≤ Y)
    (hprimes : Nat.primeCounting L+K ≤ Nat.primeCounting Y) (omega : InfiniteSample) :
    finiteClock Y L K (restrictToFinite Y omega) = cappedPrimeClock L K omega := by
  have hb : (∀ n : ℕ, 1 ≤ n → n ≤ L → valueBit (restrictToFinite Y omega) n = 0) ↔
      omega ∈ borderEvent L := by
    constructor <;> intro h n hn hnL
    · rw [← valueBit_restrictToFinite_eq_infiniteValueBit omega (hnL.trans hLY)]
      exact h n hn hnL
    · rw [valueBit_restrictToFinite_eq_infiniteValueBit omega (hnL.trans hLY)]
      exact h n hn hnL
  simp only [finiteClock,cappedPrimeClock,hb]
  split_ifs
  · apply cappedIndex_congr
    intro j hj
    exact finitePrimeBit_restrict (by omega) omega
  · rfl

/-- The measurability statement is for the finite representative, including null samples. -/
theorem measurable_cappedPrimeClock_fullFY {Y L K : ℕ} (hLY : L ≤ Y)
    (hprimes : Nat.primeCounting L+K ≤ Nat.primeCounting Y) :
    Measurable[MeasurableSpace.comap (restrictToFinite Y) inferInstance] (cappedPrimeClock L K) := by
  have h := (measurable_of_countable (finiteClock Y L K)).comp (comap_measurable (restrictToFinite Y))
  have he : finiteClock Y L K ∘ restrictToFinite Y = cappedPrimeClock L K :=
    funext (finiteClock_restrict hLY hprimes)
  rw [← he]
  exact h

theorem measurable_cappedPrimeClock (L K : ℕ) : Measurable (cappedPrimeClock L K) := by
  let Y := max L (Nat.nth Nat.Prime (Nat.primeCounting L+K))
  have hp : Nat.primeCounting L+K ≤ Nat.primeCounting Y := by
    exact (nth_prime_le_iff.mp (le_max_right _ _)).le
  have he : finiteClock Y L K ∘ restrictToFinite Y = cappedPrimeClock L K :=
    funext (finiteClock_restrict (le_max_left _ _) hp)
  rw [← he]
  exact (measurable_of_countable _).comp (measurable_pi_lambda _ fun p => measurable_pi_apply _)

/-- The border and the finite prime clock are retained together. -/
def borderClockRecord (L K : ℕ) (omega : InfiniteSample) : Bool × ℕ :=
  (if omega ∈ borderEvent L then true else false,cappedPrimeClock L K omega)

theorem measurable_borderClockRecord_fullFY {Y L K : ℕ} (hcut : 2*L^2+L ≤ Y)
    (hprimes : Nat.primeCounting L+K ≤ Nat.primeCounting Y) :
    Measurable[MeasurableSpace.comap (restrictToFinite Y) inferInstance] (borderClockRecord L K) := by
  have hb := (measurable_pi_apply 1).comp (BulkMicroscopicRecord.measurable_microscopicRecord_fullFY hcut)
  have he : (fun omega => MesoscopicStability.microscopicRecord L 0 omega 1) =
      (fun omega : InfiniteSample => if omega ∈ borderEvent L then true else false) := by
    funext omega
    simp only [MesoscopicStability.microscopicRecord,ite_true]
  change Measurable[MeasurableSpace.comap (restrictToFinite Y) inferInstance]
    (fun omega => MesoscopicStability.microscopicRecord L 0 omega 1) at hb
  rw [he] at hb
  exact hb.prodMk (measurable_cappedPrimeClock_fullFY (by omega) hprimes)

theorem measurable_borderClockRecord (L K : ℕ) : Measurable (borderClockRecord L K) := by
  exact (Measurable.ite (measurableSet_borderEvent L) measurable_const measurable_const).prodMk
    (measurable_cappedPrimeClock L K)

end
end PaperC.V282.CrossoverPrimeClockCylinder
