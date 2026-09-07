import PaperCV282.MaximalCouplingMass
import PaperCV282.InfiniteMassCoupling
import Mathlib.Probability.ProbabilityMassFunction.Basic

/-! # A genuine maximal coupling on the countable product probability space -/
namespace PaperC.V282.MaximalCouplingMeasure

open MeasureTheory ProbabilityTheory FiniteFieldTotalVariation MaximalCouplingMass InfiniteMassCoupling

noncomputable section

variable {α : Type*}

/-- Convert a real probability mass into mathlib's probability mass function. -/
def probabilityMass (p : α → ℝ) (hp : HasSum p 1) (hp0 : ∀ x,0≤p x) : PMF α :=
  ⟨fun x => ENNReal.ofReal (p x), by
    have hs := (ENNReal.summable (f := fun x => ENNReal.ofReal (p x))).hasSum
    rw [← ENNReal.ofReal_tsum_of_nonneg hp0 hp.summable,hp.tsum_eq,ENNReal.ofReal_one] at hs
    exact hs⟩

@[reducible]
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

/-- Every atom of the constructed probability measure is the original real mass. -/
theorem observableLaw_probabilityMass [MeasurableSpace α] [MeasurableSingletonClass α] (p : α → ℝ) (hp : HasSum p 1) (hp0 : ∀ x,0≤p x) :
    observableLaw (probabilityMass p hp hp0).toMeasure id=p := by
  funext x
  change ((probabilityMass p hp hp0).toMeasure {x}).toReal=p x
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton x)]
  exact ENNReal.toReal_ofReal (hp0 x)

/-- An arbitrary event has precisely the sum of the constructed masses on that event. -/
theorem probabilityMass_event [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α] (p : α → ℝ) (hp : HasSum p 1) (hp0 : ∀ x,0≤p x) (A : Set α) :
    (probabilityMass p hp hp0).toMeasure.real A=(∑' x,if x∈A then p x else 0) := by
  classical
  have h := restricted_observableLaw_eq_event (probabilityMass p hp hp0).toMeasure measurable_id A
  rw [observableLaw_probabilityMass] at h
  exact h.symm

theorem couplingMass_first_fiber {p q : α → ℝ} (hp : HasSum p 1) (hq : HasSum q 1)
    (hp0 : ∀ x,0≤p x) (hq0 : ∀ x,0≤q x) (x : α) :
    (∑' z : α × α,if z.1=x then couplingMass p q z else 0)=p x := by
  classical
  have hs := summable_restricted_mass (hasSum_couplingMass hp hq hp0 hq0).summable
    (couplingMass_nonneg hp0 hq0) {z : α × α | z.1=x}
  simp only [Set.mem_setOf_eq] at hs
  calc
    _ = ∑' a : α,∑' b : α,if a=x then couplingMass p q (a,b) else 0 := hs.tsum_prod
    _ = ∑' a : α,if a=x then ∑' b : α,couplingMass p q (a,b) else 0 := by
      apply tsum_congr
      intro a
      by_cases ha : a=x <;> simp [ha]
    _ = _ := by simp [(hasSum_couplingMass_row hp hq hp0 hq0 x).tsum_eq]

theorem couplingMass_second_fiber {p q : α → ℝ} (hp : HasSum p 1) (hq : HasSum q 1)
    (hp0 : ∀ x,0≤p x) (hq0 : ∀ x,0≤q x) (y : α) :
    (∑' z : α × α,if z.2=y then couplingMass p q z else 0)=q y := by
  classical
  have hs := summable_restricted_mass (hasSum_couplingMass hp hq hp0 hq0).summable
    (couplingMass_nonneg hp0 hq0) {z : α × α | z.2=y}
  simp only [Set.mem_setOf_eq] at hs
  calc
    _ = ∑' a : α,∑' b : α,if b=y then couplingMass p q (a,b) else 0 := hs.tsum_prod
    _ = ∑' a : α,couplingMass p q (a,y) := by simp only [tsum_ite_eq]
    _ = _ := (hasSum_couplingMass_column hp hq hp0 hq0 y).tsum_eq

theorem couplingMass_diagonal_sum {p q : α → ℝ} (hp : HasSum p 1) (hq : HasSum q 1)
    (hp0 : ∀ x,0≤p x) (hq0 : ∀ x,0≤q x) :
    (∑' z : α × α,if z.1=z.2 then couplingMass p q z else 0)=∑' x,overlap p q x := by
  classical
  have hs := summable_restricted_mass (hasSum_couplingMass hp hq hp0 hq0).summable
    (couplingMass_nonneg hp0 hq0) {z : α × α | z.1=z.2}
  simp only [Set.mem_setOf_eq] at hs
  calc
    _ = ∑' a : α,∑' b : α,if a=b then couplingMass p q (a,b) else 0 := hs.tsum_prod
    _ = _ := by
      apply tsum_congr
      intro x
      simp only [tsum_ite_eq',couplingMass_diagonal]

/-- Existence on the literal product space, with exact marginals and optimal disagreement probability. -/
theorem exists_maximal_coupling [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α] (p q : α → ℝ) (hp : HasSum p 1) (hq : HasSum q 1)
    (hp0 : ∀ x,0≤p x) (hq0 : ∀ x,0≤q x) :
    ∃ mu : Measure (α × α), IsProbabilityMeasure mu ∧
      observableLaw mu Prod.fst=p ∧ observableLaw mu Prod.snd=q ∧
      mu.real {z | z.1≠z.2}=massTotalVariation p q := by
  classical
  let pmf := probabilityMass (couplingMass p q) (hasSum_couplingMass hp hq hp0 hq0)
    (couplingMass_nonneg hp0 hq0)
  let mu := pmf.toMeasure
  letI instProbabilityCoupling : IsProbabilityMeasure mu := inferInstance
  have hevent (A : Set (α × α)) : mu.real A=∑' z,if z∈A then couplingMass p q z else 0 :=
    probabilityMass_event _ _ _ A
  have hfst : observableLaw mu Prod.fst=p := by
    funext x
    exact (hevent _).trans (couplingMass_first_fiber hp hq hp0 hq0 x)
  have hsnd : observableLaw mu Prod.snd=q := by
    funext y
    exact (hevent _).trans (couplingMass_second_fiber hp hq hp0 hq0 y)
  refine ⟨mu,inferInstance,hfst,hsnd,?_⟩
  have hdiag : mu.real {z : α × α | z.1=z.2}=∑' x,overlap p q x :=
    (hevent _).trans (couplingMass_diagonal_sum hp hq hp0 hq0)
  have hcomp := measureReal_compl (μ := mu) (s := {z : α × α | z.1=z.2})
    (Set.to_countable _).measurableSet
  rw [probReal_univ,hdiag] at hcomp
  rw [variation_eq_one_sub_overlap hp hq hp0 hq0]
  exact hcomp

end
end PaperC.V282.MaximalCouplingMeasure
