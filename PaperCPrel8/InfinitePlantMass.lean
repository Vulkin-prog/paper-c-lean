import PaperCPrel8.InfinitePlantPresence
import PaperCPrel8.RegularConfigurationAtoms

/-! # Exact arithmetic configuration masses for enumerated regular plants -/
namespace PaperC.Prel8.InfinitePlantMass
open Finset MeasureTheory ProbabilityTheory InfiniteRademacher
open ConditionalStartProbability V282.ExactMarkedModel V282.BulkMarkedTypes V282.BulkMarkedSource
open V282.SharpConditioning MicroscopicConditionalSpatial RoughKernelRegularity InfinitePlantPresence
noncomputable section
local instance : MeasurableSpace F₂ := ⊤

/-- Every labelled occurrence is retained in this sum, including multiplicity. -/
def enumeratedConfiguration {k : ℕ} (sites : Finset ℕ) (labels : Fin k → SpatialMarkedIndex sites) :
    SpatialMarkedConfig sites := ∑ i, Finsupp.single (labels i) 1

/-- Equality to a planted configuration implies every prescribed mark is present. -/
theorem equality_implies_presence {k : ℕ} (sites : Finset ℕ) (L : ℕ)
    (labels : Fin k → SpatialMarkedIndex sites) (w : InfiniteSample)
    (h : spatialMarkedSource sites L w=enumeratedConfiguration sites labels) :
    ∀ i, SignedExactMark (infiniteValueBit w) (labels i).1.val L (labels i).2.1 (labels i).2.2 := by
  intro i
  apply (spatialMarkedValue_ne_zero_iff sites L w (labels i)).mp
  change spatialMarkedSource sites L w (labels i)≠0
  rw [h]
  apply Nat.ne_of_gt
  simp only [enumeratedConfiguration,Finsupp.finsetSum_apply]
  exact Finset.sum_pos' (fun _ _ ↦ Nat.zero_le _) ⟨i,mem_univ _,by simp⟩

/-- Distinct-site regularity follows from the actual private-prime predicate. -/
theorem regular_sites_injective {k Q Y : ℕ} (j : Fin k → ℕ) (hr : Regular Q Y j) :
    Function.Injective j := by
  intro i l he
  by_contra hil
  obtain ⟨p,hp,hprivate⟩ := hr i ⟨0,by omega⟩
  have hd := Nat.dvd_of_mem_primeFactors (LargeOddKernel.largeOddPrimeSupport_subset_primeFactors _ _ hp)
  apply hprivate l ⟨0,by omega⟩ (Or.inl (Ne.symm hil))
  simpa only [he] using hd

/-- Exact source mass equals the proved presence product times the actual Palm
void probability, on the original infinite arithmetic probability space. -/
theorem arithmetic_mass {C k L E Y : ℕ} (sites : Finset ℕ) (hL : 1≤L)
    (labels : Fin k → SpatialMarkedIndex sites)
    (hj : ∀ i, 2≤(labels i).1.val) (he : ∀ i, (labels i).2.1≤E)
    (hC : ∀ i, (labels i).1.val-1+(L+E+1)≤C)
    (hr : Regular (L+E+1) Y (fun i ↦ (labels i).1.val-1))
    (A : SmallSample C Y → Prop) (hA : 0 < infiniteRademacherMeasure.real (traceEvent C Y A)) :
    (cond infiniteRademacherMeasure (traceEvent C Y A)).real
      {w | spatialMarkedSource sites L w=enumeratedConfiguration sites labels} =
    (∏ i, (signedMarkRate L (labels i).2.1:ℝ)) *
      (cond (cond infiniteRademacherMeasure (traceEvent C Y A))
        (occurrence L (fun i ↦ (labels i).1.val-1) (fun i ↦ (labels i).2.1) (fun i ↦ (labels i).2.2))).real
          {w | spatialMarkedSource sites L w=enumeratedConfiguration sites labels} := by
  let j := fun i ↦ (labels i).1.val-1
  let e := fun i ↦ (labels i).2.1
  let s := fun i ↦ (labels i).2.2
  let mu := cond infiniteRademacherMeasure (traceEvent C Y A)
  have hpresence := conditional_presence hL j e s (fun i ↦ by have := hj i; dsimp [j]; omega)
    he hC hr A hA
  have hpos : 0<∏ i, (signedMarkRate L (labels i).2.1:ℝ) := by
    apply prod_pos
    intro i hi
    change 0<1/(2:ℝ)^_
    positivity
  have himp : {w | spatialMarkedSource sites L w=enumeratedConfiguration sites labels} ⊆ occurrence L j e s := by
    intro w hw i
    have hx := equality_implies_presence sites L labels w hw i
    have heq : j i+1=(labels i).1.val := by dsimp [j]; have := hj i; omega
    simpa only [heq] using hx
  have hvoid := cond_real_apply mu (occurrence L j e s) (measurableSet_occurrence L j e s)
    {w | spatialMarkedSource sites L w=enumeratedConfiguration sites labels}
  rw [Set.inter_eq_right.mpr himp,hpresence] at hvoid
  exact (eq_div_iff hpos.ne').mp hvoid |>.symm.trans (mul_comm _ _)

end
end PaperC.Prel8.InfinitePlantMass
