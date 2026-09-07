import PaperCV282.AffineCrossoverFuture
import PaperCV282.CrossoverPrimeClockLaw
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-! # The genuine capped prime-clock law under an affine border condition

Neutrality is needed only for the first K future coordinates. The proof
identifies the entire capped law, rather than assuming a geometric law
from a single survival probability.
-/
namespace PaperC.V282.AffineCrossoverPrimeClock

open Affine MeasureTheory ProbabilityTheory InfiniteRademacher MicroscopicBorderEvents
open AffineBorderCylinders AffineBorderPrimeClock AffineCrossoverCylinder AffineCrossoverFuture
open PrimeClockDistribution CrossoverPrimeClockStable CrossoverPrimeClockLaw
open GeometricClusterTarget ConditionedCountableLaw

noncomputable section

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P
local instance instPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
local instance instProbabilityInfinite : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

/-- Finite survival data identify the entire capped law on the discrete count space. -/
theorem map_min_eq_of_survival (mu nu : Measure ℕ) [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (K : ℕ) (h : ∀ j ≤ K, mu.real (Set.Ici j) = nu.real (Set.Ici j)) :
    mu.map (fun n => min n K) = nu.map (fun n => min n K) := by
  apply Measure.ext_of_Ici
  intro j
  rw [Measure.map_apply (measurable_of_countable _) measurableSet_Ici,
    Measure.map_apply (measurable_of_countable _) measurableSet_Ici]
  by_cases hj : j ≤ K
  · have he : (fun n : ℕ => min n K) ⁻¹' Set.Ici j = Set.Ici j := by
      ext n
      simp [hj]
    rw [he]
    exact (measureReal_eq_measureReal_iff).mp (h j hj)
  · have he : (fun n : ℕ => min n K) ⁻¹' Set.Ici j = ∅ := by
      ext n
      simp [hj]
    simp [he]

variable {Y L K : ℕ} {W : Type*} [AddCommGroup W] [Module F₂ W]

/-- Every required shorter survival follows from neutrality of the K-coordinate space. -/
theorem affine_clock_survival_of_neutral (G : SampleSpace Y →ₗ[F₂] W) (b : W)
    (hLY : L ≤ Y) (hcut : Nat.nth Nat.Prime (Nat.primeCounting L+K) ≤ Y)
    (hstack : Compatible (G.prod (borderProjection hLY)) (b,0))
    (hneutral : FutureNeutral G hLY hcut) (j : ℕ) (hj : j ≤ K) :
    (cond infiniteRademacherMeasure (affineCylinder G b ∩ borderEvent L)).real
      {omega | j ≤ primeOvershoot L omega} = 1 / (2 : ℝ)^j := by
  exact geometric_prime_tail_of_zero_overlap hLY (future_cutoff_mono hcut hj) G b hstack
    ((futureNeutral_iff_overlap_zero G hLY _).mp (futureNeutral_mono G hLY hcut hj hneutral))

/-- The complete truncated clock has the standard geometric image law. -/
theorem conditional_capped_prime_clock (G : SampleSpace Y →ₗ[F₂] W) (b : W)
    (hLY : L ≤ Y) (hcut : Nat.nth Nat.Prime (Nat.primeCounting L+K) ≤ Y)
    (hstack : Compatible (G.prod (borderProjection hLY)) (b,0))
    (hneutral : FutureNeutral G hLY hcut) :
    (cond infiniteRademacherMeasure (affineCylinder G b ∩ borderEvent L)).map
      (fun omega => min (primeOvershoot L omega) K) =
      (geometricMeasure halfSuccess).map (fun n => min n K) := by
  let mu := cond infiniteRademacherMeasure (affineCylinder G b ∩ borderEvent L)
  letI instProbabilityAffineBorder : IsProbabilityMeasure mu :=
    cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _
      (affine_border_intersection_probability_pos G b hLY hstack))
  letI instProbabilityClock : IsProbabilityMeasure (mu.map (primeOvershoot L)) :=
    Measure.isProbabilityMeasure_map (measurable_primeOvershoot L).aemeasurable
  have h := map_min_eq_of_survival (mu.map (primeOvershoot L)) (geometricMeasure halfSuccess) K
    (fun j hj => by
      rw [map_measureReal_apply (measurable_primeOvershoot L) measurableSet_Ici]
      exact (affine_clock_survival_of_neutral G b hLY hcut hstack hneutral j hj).trans
        (geometric_survival j).symm)
  rw [Measure.map_map (measurable_of_countable _) (measurable_primeOvershoot L)] at h
  exact h

/-- The Bool coordinate is the actual border indicator and equals true under the condition. -/
theorem conditional_actualClockRecord (G : SampleSpace Y →ₗ[F₂] W) (b : W)
    (hLY : L ≤ Y) (hcut : Nat.nth Nat.Prime (Nat.primeCounting L+K) ≤ Y)
    (hstack : Compatible (G.prod (borderProjection hLY)) (b,0))
    (hneutral : FutureNeutral G hLY hcut) :
    (cond infiniteRademacherMeasure (affineCylinder G b ∩ borderEvent L)).map
      (actualClockRecord L K) =
      (geometricMeasure halfSuccess).map (fun n => (true,min n K)) := by
  have h := congrArg (fun mu : Measure ℕ => mu.map (fun n => (true,n)))
    (conditional_capped_prime_clock G b hLY hcut hstack hneutral)
  have hm : Measurable (fun omega : InfiniteSample => min (primeOvershoot L omega) K) :=
    (measurable_of_countable (fun n : ℕ => min n K)).comp (measurable_primeOvershoot L)
  rw [Measure.map_map (measurable_of_countable _) hm,
    Measure.map_map (measurable_of_countable _) (measurable_of_countable _)] at h
  refine Eq.trans ?_ h
  apply Measure.map_congr
  filter_upwards [ae_cond_mem (μ := infiniteRademacherMeasure)
    ((measurableSet_affineCylinder G b).inter (measurableSet_borderEvent L))] with omega homega
  simp [actualClockRecord, homega.2]

/-- The nested conditional measure used by the crossover engine is the same genuine law. -/
theorem nested_conditional_actualClockRecord (G : SampleSpace Y →ₗ[F₂] W) (b : W)
    (hLY : L ≤ Y) (hcut : Nat.nth Nat.Prime (Nat.primeCounting L+K) ≤ Y)
    (hstack : Compatible (G.prod (borderProjection hLY)) (b,0))
    (hneutral : FutureNeutral G hLY hcut) :
    (cond (cond infiniteRademacherMeasure (affineCylinder G b)) (borderEvent L)).map
      (actualClockRecord L K) =
      (geometricMeasure halfSuccess).map (fun n => (true,min n K)) := by
  rw [cond_cond_eq_cond_inter (measurableSet_affineCylinder G b) (measurableSet_borderEvent L)]
  exact conditional_actualClockRecord G b hLY hcut hstack hneutral

/-- Without neutrality the true future survival retains its affine compatibility test and rank. -/
theorem nested_affine_prime_tail_probability (G : SampleSpace Y →ₗ[F₂] W) (b : W)
    (hLY : L ≤ Y) (hcut : Nat.nth Nat.Prime (Nat.primeCounting L+K) ≤ Y) :
    (cond (cond infiniteRademacherMeasure (affineCylinder G b)) (borderEvent L)).real
      {omega | K ≤ primeOvershoot L omega} =
      if Compatible ((G.prod (borderProjection hLY)).prod (futurePrimeProjection hcut)) ((b,0),0)
      then 1 / (2 : ℝ)^(K-AffineBorderLinear.rowOverlap
        (G.prod (borderProjection hLY)) (futurePrimeProjection hcut)) else 0 := by
  rw [cond_cond_eq_cond_inter (measurableSet_affineCylinder G b) (measurableSet_borderEvent L)]
  exact affine_prime_tail_probability hLY hcut G b

end
end PaperC.V282.AffineCrossoverPrimeClock
