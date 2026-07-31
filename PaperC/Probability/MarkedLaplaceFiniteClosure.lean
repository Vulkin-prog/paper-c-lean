import PaperC.Analysis.SpatialMarkedParameters
import PaperC.Probability.ConditionalExpectationAverage
import PaperC.Probability.InfiniteExactLengthProbabilityTransfer
import PaperC.Probability.InfiniteLaplaceTransfer
import PaperC.Probability.LaplaceVoidClosure
import PaperC.Probability.MarkedSteinChenTerms
import PaperC.Probability.SectionThirteenCouplings

set_option maxHeartbeats 1800000

/-!
# Finite marked Laplace closure

This module carries out the finite part of §14.4.  For a fixed mark cutoff
`E`, it compares the complete marked Laplace functional with the family
obtained after removing `D(Q)`, where `Q = L+E+1`.

The retained family has the exact conditional dependency graph from
`MarkedConditionalDependencyGraph`.  Independent exponential thinning and
Arratia--Goldstein--Gordon therefore give a conditional Laplace estimate.
The estimate is then averaged exactly over the small-prime assignment.

The two deterministic comparison terms are kept separate:

* the functional comparison is bounded by the complete removed
  exact-length probability mass from Lemma 14.8;
* the Poisson-parameter comparison is bounded by
  `(E+1) 2^E · #D(Q)/2^Q`.

Everything in this file is finite and exact.
-/

namespace PaperC
namespace MarkedLaplaceFiniteClosure

open scoped BigOperators

open ArratiaGoldsteinGordonInput
open ConditionalAGGAverage
open ConditionalAGGInstantiation
open ConditionalExpectationAverage
open ConditionalStartProbability
open ExactLengthBadStartMass
open IndependentThinning
open InfiniteCylinderTransfer
open InfiniteExactLengthProbabilityTransfer
open InfiniteLaplaceTransfer
open LaplaceVoidClosure
open MarkedConditionalDependencyGraph
open MarkedSteinChenTerms
open MeasureTheory
open MixedLengthAffine
open SectionThirteenFiniteBound
open SpatialMarkedParameters
open SpatialThinningFinite

noncomputable section

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

local instance (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- Absolute value of a uniform average after centering by a constant. -/
private theorem abs_finiteUniformAverage_sub_const_le
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (A : ι → ℝ) (c : ℝ) :
    |finiteUniformAverage A - c| ≤
      finiteUniformAverage (fun i ↦ |A i - c|) := by
  have hcard : (0 : ℝ) < Fintype.card ι := by
    positivity
  have hcenter :
      finiteUniformAverage A - c =
        (∑ i, (A i - c)) / (Fintype.card ι : ℝ) := by
    unfold finiteUniformAverage
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    field_simp
    rw [Finset.card_univ]
    ring
  rw [hcenter]
  unfold finiteUniformAverage
  rw [abs_div, abs_of_pos hcard]
  exact
    div_le_div_of_nonneg_right
      (Finset.abs_sum_le_sum_abs _ _) hcard.le

/-! ## Retained finite functional and parameter -/

/-- Test value attached to a retained marked index. -/
def retainedMarkedTest
    {N L E : ℕ} (g : ℝ → ℕ → ℝ)
    (α : MarkedIndex N L E) : ℝ :=
  g ((α.1.1 : ℝ) / (N : ℝ)) α.2.1

/-- Complete-cylinder Laplace functional restricted to retained starts. -/
def retainedMarkedLaplaceFunctional
    (N L E : ℕ) (g : ℝ → ℕ → ℝ)
    (ω : SampleSpace (markedCylinderCutoff N L E)) : ℝ :=
  Real.exp
    (-(∑ x ∈ retainedMarkedStarts N L E,
      ∑ e ∈ Finset.range (E + 1),
        if exactLengthAt ω x (excessRowCount L e) then
          g ((x : ℝ) / (N : ℝ)) e
        else 0))

/--
The Poisson parameter of the retained, exponentially thinned marked family.
-/
def retainedMarkedThinnedParameter
    (N L E : ℕ) (g : ℝ → ℕ → ℝ) : ℝ :=
  ∑ x ∈ retainedMarkedStarts N L E,
    ∑ e ∈ Finset.range (E + 1),
      spatialRetention (fun t ↦ g t e)
          ((x : ℝ) / (N : ℝ)) /
        (2 : ℝ) ^ excessRowCount L e

/-- Number of removed marked occurrences in one cylinder configuration. -/
def removedMarkedActiveCount
    (N L E : ℕ)
    (ω : SampleSpace (markedCylinderCutoff N L E)) : ℕ :=
  ∑ e ∈ Finset.range (E + 1),
    ∑ x ∈ removedExactLengthStarts N L E,
      if exactLengthAt ω x (excessRowCount L e) then 1 else 0

/--
The abstract exponential functional of the conditioned marked family is
literally the retained complete-cylinder functional after assembly.
-/
theorem exponentialFunctional_conditionedMarkedIndicator_eq_retained
    (N L E : ℕ) (g : ℝ → ℕ → ℝ)
    (σ : SmallSample (markedCylinderCutoff N L E) (markedPrimeCutoff L E))
    (η : LargeSample (markedCylinderCutoff N L E) (markedPrimeCutoff L E)) :
    exponentialFunctional
        (retainedMarkedTest g)
        (conditionedMarkedIndicator N L E σ) η =
      retainedMarkedLaplaceFunctional N L E g
        (assemble (markedCylinderCutoff N L E)
          (markedPrimeCutoff L E) σ η) := by
  classical
  unfold exponentialFunctional retainedMarkedLaplaceFunctional
    retainedMarkedTest
  congr 2
  rw [Fintype.sum_prod_type]
  calc
    (∑ x : {x : ℕ // x ∈ retainedMarkedStarts N L E},
        ∑ e : Fin (E + 1),
          if conditionedMarkedIndicator N L E σ (x, e) η = true then
            g ((x.1 : ℝ) / (N : ℝ)) e.1
          else 0) =
        ∑ x : {x : ℕ // x ∈ retainedMarkedStarts N L E},
          ∑ e ∈ Finset.range (E + 1),
            if exactLengthAt
                (assemble (markedCylinderCutoff N L E)
                  (markedPrimeCutoff L E) σ η)
                x.1 (excessRowCount L e) then
              g ((x.1 : ℝ) / (N : ℝ)) e
            else 0 := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro e he
      have he' : e < E + 1 := Finset.mem_range.mp he
      simp [conditionedMarkedIndicator_eq_true_iff,
        markedRowCount, he']
    _ =
        ∑ x ∈ retainedMarkedStarts N L E,
          ∑ e ∈ Finset.range (E + 1),
            if exactLengthAt
                (assemble (markedCylinderCutoff N L E)
                  (markedPrimeCutoff L E) σ η)
                x (excessRowCount L e) then
              g ((x : ℝ) / (N : ℝ)) e
            else 0 := by
      exact
        Finset.sum_subtype
          (retainedMarkedStarts N L E) (fun _ ↦ Iff.rfl)
          (fun x ↦
            ∑ e ∈ Finset.range (E + 1),
              if exactLengthAt
                  (assemble (markedCylinderCutoff N L E)
                    (markedPrimeCutoff L E) σ η)
                  x (excessRowCount L e) then
                g ((x : ℝ) / (N : ℝ)) e
              else 0) |>.symm

/--
The conditional thinned Poisson parameter is independent of the small-prime
assignment and equals the retained parameter.
-/
theorem conditionedMarked_thinnedParameter_eq_retained
    {N L E : ℕ} (hN : 2 ≤ N) (hL : 1 ≤ L)
    (g : ℝ → ℕ → ℝ)
    (σ : SmallSample (markedCylinderCutoff N L E) (markedPrimeCutoff L E)) :
    (∑ α : MarkedIndex N L E,
        marginal
            (largeUniformPMF
              (markedCylinderCutoff N L E) (markedPrimeCutoff L E))
            (conditionedMarkedIndicator N L E σ) α *
          exponentialRetention (retainedMarkedTest g) α) =
      retainedMarkedThinnedParameter N L E g := by
  classical
  simp_rw [marginal_conditionedMarkedIndicator_eq_baseline hN hL σ]
  unfold retainedMarkedThinnedParameter retainedMarkedTest
    exponentialRetention spatialRetention
  rw [Fintype.sum_prod_type]
  calc
    (∑ x : {x : ℕ // x ∈ retainedMarkedStarts N L E},
        ∑ e : Fin (E + 1),
          (1 / (2 : ℝ) ^ markedRowCount (x, e)) *
            (1 - Real.exp
              (-g ((x.1 : ℝ) / (N : ℝ)) e.1))) =
        ∑ x : {x : ℕ // x ∈ retainedMarkedStarts N L E},
          ∑ e ∈ Finset.range (E + 1),
            (1 - Real.exp
              (-g ((x.1 : ℝ) / (N : ℝ)) e)) /
              (2 : ℝ) ^ excessRowCount L e := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro e he
      have he' : e < E + 1 := Finset.mem_range.mp he
      rw [dif_pos he']
      simp only [markedRowCount]
      ring
    _ =
        ∑ x ∈ retainedMarkedStarts N L E,
          ∑ e ∈ Finset.range (E + 1),
            (1 - Real.exp
              (-g ((x : ℝ) / (N : ℝ)) e)) /
              (2 : ℝ) ^ excessRowCount L e := by
      exact
        Finset.sum_subtype
          (retainedMarkedStarts N L E) (fun _ ↦ Iff.rfl)
          (fun x ↦
            ∑ e ∈ Finset.range (E + 1),
              (1 - Real.exp
                (-g ((x : ℝ) / (N : ℝ)) e)) /
                (2 : ℝ) ^ excessRowCount L e) |>.symm

/-! ## Conditional AGG closure and exact averaging -/

/--
Pointwise conditional Laplace estimate for the retained marked family.
-/
theorem conditionalRetainedMarkedLaplace_le
    (hAGG : ArratiaGoldsteinGordonStatement)
    {N L E : ℕ} (hN : 2 ≤ N) (hL : 1 ≤ L)
    (g : ℝ → ℕ → ℝ) (hg : ∀ t e, 0 ≤ g t e)
    (σ : SmallSample (markedCylinderCutoff N L E) (markedPrimeCutoff L E)) :
    |finitePMFExpectation
        (largeUniformPMF
          (markedCylinderCutoff N L E) (markedPrimeCutoff L E))
        (fun η ↦
          retainedMarkedLaplaceFunctional N L E g
            (assemble (markedCylinderCutoff N L E)
              (markedPrimeCutoff L E) σ η)) -
      Real.exp (-retainedMarkedThinnedParameter N L E g)| ≤
      4 *
        (bOne
            (largeUniformPMF
              (markedCylinderCutoff N L E) (markedPrimeCutoff L E))
            (conditionedMarkedIndicator N L E σ)
            (markedDependencyGraph N L E) +
          bTwo
            (largeUniformPMF
              (markedCylinderCutoff N L E) (markedPrimeCutoff L E))
            (conditionedMarkedIndicator N L E σ)
            (markedDependencyGraph N L E)) := by
  have hfinite :=
    abs_exponentialFunctional_sub_exp_neg_parameter_le_of_dependency
      hAGG
      (largeUniformPMF
        (markedCylinderCutoff N L E) (markedPrimeCutoff L E))
      (conditionedMarkedIndicator N L E σ)
      (markedDependencyGraph N L E)
      (retainedMarkedTest g)
      (fun α ↦ hg ((α.1.1 : ℝ) / (N : ℝ)) α.2.1)
      (hasExactDependencyGraph_conditionedMarkedIndicator hL σ)
  rw [conditionedMarked_thinnedParameter_eq_retained hN hL g σ] at hfinite
  simpa only [finitePMFExpectation,
    exponentialFunctional_conditionedMarkedIndicator_eq_retained] using
      hfinite

/--
After exact averaging over small primes, the retained functional is within
`4(b₁+b₂)` of its matching Poisson exponential.
-/
theorem averagedRetainedMarkedLaplace_le
    (hAGG : ArratiaGoldsteinGordonStatement)
    {N L E : ℕ} (hN : 2 ≤ N) (hL : 1 ≤ L)
    (g : ℝ → ℕ → ℝ) (hg : ∀ t e, 0 ≤ g t e) :
    |finitePMFExpectation
        (FinitePMF.uniform
          (SampleSpace (markedCylinderCutoff N L E)))
        (retainedMarkedLaplaceFunctional N L E g) -
      Real.exp (-retainedMarkedThinnedParameter N L E g)| ≤
      4 *
        (((markedBOneFinite N L E : ℚ) : ℝ) +
          ((markedBTwoAverage N L E : ℚ) : ℝ)) := by
  let A :=
    fun σ :
        SmallSample
          (markedCylinderCutoff N L E) (markedPrimeCutoff L E) ↦
      finitePMFExpectation
        (largeUniformPMF
          (markedCylinderCutoff N L E) (markedPrimeCutoff L E))
        (fun η ↦
          retainedMarkedLaplaceFunctional N L E g
            (assemble (markedCylinderCutoff N L E)
              (markedPrimeCutoff L E) σ η))
  let c := Real.exp (-retainedMarkedThinnedParameter N L E g)
  have hpoint :
      ∀ σ :
          SmallSample
            (markedCylinderCutoff N L E) (markedPrimeCutoff L E),
        |A σ - c| ≤
          4 *
            (bOne
                (largeUniformPMF
                  (markedCylinderCutoff N L E) (markedPrimeCutoff L E))
                (conditionedMarkedIndicator N L E σ)
                (markedDependencyGraph N L E) +
              bTwo
                (largeUniformPMF
                  (markedCylinderCutoff N L E) (markedPrimeCutoff L E))
                (conditionedMarkedIndicator N L E σ)
                (markedDependencyGraph N L E)) := by
    intro σ
    exact conditionalRetainedMarkedLaplace_le
      hAGG hN hL g hg σ
  have havgA :
      finiteUniformAverage A =
        finitePMFExpectation
          (FinitePMF.uniform
            (SampleSpace (markedCylinderCutoff N L E)))
          (retainedMarkedLaplaceFunctional N L E g) := by
    exact
      finiteUniformAverage_largePMFExpectation_eq_full
        (markedCylinderCutoff N L E) (markedPrimeCutoff L E)
        (retainedMarkedLaplaceFunctional N L E g)
  have hc :
      finiteUniformAverage (fun _ :
          SmallSample
            (markedCylinderCutoff N L E) (markedPrimeCutoff L E) ↦ c) = c := by
    unfold finiteUniformAverage
    simp
  calc
    |finitePMFExpectation
        (FinitePMF.uniform
          (SampleSpace (markedCylinderCutoff N L E)))
        (retainedMarkedLaplaceFunctional N L E g) - c| =
        |finiteUniformAverage A - c| := by rw [havgA]
    _ ≤ finiteUniformAverage (fun σ ↦ |A σ - c|) :=
      abs_finiteUniformAverage_sub_const_le A c
    _ ≤
        finiteUniformAverage
          (fun σ ↦
            4 *
              (bOne
                  (largeUniformPMF
                    (markedCylinderCutoff N L E) (markedPrimeCutoff L E))
                  (conditionedMarkedIndicator N L E σ)
                  (markedDependencyGraph N L E) +
                bTwo
                  (largeUniformPMF
                    (markedCylinderCutoff N L E) (markedPrimeCutoff L E))
                  (conditionedMarkedIndicator N L E σ)
                  (markedDependencyGraph N L E))) :=
      finiteUniformAverage_mono hpoint
    _ =
        4 *
          (conditionalMarkedBOneAverage N L E +
            conditionalMarkedBTwoAverage N L E) := by
      unfold conditionalMarkedBOneAverage conditionalMarkedBTwoAverage
      unfold finiteUniformAverage
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
      ring
    _ =
        4 *
          (((markedBOneFinite N L E : ℚ) : ℝ) +
            ((markedBTwoAverage N L E : ℚ) : ℝ)) := by
      rw [conditionalMarkedBOneAverage_eq hN hL,
        conditionalMarkedBTwoAverage_eq]

/-! ## Removing `D(Q)`: comparison of the functionals -/

theorem removedExactLengthStarts_subset_dyadicBlock
    (N L E : ℕ) :
    removedExactLengthStarts N L E ⊆ dyadicBlock N := by
  intro x hx
  exact (BadStartCount.mem_terminalBadStarts.mp hx).1

theorem retainedMarkedStarts_eq_sdiff
    (N L E : ℕ) :
    retainedMarkedStarts N L E =
      dyadicBlock N \ removedExactLengthStarts N L E := by
  ext x
  simp only [mem_retainedMarkedStarts, Finset.mem_sdiff]

/--
If no removed exact-length event occurs, the complete and retained
functionals coincide pointwise.
-/
theorem finiteMarkedLaplaceFunctional_eq_retained_of_no_removed
    {N L E : ℕ} (g : ℝ → ℕ → ℝ)
    (ω : SampleSpace (markedCylinderCutoff N L E))
    (hno :
      ¬∃ e ∈ Finset.range (E + 1),
        ∃ x ∈ removedExactLengthStarts N L E,
          exactLengthAt ω x (excessRowCount L e)) :
    finiteMarkedLaplaceFunctional
        (markedCylinderCutoff N L E) N L E g ω =
      retainedMarkedLaplaceFunctional N L E g ω := by
  classical
  unfold finiteMarkedLaplaceFunctional retainedMarkedLaplaceFunctional
  congr 2
  let f : ℕ → ℝ :=
    fun x ↦
      ∑ e ∈ Finset.range (E + 1),
        if exactLengthAt ω x (excessRowCount L e) then
          g ((x : ℝ) / (N : ℝ)) e
        else 0
  have hremoved :
      (∑ x ∈ removedExactLengthStarts N L E, f x) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    dsimp only [f]
    apply Finset.sum_eq_zero
    intro e he
    rw [if_neg]
    exact fun hexact ↦ hno ⟨e, he, x, hx, hexact⟩
  rw [retainedMarkedStarts_eq_sdiff]
  change
    (∑ x ∈ dyadicBlock N, f x) =
      ∑ x ∈ dyadicBlock N \ removedExactLengthStarts N L E, f x
  have hsplit :
      (∑ x ∈ dyadicBlock N \ removedExactLengthStarts N L E, f x) +
          (∑ x ∈ removedExactLengthStarts N L E, f x) =
        ∑ x ∈ dyadicBlock N, f x :=
    Finset.sum_sdiff
      (removedExactLengthStarts_subset_dyadicBlock N L E)
  linarith

/-- Every complete or retained marked Laplace functional lies in `[0,1]`. -/
theorem finiteMarkedLaplaceFunctional_mem_unitInterval
    {N L E : ℕ} {g : ℝ → ℕ → ℝ}
    (hg : ∀ t e, 0 ≤ g t e)
    (ω : SampleSpace (markedCylinderCutoff N L E)) :
    0 ≤
        finiteMarkedLaplaceFunctional
          (markedCylinderCutoff N L E) N L E g ω ∧
      finiteMarkedLaplaceFunctional
          (markedCylinderCutoff N L E) N L E g ω ≤ 1 := by
  constructor
  · exact Real.exp_nonneg _
  · unfold finiteMarkedLaplaceFunctional
    apply Real.exp_le_one_iff.mpr
    simp only [neg_nonpos]
    exact Finset.sum_nonneg fun x _ ↦
      Finset.sum_nonneg fun e _ ↦ by
        split_ifs
        · exact hg ((x : ℝ) / (N : ℝ)) e
        · exact le_rfl

theorem retainedMarkedLaplaceFunctional_mem_unitInterval
    {N L E : ℕ} {g : ℝ → ℕ → ℝ}
    (hg : ∀ t e, 0 ≤ g t e)
    (ω : SampleSpace (markedCylinderCutoff N L E)) :
    0 ≤ retainedMarkedLaplaceFunctional N L E g ω ∧
      retainedMarkedLaplaceFunctional N L E g ω ≤ 1 := by
  constructor
  · exact Real.exp_nonneg _
  · unfold retainedMarkedLaplaceFunctional
    apply Real.exp_le_one_iff.mpr
    simp only [neg_nonpos]
    exact Finset.sum_nonneg fun x _ ↦
      Finset.sum_nonneg fun e _ ↦ by
        split_ifs
        · exact hg ((x : ℝ) / (N : ℝ)) e
        · exact le_rfl

/--
Pointwise, the functional changes by at most the number of removed marked
events that occur.
-/
theorem abs_finiteMarkedLaplaceFunctional_sub_retained_le_count
    {N L E : ℕ} {g : ℝ → ℕ → ℝ}
    (hg : ∀ t e, 0 ≤ g t e)
    (ω : SampleSpace (markedCylinderCutoff N L E)) :
    |finiteMarkedLaplaceFunctional
        (markedCylinderCutoff N L E) N L E g ω -
      retainedMarkedLaplaceFunctional N L E g ω| ≤
      (removedMarkedActiveCount N L E ω : ℝ) := by
  classical
  by_cases hoccurs :
      ∃ e ∈ Finset.range (E + 1),
        ∃ x ∈ removedExactLengthStarts N L E,
          exactLengthAt ω x (excessRowCount L e)
  · obtain ⟨e, he, x, hx, hexact⟩ := hoccurs
    have hinner :
        1 ≤
          ∑ y ∈ removedExactLengthStarts N L E,
            if exactLengthAt ω y (excessRowCount L e) then 1 else 0 := by
      calc
        1 =
            (if exactLengthAt ω x (excessRowCount L e) then 1 else 0) := by
          rw [if_pos hexact]
        _ ≤
            ∑ y ∈ removedExactLengthStarts N L E,
              if exactLengthAt ω y (excessRowCount L e) then 1 else 0 := by
          apply Finset.single_le_sum
            (s := removedExactLengthStarts N L E)
            (f := fun y ↦
              if exactLengthAt ω y (excessRowCount L e) then 1 else 0)
          · intro y _hy
            split_ifs <;> omega
          · exact hx
    have hcount : 1 ≤ removedMarkedActiveCount N L E ω := by
      unfold removedMarkedActiveCount
      exact hinner.trans
        (Finset.single_le_sum
          (s := Finset.range (E + 1))
          (f := fun e ↦
            ∑ x ∈ removedExactLengthStarts N L E,
              if exactLengthAt ω x (excessRowCount L e) then 1 else 0)
          (fun _ _ ↦ Nat.zero_le _) he)
    have hfull :=
      finiteMarkedLaplaceFunctional_mem_unitInterval hg ω
    have hret :=
      retainedMarkedLaplaceFunctional_mem_unitInterval hg ω
    have habs :
        |finiteMarkedLaplaceFunctional
            (markedCylinderCutoff N L E) N L E g ω -
          retainedMarkedLaplaceFunctional N L E g ω| ≤ 1 := by
      exact abs_sub_le_iff.mpr
        ⟨by linarith [hfull.1, hret.2],
          by linarith [hret.1, hfull.2]⟩
    exact habs.trans (by exact_mod_cast hcount)
  · rw [finiteMarkedLaplaceFunctional_eq_retained_of_no_removed
      g ω hoccurs, sub_self, abs_zero]
    exact Nat.cast_nonneg _

/--
At the common cylinder cutoff, a one-point exact-length probability is the
literal source probability.
-/
theorem eventProbability_uniform_exactLength_eq_infinite
    {N L E e x : ℕ}
    (he : e ∈ Finset.range (E + 1))
    (hx : x ∈ dyadicBlock N) :
    eventProbability
        (FinitePMF.uniform
          (SampleSpace (markedCylinderCutoff N L E)))
        (fun ω ↦ exactLengthAt ω x (excessRowCount L e)) =
      infiniteExactLengthProbability x (excessRowCount L e) := by
  classical
  have heE : e ≤ E :=
    Nat.le_of_lt_succ (Finset.mem_range.mp he)
  have hxUpper : x < 2 * N :=
    (Finset.mem_Ico.mp (by simpa only [dyadicBlock] using hx)).2
  have hrows :
      excessRowCount L e ≤ markedCommonRowCount L E := by
    simp only [markedCommonRowCount, commonExactRowCount, excessRowCount]
    omega
  have hcut :
      x + (excessRowCount L e - 1) ≤
        markedCylinderCutoff N L E := by
    unfold markedCylinderCutoff dyadicCutoff
    omega
  have hmeasure :=
    infiniteExactLengthEvent_measure_eq_finiteProbabilityAtCutoff
      (M := markedCylinderCutoff N L E)
      (x := x) (q := excessRowCount L e) hcut
  unfold infiniteExactLengthProbability
  rw [hmeasure, ENNReal.toReal_ofReal]
  · change
      eventProbability
          (SectionThirteenCouplings.fullUniformPMF
            (markedCylinderCutoff N L E))
          (fun ω ↦ exactLengthAt ω x (excessRowCount L e)) =
        (((uniformEventProbability
          (M := markedCylinderCutoff N L E)
          (fun ω ↦ exactLengthAt ω x (excessRowCount L e)) : ℚ) : ℝ))
    rw [SectionThirteenCouplings.eventProbability_fullUniformPMF_eq]
    rw [finiteUniformProbability_eq_uniformEventProbability]
  · unfold finiteExactLengthProbabilityAtCutoff uniformEventProbability
    positivity

/--
The expectation-level functional comparison is bounded by the exact source
mass appearing in Lemma 14.8.
-/
theorem abs_fullMarkedExpectation_sub_retained_le_removedMass
    {N L E : ℕ} {g : ℝ → ℕ → ℝ}
    (hg : ∀ t e, 0 ≤ g t e) :
    |finitePMFExpectation
        (FinitePMF.uniform
          (SampleSpace (markedCylinderCutoff N L E)))
        (finiteMarkedLaplaceFunctional
          (markedCylinderCutoff N L E) N L E g) -
      finitePMFExpectation
        (FinitePMF.uniform
          (SampleSpace (markedCylinderCutoff N L E)))
        (retainedMarkedLaplaceFunctional N L E g)| ≤
      totalRemovedInfiniteExactLengthProbability N L E := by
  classical
  let μ :=
    FinitePMF.uniform
      (SampleSpace (markedCylinderCutoff N L E))
  let F :=
    finiteMarkedLaplaceFunctional
      (markedCylinderCutoff N L E) N L E g
  let R := retainedMarkedLaplaceFunctional N L E g
  calc
    |finitePMFExpectation μ F - finitePMFExpectation μ R| =
        |∑ ω, μ.prob ω * (F ω - R ω)| := by
      unfold finitePMFExpectation
      rw [← Finset.sum_sub_distrib]
      apply congrArg abs
      apply Finset.sum_congr rfl
      intro ω _hω
      ring
    _ ≤ ∑ ω, |μ.prob ω * (F ω - R ω)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤
        ∑ ω, μ.prob ω *
          (removedMarkedActiveCount N L E ω : ℝ) := by
      apply Finset.sum_le_sum
      intro ω _hω
      rw [abs_mul, abs_of_nonneg (μ.nonneg ω)]
      exact mul_le_mul_of_nonneg_left
        (abs_finiteMarkedLaplaceFunctional_sub_retained_le_count hg ω)
        (μ.nonneg ω)
    _ =
        ∑ e ∈ Finset.range (E + 1),
          ∑ x ∈ removedExactLengthStarts N L E,
            eventProbability μ
              (fun ω ↦ exactLengthAt ω x (excessRowCount L e)) := by
      unfold removedMarkedActiveCount eventProbability
      simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e he
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro ω _hω
      by_cases h : exactLengthAt ω x (excessRowCount L e) <;>
        simp [h]
    _ = totalRemovedInfiniteExactLengthProbability N L E := by
      unfold totalRemovedInfiniteExactLengthProbability
      apply Finset.sum_congr rfl
      intro e he
      apply Finset.sum_congr rfl
      intro x hx
      exact eventProbability_uniform_exactLength_eq_infinite
        he (removedExactLengthStarts_subset_dyadicBlock N L E hx)

/-! ## Removing `D(Q)`: comparison of the Poisson parameters -/

/-- The part of the thinned parameter supported on removed starts. -/
def removedMarkedThinnedParameter
    (N L E : ℕ) (g : ℝ → ℕ → ℝ) : ℝ :=
  ∑ x ∈ removedExactLengthStarts N L E,
    ∑ e ∈ Finset.range (E + 1),
      spatialRetention (fun t ↦ g t e)
          ((x : ℝ) / (N : ℝ)) /
        (2 : ℝ) ^ excessRowCount L e

/--
The complete parameter is the sum of the retained and removed parameters.
-/
theorem markedThinnedParameter_eq_retained_add_removed
    (N L E : ℕ) (g : ℝ → ℕ → ℝ) :
    markedThinnedParameter N L E g =
      retainedMarkedThinnedParameter N L E g +
        removedMarkedThinnedParameter N L E g := by
  rw [markedThinnedParameter_eq_literal]
  unfold literalMarkedThinnedParameter retainedMarkedThinnedParameter
    removedMarkedThinnedParameter
  let f : ℕ → ℝ :=
    fun x ↦
      ∑ e ∈ Finset.range (E + 1),
        spatialRetention (fun t ↦ g t e)
            ((x : ℝ) / (N : ℝ)) /
          (2 : ℝ) ^ (L + e + 1)
  have hsplit :
      (∑ x ∈ dyadicBlock N \ removedExactLengthStarts N L E, f x) +
          (∑ x ∈ removedExactLengthStarts N L E, f x) =
        ∑ x ∈ dyadicBlock N, f x :=
    Finset.sum_sdiff
      (removedExactLengthStarts_subset_dyadicBlock N L E)
  rw [retainedMarkedStarts_eq_sdiff]
  change
    (∑ x ∈ dyadicBlock N, f x) =
      (∑ x ∈ dyadicBlock N \ removedExactLengthStarts N L E, f x) +
        ∑ x ∈ removedExactLengthStarts N L E, f x
  exact hsplit.symm

/--
Explicit deterministic envelope for the removed parameter:
`(E+1) 2^E · #D(Q)/2^Q`.
-/
def removedMarkedParameterEnvelope
    (E N L : ℕ) : ℝ :=
  (E + 1 : ℝ) * (2 : ℝ) ^ E *
    (((removedExactLengthStarts N L E).card : ℝ) /
      (2 : ℝ) ^ markedCommonRowCount L E)

theorem removedMarkedThinnedParameter_nonneg
    {N L E : ℕ} {g : ℝ → ℕ → ℝ}
    (hg : ∀ t e, 0 ≤ g t e) :
    0 ≤ removedMarkedThinnedParameter N L E g := by
  unfold removedMarkedThinnedParameter
  exact Finset.sum_nonneg fun x _ ↦
    Finset.sum_nonneg fun e _ ↦
      div_nonneg
        (spatialRetention_nonneg
          (fun t ↦ hg t e) ((x : ℝ) / (N : ℝ)))
        (by positivity)

theorem removedMarkedParameterEnvelope_nonneg
    (E N L : ℕ) :
    0 ≤ removedMarkedParameterEnvelope E N L := by
  unfold removedMarkedParameterEnvelope
  positivity

/--
The removed parameter is bounded by its cardinal envelope, uniformly in
every nonnegative test function.
-/
theorem removedMarkedThinnedParameter_le_envelope
    {N L E : ℕ} {g : ℝ → ℕ → ℝ} :
    removedMarkedThinnedParameter N L E g ≤
      removedMarkedParameterEnvelope E N L := by
  classical
  have hterm :
      ∀ x ∈ removedExactLengthStarts N L E,
        ∀ e ∈ Finset.range (E + 1),
          spatialRetention (fun t ↦ g t e)
              ((x : ℝ) / (N : ℝ)) /
              (2 : ℝ) ^ excessRowCount L e ≤
            1 / (2 : ℝ) ^ (L + 1) := by
    intro x hx e he
    apply div_le_div₀ (by positivity)
      (spatialRetention_le_one (fun t ↦ g t e)
        ((x : ℝ) / (N : ℝ)))
    · positivity
    · apply pow_le_pow_right₀ (by norm_num)
      simp only [excessRowCount]
      omega
  calc
    removedMarkedThinnedParameter N L E g ≤
        ∑ x ∈ removedExactLengthStarts N L E,
          ∑ _e ∈ Finset.range (E + 1),
            1 / (2 : ℝ) ^ (L + 1) := by
      unfold removedMarkedThinnedParameter
      exact Finset.sum_le_sum fun x hx ↦
        Finset.sum_le_sum fun e he ↦ hterm x hx e he
    _ =
        ((removedExactLengthStarts N L E).card : ℝ) *
          (E + 1 : ℝ) / (2 : ℝ) ^ (L + 1) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      ring
    _ = removedMarkedParameterEnvelope E N L := by
      unfold removedMarkedParameterEnvelope markedCommonRowCount
        commonExactRowCount excessRowCount
      rw [show L + E + 1 = (L + 1) + E by omega, pow_add]
      field_simp
      ring

/--
The complete and retained parameters differ by at most the cardinal
envelope.
-/
theorem abs_markedThinnedParameter_sub_retained_le_envelope
    {N L E : ℕ} {g : ℝ → ℕ → ℝ}
    (hg : ∀ t e, 0 ≤ g t e) :
    |markedThinnedParameter N L E g -
      retainedMarkedThinnedParameter N L E g| ≤
      removedMarkedParameterEnvelope E N L := by
  rw [markedThinnedParameter_eq_retained_add_removed,
    add_sub_cancel_left, abs_of_nonneg
      (removedMarkedThinnedParameter_nonneg hg)]
  exact removedMarkedThinnedParameter_le_envelope

/--
Finite complete marked Laplace approximation, with the two removal errors
displayed separately.
-/
theorem fullMarkedLaplace_le_retainedPoisson
    (hAGG : ArratiaGoldsteinGordonStatement)
    {N L E : ℕ} (hN : 2 ≤ N) (hL : 1 ≤ L)
    (g : ℝ → ℕ → ℝ) (hg : ∀ t e, 0 ≤ g t e) :
    |finitePMFExpectation
        (FinitePMF.uniform
          (SampleSpace (markedCylinderCutoff N L E)))
        (finiteMarkedLaplaceFunctional
          (markedCylinderCutoff N L E) N L E g) -
      Real.exp (-retainedMarkedThinnedParameter N L E g)| ≤
      totalRemovedInfiniteExactLengthProbability N L E +
        4 *
          (((markedBOneFinite N L E : ℚ) : ℝ) +
            ((markedBTwoAverage N L E : ℚ) : ℝ)) := by
  have hremove :=
    abs_fullMarkedExpectation_sub_retained_le_removedMass
      (N := N) (L := L) (E := E) hg
  have hagg :=
    averagedRetainedMarkedLaplace_le (E := E) hAGG hN hL g hg
  exact (abs_sub_le _ _ _).trans (add_le_add hremove hagg)

end

end MarkedLaplaceFiniteClosure
end PaperC
