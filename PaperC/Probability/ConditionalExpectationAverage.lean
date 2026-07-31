import PaperC.Probability.ConditionalAGGAverage
import PaperC.Probability.IndependentThinning
import PaperC.Probability.InfiniteCylinderTransfer

set_option maxHeartbeats 1200000

/-!
# Averaging finite conditional expectations

This module supplies the real-valued expectation counterpart of the
law-of-total-probability identity in `ConditionalAGGAverage`.  It applies to
an arbitrary observable on the full prime-sign cylinder, so both the spatial
and marked Laplace arguments can reuse it.
-/

namespace PaperC
namespace ConditionalExpectationAverage

open scoped BigOperators

open ConditionalAGGAverage
open ConditionalAGGInstantiation
open ConditionalStartProbability
open IndependentThinning
open InfiniteCylinderTransfer
open MeasureTheory
open SectionThirteenFiniteBound

noncomputable section

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

/-- Absolute deviation of a finite uniform average is bounded by the
uniform average of the pointwise absolute deviations. -/
theorem abs_finiteUniformAverage_sub_le
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → ℝ) (c : ℝ) :
    |finiteUniformAverage f - c| ≤
      finiteUniformAverage (fun i ↦ |f i - c|) := by
  unfold finiteUniformAverage
  have hd : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι)
  have hsumc :
      (∑ _i : ι, c) = (Fintype.card ι : ℝ) * c := by
    simp
  rw [show (∑ i, f i) / (Fintype.card ι : ℝ) - c =
      (∑ i, (f i - c)) / (Fintype.card ι : ℝ) by
    rw [Finset.sum_sub_distrib, hsumc]
    field_simp]
  rw [abs_div, abs_of_pos hd]
  exact div_le_div_of_nonneg_right
    (Finset.abs_sum_le_sum_abs _ _) hd.le

/--
Exact law of total expectation for the small/large-prime coordinate split.
The left-hand side first averages under the large-prime uniform PMF and then
uniformly over the fixed small-prime assignment; the result is expectation
under the uniform full cylinder.
-/
theorem finiteUniformAverage_largePMFExpectation_eq_full
    (M Y : ℕ) (F : SampleSpace M → ℝ) :
    finiteUniformAverage
        (fun σ : SmallSample M Y ↦
          finitePMFExpectation
            (largeUniformPMF M Y)
            (fun η : LargeSample M Y ↦
              F (assemble M Y σ η))) =
      finitePMFExpectation
        (FinitePMF.uniform (SampleSpace M)) F := by
  classical
  have hsum :
      (∑ σ : SmallSample M Y,
          ∑ η : LargeSample M Y,
            F (assemble M Y σ η)) =
        ∑ ω : SampleSpace M, F ω := by
    have hequiv :=
      (sampleSplitEquiv M Y).symm.sum_comp F
    rw [Fintype.sum_prod_type] at hequiv
    exact hequiv
  unfold finiteUniformAverage finitePMFExpectation
  simp only [largeUniformPMF, FinitePMF.uniform_prob]
  rw [card_sampleSpace_eq_mul M Y]
  rw [← Finset.mul_sum]
  simp_rw [← Finset.mul_sum]
  rw [hsum]
  have hsmall :
      (Fintype.card (SmallSample M Y) : ℝ) ≠ 0 := by
    positivity
  have hlarge :
      (Fintype.card (LargeSample M Y) : ℝ) ≠ 0 := by
    positivity
  field_simp [mul_comm]
  push_cast
  ring

/--
The measure-theoretic integral under the finite Rademacher product law is
exactly expectation under the uniform finite PMF.  This is the generic
finite-cylinder bridge used by all Laplace observables.
-/
theorem finiteRademacherIntegral_eq_uniformPMFExpectation
    (M : ℕ) (F : SampleSpace M → ℝ) :
    (∫ ω, F ω ∂finiteRademacherMeasure M) =
      finitePMFExpectation
        (FinitePMF.uniform (SampleSpace M)) F := by
  classical
  have hIntegrable :
      Integrable F (finiteRademacherMeasure M) :=
    ⟨(measurable_of_finite F).aestronglyMeasurable,
      HasFiniteIntegral.of_finite⟩
  rw [integral_fintype hIntegrable]
  unfold finitePMFExpectation
  apply Finset.sum_congr rfl
  intro σ _hσ
  congr 1
  rw [measureReal_def,
    finiteRademacherMeasure_singleton]
  simp only [FinitePMF.uniform_prob, Fintype.card_fun,
    ZMod.card, ENNReal.toReal_pow, ENNReal.toReal_inv,
    ENNReal.toReal_ofNat]
  rw [inv_pow]
  congr 1
  norm_num

end

end ConditionalExpectationAverage
end PaperC
