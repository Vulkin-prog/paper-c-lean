import PaperCV282.InfiniteWordTransfer
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Finite first moments of prescribed words in the infinite model

An arbitrary finite position mask and a finite set of distinct binary words
define a genuine occurrence count under the retained infinite Rademacher
law. Its integral is the sum of word probabilities. The pointwise estimate
of Corollary 2.6 gives the finite summed error, before any asymptotic
estimate for the total defect weight.
-/

namespace PaperC.V282.InfiniteWordFirstMoment

open MeasureTheory Set
open InfiniteRademacher WindowValues InfiniteWordTransfer
open scoped BigOperators

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

noncomputable section

local instance instIsProbabilityMeasureInfiniteRademacher :
    IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

/-- The sum of source word probabilities on a finite mask and a dictionary
of distinct words. The `Finset` representation includes the empty dictionary. -/
def wordProbabilitySum (B : ℕ) (s : Finset ℕ) (W : Finset (Fin B → F₂)) : ℝ :=
  ∑ x ∈ s, ∑ b ∈ W, infiniteWordProbability x B b

/-- The finite random number of word occurrences, as a real-valued sum of
indicators of actual infinite-model word events. -/
def wordOccurrenceCount (B : ℕ) (s : Finset ℕ) (W : Finset (Fin B → F₂))
    (ω : InfiniteSample) : ℝ :=
  ∑ x ∈ s, ∑ b ∈ W, (infiniteWordEvent x B b).indicator (fun _ => (1 : ℝ)) ω

/-- Each individual word indicator is integrable under the source law. -/
theorem integrable_wordIndicator (x B : ℕ) (b : Fin B → F₂) :
    Integrable ((infiniteWordEvent x B b).indicator (fun _ => (1 : ℝ)))
      infiniteRademacherMeasure :=
  (integrable_const (1 : ℝ)).indicator (measurableSet_infiniteWordEvent x B b)

/-- The finite occurrence count is integrable. -/
theorem integrable_wordOccurrenceCount (B : ℕ) (s : Finset ℕ)
    (W : Finset (Fin B → F₂)) :
    Integrable (wordOccurrenceCount B s W) infiniteRademacherMeasure := by
  apply integrable_finsetSum s
  intro x _
  exact integrable_finsetSum W fun b _ => integrable_wordIndicator x B b

/-- Integrating a word indicator gives the exact source word probability. -/
theorem integral_wordIndicator (x B : ℕ) (b : Fin B → F₂) :
    (∫ ω, (infiniteWordEvent x B b).indicator (fun _ => (1 : ℝ)) ω
      ∂infiniteRademacherMeasure) = infiniteWordProbability x B b := by
  rw [integral_indicator_const (1 : ℝ) (measurableSet_infiniteWordEvent x B b)]
  simp [infiniteWordProbability, measureReal_def]

/-- The probability sum is the first moment of the actual finite occurrence count. -/
theorem integral_wordOccurrenceCount (B : ℕ) (s : Finset ℕ)
    (W : Finset (Fin B → F₂)) :
    (∫ ω, wordOccurrenceCount B s W ω ∂infiniteRademacherMeasure) =
      wordProbabilitySum B s W := by
  unfold wordOccurrenceCount wordProbabilitySum
  rw [integral_finsetSum s (fun x _ =>
    integrable_finsetSum W fun b _ => integrable_wordIndicator x B b)]
  apply Finset.sum_congr rfl
  intro x _
  rw [integral_finsetSum W (fun b _ => integrable_wordIndicator x B b)]
  exact Finset.sum_congr rfl fun b _ => integral_wordIndicator x B b

/-- The sum of absolute pointwise errors has a word-independent defect majorant. -/
theorem sum_abs_wordProbability_sub_baseline_le (B : ℕ) (s : Finset ℕ)
    (W : Finset (Fin B → F₂)) (hs : ∀ x ∈ s, 2 ≤ x) :
    (∑ x ∈ s, ∑ b ∈ W, |infiniteWordProbability x B b - 1 / (2 : ℝ) ^ B|) ≤
      ((W.card : ℝ) / (2 : ℝ) ^ B) *
        ∑ x ∈ s, ((2 : ℝ) ^ (defectIndices B x B).card - 1) := by
  calc
    _ ≤ ∑ x ∈ s, ∑ _b ∈ W,
        ((2 : ℝ) ^ (defectIndices B x B).card - 1) / (2 : ℝ) ^ B :=
      Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun b _ =>
        corollary_two_six_pointwise_infinite (hs x hx) b
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      simp only [div_eq_mul_inv, mul_comm _ ((2 : ℝ) ^ B)⁻¹, ← mul_assoc,
        ← Finset.mul_sum]

/-- Finite summed form of (2.6), for every mask of positive starts and every
dictionary of distinct prescribed words. No asymptotic premise is used. -/
theorem abs_wordProbabilitySum_sub_baseline_le (B : ℕ) (s : Finset ℕ)
    (W : Finset (Fin B → F₂)) (hs : ∀ x ∈ s, 2 ≤ x) :
    |wordProbabilitySum B s W - (s.card : ℝ) * (W.card : ℝ) / (2 : ℝ) ^ B| ≤
      ((W.card : ℝ) / (2 : ℝ) ^ B) *
        ∑ x ∈ s, ((2 : ℝ) ^ (defectIndices B x B).card - 1) := by
  have hbase : (s.card : ℝ) * (W.card : ℝ) / (2 : ℝ) ^ B =
      ∑ _x ∈ s, ∑ _b ∈ W, (1 : ℝ) / (2 : ℝ) ^ B := by
    simp only [Finset.sum_const, nsmul_eq_mul]
    ring
  rw [wordProbabilitySum, hbase, ← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ x ∈ s, |∑ b ∈ W, (infiniteWordProbability x B b - 1 / (2 : ℝ) ^ B)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x ∈ s, ∑ b ∈ W, |infiniteWordProbability x B b - 1 / (2 : ℝ) ^ B| :=
      Finset.sum_le_sum fun _ _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := sum_abs_wordProbability_sub_baseline_le B s W hs

end
end PaperC.V282.InfiniteWordFirstMoment
