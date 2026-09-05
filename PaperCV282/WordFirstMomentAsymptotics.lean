import PaperCV282.InfiniteWordFirstMoment
import PaperCV282.WordDefectAsymptotics

/-!
# The summed clause of Corollary 2.6

The square-root defect bound and the finite first-moment identity give an
error of `m * 2⁻ᴮ * N^(1/2+o(1))`. The quantified endpoints choose their
threshold before the length, position mask and dictionary. The number of
words may vary with both `N` and `B`, including an empty dictionary.
-/

namespace PaperC.V282.WordFirstMomentAsymptotics

open MeasureTheory InfiniteRademacher
open WindowValues InfiniteWordFirstMoment WordDefectCounting WordDefectAsymptotics
open CriticalWindowParameters
open scoped BigOperators

noncomputable section

/-- Natural subtraction in a defect weight agrees with real subtraction. -/
theorem cast_wordDefectWeight (x B : ℕ) :
    ((2 ^ (defectIndices B x B).card - 1 : ℕ) : ℝ) =
      (2 : ℝ) ^ (defectIndices B x B).card - 1 := by
  rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega))]
  norm_num

/-- Every deterministic mask has no more total defect weight than its dyadic block. -/
theorem sum_wordDefectWeight_cast_le_wordDefectMass
    (N B : ℕ) (s : Finset ℕ) (hs : s ⊆ dyadicBlock N) :
    (∑ x ∈ s, ((2 : ℝ) ^ (defectIndices B x B).card - 1)) ≤
      (wordDefectMass N B : ℝ) := by
  have hnat : ∑ x ∈ s, (2 ^ (defectIndices B x B).card - 1) ≤
      wordDefectMass N B := Finset.sum_le_sum_of_subset hs
  have hcast : ((∑ x ∈ s, (2 ^ (defectIndices B x B).card - 1) : ℕ) : ℝ) ≤
      (wordDefectMass N B : ℝ) := by exact_mod_cast hnat
  simpa only [Nat.cast_sum, cast_wordDefectWeight] using hcast

/-- The first-moment error is bounded by the exact word mass, independently
of the dictionary and position mask. -/
theorem abs_wordProbabilitySum_sub_baseline_le_wordDefectMass
    {N B : ℕ} (hN : 2 ≤ N) (s : Finset ℕ) (hs : s ⊆ dyadicBlock N)
    (W : Finset (Fin B → F₂)) :
    |wordProbabilitySum B s W - (s.card : ℝ) * (W.card : ℝ) / (2 : ℝ) ^ B| ≤
      ((W.card : ℝ) / (2 : ℝ) ^ B) * (wordDefectMass N B : ℝ) := by
  refine (abs_wordProbabilitySum_sub_baseline_le B s W
    (fun x hx => two_le_of_mem_dyadicBlock hN (hs hx))).trans ?_
  exact mul_le_mul_of_nonneg_left
    (sum_wordDefectWeight_cast_le_wordDefectMass N B s hs) (by positivity)

/-- Uniform summed word-probability error in a fixed logarithmic band.
The threshold precedes `B`, `s`, and `W`, so their choices may vary with `N`.
No balance condition on `N / 2^B` or independence of occurrences is assumed. -/
theorem corollary_two_six_summed_probability
    {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₁c₂ : c₁ < c₂) :
    ∀ k : ℕ, 0 < k → ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ B : ℕ,
      InCriticalWindow c₁ c₂ N B →
      ∀ s : Finset ℕ, s ⊆ dyadicBlock N →
      ∀ W : Finset (Fin B → F₂),
        |wordProbabilitySum B s W - (s.card : ℝ) * (W.card : ℝ) / (2 : ℝ) ^ B| ^
          (2 * k) ≤ ((W.card : ℝ) / (2 : ℝ) ^ B) ^ (2 * k) * (N : ℝ) ^ (k + 1) := by
  intro k hk
  obtain ⟨Nmass, hNmass⟩ := wordDefectMass_uniformHalfPower_on_window hc₁ hc₁c₂ k hk
  refine ⟨max Nmass 2, ?_⟩
  intro N hN B hwindow s hs W
  have hNtwo : 2 ≤ N := (le_max_right _ _).trans hN
  have hmass := hNmass N ((le_max_left _ _).trans hN) B hwindow
  rw [abs_of_nonneg (by positivity)] at hmass
  calc
    _ ≤ (((W.card : ℝ) / (2 : ℝ) ^ B) * (wordDefectMass N B : ℝ)) ^ (2 * k) :=
      pow_le_pow_left₀ (abs_nonneg _)
        (abs_wordProbabilitySum_sub_baseline_le_wordDefectMass hNtwo s hs W) _
    _ = ((W.card : ℝ) / (2 : ℝ) ^ B) ^ (2 * k) *
        (wordDefectMass N B : ℝ) ^ (2 * k) := mul_pow _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hmass (by positivity)

/-- Literal first-moment formulation of the summed clause of Corollary 2.6,
for the actual occurrence count in the infinite Rademacher model. -/
theorem corollary_two_six_summed_expectation
    {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₁c₂ : c₁ < c₂) :
    ∀ k : ℕ, 0 < k → ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ B : ℕ,
      InCriticalWindow c₁ c₂ N B →
      ∀ s : Finset ℕ, s ⊆ dyadicBlock N →
      ∀ W : Finset (Fin B → F₂),
        |(∫ ω, wordOccurrenceCount B s W ω ∂infiniteRademacherMeasure) -
          (s.card : ℝ) * (W.card : ℝ) / (2 : ℝ) ^ B| ^ (2 * k) ≤
          ((W.card : ℝ) / (2 : ℝ) ^ B) ^ (2 * k) * (N : ℝ) ^ (k + 1) := by
  simpa only [integral_wordOccurrenceCount] using
    corollary_two_six_summed_probability hc₁ hc₁c₂

end
end PaperC.V282.WordFirstMomentAsymptotics
