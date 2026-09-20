import PaperCPrel8.AffineDictionaryUniform

/-! # Exceptional proportions in the actual affine matrix and offset sample -/
namespace PaperC.Prel8.AffineDictionaryExceptional
open PaperC.SectionThirteenFiniteBound PaperC.ConditionalAGGAverage
open PaperC.Prel8.DictionaryAverage PaperC.Prel8.AffineDictionarySample
open PaperC.Prel8.AffineDictionaryInclusion PaperC.Prel8.AffineDictionaryMoments
open PaperC.V282.DictionaryFieldInfinite
open scoped BigOperators
noncomputable section
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

def affineFraction (B r : ℕ) (p : Finset (Word B) → Prop) : ℝ :=
  affineAverage B r (fun W => if p W then 1 else 0)

/-- This is a proportion of matrix/offset samples, not a uniform subset proportion. -/
theorem fraction_eq_card (B r : ℕ) (p : Finset (Word B) → Prop) :
    affineFraction B r p =
      ((Finset.univ.filter (fun s : Sample B r => p (dictionary s))).card:ℝ)/Fintype.card (Sample B r) := by
  simp [affineFraction,affineAverage,finiteUniformAverage]

theorem fraction_nonneg (B r : ℕ) (p : Finset (Word B) → Prop) : 0 ≤ affineFraction B r p := by
  rw [fraction_eq_card]; positivity

/-- Markov's inequality keeps each dictionary fixed inside its error. -/
theorem fraction_gt_le {B r : ℕ} (hrank : r ≤ B)
    (f : Finset (Word B) → ℝ) (hf : ∀ s : Sample B r, 0 ≤ f (dictionary s))
    {t R : ℝ} (ht : 0 < t) (hR : affineAverage B r f ≤ R) :
    affineFraction B r (fun W => t < f W) ≤ min 1 (R/t) := by
  have h1 := affine_mono hrank (f := fun W => if t < f W then (1:ℝ) else 0)
    (g := fun _ => 1) (fun s => by split_ifs <;> norm_num)
  rw [affine_const hrank] at h1
  have h2 := affine_mono hrank (f := fun W => t*(if t < f W then (1:ℝ) else 0))
    (g := f) (fun s => by split_ifs with h; simpa using h.le; simpa using hf s)
  rw [affine_mul] at h2
  apply le_min h1
  apply (le_div_iff₀ ht).mpr
  change affineAverage B r (fun W => if t < f W then 1 else 0)*t ≤ R
  simpa only [mul_comm] using h2.trans hR

theorem mean_unconditional_le {N L Y r : ℕ} (hrank : r ≤ L+1) {R : ℝ}
    (hR : affineAverage (L+1) r (dictionaryConditionalDistance N L Y) ≤ R) :
    affineAverage (L+1) r (dictionaryDistance N L) ≤ R :=
  (affine_mono hrank (fun s => dictionaryDistance_le_conditionalDistance N L Y (dictionary s))).trans hR

theorem exceptional_fraction_le {N L Y r : ℕ} (hrank : r ≤ L+1) {R t : ℝ} (ht : 0 < t)
    (hR : affineAverage (L+1) r (dictionaryConditionalDistance N L Y) ≤ R) :
    affineFraction (L+1) r (fun W => t < dictionaryConditionalDistance N L Y W) ≤ min 1 (R/t) :=
  fraction_gt_le hrank _ (fun s => dictionaryConditionalDistance_nonneg N L Y (dictionary s)) ht hR

end
end PaperC.Prel8.AffineDictionaryExceptional
