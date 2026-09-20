import PaperCPrel8.DictionarySamplingBounds
import PaperCV282.DictionaryPairCosts

/-! # Finite averages with a fixed dictionary inside each comparison -/
namespace PaperC.Prel8.DictionaryAverage
open PaperC.V282.RandomDictionary PaperC.V282.RandomDictionaryOverlap
open PaperC.ConditionalAGGAverage PaperC.SectionThirteenFiniteBound
open scoped BigOperators
noncomputable section
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- Pointwise domination is averaged only after fixing the dictionary. -/
theorem average_mono {B m : ℕ} {f g : Finset (Fin B → PaperC.F₂) → ℝ}
    (h : ∀ W ∈ dictionaries B m, f W ≤ g W) : dictionaryAverage B m f ≤ dictionaryAverage B m g :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum h) (Nat.cast_nonneg _)

/-- Equality on the actual dictionary sample suffices. -/
theorem average_congr {B m : ℕ} {f g : Finset (Fin B → PaperC.F₂) → ℝ}
    (h : ∀ W ∈ dictionaries B m, f W = g W) : dictionaryAverage B m f = dictionaryAverage B m g := by
  unfold dictionaryAverage
  rw [Finset.sum_congr rfl h]

theorem average_add (B m : ℕ) (f g : Finset (Fin B → PaperC.F₂) → ℝ) :
    dictionaryAverage B m (fun W => f W+g W)=dictionaryAverage B m f+dictionaryAverage B m g := by
  simp [dictionaryAverage,Finset.sum_add_distrib,add_div]

theorem average_mul (B m : ℕ) (c : ℝ) (f : Finset (Fin B → PaperC.F₂) → ℝ) :
    dictionaryAverage B m (fun W => c*f W)=c*dictionaryAverage B m f := by
  simp [dictionaryAverage,← Finset.mul_sum,mul_div_assoc]

theorem average_const (B m : ℕ) (hm : m ≤ 2^B) (c : ℝ) :
    dictionaryAverage B m (fun _ => c)=c := by
  have hc : (dictionaries B m).card ≠ 0 := (Finset.card_pos.mpr (dictionaries_nonempty hm)).ne'
  simp [dictionaryAverage,show ((dictionaries B m).card:ℝ) ≠ 0 by exact_mod_cast hc]

theorem environment_add {Ω : Type*} [Fintype Ω] (f g : Ω → ℝ) :
    finiteUniformAverage (fun x => f x+g x)=finiteUniformAverage f+finiteUniformAverage g := by
  simp [finiteUniformAverage,Finset.sum_add_distrib,add_div]

theorem environment_mul {Ω : Type*} [Fintype Ω] (c : ℝ) (f : Ω → ℝ) :
    finiteUniformAverage (fun x => c*f x)=c*finiteUniformAverage f := by
  simp [finiteUniformAverage,← Finset.mul_sum,mul_div_assoc]

theorem environment_const {Ω : Type*} [Fintype Ω] [Nonempty Ω] (c : ℝ) :
    finiteUniformAverage (fun _ : Ω => c)=c := by
  have hc : (Fintype.card Ω:ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero (α := Ω)
  simp [finiteUniformAverage,hc]

/-- The prime environment and the independent dictionary sums commute. -/
theorem average_environment_commute (B m : ℕ) {Ω : Type*} [Fintype Ω]
    (f : Finset (Fin B → PaperC.F₂) → Ω → ℝ) :
    dictionaryAverage B m (fun W => finiteUniformAverage (f W)) =
      finiteUniformAverage (fun omega => dictionaryAverage B m (fun W => f W omega)) := by
  unfold dictionaryAverage finiteUniformAverage
  rw [← Finset.sum_div,← Finset.sum_div,Finset.sum_comm]
  ring

/-- The exact Markov inequality for any nonnegative fixed-dictionary error. -/
theorem fraction_gt_le {B m : ℕ} (hm : m ≤ 2^B)
    (f : Finset (Fin B → PaperC.F₂) → ℝ) (hf : ∀ W ∈ dictionaries B m, 0 ≤ f W)
    {t r : ℝ} (ht : 0 < t) (hr : dictionaryAverage B m f ≤ r) :
    dictionaryFraction B m (fun W => t < f W) ≤ min 1 (r/t) := by
  let bad := (dictionaries B m).filter (fun W => t < f W)
  have hc : (0:ℝ)<(dictionaries B m).card := by
    exact_mod_cast Finset.card_pos.mpr (dictionaries_nonempty hm)
  have hs : t*(bad.card:ℝ) ≤ ∑ W ∈ dictionaries B m, f W := by
    calc
      _ = ∑ W ∈ bad, t := by simp [mul_comm]
      _ ≤ ∑ W ∈ bad, f W := Finset.sum_le_sum (fun W hW => (Finset.mem_filter.mp hW).2.le)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun W hW _ => hf W hW)
  apply le_min
  · apply (div_le_one hc).mpr
    exact_mod_cast Finset.card_filter_le (dictionaries B m) (fun W => t < f W)
  · apply (le_div_iff₀ ht).mpr
    change (bad.card:ℝ)/(dictionaries B m).card*t ≤ r
    have h := div_le_div_of_nonneg_right hs hc.le
    change t*(bad.card:ℝ)/(dictionaries B m).card ≤ dictionaryAverage B m f at h
    calc
      _ = t*(bad.card:ℝ)/(dictionaries B m).card := by ring
      _ ≤ _ := h.trans hr

end
end PaperC.Prel8.DictionaryAverage
