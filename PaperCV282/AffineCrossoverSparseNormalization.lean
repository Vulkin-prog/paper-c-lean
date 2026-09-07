import PaperCV282.AffineCrossoverNormalization
import PaperCV282.AffineCrossoverSparseTarget

/-! # Actual sparse probabilities on the affine border-plus-bulk scale

The product normalization uses only the true border mass and a vanishing
bulk intensity. The source normalization then follows from the genuine
joint total-variation error, without a clock-law or population-nonemptiness
assumption.
-/
namespace PaperC.V282.AffineCrossoverSparseNormalization

open MeasureTheory ProbabilityTheory Filter Topology InfiniteRademacher
open AffineCrossoverModel AffineCrossoverNormalization AffineCrossoverSparseTarget
open CrossoverSparseTarget CrossoverSparseSource CrossoverSparseWeights CrossoverBulkAtoms
open MicroscopicBorderEvents BulkMarkedGeometry SharpConditioning
open scoped NNReal

noncomputable section

variable (mu : ℕ → Measure InfiniteSample) [∀ n, IsProbabilityMeasure (mu n)]
  (sizes lengths : ℕ → ℕ) (delta : ℝ) (alpha : ℕ → ℝ≥0) (K : ℕ)

theorem product_sparse_ratio_tendsto_one
    (ha : ∀ᶠ n in atTop, 0 < alpha n)
    (heq : ∀ᶠ n in atTop, (mu n).real (borderEvent (lengths n)) = (alpha n : ℝ))
    (hb : Tendsto (fun n => (totalRate (bulkStarts (sizes n) (lengths n) delta) (lengths n) : ℝ))
      atTop (𝓝 0)) :
    Tendsto (fun n => (productJoint (mu n) (bulkStarts (sizes n) (lengths n) delta) (lengths n) K).real
      (sparseEvent (bulkStarts (sizes n) (lengths n) delta)) /
      rareScale (sizes n) (lengths n) delta (alpha n)) atTop (𝓝 1) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (by simpa using hb.const_mul 2)
  filter_upwards [ha,heq] with n han heqn
  rw [Real.norm_eq_abs,
    AffineCrossoverSparseTarget.sparse_mass (mu n) _ _ K (alpha n) heqn,rareScale]
  have haOne : (alpha n : ℝ) ≤ 1 := by rw [← heqn]; exact measureReal_le_one
  exact sparse_mass_relative_error (by exact_mod_cast han) haOne (by positivity)

theorem source_sparse_ratio_tendsto_one
    (ha : ∀ᶠ n in atTop, 0 < alpha n)
    (heq : ∀ᶠ n in atTop, (mu n).real (borderEvent (lengths n)) = (alpha n : ℝ))
    (hb : Tendsto (fun n => (totalRate (bulkStarts (sizes n) (lengths n) delta) (lengths n) : ℝ))
      atTop (𝓝 0))
    (hd : Tendsto (fun n => jointDistance (mu n) (sizes n) (lengths n) K delta /
      rareScale (sizes n) (lengths n) delta (alpha n)) atTop (𝓝 0)) :
    Tendsto (fun n => (sourceJoint (mu n) (sizes n) (lengths n) K delta).real
      (sparseEvent (bulkStarts (sizes n) (lengths n) delta)) /
      rareScale (sizes n) (lengths n) delta (alpha n)) atTop (𝓝 1) := by
  have hp := product_sparse_ratio_tendsto_one mu sizes lengths delta alpha K ha heq hb
  have he : Tendsto (fun n =>
      (sourceJoint (mu n) (sizes n) (lengths n) K delta).real
        (sparseEvent (bulkStarts (sizes n) (lengths n) delta)) / rareScale (sizes n) (lengths n) delta (alpha n) -
      (productJoint (mu n) (bulkStarts (sizes n) (lengths n) delta) (lengths n) K).real
        (sparseEvent (bulkStarts (sizes n) (lengths n) delta)) / rareScale (sizes n) (lengths n) delta (alpha n))
      atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hd
    filter_upwards [ha] with n han
    have hr := rareScale_pos (sizes n) (lengths n) delta (alpha n) han
    rw [Real.norm_eq_abs,← sub_div,abs_div,abs_of_pos hr]
    apply div_le_div_of_nonneg_right ?_ hr.le
    exact discrepancy_le _ _ _ (Set.to_countable _).measurableSet
  simpa only [sub_add_cancel,zero_add] using he.add hp

theorem source_sparse_event_ratio_tendsto_one
    (ha : ∀ᶠ n in atTop, 0 < alpha n)
    (heq : ∀ᶠ n in atTop, (mu n).real (borderEvent (lengths n)) = (alpha n : ℝ))
    (hb : Tendsto (fun n => (totalRate (bulkStarts (sizes n) (lengths n) delta) (lengths n) : ℝ))
      atTop (𝓝 0))
    (hd : Tendsto (fun n => jointDistance (mu n) (sizes n) (lengths n) K delta /
      rareScale (sizes n) (lengths n) delta (alpha n)) atTop (𝓝 0)) :
    Tendsto (fun n => (mu n).real (sourceSparseEvent (sizes n) (lengths n) K delta) /
      rareScale (sizes n) (lengths n) delta (alpha n)) atTop (𝓝 1) := by
  simpa only [AffineCrossoverModel.sourceSparse_mass] using
    source_sparse_ratio_tendsto_one mu sizes lengths delta alpha K ha heq hb hd

end
end PaperC.V282.AffineCrossoverSparseNormalization
