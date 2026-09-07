import PaperCV282.AffineCrossoverCappedBudget
import PaperCV282.AffineCrossoverSparseNormalization

/-! # Closing the actual capped law after affine normalization

This assembly module is independent of the arithmetic that supplies its
concrete error limits. In particular its zero-cap endpoint needs no
condition on the future primes.
-/
namespace PaperC.V282.AffineCrossoverMarkedConvergence

open MeasureTheory ProbabilityTheory Filter Topology InfiniteRademacher
open AffineCrossoverModel AffineCrossoverNormalization AffineCrossoverSparseNormalization
open AffineCrossoverCappedBudget AffineCrossoverRecordMass
open CrossoverPrimeClockStable CrossoverBulkAtoms BulkMarkedGeometry
open RarePrefixGeometry RarePrefixEvents MicroscopicNonvacancy MicroscopicBorderEvents
open ConditionedCountableLaw SharpConditioning
open scoped NNReal

noncomputable section

variable (mu : ℕ→Measure InfiniteSample) [∀ n, IsProbabilityMeasure (mu n)]
  (sizes lengths : ℕ→ℕ) (delta : ℝ) (alpha : ℕ→ℝ≥0)

theorem cappedDistance_tendsto_zero
    (habs : ∀ n,mu n ≪ infiniteRademacherMeasure)
    (hM : ∀ᶠ n in atTop,2≤sizes n) (hL : ∀ᶠ n in atTop,1≤lengths n)
    (hLM : ∀ᶠ n in atTop,lengths n≤sizes n) (hdelta : 0<delta)
    (hne : ∀ᶠ n in atTop,(bulkStarts (sizes n) (lengths n) delta).Nonempty)
    (ha : ∀ᶠ n in atTop,0<alpha n)
    (heq : ∀ᶠ n in atTop,(mu n).real (borderEvent (lengths n))=(alpha n : ℝ))
    (K : ℕ)
    (hclock : ∀ᶠ n in atTop,(cond (mu n) (borderEvent (lengths n))).map
      (actualClockRecord (lengths n) K)=
      (geometricMeasure GeometricClusterTarget.halfSuccess).map (fun j => (true,min j K)))
    (he : Tendsto (fun n=>((mu n).real (interiorEvent (lengths n))+
      (mu n).real (middleEvent (sizes n) (lengths n) delta))/
      rareScale (sizes n) (lengths n) delta (alpha n)) atTop (𝓝 0))
    (hd : Tendsto (fun n=>jointDistance (mu n) (sizes n) (lengths n) K delta/
      rareScale (sizes n) (lengths n) delta (alpha n)) atTop (𝓝 0))
    (hb : Tendsto (fun n=>(totalRate (bulkStarts (sizes n) (lengths n) delta) (lengths n) : ℝ))
      atTop (𝓝 0)) :
    Tendsto (fun n=>cappedDistance (mu n) (sizes n) (lengths n) K delta (alpha n)) atTop (𝓝 0) := by
  have hh := hit_probability_ratio_tendsto_one mu sizes lengths delta alpha habs hM hL hLM hdelta ha heq K he hd hb
  have hp := product_sparse_ratio_tendsto_one mu sizes lengths delta alpha K ha heq hb
  have hs := source_sparse_event_ratio_tendsto_one mu sizes lengths delta alpha K ha heq hb hd
  exact cappedDistance_tendsto_of_normalized mu sizes lengths K delta alpha habs hM hL hLM hdelta hne
    ha heq hclock hh hp hd (cappedErrorBudget_tendsto_zero mu sizes lengths K delta alpha ha hh hs hp he hd hb)

/-- Spatial and sign observations forget only the border clock. Their comparison therefore
requires no future-neutrality premise at any index. -/
theorem cappedDistance_zero_tendsto_zero
    (habs : ∀ n,mu n ≪ infiniteRademacherMeasure)
    (hM : ∀ᶠ n in atTop,2≤sizes n) (hL : ∀ᶠ n in atTop,1≤lengths n)
    (hLM : ∀ᶠ n in atTop,lengths n≤sizes n) (hdelta : 0<delta)
    (hne : ∀ᶠ n in atTop,(bulkStarts (sizes n) (lengths n) delta).Nonempty)
    (ha : ∀ᶠ n in atTop,0<alpha n)
    (heq : ∀ᶠ n in atTop,(mu n).real (borderEvent (lengths n))=(alpha n : ℝ))
    (he : Tendsto (fun n=>((mu n).real (interiorEvent (lengths n))+
      (mu n).real (middleEvent (sizes n) (lengths n) delta))/
      rareScale (sizes n) (lengths n) delta (alpha n)) atTop (𝓝 0))
    (hd : Tendsto (fun n=>jointDistance (mu n) (sizes n) (lengths n) 0 delta/
      rareScale (sizes n) (lengths n) delta (alpha n)) atTop (𝓝 0))
    (hb : Tendsto (fun n=>(totalRate (bulkStarts (sizes n) (lengths n) delta) (lengths n) : ℝ))
      atTop (𝓝 0)) :
    Tendsto (fun n=>cappedDistance (mu n) (sizes n) (lengths n) 0 delta (alpha n)) atTop (𝓝 0) := by
  apply cappedDistance_tendsto_zero mu sizes lengths delta alpha habs hM hL hLM hdelta hne ha heq 0 ?_ he hd hb
  filter_upwards [ha,heq] with n han heqn
  exact conditional_actualClockRecord_zero (mu n) (lengths n) (by rw [heqn]; exact_mod_cast han)

/-- Interior errors remain negligible after conditioning by the real hit event. -/
theorem conditional_interior_tendsto_zero
    (ha : ∀ᶠ n in atTop,0<alpha n)
    (hh : Tendsto (fun n=>hitProbability (mu n) (sizes n) (lengths n)/
      rareScale (sizes n) (lengths n) delta (alpha n)) atTop (𝓝 1))
    (hi : Tendsto (fun n=>(mu n).real (interiorEvent (lengths n))/
      rareScale (sizes n) (lengths n) delta (alpha n)) atTop (𝓝 0)) :
    Tendsto (fun n=>(cond (mu n) (hitEvent (sizes n) (lengths n))).real
      (interiorEvent (lengths n))) atTop (𝓝 0) := by
  have ht := hi.div hh (by norm_num : (1 : ℝ)≠0)
  simp only [zero_div] at ht
  have he : Tendsto (fun n=>(mu n).real (interiorEvent (lengths n))/
      hitProbability (mu n) (sizes n) (lengths n)) atTop (𝓝 0) := by
    apply ht.congr'
    filter_upwards [ha] with n han
    exact div_div_div_cancel_right₀ (rareScale_pos _ _ _ _ han).ne' _ _
  apply squeeze_zero' (Eventually.of_forall fun _=>measureReal_nonneg) ?_ he
  filter_upwards [] with n
  rw [cond_real_apply _ _ (measurableSet_hitEvent _ _)]
  exact div_le_div_of_nonneg_right (measureReal_mono Set.inter_subset_right) measureReal_nonneg

end
end PaperC.V282.AffineCrossoverMarkedConvergence
