import PaperCV282.AffineCrossoverNormalization
import PaperCV282.CrossoverRareScale

/-! # Replacing the exact contained bulk intensity by M times two to minus L -/
namespace PaperC.V282.AffineCrossoverFullScale

open Filter Topology MeasureTheory InfiniteRademacher AllStartSoftPoisson BulkPopulation
open CrossoverBulkAtoms BulkMarkedGeometry AffineCrossoverNormalization AffineCrossoverModel
open scoped NNReal

noncomputable section

theorem denominator_ratio_tendsto_one
    (sizes lengths : ℕ→ℕ) (hsizes : Tendsto sizes atTop atTop)
    (beta delta : ℝ) (hdelta : 0<delta) (hdeltaOne : delta<1)
    (hupper : ∀ᶠ n in atTop,(lengths n : ℝ)≤beta*Real.log (sizes n))
    (hpositive : ∀ᶠ n in atTop,1≤lengths n)
    (alpha : ℕ→ℝ≥0) (ha : ∀ᶠ n in atTop,0<alpha n) :
    Tendsto (fun n=>rareScale (sizes n) (lengths n) delta (alpha n)/
      ((alpha n : ℝ)+(fullRate (sizes n) (lengths n) : ℝ))) atTop (𝓝 1) := by
  have hf : ∀ᶠ n in atTop,0<(fullRate (sizes n) (lengths n) : ℝ) := by
    filter_upwards [hsizes.eventually (eventually_ge_atTop 1)] with n hn
    change 0<(sizes n : ℝ)/(2 : ℝ)^lengths n
    positivity
  have har : Tendsto (fun n=>(alpha n : ℝ)/(alpha n : ℝ)) atTop (𝓝 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [ha] with n hn
    exact (div_self (show (alpha n : ℝ)≠0 by exact_mod_cast hn.ne')).symm
  exact CrossoverRareScale.sum_ratio_tendsto_one
    (ha.mono fun n hn=>by exact_mod_cast hn) hf har
    (bulkRate_ratio_tendsto_one sizes lengths hsizes beta delta hdelta hdeltaOne hupper hpositive)

/-- The printed rare-tail denominator uses the full prefix intensity. -/
theorem hit_full_rate_ratio_tendsto_one
    (mu : ℕ→Measure InfiniteSample) (sizes lengths : ℕ→ℕ)
    (hsizes : Tendsto sizes atTop atTop) (beta delta : ℝ) (hdelta : 0<delta) (hdeltaOne : delta<1)
    (hupper : ∀ᶠ n in atTop,(lengths n : ℝ)≤beta*Real.log (sizes n))
    (hpositive : ∀ᶠ n in atTop,1≤lengths n)
    (alpha : ℕ→ℝ≥0) (ha : ∀ᶠ n in atTop,0<alpha n)
    (hh : Tendsto (fun n=>hitProbability (mu n) (sizes n) (lengths n)/
      rareScale (sizes n) (lengths n) delta (alpha n)) atTop (𝓝 1)) :
    Tendsto (fun n=>hitProbability (mu n) (sizes n) (lengths n)/
      ((alpha n : ℝ)+(fullRate (sizes n) (lengths n) : ℝ))) atTop (𝓝 1) := by
  have hd := denominator_ratio_tendsto_one sizes lengths hsizes beta delta hdelta hdeltaOne hupper
    hpositive alpha ha
  have ht := hh.mul hd
  simp only [mul_one] at ht
  apply ht.congr'
  filter_upwards [ha] with n han
  have hr := (rareScale_pos (sizes n) (lengths n) delta (alpha n) han).ne'
  rw [div_mul_div_cancel₀ hr]

end
end PaperC.V282.AffineCrossoverFullScale
