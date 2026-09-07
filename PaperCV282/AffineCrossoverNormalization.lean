import PaperCV282.AffineCrossoverRareMass

/-! # Normalization by the actual affine border-plus-bulk scale -/
namespace PaperC.V282.AffineCrossoverNormalization

open MeasureTheory ProbabilityTheory Filter Topology InfiniteRademacher
open AffineCrossoverModel AffineCrossoverRareMass CrossoverBulkAtoms
open RarePrefixGeometry RarePrefixEvents MicroscopicNonvacancy MicroscopicBorderEvents
open BulkMarkedGeometry
open scoped NNReal ENNReal

noncomputable section

def rareScale (M L : ℕ) (delta : ℝ) (alpha : ℝ≥0) : ℝ :=
  (alpha : ℝ)+(totalRate (bulkStarts M L delta) L : ℝ)

theorem rareScale_pos (M L : ℕ) (delta : ℝ) (alpha : ℝ≥0) (ha : 0<alpha) :
    0<rareScale M L delta alpha := by
  unfold rareScale
  have h : (0 : ℝ)<alpha := ha
  positivity

theorem hit_ratio_error_le (mu : Measure InfiniteSample) [IsProbabilityMeasure mu]
    (habs : mu ≪ infiniteRademacherMeasure) {M L K : ℕ} {delta : ℝ} {alpha : ℝ≥0}
    (hM : 2≤M) (hL : 1≤L) (hLM : L≤M) (hdelta : 0<delta)
    (ha : 0<alpha) (heq : mu.real (borderEvent L)=(alpha : ℝ)) :
    |hitProbability mu M L/rareScale M L delta alpha-1| ≤
      (mu.real (interiorEvent L)+mu.real (middleEvent M L delta))/rareScale M L delta alpha+
      jointDistance mu M L K delta/rareScale M L delta alpha+
      (totalRate (bulkStarts M L delta) L : ℝ) := by
  have hr := rareScale_pos M L delta alpha ha
  have h := hit_probability_error_le mu habs (K := K) hM hL hLM hdelta
  rw [heq] at h
  have hid : hitProbability mu M L/rareScale M L delta alpha-1=
      (hitProbability mu M L-rareScale M L delta alpha)/rareScale M L delta alpha := by
    field_simp
  rw [hid,abs_div,abs_of_pos hr]
  apply (div_le_div_of_nonneg_right h hr.le).trans_eq
  dsimp [rareScale]
  field_simp
  ring

variable (mu : ℕ→Measure InfiniteSample) [∀ n, IsProbabilityMeasure (mu n)]
  (sizes lengths : ℕ→ℕ) (delta : ℝ) (alpha : ℕ→ℝ≥0)

/-- All approximation hypotheses are concrete source probabilities and joint total variation.
The affine arithmetic endpoints below establish them before this normalization is invoked. -/
theorem hit_probability_ratio_tendsto_one
    (habs : ∀ n,mu n ≪ infiniteRademacherMeasure)
    (hM : ∀ᶠ n in atTop,2≤sizes n) (hL : ∀ᶠ n in atTop,1≤lengths n)
    (hLM : ∀ᶠ n in atTop,lengths n≤sizes n) (hdelta : 0<delta)
    (ha : ∀ᶠ n in atTop,0<alpha n)
    (heq : ∀ᶠ n in atTop,(mu n).real (borderEvent (lengths n))=(alpha n : ℝ))
    (K : ℕ)
    (he : Tendsto (fun n=>((mu n).real (interiorEvent (lengths n))+
      (mu n).real (middleEvent (sizes n) (lengths n) delta))/
      rareScale (sizes n) (lengths n) delta (alpha n)) atTop (𝓝 0))
    (hd : Tendsto (fun n=>jointDistance (mu n) (sizes n) (lengths n) K delta/
      rareScale (sizes n) (lengths n) delta (alpha n)) atTop (𝓝 0))
    (hb : Tendsto (fun n=>(totalRate (bulkStarts (sizes n) (lengths n) delta) (lengths n) : ℝ))
      atTop (𝓝 0)) :
    Tendsto (fun n=>hitProbability (mu n) (sizes n) (lengths n)/
      rareScale (sizes n) (lengths n) delta (alpha n)) atTop (𝓝 1) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _=>norm_nonneg _) ?_
    (by simpa using (he.add hd).add hb)
  filter_upwards [hM,hL,hLM,ha,heq] with n hmn hln hlmn han heqn
  rw [Real.norm_eq_abs]
  exact hit_ratio_error_le (mu n) (habs n) (K := K) hmn hln hlmn hdelta han heqn

end
end PaperC.V282.AffineCrossoverNormalization
