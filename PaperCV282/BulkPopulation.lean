import PaperCV282.BulkMarkedGeometry
import PaperCV282.FiniteStartMaskAverages
import PaperCV282.MesoscopicRareLimit
import PaperCV282.AllStartSoftPoisson

/-! # The actual contained bulk population and its asymptotic intensity -/
namespace PaperC.V282.BulkPopulation

open Filter Topology BulkMarkedGeometry FiniteStartMaskAverages AllStartSoftPoisson

open scoped NNReal

noncomputable section

/-- The exact intensity retains both integer endpoints of the contained population. -/
def bulkRate (M L : ℕ) (delta : ℝ) : ℝ≥0 := maskRate L (bulkStarts M L delta)

theorem bulkRate_coe (M L : ℕ) (delta : ℝ) :
    (bulkRate M L delta : ℝ) = (bulkStarts M L delta).card / (2 : ℝ)^L := rfl

theorem population_deficit_le (M L : ℕ) (delta : ℝ) :
    M ≤ (bulkStarts M L delta).card + L + ⌈(M : ℝ)^delta⌉₊ := by
  rw [bulkStarts, Nat.card_Icc]
  omega

theorem population_ratio_error_le {M L : ℕ} {delta : ℝ}
    (hM : 2 ≤ M) (hL : 1 ≤ L) (hdelta : 0 < delta) :
    |((bulkStarts M L delta).card : ℝ) / M - 1| ≤
      ((L : ℝ) + ⌈(M : ℝ)^delta⌉₊) / M := by
  have hp : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hu : ((bulkStarts M L delta).card : ℝ) ≤ M := by exact_mod_cast card_bulkStarts_le hM hL hdelta
  have hlo : (M : ℝ) ≤ (bulkStarts M L delta).card + L + ⌈(M : ℝ)^delta⌉₊ := by
    exact_mod_cast population_deficit_le M L delta
  rw [abs_of_nonpos (by exact sub_nonpos.mpr ((div_le_one hp).mpr hu))]
  apply (le_div_iff₀ hp).mpr
  field_simp
  linarith

theorem logarithmic_lengths_div_size_tendsto_zero
    (sizes lengths : ℕ → ℕ) (hsizes : Tendsto sizes atTop atTop)
    (beta : ℝ) (hupper : ∀ᶠ n in atTop, (lengths n : ℝ) ≤ beta * Real.log (sizes n)) :
    Tendsto (fun n => (lengths n : ℝ) / sizes n) atTop (𝓝 0) := by
  have hs : Tendsto (fun n => (sizes n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hsizes
  have ht := (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hs).const_mul beta
  apply squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_
    (by simpa only [mul_zero] using ht)
  filter_upwards [hupper] with n hn
  simpa only [mul_div_assoc, Function.comp_def, id_eq] using div_le_div_of_nonneg_right hn (by positivity : (0 : ℝ) ≤ sizes n)

theorem lower_endpoint_div_size_tendsto_zero
    (sizes : ℕ → ℕ) (hsizes : Tendsto sizes atTop atTop)
    (delta : ℝ) (hdeltaOne : delta < 1) :
    Tendsto (fun n => (⌈(sizes n : ℝ)^delta⌉₊ : ℝ) / sizes n) atTop (𝓝 0) := by
  have hs : Tendsto (fun n => (sizes n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hsizes
  have hp : Tendsto (fun n => (sizes n : ℝ)^(delta-1)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_sub] using
      (tendsto_rpow_neg_atTop (by linarith : 0 < 1-delta)).comp hs
  have hi : Tendsto (fun n => (1 : ℝ)/(sizes n : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, one_div] using tendsto_inv_atTop_zero.comp hs
  apply squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_
    (by simpa only [add_zero] using hp.add hi)
  filter_upwards [hsizes.eventually (eventually_ge_atTop 1)] with n hn
  have hnpos : (0 : ℝ) < sizes n := by exact_mod_cast (show 0 < sizes n by omega)
  have hc := Nat.ceil_lt_add_one (Real.rpow_nonneg hnpos.le delta)
  calc
    _ ≤ ((sizes n : ℝ)^delta+1)/(sizes n : ℝ) := div_le_div_of_nonneg_right hc.le hnpos.le
    _ = _ := by rw [Real.rpow_sub hnpos, Real.rpow_one, add_div]

/-- Uniformity in the lengths permits arbitrary subsequences of prefix sizes. -/
theorem population_ratio_tendsto_one
    (sizes lengths : ℕ → ℕ) (hsizes : Tendsto sizes atTop atTop)
    (beta delta : ℝ) (hdelta : 0 < delta) (hdeltaOne : delta < 1)
    (hupper : ∀ᶠ n in atTop, (lengths n : ℝ) ≤ beta * Real.log (sizes n))
    (hpositive : ∀ᶠ n in atTop, 1 ≤ lengths n) :
    Tendsto (fun n => ((bulkStarts (sizes n) (lengths n) delta).card : ℝ) / sizes n) atTop (𝓝 1) := by
  have ht := (logarithmic_lengths_div_size_tendsto_zero sizes lengths hsizes beta hupper).add
    (lower_endpoint_div_size_tendsto_zero sizes hsizes delta hdeltaOne)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (by simpa only [add_zero] using ht)
  filter_upwards [hsizes.eventually (eventually_ge_atTop 2), hpositive] with n hn hl
  simpa only [Real.norm_eq_abs, add_div] using population_ratio_error_le hn hl hdelta

theorem bulkRate_ratio_eq {M : ℕ} (hM : 0 < M) (L : ℕ) (delta : ℝ) :
    (bulkRate M L delta : ℝ) / (fullRate M L : ℝ) = ((bulkStarts M L delta).card : ℝ) / M := by
  have hp : (0 : ℝ) < M := by exact_mod_cast hM
  change (_ / (2 : ℝ)^L) / ((M : ℝ) / (2 : ℝ)^L) = _
  field_simp

/-- The intensity printed as lambda is asymptotically the exact finite population intensity. -/
theorem bulkRate_ratio_tendsto_one
    (sizes lengths : ℕ → ℕ) (hsizes : Tendsto sizes atTop atTop)
    (beta delta : ℝ) (hdelta : 0 < delta) (hdeltaOne : delta < 1)
    (hupper : ∀ᶠ n in atTop, (lengths n : ℝ) ≤ beta * Real.log (sizes n))
    (hpositive : ∀ᶠ n in atTop, 1 ≤ lengths n) :
    Tendsto (fun n => (bulkRate (sizes n) (lengths n) delta : ℝ) /
      (fullRate (sizes n) (lengths n) : ℝ)) atTop (𝓝 1) := by
  apply (population_ratio_tendsto_one sizes lengths hsizes beta delta hdelta hdeltaOne hupper hpositive).congr'
  filter_upwards [hsizes.eventually (eventually_ge_atTop 1)] with n hn
  exact (bulkRate_ratio_eq (by omega : 0 < sizes n) (lengths n) delta).symm

end
end PaperC.V282.BulkPopulation
