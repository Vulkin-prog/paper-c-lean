import PaperCPrel8.MicroscopicNormalization

/-! # Hard-scale monotonicity and bounded changes of logarithmic height

These estimates follow from the defining increasing saddle equation, without
implicit differentiation or a derivative remainder.
-/
namespace PaperC.Prel8.SaddleScaleMonotonicity
open Set Filter Topology
open PaperC.V282.SaddleParameters PaperC.V282.SaddleScales PaperC.V282.SaddleBranch
open PaperC.V282.ExponentialIntegral
noncomputable section

/-- The actual inverse saddle parameter is monotone above its construction threshold. -/
theorem parameter_mono {a H K : ℝ} (ha : 0 < a) (hH : saddleThreshold a ≤ H) (hHK : H ≤ K) :
    saddleParameter a H ≤ saddleParameter a K := by
  have hp := saddleParameter_spec ha hH
  have hq := saddleParameter_spec ha (hH.trans hHK)
  by_contra hn
  have hh := strictMonoOn_saddleHeight ha hq.1 hp.1 (lt_of_not_ge hn)
  rw [hp.2,hq.2] at hh
  linarith

/-- Enlarging height enlarges the cutoff and hence its prime sigma-algebra. -/
theorem cutoff_mono {a H K : ℝ} (ha : 0 < a) (hH : saddleThreshold a ≤ H) (hHK : H ≤ K) :
    saddleCutoff a H ≤ saddleCutoff a K := by
  have hp := saddleParameter_spec ha hH
  have hq := saddleParameter_spec ha (hH.trans hHK)
  have hbase : 1 ≤ saddleParameterBase := by linarith [saddleParameterBase_ge_two]
  exact mul_le_mul_of_nonneg_left
    (strictMonoOn_saddleCostParam.monotoneOn (hbase.trans hp.1) (hbase.trans hq.1)
      (parameter_mono ha hH hHK)) ha.le

/-- The secondary scale also increases with height. -/
theorem nu_mono {a H K : ℝ} (ha : 0 < a) (hH : saddleThreshold a ≤ H) (hHK : H ≤ K) :
    saddleNu a H ≤ saddleNu a K := by
  unfold saddleNu
  rw [div_saddleCutoff_eq_ratio ha hH,div_saddleCutoff_eq_ratio ha (hH.trans hHK)]
  have hp := saddleParameter_spec ha hH
  have hq := saddleParameter_spec ha (hH.trans hHK)
  have hbase : 1 ≤ saddleParameterBase := by linarith [saddleParameterBase_ge_two]
  exact strictMonoOn_saddleRatio.monotoneOn (hbase.trans hp.1) (hbase.trans hq.1)
    (parameter_mono ha hH hHK)

/-- A finite multiplicative bound for nu follows only from cutoff monotonicity. -/
theorem nu_height_ratio_bound {a H K : ℝ} (ha : 0 < a) (hH : saddleThreshold a ≤ H) (hHK : H ≤ K) :
    saddleNu a K ≤ (K/H)*saddleNu a H := by
  have hHp := (saddleThreshold_pos ha).trans_le hH
  have hV := saddleCutoff_pos ha hH
  have hm := cutoff_mono ha hH hHK
  unfold saddleNu
  calc
    K/saddleCutoff a K ≤ K/saddleCutoff a H := div_le_div_of_nonneg_left (hHp.le.trans hHK) hV hm
    _ = _ := by field_simp

/-- Any fixed logarithmic dilation changes nu by at most an arbitrarily small relative amount. -/
theorem nu_shift_bound_eventually (a D delta : ℝ) (ha : 0 < a) (hD : 0 ≤ D) (hdelta : 0 < delta) :
    ∀ᶠ H : ℝ in atTop, saddleNu a H ≤ saddleNu a (H+D) ∧
      saddleNu a (H+D) ≤ (1+delta)*saddleNu a H := by
  filter_upwards [eventually_ge_atTop (max (saddleThreshold a) (D/delta))] with H hH
  have hs := (le_max_left _ _).trans hH
  have hHp := (saddleThreshold_pos ha).trans_le hs
  have hratio : (H+D)/H ≤ 1+delta := by
    apply (div_le_iff₀ hHp).mpr
    have hd := (div_le_iff₀ hdelta).mp ((le_max_right _ _).trans hH)
    nlinarith
  refine ⟨nu_mono ha hs (by linarith), (nu_height_ratio_bound ha hs (by linarith)).trans ?_⟩
  exact mul_le_mul_of_nonneg_right hratio (div_nonneg hHp.le (saddleCutoff_pos ha hs).le)

/-- A bounded logarithmic intensity cost is absorbed by any strict information margin. -/
theorem shifted_information_margin (D B c a : ℝ) (hD : 0 ≤ D) (ha : 0 < a) (hac : a < c) :
    ∀ᶠ H : ℝ in atTop,
      saddleCutoff 1 H-c*saddleNu 1 H+B ≤ saddleCutoff 1 (H+D)-a*saddleNu 1 (H+D) := by
  let delta := (c-a)/(2*a)
  have hd : 0 < delta := by dsimp [delta]; positivity
  have hn := (tendsto_saddleNu_atTop (by norm_num : (0:ℝ)<1)).eventually
    (eventually_ge_atTop (2*B/(c-a)))
  filter_upwards [eventually_ge_atTop (saddleThreshold 1),nu_shift_bound_eventually 1 D delta (by norm_num) hD hd,hn] with H hH hnu hB
  have hV := cutoff_mono (by norm_num : (0:ℝ)<1) hH (show H ≤ H+D by linarith)
  have hm := (div_le_iff₀ (sub_pos.mpr hac)).mp hB
  have he : a*(1+delta)=(a+c)/2 := by dsimp [delta]; field_simp; ring
  have hx := mul_le_mul_of_nonneg_left hnu.2 ha.le
  rw [← mul_assoc,he] at hx
  nlinarith

end
end PaperC.Prel8.SaddleScaleMonotonicity
