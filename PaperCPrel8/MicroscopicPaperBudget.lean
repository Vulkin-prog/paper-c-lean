import PaperCPrel8.MicroscopicProfileBudget

/-! # Transfer from the paper's interior intensity to the ambient intensity

The margin loss is any prescribed positive fraction of the second saddle scale.
The two intensities are never identified: the comparison uses an explicit ratio.
-/
namespace PaperC.Prel8.MicroscopicPaperBudget
open Filter Topology PaperC.V282.SaddleParameters PaperC.V282.SaddleScales
open PaperC.V282.AllStartSoftPoisson
noncomputable section

/-- The paper's actual target intensity `Lambda=(M-L)2^-L`. -/
def siteRate (M L : ℕ) : ℝ := ((M-L:ℕ):ℝ)/(2:ℝ)^L

/-- Every fixed logarithmic length is eventually at most one quarter of the population. -/
theorem logarithmic_length_quarter (beta : ℝ) (_hbeta : 0 < beta) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      (L+1:ℝ) ≤ beta*Real.log M → 4*L ≤ M := by
  have ht := (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
    tendsto_natCast_atTop_atTop).const_mul (4*beta)
  obtain ⟨Mzero,h⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds (by simp : 4*beta*0 < (1:ℝ))))
  refine ⟨max Mzero 1, ?_⟩
  intro M hM L hL
  have hm : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hh : 4*beta*(Real.log M/(M:ℝ)) < 1 := by simpa using h M (by omega)
  have hh' : 4*beta*Real.log M < (M:ℝ) := by
    have := (div_lt_iff₀ hm).mp (show (4*beta*Real.log M)/(M:ℝ)<1 by convert hh using 1; ring)
    linarith
  have hl : 4*(L:ℝ) ≤ M := by linarith
  exact_mod_cast hl

/-- Finite comparison of the two true intensities, with the subtraction still in naturals. -/
theorem siteRate_comparison (M L : ℕ) (hL : 2*L ≤ M) :
    siteRate M L ≤ (fullRate M L:ℝ) ∧ (fullRate M L:ℝ) ≤ 2*siteRate M L := by
  rw [fullRate_coe]
  unfold siteRate
  have hn : (((M-L:ℕ):ℝ)) = (M:ℝ)-L := by exact_mod_cast Nat.cast_sub (show L≤M by omega)
  rw [hn]
  constructor
  · apply div_le_div_of_nonneg_right _ (by positivity)
    have : (0:ℝ) ≤ L := Nat.cast_nonneg L
    linarith
  · have hreal : 2*(L:ℝ) ≤ M := by exact_mod_cast hL
    calc
      _ ≤ (2*((M:ℝ)-L))/(2:ℝ)^L := div_le_div_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by ring

/-- The logarithmic change of intensity costs at most log 2. -/
theorem intensity_log_gap (M L : ℕ) (hL : 2*L ≤ M) (hr : 1 ≤ siteRate M L) :
    Real.log (fullRate M L:ℝ) ≤ Real.log (siteRate M L)+Real.log 2 := by
  obtain ⟨hlo,hhi⟩ := siteRate_comparison M L hL
  have hm : 0 < (fullRate M L:ℝ) := by linarith
  have hs : 0 < siteRate M L := by linarith
  have h := Real.log_le_log hm hhi
  rw [Real.log_mul (by norm_num : (2:ℝ)≠0) hs.ne'] at h
  linarith

/-- Any fixed second-scale margin absorbs the exact intensity change, uniformly in L and I. -/
theorem paper_to_ambient_budget_eventually (beta c c' : ℝ)
    (hbeta : 0 < beta) (hcc : c' < c) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ, ∀ I : ℝ,
      (L+1:ℝ) ≤ beta*Real.log M → 1 ≤ siteRate M L →
      I+Real.log (siteRate M L) ≤ saddleCutoff 1 (Real.log M)-c*saddleNu 1 (Real.log M) →
      1 ≤ (fullRate M L:ℝ) ∧
      I+Real.log (fullRate M L:ℝ) ≤ saddleCutoff 1 (Real.log M)-c'*saddleNu 1 (Real.log M) := by
  obtain ⟨Ml,hl⟩ := logarithmic_length_quarter beta hbeta
  have hlog : Tendsto (fun M : ℕ => Real.log M) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨Mn,hn⟩ := eventually_atTop.mp
    (((tendsto_saddleNu_atTop (by norm_num : (0:ℝ)<1)).comp hlog).eventually
      (eventually_ge_atTop (Real.log 2/(c-c'))))
  refine ⟨max Ml Mn, ?_⟩
  intro M hM L I hL hr hb
  have hlen := hl M (by omega) L hL
  have hcpos : 0 < c-c' := by linarith
  have hnu := (div_le_iff₀ hcpos).mp (hn M (by omega))
  simp only [Function.comp_apply] at hnu
  have hg := intensity_log_gap M L (by omega) hr
  exact ⟨hr.trans (siteRate_comparison M L (by omega)).1, by nlinarith⟩

/-- The literal paper budget supplies the ambient budget required by the cutoff and profile proofs. -/
theorem paper_to_ambient_unmargined (beta c : ℝ) (hbeta : 0 < beta) (hc : 0 < c) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ, ∀ I : ℝ,
      (L+1:ℝ) ≤ beta*Real.log M → 1 ≤ siteRate M L →
      I+Real.log (siteRate M L) ≤ saddleCutoff 1 (Real.log M)-c*saddleNu 1 (Real.log M) →
      1 ≤ (fullRate M L:ℝ) ∧ I+Real.log (fullRate M L:ℝ) ≤ saddleCutoff 1 (Real.log M) := by
  simpa only [zero_mul,sub_zero] using paper_to_ambient_budget_eventually beta c 0 hbeta hc

end
end PaperC.Prel8.MicroscopicPaperBudget
