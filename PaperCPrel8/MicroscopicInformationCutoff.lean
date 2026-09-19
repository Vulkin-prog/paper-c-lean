import PaperCV282.AggregateCutoffRemainder

/-! # The literal information-dependent excess cutoff of 3PREL8

The ceiling is applied to `(I+V+log(2+lambda))/log 2`, rather than to an
information-independent surrogate. All rounding and exponential costs are kept.
-/
namespace PaperC.Prel8.MicroscopicInformationCutoff
open Filter Topology PaperC.V282.SaddleParameters PaperC.V282.SaddleScales
open PaperC.V282.SaddleCutoffAdmissibility PaperC.V282.AggregateCutoffRemainder
noncomputable section

/-- Exact integer cutoff in equation `micro-cutoff`. -/
def excessCutoff (I V lambda : ℝ) : ℕ := ⌈(I+V+Real.log (2+lambda))/Real.log 2⌉₊

/-- The lower ceiling inequality gives the full tail budget without rounding loss. -/
theorem cutoff_exponential_lower (I V : ℝ) {lambda : ℝ} (hlambda : 0 ≤ lambda) :
    Real.exp (I+V)*(2+lambda) ≤ (2:ℝ)^excessCutoff I V lambda := by
  have hlog : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hc := Nat.le_ceil ((I+V+Real.log (2+lambda))/Real.log 2)
  have hh := (div_le_iff₀ hlog).mp hc
  have he := Real.exp_le_exp.mpr hh
  simpa only [excessCutoff,Real.exp_add,Real.exp_log (by linarith : 0 < 2+lambda),
    Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)] using he

/-- The actual conditional bulk tail is at most half the stated exponential budget. -/
theorem cutoff_tail_bound (I V : ℝ) {lambda : ℝ} (hlambda : 0 ≤ lambda) :
    Real.exp I * lambda / (2:ℝ)^(excessCutoff I V lambda+1) ≤ Real.exp (-V)/2 := by
  have hc := cutoff_exponential_lower I V hlambda
  have hv : 0 < Real.exp V := Real.exp_pos V
  have hbase : Real.exp I*lambda ≤ (2:ℝ)^excessCutoff I V lambda / Real.exp V := by
    apply (le_div_iff₀ hv).mpr
    rw [Real.exp_add] at hc
    nlinarith [Real.exp_pos I]
  rw [pow_succ,Real.exp_neg]
  apply (div_le_iff₀ (by positivity : 0 < (2:ℝ)^excessCutoff I V lambda * 2)).mpr
  convert hbase using 1
  ring

/-- The logarithm with `2+lambda` differs by at most log 3 once lambda is at least one. -/
theorem log_two_add_le {lambda : ℝ} (hlambda : 1 ≤ lambda) :
    Real.log (2+lambda) ≤ Real.log lambda + Real.log 3 := by
  have h := Real.log_le_log (by linarith : 0 < 2+lambda) (by linarith : 2+lambda ≤ lambda*3)
  rwa [Real.log_mul (by positivity : lambda ≠ 0) (by norm_num : (3:ℝ) ≠ 0)] at h

/-- Ceiling cost under the weaker information budget; strict second-scale margins are unnecessary here. -/
theorem cutoff_cost_upper {I V lambda : ℝ} (hI : 0 ≤ I) (hlambda : 1 ≤ lambda)
    (hbudget : I+Real.log lambda ≤ V) :
    (excessCutoff I V lambda:ℝ)*Real.log 2 ≤ 2*V+Real.log 3+Real.log 2 := by
  have hlog : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hl := Real.log_nonneg hlambda
  have hV : 0 ≤ V := by linarith
  have ht := Real.log_nonneg (show (1:ℝ) ≤ 2+lambda by linarith)
  have hu := (Nat.ceil_lt_add_one (div_nonneg (by linarith : 0 ≤ I+V+Real.log (2+lambda)) hlog.le)).le
  change (excessCutoff I V lambda:ℝ) ≤ (I+V+Real.log (2+lambda))/Real.log 2+1 at hu
  have hh := mul_le_mul_of_nonneg_right hu hlog.le
  rw [add_mul,div_mul_cancel₀ _ hlog.ne',one_mul] at hh
  linarith [log_two_add_le hlambda]

/-- The exact cost of the enlarged profile is bounded by a fixed multiple of exp(4V). -/
theorem cutoff_profile_cost {I V lambda : ℝ} (hI : 0 ≤ I) (hlambda : 1 ≤ lambda)
    (hbudget : I+Real.log lambda ≤ V) :
    (2:ℝ)^(2*excessCutoff I V lambda+2) ≤ 144*Real.exp (4*V) := by
  have hc := cutoff_cost_upper hI hlambda hbudget
  have hp : (2:ℝ)^(2*excessCutoff I V lambda+2) =
      Real.exp (((2*excessCutoff I V lambda+2:ℕ):ℝ)*Real.log 2) := by
    rw [Real.exp_nat_mul,Real.exp_log (by norm_num)]
  rw [hp]
  calc
    _ ≤ Real.exp (4*V+2*Real.log 3+4*Real.log 2) := Real.exp_le_exp.mpr (by push_cast; linarith)
    _ = _ := by
      simp only [Real.exp_add]
      have h3 : Real.exp (2*Real.log (3:ℝ)) = 9 := by
        have h := Real.exp_nat_mul (Real.log 3) 2
        norm_num [Real.exp_log (by norm_num : (0:ℝ)<3)] at h
        exact h
      have h2 : Real.exp (4*Real.log (2:ℝ)) = 16 := by
        have h := Real.exp_nat_mul (Real.log 2) 4
        norm_num [Real.exp_log (by norm_num : (0:ℝ)<2)] at h
        exact h
      rw [h3,h2]; ring

/-- Uniform subpolynomial profile inflation for the literal varying information cutoff. -/
theorem cutoff_profile_subpolynomial (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ I lambda : ℝ, 0 ≤ I → 1 ≤ lambda →
      I+Real.log lambda ≤ saddleCutoff 1 (Real.log M) →
      (2:ℝ)^(2*excessCutoff I (saddleCutoff 1 (Real.log M)) lambda+2) ≤ (M:ℝ)^epsilon := by
  obtain ⟨Mzero,h⟩ := eventually_atTop.mp
    (constant_exp_saddle_le_power_eventually 144 4 epsilon (by norm_num) hepsilon)
  exact ⟨Mzero,fun M hM I lambda hI hl hb => (cutoff_profile_cost hI hl hb).trans (h M hM)⟩

/-- The exact cutoff is smaller than every positive logarithmic margin, uniformly in information. -/
theorem cutoff_length_small_eventually (delta : ℝ) (hdelta : 0 < delta) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ I lambda : ℝ, 0 ≤ I → 1 ≤ lambda →
      I+Real.log lambda ≤ saddleCutoff 1 (Real.log M) →
      (excessCutoff I (saddleCutoff 1 (Real.log M)) lambda:ℝ)+1 ≤ delta*Real.log M := by
  have hl : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  obtain ⟨Mzero,h⟩ := cutoff_profile_subpolynomial (2*delta*Real.log 2) (by positivity)
  refine ⟨max Mzero 1, ?_⟩
  intro M hM I lambda hI hlam hb
  have hm : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hp := h M (by omega) I lambda hI hlam hb
  have hh := Real.log_le_log (by positivity : (0:ℝ) < 2^(2*excessCutoff I (saddleCutoff 1 (Real.log M)) lambda+2)) hp
  rw [Real.log_pow,Real.log_rpow hm] at hh
  push_cast at hh
  nlinarith

/-- A fixed base logarithmic band expands by any prescribed positive upper margin. -/
theorem shifted_band_eventually (betaMin betaMax delta : ℝ) (hdelta : 0 < delta) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ, ∀ I lambda : ℝ,
      betaMin*Real.log M ≤ (L+1:ℝ) → (L+1:ℝ) ≤ betaMax*Real.log M →
      0 ≤ I → 1 ≤ lambda → I+Real.log lambda ≤ saddleCutoff 1 (Real.log M) →
      betaMin*Real.log M ≤ (L+excessCutoff I (saddleCutoff 1 (Real.log M)) lambda+2:ℝ) ∧
      (L+excessCutoff I (saddleCutoff 1 (Real.log M)) lambda+2:ℝ) ≤ (betaMax+delta)*Real.log M := by
  obtain ⟨Mzero,h⟩ := cutoff_length_small_eventually delta hdelta
  refine ⟨Mzero, ?_⟩
  intro M hM L I lambda hlo hhi hI hlam hb
  have hh := h M hM I lambda hI hlam hb
  have he : (0:ℝ) ≤ excessCutoff I (saddleCutoff 1 (Real.log M)) lambda := Nat.cast_nonneg _
  constructor <;> nlinarith

end
end PaperC.Prel8.MicroscopicInformationCutoff
