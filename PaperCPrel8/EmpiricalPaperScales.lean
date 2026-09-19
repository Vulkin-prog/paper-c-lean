import PaperCPrel8.EmpiricalScaleBounds
import PaperCPrel8.MicroscopicNormalization

/-! # Literal dyadic scales of the empirical Poisson corollary

Natural subtraction gives a harmless definition at the finitely many initial
indices. The theorems below establish when it agrees with the paper's integer
subtraction and when all windows lie inside the prefix.
-/
namespace PaperC.Prel8.EmpiricalPaperScales
open Filter Topology
open PaperC.V282.PrimeEulerSaddle
open PaperC.V282.SaddleParameters PaperC.V282.SaddleScales
open PaperC.V282.SaddleCutoffAdmissibility PaperC.V282.SaddlePoissonScales
open PaperC.V282.GeometricSaddleSummability
open PaperC.Prel8.EmpiricalScaleBounds PaperC.Prel8.MicroscopicNormalization
open PaperC.Prel8.MicroscopicPaperBudget
noncomputable section

def size (k : ℕ) : ℕ := 2^k
def cutoff (k : ℕ) : ℝ := saddleCutoff 1 (Real.log (size k))
def depth (alpha : ℝ) (k : ℕ) : ℕ := ⌊alpha*cutoff k/Real.log 2⌋₊
def length (alpha : ℝ) (k : ℕ) : ℕ := k-depth alpha k
def sites (alpha : ℝ) (k : ℕ) : ℕ := size k-length alpha k
def windowSize (alpha tau : ℝ) (k : ℕ) : ℕ := ⌊tau*(2:ℝ)^(length alpha k)⌋₊
def origins (alpha tau : ℝ) (k : ℕ) : ℕ := sites alpha k-windowSize alpha tau k+1

/-- The exact logarithmic height, without a rounding error. -/
theorem log_size (k : ℕ) : Real.log (size k) = (k:ℝ)*Real.log 2 := by
  simp [size, Real.log_pow]

/-- Literal dyadic heights tend to infinity. -/
theorem size_tendsto : Tendsto size atTop atTop :=
  tendsto_pow_atTop_atTop_of_one_lt (by norm_num)

/-- The actual hard saddle grows without bound on these heights. -/
theorem cutoff_tendsto : Tendsto cutoff atTop atTop :=
  (tendsto_saddleCutoff_atTop (by norm_num : (0:ℝ)<1)).comp
    (log_sizes_tendsto_atTop dyadic_geometric_growth)

/-- Rounding the microscopic depth preserves its o(log M) property. -/
theorem rounded_depth_small (alpha : ℝ) (ha : 0 ≤ alpha) :
    Tendsto (fun M : ℕ => (⌊alpha*saddleCutoff 1 (Real.log M)/Real.log 2⌋₊:ℝ)/Real.log M)
      atTop (𝓝 0) := by
  have hlog : Tendsto (fun M : ℕ => Real.log M) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hv := (tendsto_saddleCutoff_div_height (by norm_num : (0:ℝ)<1)).comp hlog
  have ht : Tendsto (fun M : ℕ => (alpha/Real.log 2)*(saddleCutoff 1 (Real.log M)/Real.log M))
      atTop (𝓝 0) := by simpa using hv.const_mul (alpha/Real.log 2)
  apply squeeze_zero' ?_ ?_ ht
  · filter_upwards [hlog.eventually (eventually_gt_atTop (0:ℝ))] with M hM
    positivity
  · filter_upwards [hlog.eventually (eventually_gt_atTop (0:ℝ)),
      ((tendsto_saddleCutoff_atTop (by norm_num : (0:ℝ)<1)).comp hlog).eventually
        (eventually_ge_atTop (0:ℝ))] with M hM hV
    have hf := Nat.floor_le (by positivity : 0 ≤ alpha*saddleCutoff 1 (Real.log M)/Real.log 2)
    apply (div_le_div_of_nonneg_right hf hM.le).trans_eq
    ring

/-- Literal lengths satisfy the same fixed logarithmic band as 7.7. -/
theorem length_band (alpha : ℝ) (ha : 0 ≤ alpha) :
    ∀ᶠ k in atTop, depth alpha k ≤ k ∧
      (1/(2*Real.log 2))*Real.log (size k) ≤ (length alpha k+1:ℝ) ∧
      (length alpha k+1:ℝ) ≤ (2/Real.log 2)*Real.log (size k) := by
  have hb := size_tendsto.eventually
    (paper_length_band (fun M => ⌊alpha*saddleCutoff 1 (Real.log M)/Real.log 2⌋₊)
      (rounded_depth_small alpha ha))
  have he (k : ℕ) : ⌊Real.log (size k)/Real.log 2⌋₊ = k := by
    rw [log_size, mul_div_cancel_right₀ _ (ne_of_gt (Real.log_pos (by norm_num)))]
    exact Nat.floor_natCast k
  simpa only [paperLength,he,length,depth,cutoff] using hb

/-- The literal base lengths tend to infinity. -/
theorem length_tendsto (alpha : ℝ) (ha : 0 ≤ alpha) :
    Tendsto (length alpha) atTop atTop := by
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hh : Tendsto (fun k : ℕ => (1/(2*Real.log 2))*Real.log (size k)-1) atTop atTop :=
    by simpa only [sub_eq_add_neg,size] using
      tendsto_atTop_add_const_right atTop (-1:ℝ)
        ((log_sizes_tendsto_atTop dyadic_geometric_growth).const_mul_atTop
          (by positivity : 0 < 1/(2*Real.log 2)))
  have hl : Tendsto (fun k => (length alpha k:ℝ)) atTop atTop :=
    tendsto_atTop_mono' atTop ((length_band alpha ha).mono (fun k hk => by linarith [hk.2.1])) hh
  exact tendsto_natCast_atTop_iff.mp hl

/-- Base windows occupy at most one quarter of the prefix eventually. -/
theorem length_quarter (alpha : ℝ) (ha : 0 ≤ alpha) :
    ∀ᶠ k in atTop, 4*length alpha k ≤ size k := by
  obtain ⟨Mzero,hM⟩ := logarithmic_length_quarter (2/Real.log 2) (by positivity)
  filter_upwards [size_tendsto.eventually (eventually_ge_atTop Mzero),length_band alpha ha] with k hk hb
  exact hM _ hk _ hb.2.2

/-- Natural origin counts are positive at every index, so all empirical masses normalize. -/
theorem origins_pos (alpha tau : ℝ) (k : ℕ) : 0 < origins alpha tau k := by
  unfold origins
  omega

/-- The rounded depth controls the exact dyadic rate between two fixed constants. -/
theorem rounded_intensity_bounds (alpha : ℝ) {k : ℕ} (haV : 0 ≤ alpha*cutoff k) :
    Real.exp (alpha*cutoff k)/2 ≤ (2:ℝ)^(depth alpha k) ∧
      (2:ℝ)^(depth alpha k) ≤ Real.exp (alpha*cutoff k) := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hf := Nat.floor_le (div_nonneg haV hl.le)
  have hr := Nat.lt_floor_add_one (alpha*cutoff k/Real.log 2)
  have hlow : alpha*cutoff k-Real.log 2 ≤ (depth alpha k:ℝ)*Real.log 2 := by
    have := (div_lt_iff₀ hl).mp hr
    change alpha*cutoff k < ((depth alpha k:ℝ)+1)*Real.log 2 at this
    linarith
  have hhi : (depth alpha k:ℝ)*Real.log 2 ≤ alpha*cutoff k := (le_div_iff₀ hl).mp hf
  have he : Real.exp ((depth alpha k:ℝ)*Real.log 2) = (2:ℝ)^(depth alpha k) := by
    rw [Real.exp_nat_mul,Real.exp_log (by norm_num)]
  constructor
  · have := Real.exp_le_exp.mpr hlow
    rwa [Real.exp_sub,Real.exp_log (by norm_num),he] at this
  · simpa only [he] using Real.exp_le_exp.mpr hhi

/-- The height/base-rate ratio equals the exact power of the rounded depth. -/
theorem dyadic_rate_identity (alpha : ℝ) {k : ℕ} (hd : depth alpha k ≤ k) :
    (size k:ℝ)/(2:ℝ)^(length alpha k) = (2:ℝ)^(depth alpha k) := by
  have he : length alpha k+depth alpha k=k := Nat.sub_add_cancel hd
  have hp : (size k:ℝ) = (2:ℝ)^(length alpha k)*(2:ℝ)^(depth alpha k) := by
    rw [← pow_add,he]
    simp [size]
  rw [hp]
  field_simp

/-- The literal site rate vanishes, which will identify the rounded window mean. -/
theorem site_probability_tendsto (alpha : ℝ) (ha : 0 ≤ alpha) :
    Tendsto (fun k => (1:ℝ)/(2:ℝ)^(length alpha k)) atTop (𝓝 0) := by
  simpa only [one_div, inv_pow,Function.comp_def] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤(2:ℝ)⁻¹)
      (by norm_num : (2:ℝ)⁻¹<1)).comp (length_tendsto alpha ha)

/-- The paper's rounded windows have the exact limiting mean tau. -/
theorem window_mean_tendsto (alpha tau : ℝ) (ha : 0 ≤ alpha) (ht : 0 ≤ tau) :
    Tendsto (fun k => (windowSize alpha tau k:ℝ)*((1:ℝ)/2^(length alpha k)))
      atTop (𝓝 tau) := by
  have h := floor_window_mean_tendsto tau ht (fun k => (1:ℝ)/2^(length alpha k))
    (fun k => by positivity) (site_probability_tendsto alpha ha)
  simpa [windowSize,div_div] using h

end
end PaperC.Prel8.EmpiricalPaperScales
