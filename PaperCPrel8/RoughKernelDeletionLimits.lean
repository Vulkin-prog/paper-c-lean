import PaperCPrel8.RoughKernelGoodSet
import PaperCPrel8.MicroscopicDiscardRates

/-! # Vanishing mass and density of the literal stronger deletion

The hypotheses below are geometric and numerical regime assumptions, not
bounds on an unknown arithmetic error. The actual deleted populations occur
on the left-hand sides.
-/
namespace PaperC.Prel8.RoughKernelDeletionLimits
open RoughKernelThreshold RoughKernelDeletion RoughKernelStrongCount RoughKernelGoodSet
open V282.SaddleParameters V282.SaddleScales V282.SaddlePoissonScales V282.PrimeEulerPNT
open Set Filter Topology
noncomputable section

/-- Under the information margin, extra deletion mass has a uniform exponential saving. -/
theorem added_mass_bound (hPNT : PrimeNumberTheoremRemainder)
    (beta theta c : ℝ) (hbeta : 0 < beta) (htheta : 0 ≤ theta) (htc : theta < c) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ n Q : ℕ,
      M ≤ 2*(n+Q) → Q ≤ n → (Q : ℝ) ≤ beta*Real.log M →
      ∀ G : Finset ℕ, G ⊆ Finset.Icc 1 n → ∀ p : ℝ, 0 ≤ p →
      p*n ≤ Real.exp (saddleCutoff 1 (Real.log M)-c*saddleNu 1 (Real.log M)) →
      p * ((G \ strongGood G ⌊Real.exp (saddleCutoff 1 (Real.log M))⌋₊ Q
          ⌊threshold theta (Real.log M)⌋₊).card : ℝ) ≤
        Real.exp (-((c-theta)/2)*saddleNu 1 (Real.log M)) := by
  obtain ⟨Mc,hc⟩ := added_count hPNT beta theta ((c-theta)/2) hbeta htheta (by linarith)
  refine ⟨Mc, ?_⟩
  intro M hM n Q hpop hqn hq G hg p hp hi
  have hh := mul_le_mul_of_nonneg_left (hc M hM n Q hpop hqn hq G hg) hp
  calc
    _ ≤ p * (n * Real.exp (-saddleCutoff 1 (Real.log M)+
        (theta+(c-theta)/2)*saddleNu 1 (Real.log M))) := hh
    _ = (p*n) * Real.exp (-saddleCutoff 1 (Real.log M)+
        (theta+(c-theta)/2)*saddleNu 1 (Real.log M)) := by ring
    _ ≤ Real.exp (saddleCutoff 1 (Real.log M)-c*saddleNu 1 (Real.log M)) *
        Real.exp (-saddleCutoff 1 (Real.log M)+(theta+(c-theta)/2)*saddleNu 1 (Real.log M)) := by gcongr
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- The paper's logarithmic information budget implies the preceding intensity premise. -/
theorem intensity_of_budget {p n I V c nu : ℝ} (hp : 0 < p*n) (hI : 0 ≤ I)
    (h : Real.log (p*n) + I ≤ V-c*nu) : p*n ≤ Real.exp (V-c*nu) := by
  rw [← Real.exp_log hp]
  exact Real.exp_le_exp.mpr (by linarith)

/-- Actual additional deletion mass tends to zero for every admissible sequence. -/
theorem added_mass_tendsto (hPNT : PrimeNumberTheoremRemainder)
    (beta theta c : ℝ) (hbeta : 0 < beta) (htheta : 0 ≤ theta) (htc : theta < c)
    (n Q : ℕ → ℕ) (G : ℕ → Finset ℕ) (p : ℕ → ℝ)
    (hregime : ∀ᶠ M in atTop, M ≤ 2*(n M+Q M) ∧ Q M ≤ n M ∧
      (Q M : ℝ) ≤ beta*Real.log M ∧ G M ⊆ Finset.Icc 1 (n M) ∧ 0 ≤ p M ∧
      p M*n M ≤ Real.exp (saddleCutoff 1 (Real.log M)-c*saddleNu 1 (Real.log M))) :
    Tendsto (fun M ↦ p M * ((G M \ strongGood (G M)
      ⌊Real.exp (saddleCutoff 1 (Real.log M))⌋₊ (Q M) ⌊threshold theta (Real.log M)⌋₊).card : ℝ))
      atTop (𝓝 0) := by
  obtain ⟨Mc,hc⟩ := added_mass_bound hPNT beta theta c hbeta htheta htc
  have hl : Tendsto (fun M : ℕ ↦ Real.log M) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have he := Real.tendsto_exp_atBot.comp
    (((tendsto_saddleNu_atTop (by norm_num : (0:ℝ)<1)).comp hl).const_mul_atTop_of_neg
      (show -((c-theta)/2) < 0 by linarith))
  apply squeeze_zero' _ _ he
  · filter_upwards [hregime] with M h
    exact mul_nonneg h.2.2.2.2.1 (Nat.cast_nonneg _)
  · filter_upwards [hregime,eventually_ge_atTop Mc] with M h hm
    exact hc M hm (n M) (Q M) h.1 h.2.1 h.2.2.1 (G M) h.2.2.2.1 (p M) h.2.2.2.2.1 h.2.2.2.2.2

/-- Multiplication by H still leaves every fixed saddle exponential vanishing. -/
theorem height_exponential_tendsto (eta : ℝ) :
    Tendsto (fun H ↦ H * Real.exp (-saddleCutoff 1 H+eta*saddleNu 1 H)) atTop (𝓝 0) := by
  apply squeeze_zero'
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with H hH
    positivity
  · filter_upwards [(tendsto_log_div_saddleNu (by norm_num : (0:ℝ)<1)).eventually
      (gt_mem_nhds (by norm_num : (0:ℝ)<1)),
      (tendsto_saddleNu_atTop (by norm_num : (0:ℝ)<1)).eventually (eventually_gt_atTop (0:ℝ)),
      eventually_gt_atTop (0:ℝ)] with H he hn hH
    have hh := (div_lt_iff₀ hn).mp he
    calc
      _ = Real.exp (Real.log H + (-saddleCutoff 1 H+eta*saddleNu 1 H)) := by
        simp only [Real.exp_add,Real.exp_log hH]
      _ ≤ Real.exp (-saddleCutoff 1 H+(eta+1)*saddleNu 1 H) :=
        Real.exp_le_exp.mpr (by linarith)
  · simpa only [neg_mul,one_mul] using saddle_exponential_tendsto_zero 1 1 (eta+1) (by norm_num) (by norm_num)

/-- The exact rounded shallow prefix is negligible even after multiplication by log M. -/
theorem shallow_density_tendsto :
    Tendsto (fun M : ℕ ↦ (⌈Real.sqrt M⌉₊ : ℝ)/(M:ℝ)*Real.log M) atTop (𝓝 0) := by
  have hlim := ((isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/2)).tendsto_div_nhds_zero).comp
    tendsto_natCast_atTop_atTop
  have he : Tendsto (fun M : ℕ ↦ 2*(M:ℝ)^(-(1/(2:ℝ)))*Real.log M) atTop (𝓝 0) := by
    convert hlim.const_mul 2 using 1
    · ext M
      dsimp only [Function.comp_def]
      rw [Real.rpow_neg (Nat.cast_nonneg M)]
      ring
    · norm_num
  apply squeeze_zero' _ _ he
  · filter_upwards [eventually_ge_atTop 1] with M hM
    exact mul_nonneg (by positivity) (Real.log_nonneg (by exact_mod_cast hM))
  · filter_upwards [eventually_ge_atTop 1] with M hM
    exact mul_le_mul_of_nonneg_right (MicroscopicDiscardRates.rounded_sqrt_ratio M hM)
      (Real.log_nonneg (by exact_mod_cast hM))

/-- The actual total omitted set is o(M/log M), in the literal maximal-support geometry. -/
theorem total_density_tendsto (hPNT : PrimeNumberTheoremRemainder)
    (beta theta : ℝ) (hbeta : 0 < beta) (htheta : 0 ≤ theta)
    (n L E : ℕ → ℕ)
    (hregime : ∀ᶠ M in atTop, n M ≤ M ∧ M ≤ 2*(n M+(L M+E M+1)) ∧
      L M+E M+1 ≤ n M ∧ (L M+E M+1:ℝ) ≤ beta*Real.log M) :
    Tendsto (fun M ↦ (((Finset.Icc 1 (n M)) \ paperGood M (n M) (L M) (E M)
      ⌊Real.exp (saddleCutoff 1 (Real.log M))⌋₊ ⌊threshold theta (Real.log M)⌋₊).card : ℝ) /
      (M:ℝ) * Real.log M) atTop (𝓝 0) := by
  obtain ⟨Mc,hc⟩ := total_count hPNT beta theta 1 hbeta htheta (by norm_num)
  have hl : Tendsto (fun M : ℕ ↦ Real.log M) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hb := shallow_density_tendsto.add ((height_exponential_tendsto (theta+1)).comp hl)
  simp only [add_zero] at hb
  apply squeeze_zero' _ _ hb
  · filter_upwards [eventually_ge_atTop 1] with M hM
    exact mul_nonneg (by positivity) (Real.log_nonneg (by exact_mod_cast hM))
  · filter_upwards [hregime,eventually_ge_atTop (max Mc 1)] with M h hM
    have hm : (0:ℝ)<M := by exact_mod_cast (show 0<M by omega)
    have hh := hc M (by omega) (n M) (L M) (E M) h.2.1 h.2.2.1 h.2.2.2
    have hn : (n M:ℝ) ≤ M := by exact_mod_cast h.1
    have hh' := hh.trans (add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hn (Real.exp_pos _).le))
    have hmul := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hh' hm.le)
      (Real.log_nonneg (show (1:ℝ)≤M by exact_mod_cast (show 1≤M by omega)))
    convert hmul using 1; dsimp only [Function.comp_def]; field_simp [hm.ne']

end
end PaperC.Prel8.RoughKernelDeletionLimits
