import PaperCPrel8.RoughKernelThreshold
import PaperCPrel8.RoughKernelDeletion

/-! # Uniform stronger-good-set counts at the literal paper threshold -/
namespace PaperC.Prel8.RoughKernelStrongCount
open RoughKernelThreshold RoughKernelDeletion
open TerminalKernelCount
open V282.SaddleParameters V282.SaddleScales V282.PrimeEulerPNT
open Set Filter Topology
noncomputable section

/-- All support and reciprocal-tilt factors are absorbed at scale nu. -/
theorem polynomial_absorption (beta delta : ℝ) (hbeta : 0 < beta) (hdelta : 0 < delta) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ Q : ℕ, (Q : ℝ) ≤ beta * Real.log M →
      4 * (Q+1 : ℝ) * (1 + Real.log M) ≤ Real.exp (delta * saddleNu 1 (Real.log M)) := by
  let C : ℝ := 8 * (beta+1)
  have hC : 0 < C := by dsimp [C]; positivity
  have hlim : Tendsto (fun H ↦ (Real.log C + 2 * Real.log H) / saddleNu 1 H) atTop (𝓝 0) := by
    have h := ((tendsto_const_nhds (x := Real.log C)).div_atTop
      (tendsto_saddleNu_atTop (by norm_num : (0:ℝ)<1))).add
      ((tendsto_log_div_saddleNu (by norm_num : (0:ℝ)<1)).const_mul 2)
    simpa only [add_div, mul_div_assoc, mul_zero, add_zero] using h
  have hl : Tendsto (fun M : ℕ ↦ Real.log M) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  apply eventually_atTop.mp
  filter_upwards [hl.eventually (hlim.eventually (gt_mem_nhds hdelta)),
    hl.eventually (eventually_ge_atTop (1:ℝ)),
    hl.eventually ((tendsto_saddleNu_atTop (by norm_num : (0:ℝ)<1)).eventually
      (eventually_gt_atTop (0:ℝ)))] with M herr hH hnu
  intro Q hQ
  have hp := (div_le_iff₀ hnu).mp herr.le
  have hq : (Q+1 : ℝ) ≤ (beta+1) * Real.log M := by linarith
  calc
    _ ≤ 4 * ((beta+1)*Real.log M) * (2*Real.log M) := by gcongr; linarith
    _ = C * (Real.log M)^2 := by dsimp [C]; ring
    _ = Real.exp (Real.log C + 2*Real.log (Real.log M)) := by
      rw [two_mul]
      simp only [Real.exp_add, Real.exp_log hC, Real.exp_log (by linarith : 0<Real.log M), pow_two]
    _ ≤ _ := Real.exp_le_exp.mpr hp

/-- Kernel population monotonicity permits a reference height above the ceiling. -/
theorem population_mono {X Z Y T : ℕ} (hXZ : X ≤ Z) :
    boundedLargeKernelValues Y T X ⊆ boundedLargeKernelValues Y T Z := by
  intro n hn
  obtain ⟨h1,hX,hT⟩ := mem_boundedLargeKernelValues.mp hn
  exact mem_boundedLargeKernelValues.mpr ⟨h1,hX.trans hXZ,hT⟩

/-- Fully absorbed actual additional deletion count, uniformly in the original good set. -/
theorem added_count (hPNT : PrimeNumberTheoremRemainder)
    (beta theta epsilon : ℝ) (hbeta : 0 < beta) (htheta : 0 ≤ theta) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ n Q : ℕ,
      M ≤ 2*(n+Q) → Q ≤ n → (Q : ℝ) ≤ beta*Real.log M →
      ∀ G : Finset ℕ, G ⊆ Finset.Icc 1 n →
      ((G \ strongGood G ⌊Real.exp (saddleCutoff 1 (Real.log M))⌋₊ Q
          ⌊threshold theta (Real.log M)⌋₊).card : ℝ) ≤
        n * Real.exp (-saddleCutoff 1 (Real.log M) + (theta+epsilon)*saddleNu 1 (Real.log M)) := by
  obtain ⟨Mc,hc⟩ := RoughKernelSaddle.hard_count hPNT (epsilon/2) (by positivity)
  obtain ⟨Mp,hp⟩ := polynomial_absorption beta (epsilon/2) hbeta (by positivity)
  have hl : Tendsto (fun M : ℕ ↦ Real.log M) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨Mh,hh⟩ := eventually_atTop.mp (hl.eventually (eventually_ge_atTop (saddleThreshold 1)))
  refine ⟨max 1 (max Mc (max Mp Mh)), ?_⟩
  intro M hM n Q hpop hQn hQ G hG
  let H := Real.log (M : ℝ)
  let V := saddleCutoff 1 H
  let nu := saddleNu 1 H
  let Y := ⌊Real.exp V⌋₊
  let T := ⌊threshold theta H⌋₊
  let Z := max M (n+Q)
  have hH : saddleThreshold 1 ≤ H := hh M (by omega)
  have hz : (0:ℝ) < Z := by exact_mod_cast (show 0 < Z by dsimp [Z]; omega)
  have hr := (div_le_iff₀ hz).mp (hc M (by omega) Z (le_max_left _ _) T)
  have hf := threshold_factor hH htheta
  have hbound : ((boundedLargeKernelValues Y T Z).card : ℝ) ≤
      Real.exp (-V+(epsilon/2)*nu) * ((1+H)*Real.exp (theta*nu)) * Z := by
    apply hr.trans
    apply mul_le_mul_of_nonneg_right _ hz.le
    exact mul_le_mul_of_nonneg_left hf (Real.exp_pos _).le
  have hmono : ((boundedLargeKernelValues Y T (n+Q)).card : ℝ) ≤
      ((boundedLargeKernelValues Y T Z).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (population_mono (le_max_right M (n+Q)))
  have hzle : (Z:ℝ) ≤ 4*n := by exact_mod_cast (show Z ≤ 4*n by dsimp [Z]; omega)
  have hpoly := hp M (by omega) Q hQ
  have hcard : ((G \ strongGood G Y Q T).card : ℝ) ≤
      (Q+1:ℝ) * ((boundedLargeKernelValues Y T (n+Q)).card : ℝ) := by
    exact_mod_cast added_deletion_card_le G n Y Q T hG
  calc
    _ ≤ (Q+1:ℝ) * ((boundedLargeKernelValues Y T Z).card : ℝ) :=
      hcard.trans (mul_le_mul_of_nonneg_left hmono (by positivity))
    _ ≤ (Q+1:ℝ) * (Real.exp (-V+(epsilon/2)*nu) * ((1+H)*Real.exp (theta*nu)) * Z) := by gcongr
    _ ≤ (Q+1:ℝ) * (Real.exp (-V+(epsilon/2)*nu) * ((1+H)*Real.exp (theta*nu)) * (4*n)) := by
      have : 0 ≤ H := (saddleThreshold_pos (by norm_num : (0:ℝ)<1)).le.trans hH
      gcongr
    _ = n * (4*(Q+1:ℝ)*(1+H)) * Real.exp (-V+(epsilon/2)*nu) * Real.exp (theta*nu) := by ring
    _ ≤ n * Real.exp ((epsilon/2)*nu) * Real.exp (-V+(epsilon/2)*nu) * Real.exp (theta*nu) := by gcongr
    _ = _ := by simp only [mul_assoc, ← Real.exp_add]; congr 2; ring

end
end PaperC.Prel8.RoughKernelStrongCount
