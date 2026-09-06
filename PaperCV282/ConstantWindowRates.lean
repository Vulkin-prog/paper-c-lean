import PaperCV282.ConstantWindowBoundary
import PaperCV282.MacroscopicFirstMoment
import PaperCV282.DictionaryCriticalWindow
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Pointwise vanishing of the two constant-window boundary errors

The critical window is centered at the actual length L. Both endpoint
probabilities are O(N^(-1+epsilon)) for every fixed positive epsilon.
No averaged defect bound is substituted at either specified endpoint.
-/

namespace PaperC.V282.ConstantWindowRates

open MeasureTheory InfiniteRademacher ConstantWindowBoundary WindowValues
open MacroscopicGeometry MacroscopicFirstMoment CriticalRunWindow DictionaryCriticalWindow
open InfiniteMassCoupling FiniteFieldTotalVariation Filter Topology

noncomputable section

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

/-- The auxiliary macroscopic interval contains both genuine affine centers. -/
theorem boundary_centers_mem_macroscopic {N x : ℕ} (hN : 4 ≤ N)
    (hlower : N ≤ x) (hupper : x ≤ 2*N) :
    x ∈ macroscopicStarts (4*N) (1/(2 : ℝ)) := by
  rw [mem_macroscopicStarts_iff_real]
  constructor
  · have hn : (4 : ℝ) ≤ N := by exact_mod_cast hN
    have hx : (N : ℝ) ≤ x := by exact_mod_cast hlower
    rw [← Real.sqrt_eq_rpow]
    apply (Real.sqrt_le_iff).mpr
    push_cast
    exact ⟨by positivity,by nlinarith⟩
  · omega

/-- A subpolynomial pointwise bound, with the threshold before length and endpoint. -/
theorem boundary_defects_le_rpow_eventually (C epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ, 1 ≤ L →
      InRunLengthWindow C N L → ∀ x : ℕ, N ≤ x → x ≤ 2*N →
      (2 : ℝ) ^ (defectIndices L x L).card ≤
        (4 : ℝ)^epsilon * (N : ℝ)^epsilon := by
  obtain ⟨Nband,hband⟩ := dictionary_critical_log_band_eventually C
  obtain ⟨Mpoint,hpoint⟩ := two_pow_fullDefects_le_rpow_eventually
    (lowerConstant/2) upperConstant (1/2) epsilon
    (div_pos lowerConstant_pos (by norm_num))
    (by linarith [lowerConstant_pos,lowerConstant_lt_upperConstant])
    (by norm_num) hepsilon
  refine ⟨max 4 (max Nband Mpoint),?_⟩
  intro N hN L hL hwindow x hNx hxN
  have hn4 : 4 ≤ N := by omega
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hone : (1 : ℝ) ≤ (N : ℝ)^(1/(2 : ℝ)) :=
    Real.one_le_rpow (by exact_mod_cast (show 1 ≤ N by omega)) (by norm_num)
  have hwin : |(L : ℝ)-Real.log ((N : ℝ)*1)/Real.log 2|≤C := by
    simpa only [mul_one,InRunLengthWindow] using hwindow
  obtain ⟨hl,hu⟩ := hband N (by omega) 1 le_rfl hone L hwin
  have hlog4 : Real.log (4 : ℝ) ≤ Real.log N :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn4)
  have hlogmul : Real.log (4*N : ℕ)=Real.log 4+Real.log N := by
    push_cast
    exact Real.log_mul (by norm_num) hn.ne'
  have hlow : lowerConstant/2*Real.log (4*N : ℕ) ≤ (L : ℝ) := by
    rw [hlogmul]
    nlinarith [lowerConstant_pos]
  have hupp : (L : ℝ) ≤ upperConstant*Real.log (4*N : ℕ) := by
    rw [hlogmul]
    have hupperpos : 0 < upperConstant := lt_trans lowerConstant_pos lowerConstant_lt_upperConstant
    have h4zero : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
    nlinarith
  have hlen : L-1+1=L := by omega
  have hlenR : ((L-1 : ℕ) : ℝ)+1=(L : ℝ) := by exact_mod_cast hlen
  have hp := hpoint (4*N) (by omega) (L-1)
    (by simpa only [hlenR] using hlow)
    (by simpa only [hlenR] using hupp)
    x (boundary_centers_mem_macroscopic hn4 hNx hxN)
  rw [hlen] at hp
  convert hp using 1
  push_cast
  exact (Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hn.le).symm

/-- The two endpoint windows cost N^(-1+epsilon), uniformly throughout the critical window. -/
theorem boundary_probability_le_rpow_eventually (C epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ, 1 ≤ L → InRunLengthWindow C N L →
      infiniteRademacherMeasure.real (boundaryWindowEvent N L) ≤
        (4 * (4 : ℝ)^epsilon * Real.exp (C*Real.log 2)) * (N : ℝ)^(-1+epsilon) := by
  obtain ⟨Nzero,hzero⟩ := boundary_defects_le_rpow_eventually C epsilon hepsilon
  refine ⟨max Nzero 2,?_⟩
  intro N hN L hL hwindow
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hp1 := hzero N (by omega) L hL hwindow (N+1) (by omega) (by omega)
  have hp2 := hzero N (by omega) L hL hwindow (2*N) (by omega) le_rfl
  have hprob := boundary_probability_le_fullDefects (N := N) (by omega) hL
  have hbound := hprob.trans (div_le_div_of_nonneg_right (add_le_add hp1 hp2) (by positivity))
  have hint : (N : ℝ)/(2 : ℝ)^L ≤ Real.exp (C*Real.log 2) := by
    simpa only [mul_one] using (dictionary_intensity_bounds (m := 1) hn (by norm_num)
      (by simpa only [mul_one,InRunLengthWindow] using hwindow)).2
  have hlen : L-1+1=L := by omega
  have hp : (2 : ℝ)^L=(2 : ℝ)^(L-1)*2 := by rw [← pow_succ,hlen]
  have halg : ((4 : ℝ)^epsilon*(N : ℝ)^epsilon+(4 : ℝ)^epsilon*(N : ℝ)^epsilon) /
      (2 : ℝ)^(L-1) = 4*(4 : ℝ)^epsilon*((N : ℝ)/(2 : ℝ)^L)*
        ((N : ℝ)^epsilon/(N : ℝ)) := by
    rw [hp]
    field_simp
    ring
  have hpower : (N : ℝ)^epsilon/(N : ℝ)=(N : ℝ)^(-1+epsilon) := by
    rw [show -1+epsilon=epsilon-1 by ring,Real.rpow_sub hn,Real.rpow_one]
  rw [halg] at hbound
  calc
    _ ≤ 4*(4 : ℝ)^epsilon*((N : ℝ)/(2 : ℝ)^L)*((N : ℝ)^epsilon/(N : ℝ)) := hbound
    _ ≤ 4*(4 : ℝ)^epsilon*Real.exp (C*Real.log 2)*((N : ℝ)^epsilon/(N : ℝ)) := by
      gcongr
    _ = _ := by rw [hpower]

/-- Therefore the actual boundary error vanishes along every critical length sequence. -/
theorem boundary_probability_tendsto_zero (C : ℝ) (L : ℕ → ℕ)
    (hL : ∀ᶠ N in atTop, 1 ≤ L N)
    (hwindow : ∀ᶠ N in atTop, InRunLengthWindow C N (L N)) :
    Tendsto (fun N => infiniteRademacherMeasure.real (boundaryWindowEvent N (L N))) atTop (𝓝 0) := by
  obtain ⟨Nzero,hzero⟩ := boundary_probability_le_rpow_eventually C (1/2) (by norm_num)
  have ht : Tendsto (fun N : ℕ => (4*(4 : ℝ)^(1/(2 : ℝ))*Real.exp (C*Real.log 2))*
      (N : ℝ)^(-1+(1/(2 : ℝ)))) atTop (𝓝 0) := by
    have hp := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ)<1/2)).comp
      tendsto_natCast_atTop_atTop
    convert hp.const_mul (4*(4 : ℝ)^(1/(2 : ℝ))*Real.exp (C*Real.log 2)) using 1 <;> norm_num
  apply squeeze_zero' (Filter.Eventually.of_forall (fun N => ENNReal.toReal_nonneg)) _ ht
  filter_upwards [eventually_ge_atTop Nzero,hL,hwindow] with N hN hl hw
  exact hzero N hN (L N) hl hw

/-- The complete untruncated source count and the weighted mark count have asymptotically equal laws. -/
theorem constantWindow_cluster_law_distance_tendsto_zero (C : ℝ) (L : ℕ → ℕ)
    (hL : ∀ᶠ N in atTop, 1 ≤ L N)
    (hwindow : ∀ᶠ N in atTop, InRunLengthWindow C N (L N)) :
    Tendsto (fun N => massTotalVariation
      (observableLaw infiniteRademacherMeasure (infiniteConstantWindowCount N (L N)))
      (observableLaw infiniteRademacherMeasure (infiniteExactClusterCount N (L N)))) atTop (𝓝 0) := by
  apply squeeze_zero' (Filter.Eventually.of_forall (fun N => massTotalVariation_nonneg _ _)) _
    (boundary_probability_tendsto_zero C L hL hwindow)
  filter_upwards [eventually_ge_atTop 1,hL] with N hN hl
  exact constantWindow_cluster_law_distance_le_boundary hN hl

end
end PaperC.V282.ConstantWindowRates
