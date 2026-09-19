import PaperCPrel8.RoughPairTailParameter

/-! # The doubled hard-saddle exponent in the rough pair reciprocal sum -/
namespace PaperC.Prel8.RoughPairReciprocalSaddle
open Filter Topology RoughKernelThreshold RoughPairTailParameter RoughKernelSaddle RoughKernelReciprocal
open V282.PrimeEulerPNT V282.SaddleParameters V282.SaddleScales V282.SaddleCutoffAdmissibility
open V282.DefectiveRankinCount V282.PrimeEulerCutoff V282.SaddlePoissonScales
open V282.PrimeEulerSaddle LargeOddKernel
noncomputable section

theorem hard_prefactor (hPNT : PrimeNumberTheoremRemainder) {epsilon : ℝ} (hepsilon : 0<epsilon) :
    ∃ M0 : ℕ, ∀ M ≥ M0, ∀ X ≥ M,
      0<tilt (Real.log M) ∧ tilt (Real.log M)≤1/2 ∧
      (X:ℝ)^(-tilt (Real.log M))*
        rankinEulerProduct ⌊Real.exp (saddleCutoff 1 (Real.log M))⌋₊ (tilt (Real.log M))≤
          Real.exp (-saddleCutoff 1 (Real.log M)+epsilon*saddleNu 1 (Real.log M)) := by
  obtain ⟨c,C,hc,hC,Hband,hband⟩ := saddleCutoff_sqrt_log_band_eventually (by norm_num : (0:ℝ)<1)
  obtain ⟨M0,hM⟩ := enlarged_prefactor hPNT c C epsilon hc hC hepsilon
  have hl : Tendsto (fun M : ℕ ↦ Real.log M) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨M1,h1⟩ := eventually_atTop.mp
    (hl.eventually (eventually_ge_atTop (max Hband (saddleThreshold 1))))
  refine ⟨max M0 M1,?_⟩
  intro M hM0 X hX
  have hh := h1 M (by omega)
  have hb := hband (Real.log M) (by order)
  have hp := hM M (by omega) X hX _ hb.1 hb.2
  have he := saddleCutoff_equation (by norm_num : (0:ℝ)<1) (by order : saddleThreshold 1≤Real.log M)
  simp only [one_mul] at he
  simpa only [tilt,saddleNu,← he] using hp

/-- The tail Euler-product argument is uniformly small for every logarithmic support weight. -/
theorem hard_parameter (beta : ℝ) (hbeta : 0<beta) {epsilon : ℝ} (hepsilon : 0<epsilon) :
    ∃ M0 : ℕ, ∀ M ≥ M0, ∀ z : ℝ, 0≤z → z≤beta*Real.log M →
      0≤tailParameter (saddleCutoff 1 (Real.log M)) z (tilt (Real.log M)) ∧
      tailParameter (saddleCutoff 1 (Real.log M)) z (tilt (Real.log M))≤
        Real.exp (-saddleCutoff 1 (Real.log M)+epsilon*saddleNu 1 (Real.log M)) ∧
      tailParameter (saddleCutoff 1 (Real.log M)) z (tilt (Real.log M))≤1 := by
  have hl : Tendsto (fun M : ℕ ↦ Real.log M) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hp := prefactor_absorption (4*beta) 1 (by positivity) hepsilon
  have ht := V282.PrimeEulerSaddle.tendsto_saddleTilt_zero (by norm_num : (0:ℝ)<1)
  have hv := (tendsto_saddleCutoff_atTop (by norm_num : (0:ℝ)<1)).eventually
    (eventually_ge_atTop (Real.log 4))
  have he := (saddle_exponential_tendsto_zero 1 1 epsilon (by norm_num) (by norm_num)).eventually
    (gt_mem_nhds (by norm_num : (0:ℝ)<1))
  apply eventually_atTop.mp
  filter_upwards [hl.eventually hp,hl.eventually hv,hl.eventually he,
    hl.eventually (ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2))),
    hl.eventually (eventually_ge_atTop (saddleThreshold 1))] with M hp hv he ht hH
  intro z hz hzB
  let H := Real.log (M:ℝ)
  let V := saddleCutoff 1 H
  let u := saddleParameter 1 H
  have hV : 0<V := saddleCutoff_pos (by norm_num) hH
  have hs : 0≤tilt H := (tilt_pos hH).le
  have hsh : tilt H≤1/2 := by
    rw [tilt_eq hH]
    exact ht.le
  have hVu : V*tilt H=u := by
    rw [tilt_eq hH]
    change V*(u/V)=u
    field_simp
  have ht1 : 0<1-tilt H := by linarith
  have hbound := parameter_le hv hz hs hsh
  rw [hVu] at hbound
  have hp' : 4*beta*H*Real.exp u≤Real.exp (epsilon*saddleNu 1 H) := by simpa [H,u] using hp
  have hmul := mul_le_mul_of_nonneg_right hp' (Real.exp_pos (-V)).le
  have ha : tailParameter V z (tilt H)≤Real.exp (-V+epsilon*saddleNu 1 H) := by
    calc
      _ ≤ 4*z*Real.exp (-V+u) := hbound
      _ ≤ 4*(beta*H)*Real.exp (-V+u) := by gcongr
      _ = (4*beta*H*Real.exp u)*Real.exp (-V) := by rw [Real.exp_add]; ring
      _ ≤ Real.exp (epsilon*saddleNu 1 H)*Real.exp (-V) := hmul
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  refine ⟨?_,ha,ha.trans ?_⟩
  · unfold tailParameter
    positivity
  · simpa only [one_mul,neg_mul] using he.le

/-- Literal reciprocal sum, with no unproved rough-host asymptotic premise. -/
theorem hard_reciprocal (hPNT : PrimeNumberTheoremRemainder)
    (beta : ℝ) (hbeta : 0<beta) {epsilon : ℝ} (hepsilon : 0<epsilon) :
    ∃ M0 : ℕ, ∀ M ≥ M0, ∀ X ≥ M, ∀ z : ℝ, 0≤z → z≤beta*Real.log M →
      (∑ m∈(Finset.Icc 1 X).filter (fun m ↦ 1<largeOddKernel
        ⌊Real.exp (saddleCutoff 1 (Real.log M))⌋₊ m),
          z^ArithmeticFunction.cardDistinctFactors (largeOddKernel ⌊Real.exp (saddleCutoff 1 (Real.log M))⌋₊ m)/
            (largeOddKernel ⌊Real.exp (saddleCutoff 1 (Real.log M))⌋₊ m:ℝ))/(X:ℝ)≤
              3*Real.exp (-2*saddleCutoff 1 (Real.log M)+epsilon*saddleNu 1 (Real.log M)) := by
  obtain ⟨Mp,hp⟩ := hard_prefactor hPNT (epsilon:=epsilon/2) (by positivity)
  obtain ⟨Mt,ht⟩ := hard_parameter beta hbeta (epsilon:=epsilon/2) (by positivity)
  have hl : Tendsto (fun M : ℕ ↦ Real.log M) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨My,hy⟩ := eventually_atTop.mp (hl.eventually
    ((tendsto_saddleCutoff_atTop (by norm_num : (0:ℝ)<1)).eventually (eventually_ge_atTop (Real.log 4))))
  refine ⟨max 1 (max Mp (max Mt My)),?_⟩
  intro M hM X hX z hz hzB
  have hp' := hp M (by omega) X hX
  have ht' := ht M (by omega) z hz hzB
  have hY : 1≤⌊Real.exp (saddleCutoff 1 (Real.log M))⌋₊ := by
    have := (floor_exp_bounds (hy M (by omega))).1
    omega
  have hb := literal_normalized_reciprocal_le _ X hY (by omega) hz hp'.2.1
  apply hb.trans
  have he := (exponential_remainder_le ht'.1 ht'.2.2).trans
    (mul_le_mul_of_nonneg_left ht'.2.1 (by norm_num : (0:ℝ)≤3))
  have hh := mul_le_mul hp'.2.2 he
    (sub_nonneg.mpr (Real.one_le_exp ht'.1)) (Real.exp_pos _).le
  apply hh.trans_eq
  rw [mul_left_comm,← Real.exp_add]
  congr 2
  ring

end
end PaperC.Prel8.RoughPairReciprocalSaddle
