import PaperCV282.SpatialMarkedFieldComparison
import PaperCV282.SaddleErrorExponent

/-!
# The full signed lattice estimate (1.3) in the literal critical window

The natural-number threshold precedes the run length. The distance is for
the actual countable spatial field, with no truncation left in the conclusion.
-/
namespace PaperC.V282.SpatialMarkedCritical

open Filter Topology SpatialMarkedFieldComparison SaddleMarkTruncation SaddleErrorExponent
open SaddleParameters SaddleScales SaddlePoissonScales CriticalRunWindow ExactMarkedRates
open PrimeEulerPNT ProcessAGGInput ConditionalStartProbability AllStartSoftPoisson

noncomputable section

def criticalFieldConstant (C : ℝ) : ℝ := 64*(1+balanceConstant C)^2

theorem criticalFieldConstant_pos (C : ℝ) : 0 < criticalFieldConstant C := by
  have h := balanceConstant_nonneg C
  unfold criticalFieldConstant
  positivity

/-- An explicit uniform bound before absorbing lower-order costs in the exponent. -/
theorem spatial_signed_critical_rate (hAGG : ProcessAGGStatement)
    (hPNT : PrimeNumberTheoremRemainder) (C : ℝ) (hC : 0 ≤ C) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ, InRunLengthWindow C N L →
      spatialSignedDistance N L ≤ criticalFieldConstant C*
        (Real.exp (-saddleCutoff 1 (Real.log N)+saddleNu 1 (Real.log N))+
          (N : ℝ)^(-(1/(6 : ℝ)))) := by
  obtain ⟨Nb,hb⟩ := critical_growing_mark_band_eventually C hC
  have hbeta : lowerConstant < 2*upperConstant := by
    have hu := lowerConstant_pos.trans lowerConstant_lt_upperConstant
    linarith [lowerConstant_lt_upperConstant]
  obtain ⟨Nr,hr⟩ := spatial_signed_full_band hAGG hPNT lowerConstant (2*upperConstant)
    (1/6) 1 lowerConstant_pos hbeta (by norm_num) (by norm_num)
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨Ns,hs⟩ := eventually_atTop.1 (hlog.eventually (eventually_ge_atTop (saddleThreshold 1)))
  refine ⟨max Nb (max Nr (max Ns 2)),?_⟩
  intro N hN L hw
  obtain ⟨_,hlo,hhi,hlam⟩ := hb N (by omega) L hw
  have hbound := hr N (by omega) L (criticalMarkCutoff N) hlo hhi
  have hv := saddleCutoff_pos (a := 1) (by norm_num) (hs N (by omega))
  have hn : 1 ≤ (N : ℝ) := by exact_mod_cast (show 1≤N by omega)
  have hlog0 : 0 ≤ Real.log N := Real.log_nonneg hn
  have hnu : 0 ≤ saddleNu 1 (Real.log N) := by unfold saddleNu; positivity
  let A := Real.exp (-saddleCutoff 1 (Real.log N)+saddleNu 1 (Real.log N))
  let B := (N : ℝ)^(-(1/(6 : ℝ)))
  let lam : ℝ := fullRate N L
  have hlam0 : 0 ≤ lam := (fullRate N L).coe_nonneg
  have hA : 0 ≤ A := Real.exp_nonneg _
  have hB : 0 ≤ B := Real.rpow_nonneg (by positivity) _
  have hpow : (N : ℝ)^(-(1/(2 : ℝ))+1/6) ≤ 1 := by
    exact Real.rpow_le_one_of_one_le_of_nonpos hn (by norm_num)
  have hgeom : 1/(2 : ℝ)^(criticalMarkCutoff N+1) ≤ A :=
    (criticalMarkCutoff_geometric_tail N).trans (Real.exp_le_exp.mpr (by linarith))
  have htail : (lam/(2 : ℝ)^(criticalMarkCutoff N+1))*(2+(N : ℝ)^(-(1/(2 : ℝ))+1/6)) ≤ 3*lam*A := by
    have hmul := mul_le_mul_of_nonneg_left hgeom hlam0
    have hratio : lam/(2 : ℝ)^(criticalMarkCutoff N+1) ≤ lam*A := by simpa only [mul_one_div] using hmul
    calc
      _ ≤ (lam*A)*3 := mul_le_mul hratio (by linarith) (by positivity) (by positivity)
      _ = _ := by ring
  have hf : spatialSignedDistance N L ≤ 32*lam*(1+lam)*(A+B)+3*lam*A := by
    have heq : -(1/(3 : ℝ))+1/6= -(1/(6 : ℝ)) := by norm_num
    unfold exactMarkedRate at hbound
    rw [heq,one_mul] at hbound
    change spatialSignedDistance N L ≤ 32*(lam*(1+lam)*(A+B))+_ at hbound
    nlinarith
  have hcoef : 32*lam*(1+lam)+3*lam ≤ criticalFieldConstant C := by
    have hk := balanceConstant_nonneg C
    change lam ≤ balanceConstant C at hlam
    unfold criticalFieldConstant
    nlinarith
  calc
    _ ≤ (32*lam*(1+lam)+3*lam)*(A+B) := by
      nlinarith [mul_nonneg (by positivity : 0 ≤ 3*lam) hB]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (add_nonneg hA hB)

/-- Equation (1.3), with its uniform o(1) expressed by every smaller exponential coefficient. -/
theorem theorem_one_one_lattice (hAGG : ProcessAGGStatement)
    (hPNT : PrimeNumberTheoremRemainder) (C : ℝ) (hC : 0 ≤ C)
    (a : ℝ) (ha : a < 1/Real.sqrt 2) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ, InRunLengthWindow C N L →
      spatialSignedDistance N L ≤ Real.exp (-a*criticalScale N) := by
  obtain ⟨Nr,hr⟩ := spatial_signed_critical_rate hAGG hPNT C hC
  obtain ⟨Ne,he⟩ := complete_error_le_exponential_eventually (criticalFieldConstant C) (1/6) 1 a
    (criticalFieldConstant_pos C) (by norm_num) (by norm_num) ha
  exact ⟨max Nr Ne,fun N hN L hw => (hr N (by omega) L hw).trans (by simpa only [one_mul] using he N (by omega))⟩

/-- No convergence of the moving intensity is required for the common-lattice comparison. -/
theorem spatial_signed_critical_tendsto_zero (hAGG : ProcessAGGStatement)
    (hPNT : PrimeNumberTheoremRemainder) (C : ℝ) (hC : 0 ≤ C) (L : ℕ → ℕ)
    (hwindow : ∀ᶠ N in atTop, InRunLengthWindow C N (L N)) :
    Tendsto (fun N => spatialSignedDistance N (L N)) atTop (𝓝 0) := by
  obtain ⟨Nr,hr⟩ := spatial_signed_critical_rate hAGG hPNT C hC
  have hlim := (saddle_exponential_nat_tendsto_zero 1 1 1 (by norm_num) (by norm_num)).add
    ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ)<1/6)).comp tendsto_natCast_atTop_atTop)
  have hlim' : Tendsto (fun N : ℕ => criticalFieldConstant C*
      (Real.exp (-saddleCutoff 1 (Real.log N)+saddleNu 1 (Real.log N))+
        (N : ℝ)^(-(1/(6 : ℝ))))) atTop (𝓝 0) := by
    simpa only [one_mul,neg_mul,Function.comp_def,add_zero,mul_zero] using hlim.const_mul (criticalFieldConstant C)
  apply squeeze_zero' (Filter.Eventually.of_forall (fun N => spatialSignedDistance_nonneg N (L N))) _ hlim'
  filter_upwards [hwindow,eventually_ge_atTop Nr] with N hw hN
  exact hr N hN (L N) hw

/-- The lattice comparison applies along any diverging sequence of block sizes.
This is the form needed for the paper's phase-dependent diffuse subsequences. -/
theorem spatial_signed_critical_tendsto_zero_along (hAGG : ProcessAGGStatement)
    (hPNT : PrimeNumberTheoremRemainder) (C : ℝ) (hC : 0 ≤ C)
    (sizes lengths : ℕ → ℕ) (hsizes : Tendsto sizes atTop atTop)
    (hwindow : ∀ᶠ j in atTop, InRunLengthWindow C (sizes j) (lengths j)) :
    Tendsto (fun j => spatialSignedDistance (sizes j) (lengths j)) atTop (𝓝 0) := by
  obtain ⟨Nr,hr⟩ := spatial_signed_critical_rate hAGG hPNT C hC
  have hlim := (saddle_exponential_nat_tendsto_zero 1 1 1 (by norm_num) (by norm_num)).add
    ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ)<1/6)).comp tendsto_natCast_atTop_atTop)
  have hlim' : Tendsto (fun N : ℕ => criticalFieldConstant C*
      (Real.exp (-saddleCutoff 1 (Real.log N)+saddleNu 1 (Real.log N))+
        (N : ℝ)^(-(1/(6 : ℝ))))) atTop (𝓝 0) := by
    simpa only [one_mul,neg_mul,Function.comp_def,add_zero,mul_zero] using hlim.const_mul (criticalFieldConstant C)
  apply squeeze_zero' (Filter.Eventually.of_forall (fun j => spatialSignedDistance_nonneg _ _)) _ (hlim'.comp hsizes)
  filter_upwards [hwindow,hsizes.eventually (eventually_ge_atTop Nr)] with j hw hj
  exact hr (sizes j) hj (lengths j) hw

end
end PaperC.V282.SpatialMarkedCritical
