import PaperCV282.ExactMarkedRates
import PaperCV282.DictionaryCriticalWindow
import PaperCV282.SaddlePoissonScales

/-!
# Vanishing finite-mark errors in the literal critical run window

Every fixed truncation is covered by the full-band theorem. This permits a
rigorous two-stage removal of tails for the scalar compound-Poisson law.
-/
namespace PaperC.V282.ExactMarkedCritical

open Filter Topology CriticalRunWindow ExactMarkedRates ExactMarkedFieldBounds
open PrimeEulerPNT ProcessAGGInput AllStartSoftPoisson SaddlePoissonScales SaddleParameters SaddleScales
open ConditionalStartProbability HardPoissonRates

noncomputable section

/-- A fixed excess enlargement stays inside a single logarithmic band. -/
theorem fixed_mark_band_eventually (C : ℝ) (hC : 0 ≤ C) (E : ℕ) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ, InRunLengthWindow C N L →
      1 ≤ L ∧ lowerConstant*Real.log N ≤ (L+1 : ℝ) ∧
      (L+E+2 : ℝ) ≤ (2*upperConstant)*Real.log N ∧
      (fullRate N L : ℝ) ≤ balanceConstant C := by
  obtain ⟨Nb,hb⟩ := firstMomentWindow_eventually hC
  have hu : 0 < upperConstant := lowerConstant_pos.trans lowerConstant_lt_upperConstant
  have ht : Tendsto (fun N : ℕ => upperConstant*Real.log N) atTop atTop :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hu
  obtain ⟨Ne,he⟩ := eventually_atTop.1 (ht.eventually (eventually_ge_atTop (E+1 : ℝ)))
  refine ⟨max Nb Ne,?_⟩
  intro N hN L hw
  obtain ⟨hband,hL,hint⟩ := hb N (by omega) L hw
  have hlow := hband.2.2.1
  have hhigh := hband.2.2.2
  have hE := he N (by omega)
  refine ⟨hL,by exact_mod_cast hlow,?_,?_⟩
  · push_cast at hhigh ⊢
    nlinarith
  · simpa only [fullRate_coe] using hint

/-- For every fixed mark truncation the complete signed source field approaches its exact target. -/
theorem exact_signed_fixed_truncation_tendsto_zero (hAGG : ProcessAGGStatement)
    (hPNT : PrimeNumberTheoremRemainder) (C : ℝ) (hC : 0 ≤ C)
    (L : ℕ → ℕ) (hwindow : ∀ᶠ N in atTop, InRunLengthWindow C N (L N)) (E : ℕ) :
    Tendsto (fun N => exactSignedDistance N (L N) E (dyadicBlock N)) atTop (𝓝 0) := by
  obtain ⟨Nb,hb⟩ := fixed_mark_band_eventually C hC E
  have hbeta : lowerConstant < 2*upperConstant := by
    have hu := lowerConstant_pos.trans lowerConstant_lt_upperConstant
    linarith [lowerConstant_lt_upperConstant]
  obtain ⟨Nr,hr⟩ := theorem_five_six_signed_full_band hAGG hPNT lowerConstant (2*upperConstant)
    (1/6) 1 lowerConstant_pos hbeta (by norm_num) (by norm_num)
  let err : ℕ → ℝ := fun N => Real.exp (-saddleCutoff 1 (Real.log N)+saddleNu 1 (Real.log N))+
    (N : ℝ)^(-(1/(6 : ℝ)))
  have he : Tendsto err atTop (𝓝 0) := by
    have hx := saddle_exponential_nat_tendsto_zero 1 1 1 (by norm_num) (by norm_num)
    have hp := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ)<1/6)).comp tendsto_natCast_atTop_atTop
    simpa only [one_mul,neg_mul,Function.comp_def,add_zero,err] using hx.add hp
  have ht : Tendsto (fun N => 32*balanceConstant C*(1+balanceConstant C)*err N) atTop (𝓝 0) := by
    simpa using he.const_mul (32*balanceConstant C*(1+balanceConstant C))
  apply squeeze_zero' (Filter.Eventually.of_forall (fun N => exactSignedDistance_nonneg _ _ _ _)) _ ht
  filter_upwards [hwindow,eventually_ge_atTop (max Nb Nr)] with N hw hN
  obtain ⟨_,hlo,hhi,hint⟩ := hb N (by omega) (L N) hw
  have hf := (hr N (by omega) (L N) E hlo hhi).2.2
  have hcoef : (fullRate N (L N) : ℝ)*(1+(fullRate N (L N) : ℝ)) ≤
      balanceConstant C*(1+balanceConstant C) := by
    have hl : 0 ≤ (fullRate N (L N) : ℝ) := by positivity
    have hk := balanceConstant_nonneg C
    nlinarith
  have he0 : 0 ≤ err N := by dsimp [err]; positivity
  have hn : -(1/(3 : ℝ))+1/6 = -(1/(6 : ℝ)) := by norm_num
  unfold exactMarkedRate at hf
  rw [hn,one_mul] at hf
  change _ ≤ 32*(((fullRate N (L N) : ℝ)*(1+(fullRate N (L N) : ℝ)))*err N) at hf
  exact hf.trans (by nlinarith [mul_le_mul_of_nonneg_right hcoef he0])

end
end PaperC.V282.ExactMarkedCritical
