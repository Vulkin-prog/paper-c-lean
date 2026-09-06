import PaperCV282.SignOverlap
import PaperCV282.DictionaryFieldRates
import PaperCV282.DictionaryCriticalWindow

/-!
# Corollary 5.5 before the final scalar pushforward

The actual two-word field has the stated three-term error throughout the
literal window centered at log_2 N. All thresholds precede the word.
-/

namespace PaperC.V282.SignPatternRates

open SignDictionary SignOverlap DictionaryFieldRates DictionaryFieldInfinite
open DictionaryFieldModel DictionaryCriticalWindow DictionaryProfileNormalization
open DictionaryErrorLedger CriticalRunWindow PrimeEulerPNT ProcessAGGInput
open HardPoissonRates SaddleParameters SaddleScales SaddlePoissonScales
open Filter Topology

noncomputable section

/-- A fixed coefficient for each of the three errors at bounded intensity. -/
def signPatternCoefficient (K : ℝ) : ℝ :=
  K + K*(1+K) + (K+K^(11/(6 : ℝ))+K^(4/(3 : ℝ)))*(2 : ℝ)^(2/(3 : ℝ))

/-- The displayed right-hand side of (5.10), with a quantified exponential remainder. -/
def signPatternError {L : ℕ} (N : ℕ) (a : Fin (L+1) → F₂) (epsilon eta : ℝ) : ℝ :=
  theta a + Real.exp (-saddleCutoff 1 (Real.log N)+eta*saddleNu 1 (Real.log N)) +
    (N : ℝ)^(-(1/(3 : ℝ))+epsilon)

theorem signPatternCoefficient_nonneg {K : ℝ} (hK : 0 ≤ K) :
    0 ≤ signPatternCoefficient K := by
  unfold signPatternCoefficient
  positivity

/-- The two word probabilities add to the actual common-sign marginal. -/
theorem sign_dictionaryRate (L : ℕ) (a : Fin (L+1) → F₂) :
    (dictionaryRate L (signDictionary a) : ℝ) = 1/(2 : ℝ)^L := by
  rw [dictionaryRate_coe,card_signDictionary (by omega),pow_succ]
  norm_num only [Nat.cast_ofNat]
  field_simp

/-- The sign-word window is exactly the two-word dictionary window. -/
theorem sign_window_eq {N : ℕ} (hN : 0 < N) (L : ℕ) :
    |((L+1 : ℕ) : ℝ)-Real.log ((N : ℝ)*2)/Real.log 2| =
      |(L : ℝ)-Real.log N/Real.log 2| := by
  congr 1
  rw [Real.log_mul (by exact_mod_cast Nat.ne_of_gt hN) (by norm_num)]
  push_cast
  field_simp
  ring

/-- Keeping m=2 fixed leaves the original N^(-1/3+epsilon) exponent intact. -/
theorem sign_dictionary_error_le {N L : ℕ} (a : Fin (L+1) → F₂)
    {K : ℝ} (hK : (N : ℝ)*(dictionaryRate L (signDictionary a) : ℝ) ≤ K)
    (epsilon eta : ℝ) :
    dictionaryFieldRate N L (signDictionary a) epsilon eta ≤
      signPatternCoefficient K * signPatternError N a epsilon eta := by
  let lam : ℝ := (N : ℝ)*(dictionaryRate L (signDictionary a) : ℝ)
  have hlam : 0 ≤ lam := by dsimp [lam]; positivity
  have hk : 0 ≤ K := hlam.trans hK
  have ht := theta_nonneg a
  have he := Real.exp_nonneg (-saddleCutoff 1 (Real.log N)+eta*saddleNu 1 (Real.log N))
  have hn := Real.rpow_nonneg (show (0 : ℝ) ≤ N by positivity) (-(1/(3 : ℝ))+epsilon)
  have hpoly := dictionary_profile_le_card_power hlam hK (show (1 : ℝ) ≤ 2 by norm_num)
  have htbound := mul_le_mul_of_nonneg_right hK ht
  have helam : lam*(1+lam) ≤ K*(1+K) := by nlinarith
  have hebound := mul_le_mul_of_nonneg_right helam he
  have hnbound := mul_le_mul_of_nonneg_left hpoly hn
  let P : ℝ := (K+K^(11/(6 : ℝ))+K^(4/(3 : ℝ)))*(2 : ℝ)^(2/(3 : ℝ))
  have hp : 0 ≤ P := by dsimp [P]; positivity
  have hkk : 0 ≤ K*(1+K) := by positivity
  have hcross1 := mul_nonneg (add_nonneg hkk hp) ht
  have hcross2 := mul_nonneg (add_nonneg hk hp) he
  have hcross3 := mul_nonneg (add_nonneg hk hkk) hn
  unfold dictionaryFieldRate dictionaryError
  rw [card_signDictionary (by omega),overlapWeight_signDictionary (by omega)]
  norm_num only [Nat.cast_ofNat]
  change lam*theta a + lam*(1+lam)*_ + _*dictionaryPolynomialProfile lam 2 ≤ _
  unfold signPatternCoefficient signPatternError
  dsimp [P] at hcross1 hcross2
  nlinarith

/-- The conditional and unconditional true labelled fields satisfy the rate in (5.10). -/
theorem sign_field_rate_eventually (hAGG : ProcessAGGStatement)
    (hPNT : PrimeNumberTheoremRemainder) (C epsilon eta : ℝ)
    (hepsilon : 0 < epsilon) (heta : 0 < eta) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      |(L : ℝ)-Real.log N/Real.log 2| ≤ C →
      ∀ a : Fin (L+1) → F₂,
        dictionaryConditionalDistance N L (hardCutoff N) (signDictionary a) ≤
          8*signPatternCoefficient (Real.exp (C*Real.log 2))*signPatternError N a epsilon eta ∧
        dictionaryDistance N L (signDictionary a) ≤
          8*signPatternCoefficient (Real.exp (C*Real.log 2))*signPatternError N a epsilon eta := by
  obtain ⟨Nb,hb⟩ := dictionary_critical_log_band_eventually C
  obtain ⟨Nr,hr⟩ := theorem_five_one_full_band hAGG hPNT lowerConstant upperConstant
    epsilon eta lowerConstant_pos lowerConstant_lt_upperConstant hepsilon heta
  refine ⟨max Nb (max Nr 4),?_⟩
  intro N hN L hwindow a
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN4 : (4 : ℝ) ≤ N := by exact_mod_cast (show 4 ≤ N by omega)
  have hm : (2 : ℝ) ≤ (N : ℝ)^(1/(2 : ℝ)) := by
    rw [← Real.sqrt_eq_rpow]
    nlinarith [Real.sq_sqrt hn.le,Real.sqrt_nonneg (N : ℝ)]
  have hw : |((L+1 : ℕ) : ℝ)-Real.log ((N : ℝ)*2)/Real.log 2| ≤ C := by
    rwa [sign_window_eq (by omega)]
  obtain ⟨hlo,hhi⟩ := hb N (by omega) 2 (by norm_num) hm (L+1) hw
  obtain ⟨_,hfield⟩ := hr N (by omega) L (by exact_mod_cast hlo) (by exact_mod_cast hhi)
  obtain ⟨hc,hu⟩ := hfield (signDictionary a) (signDictionary_nonempty a)
  have hint := (dictionary_intensity_bounds hn (by norm_num : (0 : ℝ) < 2) hw).2
  have hK : (N : ℝ)*(dictionaryRate L (signDictionary a) : ℝ) ≤ Real.exp (C*Real.log 2) := by
    rw [dictionaryRate_coe,card_signDictionary (by omega)]
    norm_num only [Nat.cast_ofNat]
    simpa only [mul_div_assoc] using hint
  have hbnd := mul_le_mul_of_nonneg_left (sign_dictionary_error_le a hK epsilon eta)
    (by norm_num : (0 : ℝ) ≤ 8)
  rw [← mul_assoc] at hbnd
  exact ⟨hc.trans hbnd,hu.trans hbnd⟩

/-- Divergence of the least compatible shift suffices for the actual fields to converge. -/
theorem sign_field_convergence (hAGG : ProcessAGGStatement)
    (hPNT : PrimeNumberTheoremRemainder) (C : ℝ)
    (L : ℕ → ℕ) (a : ∀ N : ℕ, Fin (L N+1) → F₂)
    (hwindow : ∀ᶠ N : ℕ in atTop, |(L N : ℝ)-Real.log N/Real.log 2| ≤ C)
    (hshift : Tendsto (fun N => leastCompatibleShift (a N)) atTop atTop) :
    Tendsto (fun N => dictionaryConditionalDistance N (L N) (hardCutoff N) (signDictionary (a N)))
      atTop (𝓝 0) ∧
    Tendsto (fun N => dictionaryDistance N (L N) (signDictionary (a N))) atTop (𝓝 0) := by
  obtain ⟨Nzero,hzero⟩ := sign_field_rate_eventually hAGG hPNT C (1/12) 1 (by norm_num) (by norm_num)
  have ht := theta_tendsto_zero_of_leastCompatibleShift (fun N => L N+1) a hshift
  have he := saddle_exponential_nat_tendsto_zero 1 1 1 (by norm_num) (by norm_num)
  have hp : Tendsto (fun N : ℕ => (N : ℝ)^(-(1/(3 : ℝ))+1/12)) atTop (𝓝 0) := by
    convert (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/4)).comp
      tendsto_natCast_atTop_atTop using 1
    norm_num [Function.comp_def]
  have hb : Tendsto (fun N => 8*signPatternCoefficient (Real.exp (C*Real.log 2))*
      signPatternError N (a N) (1/12) 1) atTop (𝓝 0) := by
    simpa only [signPatternError,neg_mul,one_mul,add_zero,mul_zero] using
      ((ht.add he).add hp).const_mul (8*signPatternCoefficient (Real.exp (C*Real.log 2)))
  have hbnd : ∀ᶠ N : ℕ in atTop,
      dictionaryConditionalDistance N (L N) (hardCutoff N) (signDictionary (a N)) ≤
        8*signPatternCoefficient (Real.exp (C*Real.log 2))*signPatternError N (a N) (1/12) 1 ∧
      dictionaryDistance N (L N) (signDictionary (a N)) ≤
        8*signPatternCoefficient (Real.exp (C*Real.log 2))*signPatternError N (a N) (1/12) 1 := by
    filter_upwards [hwindow,eventually_ge_atTop Nzero] with N hw hn
    exact hzero N hn (L N) hw (a N)
  exact ⟨squeeze_zero' (Eventually.of_forall fun N => dictionaryConditionalDistance_nonneg _ _ _ _)
    (hbnd.mono fun _ h => h.1) hb,
    squeeze_zero' (Eventually.of_forall fun N => dictionaryDistance_nonneg _ _ _)
    (hbnd.mono fun _ h => h.2) hb⟩

end
end PaperC.V282.SignPatternRates
