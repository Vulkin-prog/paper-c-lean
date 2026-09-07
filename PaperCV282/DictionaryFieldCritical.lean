import PaperCV282.DictionaryFieldRates
import PaperCV282.DictionaryCriticalWindow
import PaperCV282.DictionaryRateConvergence

/-!
# The actual dictionary field in the growing critical window

The length is centered at log_2(N*card W). Both the averaged full-small-prime
conditional distance and the unconditional labelled-field distance receive the
critical rate, with a threshold independent of the words and their cardinality.
-/

namespace PaperC.V282.DictionaryFieldCritical

open Filter Topology MeasureTheory DictionaryFieldRates DictionaryFieldInfinite
open DictionaryFieldModel DictionaryCriticalWindow DictionaryRateConvergence
open DictionaryErrorLedger WordOverlapSum CriticalRunWindow
open HardPoissonRates SaddleParameters SaddleScales SaddlePoissonScales
open PrimeEulerPNT ProcessAGGInput

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

noncomputable section

/-- Equation (5.4), with the actual cardinality window and both actual field distances. -/
theorem equation_five_four (hAGG : ProcessAGGStatement)
    (hPNT : PrimeNumberTheoremRemainder) (C delta eta : ℝ)
    (hdelta : 0 < delta) (heta : 0 < eta) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      ∀ W : Finset (Fin (L+1) → F₂), W.Nonempty →
      (W.card : ℝ) ≤ (N : ℝ) ^ (1 / 2 - delta) →
      |(L+1 : ℝ) - Real.log ((N : ℝ) * W.card) / Real.log 2| ≤ C →
      dictionaryConditionalDistance N L (hardCutoff N) W ≤
        8 * criticalDictionaryConstant (Real.exp (C * Real.log 2)) *
          (overlapWeight W +
            Real.exp (-saddleCutoff 1 (Real.log N) + eta * saddleNu 1 (Real.log N)) +
            (N : ℝ) ^ (-(delta / 2))) ∧
      dictionaryDistance N L W ≤
        8 * criticalDictionaryConstant (Real.exp (C * Real.log 2)) *
          (overlapWeight W +
            Real.exp (-saddleCutoff 1 (Real.log N) + eta * saddleNu 1 (Real.log N)) +
            (N : ℝ) ^ (-(delta / 2))) := by
  obtain ⟨Nb,hb⟩ := dictionary_critical_log_band_eventually C
  obtain ⟨Nr,hr⟩ := theorem_five_one_full_band hAGG hPNT lowerConstant upperConstant
    (delta / 6) eta lowerConstant_pos lowerConstant_lt_upperConstant (by positivity) heta
  refine ⟨max Nb (max Nr 2), ?_⟩
  intro N hN L W hW hcard hwindow
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hm : (1 : ℝ) ≤ W.card := by exact_mod_cast Finset.card_pos.mpr hW
  have hmpos : (0 : ℝ) < W.card := by linarith
  have hmhalf : (W.card : ℝ) ≤ (N : ℝ) ^ (1 / (2 : ℝ)) :=
    hcard.trans (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith))
  have hwindowNat : |((L+1 : ℕ) : ℝ) - Real.log ((N : ℝ) * W.card) / Real.log 2| ≤ C := by
    simpa only [Nat.cast_add,Nat.cast_one] using hwindow
  obtain ⟨hlo,hhi⟩ := hb N (by omega) W.card hm hmhalf (L+1) hwindowNat
  obtain ⟨_,hfield⟩ := hr N (by omega) L (by exact_mod_cast hlo) (by exact_mod_cast hhi)
  obtain ⟨hcond,huncond⟩ := hfield W hW
  have hlambda : 0 ≤ (N : ℝ) * (dictionaryRate L W : ℝ) := by positivity
  have hint := (dictionary_intensity_bounds hn hmpos hwindowNat).2
  have hK : (N : ℝ) * (dictionaryRate L W : ℝ) ≤ Real.exp (C * Real.log 2) := by
    simpa only [dictionaryRate_coe,mul_div_assoc] using hint
  have herr := dictionary_error_critical_le (by omega : 0 < N) hlambda hK hm
    (overlapWeight_nonneg W) hcard eta
  have hscaled := mul_le_mul_of_nonneg_left herr (by norm_num : (0 : ℝ) ≤ 8)
  change 8 * dictionaryFieldRate N L W (delta / 6) eta ≤ _ at hscaled
  rw [← mul_assoc] at hscaled
  exact ⟨hcond.trans hscaled,huncond.trans hscaled⟩

/-- The entire labelled fields converge in the printed growing-dictionary regime. -/
theorem dictionary_field_critical_convergence (hAGG : ProcessAGGStatement)
    (hPNT : PrimeNumberTheoremRemainder) (C delta : ℝ) (hdelta : 0 < delta)
    (L : ℕ → ℕ) (W : ∀ N : ℕ, Finset (Fin (L N + 1) → F₂))
    (hcritical : ∀ᶠ N : ℕ in atTop,
      (W N).Nonempty ∧ ((W N).card : ℝ) ≤ (N : ℝ) ^ (1 / 2 - delta) ∧
        |(L N + 1 : ℝ) - Real.log ((N : ℝ) * (W N).card) / Real.log 2| ≤ C)
    (hoverlap : Tendsto (fun N => overlapWeight (W N)) atTop (𝓝 0)) :
    Tendsto (fun N => dictionaryConditionalDistance N (L N) (hardCutoff N) (W N)) atTop (𝓝 0) ∧
      Tendsto (fun N => dictionaryDistance N (L N) (W N)) atTop (𝓝 0) := by
  obtain ⟨Nzero,hzero⟩ := equation_five_four hAGG hPNT C delta 1 hdelta (by norm_num)
  let bound : ℕ → ℝ := fun N =>
    8 * criticalDictionaryConstant (Real.exp (C * Real.log 2)) *
      (overlapWeight (W N) +
        Real.exp (-saddleCutoff 1 (Real.log N) + 1 * saddleNu 1 (Real.log N)) +
        (N : ℝ) ^ (-(delta / 2)))
  have hbound : ∀ᶠ N : ℕ in atTop,
      dictionaryConditionalDistance N (L N) (hardCutoff N) (W N) ≤ bound N ∧
        dictionaryDistance N (L N) (W N) ≤ bound N := by
    filter_upwards [hcritical,eventually_ge_atTop Nzero] with N hN hn
    exact hzero N hn (L N) (W N) hN.1 hN.2.1 hN.2.2
  have hexp := saddle_exponential_nat_tendsto_zero 1 1 1 (by norm_num) (by norm_num)
  have hpow : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(delta / 2))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by positivity : 0 < delta / 2)).comp tendsto_natCast_atTop_atTop
  have hlimit : Tendsto bound atTop (𝓝 0) := by
    simpa only [bound,neg_mul,one_mul,add_zero,mul_zero] using
      ((hoverlap.add hexp).add hpow).const_mul
        (8 * criticalDictionaryConstant (Real.exp (C * Real.log 2)))
  constructor
  · apply squeeze_zero' _ _ hlimit
    · exact Filter.Eventually.of_forall fun N => dictionaryConditionalDistance_nonneg _ _ _ _
    · exact hbound.mono fun N hN => hN.1
  · apply squeeze_zero' _ _ hlimit
    · exact Filter.Eventually.of_forall fun N => dictionaryDistance_nonneg _ _ _
    · exact hbound.mono fun N hN => hN.2

end
end PaperC.V282.DictionaryFieldCritical
