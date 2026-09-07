import PaperCV282.DictionaryErrorLedger
import PaperCV282.DictionaryCriticalWindow
import PaperCV282.SaddlePoissonScales

/-!
# The critical growing-dictionary error and its limit

These are numerical rate results. The following field endpoints must
supply the actual probability comparison before obtaining a true law limit.
-/

namespace PaperC.V282.DictionaryRateConvergence

open Filter Topology DictionaryErrorLedger DictionaryProfileNormalization
open DictionaryCriticalWindow SaddlePoissonScales SaddleParameters SaddleScales

noncomputable section

/-- One constant controls overlap, cutoff and polynomial errors at bounded intensity. -/
def criticalDictionaryConstant (K : ℝ) : ℝ :=
  K + K * (1 + K) + (K + K ^ (11 / (6 : ℝ)) + K ^ (4 / (3 : ℝ)))

theorem criticalDictionaryConstant_nonneg {K : ℝ} (hK : 0 ≤ K) :
    0 ≤ criticalDictionaryConstant K := by
  unfold criticalDictionaryConstant
  positivity

/-- Formula (5.4) for the displayed numerical error, with no cardinality-dependent constant. -/
theorem dictionary_error_critical_le {N : ℕ} {lambda m omega K delta : ℝ}
    (hN : 0 < N) (hlambda : 0 ≤ lambda) (hlambdaK : lambda ≤ K)
    (hm : 1 ≤ m) (homega : 0 ≤ omega) (hcard : m ≤ (N : ℝ) ^ (1 / 2 - delta))
    (eta : ℝ) :
    dictionaryError N lambda m omega (delta / 6) eta ≤
      criticalDictionaryConstant K *
        (omega + Real.exp (-saddleCutoff 1 (Real.log N) + eta * saddleNu 1 (Real.log N)) +
          (N : ℝ) ^ (-(delta / 2))) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hK : 0 ≤ K := hlambda.trans hlambdaK
  have he := Real.exp_nonneg (-saddleCutoff 1 (Real.log N) + eta * saddleNu 1 (Real.log N))
  have hpow := Real.rpow_nonneg hn.le (-(delta / 2))
  have hpoly := dictionary_polynomial_error_critical hn hlambda hlambdaK hm hcard
  have ho : lambda * omega ≤ K * omega := mul_le_mul_of_nonneg_right hlambdaK homega
  have hkprod : lambda * (1 + lambda) ≤ K * (1 + K) := by nlinarith
  have hc := mul_le_mul_of_nonneg_right hkprod he
  have hkfirst : 0 ≤ K ^ (11 / (6 : ℝ)) := Real.rpow_nonneg hK _
  have hksecond : 0 ≤ K ^ (4 / (3 : ℝ)) := Real.rpow_nonneg hK _
  let Q := K + K ^ (11 / (6 : ℝ)) + K ^ (4 / (3 : ℝ))
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hkk : 0 ≤ K * (1 + K) := by positivity
  have hko := mul_nonneg (add_nonneg hkk hQ) homega
  have hce := mul_nonneg (add_nonneg hK hQ) he
  have hcp := mul_nonneg (add_nonneg hK hkk) hpow
  dsimp [Q] at hko hce hcp
  unfold dictionaryError criticalDictionaryConstant
  nlinarith

/-- The three numerical contributions tend to zero in the growing-dictionary regime. -/
theorem dictionary_error_tendsto_zero_of_bounded_intensity
    (K delta eta : ℝ) (hdelta : 0 < delta)
    (lambda m omega : ℕ → ℝ)
    (hconditions : ∀ᶠ N : ℕ in atTop,
      0 ≤ lambda N ∧ lambda N ≤ K ∧ 1 ≤ m N ∧
      0 ≤ omega N ∧ m N ≤ (N : ℝ) ^ (1 / 2 - delta))
    (hoverlap : Tendsto omega atTop (𝓝 0)) :
    Tendsto (fun N => dictionaryError N (lambda N) (m N) (omega N) (delta / 6) eta)
      atTop (𝓝 0) := by
  apply squeeze_zero'
  · filter_upwards [hconditions] with N hN
    exact dictionaryError_nonneg N hN.1 (by linarith [hN.2.2.1]) hN.2.2.2.1
  · filter_upwards [hconditions,eventually_ge_atTop 1] with N hN hn
    exact dictionary_error_critical_le (by omega) hN.1 hN.2.1 hN.2.2.1 hN.2.2.2.1 hN.2.2.2.2 eta
  · have hexp := saddle_exponential_nat_tendsto_zero 1 1 eta (by norm_num) (by norm_num)
    have hpow : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(delta / 2))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by positivity : 0 < delta / 2)).comp tendsto_natCast_atTop_atTop
    simpa only [neg_mul,one_mul,add_zero,mul_zero] using
      ((hoverlap.add hexp).add hpow).const_mul (criticalDictionaryConstant K)

end
end PaperC.V282.DictionaryRateConvergence
