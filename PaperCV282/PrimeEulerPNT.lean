import PaperCV282.PrimeEulerAbel
import PaperCV282.ExponentialIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# The genuine prime-counting remainder in weighted partial summation

The comparison function is Ei(log t), the usual logarithmic integral up
to an additive constant. No prime number theorem is declared as an axiom.
The finite identities below expose precisely where an estimate on pi(t)
minus this function enters the weighted-prime calculation.
-/

namespace PaperC.V282.PrimeEulerPNT

open PrimeEulerAbel PrimeEulerRankin ExponentialIntegral MeasureTheory

noncomputable section

/-- The logarithmic integral with the companion's standard Ei normalization. -/
def logIntegral (t : ℝ) : ℝ := exponentialIntegral (Real.log t)

/-- The actual prime-counting remainder, not a weighted-sum assumption. -/
def primeCountingRemainder (t : ℝ) : ℝ := primeCountingReal t - logIntegral t

/-- The source-form PNT hypothesis, isolated explicitly as an unproved input. -/
def PrimeNumberTheoremRemainder : Prop :=
  ∀ eta : ℝ, 0 < eta → ∃ A : ℝ, 2 ≤ A ∧
    ∀ t : ℝ, A ≤ t → |primeCountingRemainder t| ≤ eta * t / Real.log t

/-- The logarithmic integral has the actual derivative 1/log t above one. -/
theorem hasDerivAt_logIntegral {t : ℝ} (ht : 1 < t) :
    HasDerivAt logIntegral (1 / Real.log t) t := by
  have htpos : 0 < t := lt_trans zero_lt_one ht
  have h := (hasDerivAt_exponentialIntegral (Real.log_pos ht)).comp t (Real.hasDerivAt_log htpos.ne')
  apply h.congr_deriv
  rw [Real.exp_log htpos]
  field_simp

/-- Ei(zeta log t) is a primitive of the weighted logarithmic-integral density. -/
theorem hasDerivAt_weightedEi {t zeta : ℝ} (ht : 1 < t) (hzeta : 0 < zeta) :
    HasDerivAt (fun t => exponentialIntegral (zeta * Real.log t))
      (t ^ (-1 + zeta) / Real.log t) t := by
  have htpos : 0 < t := lt_trans zero_lt_one ht
  have hlogpos := Real.log_pos ht
  have h := (hasDerivAt_exponentialIntegral (mul_pos hzeta hlogpos)).comp t
    ((Real.hasDerivAt_log htpos.ne').const_mul zeta)
  apply h.congr_deriv
  rw [show zeta * Real.log t = Real.log t * zeta by ring, Real.exp_mul, Real.exp_log htpos,
    Real.rpow_add htpos, Real.rpow_neg_one]
  field_simp

/-- Continuity of the weighted density on every compact interval above one. -/
theorem continuousOn_weightedDensity {a b zeta : ℝ} (ha : 1 < a) :
    ContinuousOn (fun t : ℝ => t ^ (-1 + zeta) / Real.log t) (Set.Icc a b) := by
  apply (continuousOn_id.rpow_const (fun t ht => Or.inl (lt_trans zero_lt_one (ha.trans_le ht.1)).ne')).div
    (Real.continuousOn_log.mono (fun t ht => (lt_trans zero_lt_one (ha.trans_le ht.1)).ne'))
  intro t ht
  exact (Real.log_pos (ha.trans_le ht.1)).ne'

/-- The weighted density integrates exactly to the Ei difference, with both endpoints retained. -/
theorem integral_weightedDensity_eq {a b zeta : ℝ} (ha : 1 < a) (hab : a ≤ b) (hzeta : 0 < zeta) :
    (∫ t in Set.Ioc a b, t ^ (-1 + zeta) / Real.log t) =
      exponentialIntegral (zeta * Real.log b) - exponentialIntegral (zeta * Real.log a) := by
  rw [← intervalIntegral.integral_of_le hab]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t ht
    rw [Set.uIcc_of_le hab] at ht
    exact hasDerivAt_weightedEi (ha.trans_le ht.1) hzeta
  · apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact continuousOn_weightedDensity ha

/-- The derivative-weight times the step-function pi(t) is genuinely integrable. -/
theorem integrableOn_rankin_derivative_primeCounting {a b : ℝ} (ha : 0 < a) (zeta : ℝ) :
    IntegrableOn (fun t => ((-1 + zeta) * t ^ (-2 + zeta)) * primeCountingReal t) (Set.Icc a b) := by
  have hc : ContinuousOn (fun t : ℝ => (-1 + zeta) * t ^ (-2 + zeta)) (Set.Icc a b) :=
    continuousOn_const.mul (continuousOn_id.rpow_const (fun t ht => Or.inl (ha.trans_le ht.1).ne'))
  have h := integrableOn_mul_sum_Icc (fun k : ℕ => if k.Prime then (1 : ℝ) else 0)
    (m := 0) ha.le hc.integrableOn_Icc
  simpa only [sum_prime_indicator_eq, primeCountingReal] using h

/-- Integration by parts for the logarithmic-integral comparison, proved from its derivative. -/
theorem weightedDensity_integral_by_parts {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) (zeta : ℝ) :
    (∫ t in Set.Ioc a b, t ^ (-1 + zeta) / Real.log t) =
      b ^ (-1 + zeta) * logIntegral b - a ^ (-1 + zeta) * logIntegral a -
        ∫ t in Set.Ioc a b, ((-1 + zeta) * t ^ (-2 + zeta)) * logIntegral t := by
  have hpower : ContinuousOn (fun t : ℝ => t ^ (-1 + zeta)) (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]
    exact continuousOn_id.rpow_const (fun t ht => Or.inl (lt_trans zero_lt_one (ha.trans_le ht.1)).ne')
  have hlogint : ContinuousOn logIntegral (Set.uIcc a b) := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    exact (hasDerivAt_logIntegral (ha.trans_le ht.1)).continuousAt.continuousWithinAt
  have hpowerderiv : IntervalIntegrable (fun t : ℝ => (-1 + zeta) * t ^ (-2 + zeta)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact continuousOn_const.mul (continuousOn_id.rpow_const (fun t ht =>
      Or.inl (lt_trans zero_lt_one (ha.trans_le ht.1)).ne'))
  have hlogderiv : IntervalIntegrable (fun t : ℝ => 1 / Real.log t) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    apply continuousOn_const.div
      (Real.continuousOn_log.mono (fun t ht => (lt_trans zero_lt_one (ha.trans_le ht.1)).ne'))
    intro t ht
    exact (Real.log_pos (ha.trans_le ht.1)).ne'
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt hpower hlogint
    (fun t ht => hasDerivAt_rankinWeight (lt_trans zero_lt_one (ha.trans_le (by simpa [hab] using ht.1.le))) zeta)
    (fun t ht => hasDerivAt_logIntegral (ha.trans_le (by simpa [hab] using ht.1.le)))
    hpowerderiv hlogderiv
  simpa only [mul_one_div, intervalIntegral.integral_of_le hab] using hparts

/-- Exact error identity: all discrepancy is expressed through pi(t)-Ei(log t). -/
theorem weighted_prime_error_identity {a b zeta : ℝ} (ha : 1 < a) (hab : a ≤ b) (hzeta : 0 < zeta) :
    rankinPrimeSum ⌊b⌋₊ zeta - rankinPrimeSum ⌊a⌋₊ zeta -
        (exponentialIntegral (zeta * Real.log b) - exponentialIntegral (zeta * Real.log a)) =
      b ^ (-1 + zeta) * primeCountingRemainder b - a ^ (-1 + zeta) * primeCountingRemainder a -
        ∫ t in Set.Ioc a b, ((-1 + zeta) * t ^ (-2 + zeta)) * primeCountingRemainder t := by
  have hpint := (integrableOn_rankin_derivative_primeCounting (b := b) (lt_trans zero_lt_one ha) zeta).mono_set Set.Ioc_subset_Icc_self
  have hlogcont : ContinuousOn (fun t : ℝ => ((-1 + zeta) * t ^ (-2 + zeta)) * logIntegral t) (Set.Icc a b) := by
    apply (continuousOn_const.mul (continuousOn_id.rpow_const (fun t ht =>
      Or.inl (lt_trans zero_lt_one (ha.trans_le ht.1)).ne'))).mul
    intro t ht
    exact (hasDerivAt_logIntegral (ha.trans_le ht.1)).continuousAt.continuousWithinAt
  have hlogint : IntegrableOn (fun t : ℝ => ((-1 + zeta) * t ^ (-2 + zeta)) * logIntegral t)
      (Set.Ioc a b) := hlogcont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hdiff : (∫ t in Set.Ioc a b, ((-1 + zeta) * t ^ (-2 + zeta)) * primeCountingRemainder t) =
      (∫ t in Set.Ioc a b, ((-1 + zeta) * t ^ (-2 + zeta)) * primeCountingReal t) -
      ∫ t in Set.Ioc a b, ((-1 + zeta) * t ^ (-2 + zeta)) * logIntegral t := by
    simp only [primeCountingRemainder, mul_sub]
    exact integral_sub hpint hlogint
  rw [← integral_weightedDensity_eq ha hab hzeta, rankinPrimeSum_partial_summation (lt_trans zero_lt_one ha) hab,
    weightedDensity_integral_by_parts ha hab, hdiff]
  unfold primeCountingRemainder
  ring

/-- A pointwise PNT remainder estimate survives multiplication by the exact power weight. -/
theorem rpow_mul_remainder_le {t eta : ℝ} (ht : 1 < t)
    (hR : |primeCountingRemainder t| ≤ eta * t / Real.log t) (q : ℝ) :
    |t ^ q * primeCountingRemainder t| ≤ eta * t ^ (q + 1) / Real.log t := by
  have htpos : 0 < t := lt_trans zero_lt_one ht
  calc
    _ = t ^ q * |primeCountingRemainder t| := by rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg htpos.le _)]
    _ ≤ t ^ q * (eta * t / Real.log t) := mul_le_mul_of_nonneg_left hR (Real.rpow_nonneg htpos.le _)
    _ = _ := by rw [Real.rpow_add_one htpos.ne']; ring

/-- The integral error is controlled by the same weighted density, from a pi(t) remainder bound. -/
theorem derivative_remainder_integral_le {a b zeta eta : ℝ}
    (ha : 1 < a) (hab : a ≤ b) (hzeta : 0 < zeta) (hzetaOne : zeta ≤ 1)
    (hR : ∀ t ∈ Set.Icc a b, |primeCountingRemainder t| ≤ eta * t / Real.log t) :
    |∫ t in Set.Ioc a b, ((-1 + zeta) * t ^ (-2 + zeta)) * primeCountingRemainder t| ≤
      (1 - zeta) * eta * (exponentialIntegral (zeta * Real.log b) - exponentialIntegral (zeta * Real.log a)) := by
  have hdensity : IntegrableOn (fun t : ℝ => ((1 - zeta) * eta) * (t ^ (-1 + zeta) / Real.log t))
      (Set.Ioc a b) := ((continuousOn_weightedDensity (zeta := zeta) ha).const_mul _).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hpoint (t : ℝ) (ht : t ∈ Set.Ioc a b) :
      |((-1 + zeta) * t ^ (-2 + zeta)) * primeCountingRemainder t| ≤
        ((1 - zeta) * eta) * (t ^ (-1 + zeta) / Real.log t) := by
    have htone := ha.trans ht.1
    have hh := rpow_mul_remainder_le htone (hR t ⟨ht.1.le, ht.2⟩) (-2 + zeta)
    have habs : |(-1 + zeta)| = 1 - zeta := by rw [abs_of_nonpos (by linarith)]; ring
    calc
      _ = (1 - zeta) * |t ^ (-2 + zeta) * primeCountingRemainder t| := by rw [mul_assoc, abs_mul, habs]
      _ ≤ (1 - zeta) * (eta * t ^ ((-2 + zeta) + 1) / Real.log t) :=
        mul_le_mul_of_nonneg_left hh (by linarith)
      _ = _ := by rw [show (-2 + zeta) + 1 = -1 + zeta by ring]; ring
  calc
    _ ≤ ∫ t in Set.Ioc a b, |((-1 + zeta) * t ^ (-2 + zeta)) * primeCountingRemainder t| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ t in Set.Ioc a b, ((1 - zeta) * eta) * (t ^ (-1 + zeta) / Real.log t) := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => abs_nonneg _)) hdensity
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact hpoint t ht
    _ = _ := by rw [integral_const_mul, integral_weightedDensity_eq ha hab hzeta]

/-- Finite PNT-to-weighted-Ei error transfer with both boundary errors explicit.
The hypothesis is only on the ordinary prime-counting remainder over [a,b]. -/
theorem weighted_prime_error_le {a b zeta eta : ℝ} (ha : 1 < a) (hab : a ≤ b)
    (hzeta : 0 < zeta) (hzetaOne : zeta ≤ 1)
    (hR : ∀ t ∈ Set.Icc a b, |primeCountingRemainder t| ≤ eta * t / Real.log t) :
    |rankinPrimeSum ⌊b⌋₊ zeta - rankinPrimeSum ⌊a⌋₊ zeta -
        (exponentialIntegral (zeta * Real.log b) - exponentialIntegral (zeta * Real.log a))| ≤
      eta * (b ^ zeta / Real.log b + a ^ zeta / Real.log a +
        (1 - zeta) * (exponentialIntegral (zeta * Real.log b) - exponentialIntegral (zeta * Real.log a))) := by
  have hb := ha.trans_le hab
  have haR := rpow_mul_remainder_le ha (hR a ⟨le_rfl, hab⟩) (-1 + zeta)
  have hbR := rpow_mul_remainder_le hb (hR b ⟨hab, le_rfl⟩) (-1 + zeta)
  simp only [show (-1 + zeta) + 1 = zeta by ring] at haR hbR
  have hi := derivative_remainder_integral_le ha hab hzeta hzetaOne hR
  rw [weighted_prime_error_identity ha hab hzeta]
  calc
    _ ≤ |b ^ (-1 + zeta) * primeCountingRemainder b - a ^ (-1 + zeta) * primeCountingRemainder a| +
        |∫ t in Set.Ioc a b, ((-1 + zeta) * t ^ (-2 + zeta)) * primeCountingRemainder t| := abs_sub _ _
    _ ≤ (|b ^ (-1 + zeta) * primeCountingRemainder b| + |a ^ (-1 + zeta) * primeCountingRemainder a|) +
        |∫ t in Set.Ioc a b, ((-1 + zeta) * t ^ (-2 + zeta)) * primeCountingRemainder t| :=
      by linarith [abs_sub (b ^ (-1 + zeta) * primeCountingRemainder b) (a ^ (-1 + zeta) * primeCountingRemainder a)]
    _ ≤ eta * b ^ zeta / Real.log b + eta * a ^ zeta / Real.log a +
        (1 - zeta) * eta * (exponentialIntegral (zeta * Real.log b) - exponentialIntegral (zeta * Real.log a)) :=
      add_le_add (add_le_add hbR haR) hi
    _ = _ := by ring

/-- Under the explicitly stated PNT, the lower split point is fixed before b and zeta.
This is a conditional theorem, not a proof of the PNT or of the final free-cutoff asymptotic. -/
theorem weighted_prime_error_uniform_of_pnt (hPNT : PrimeNumberTheoremRemainder)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ A : ℝ, 2 ≤ A ∧ ∀ b : ℝ, A ≤ b → ∀ zeta : ℝ, 0 < zeta → zeta ≤ 1 →
      |rankinPrimeSum ⌊b⌋₊ zeta - rankinPrimeSum ⌊A⌋₊ zeta -
          (exponentialIntegral (zeta * Real.log b) - exponentialIntegral (zeta * Real.log A))| ≤
        eta * (b ^ zeta / Real.log b + A ^ zeta / Real.log A +
          (1 - zeta) * (exponentialIntegral (zeta * Real.log b) - exponentialIntegral (zeta * Real.log A))) := by
  obtain ⟨A, hA, hR⟩ := hPNT eta heta
  refine ⟨A, hA, ?_⟩
  intro b hb zeta hz hzOne
  exact weighted_prime_error_le (by linarith) hb hz hzOne (fun t ht => hR t ht.1)

end
end PaperC.V282.PrimeEulerPNT
