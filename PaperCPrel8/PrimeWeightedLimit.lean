import PaperCPrel8.PrimeWeightedWitness
import PaperCPrel8.PrimeActivityDivergence

/-! # The fixed-t witness threshold on the original arithmetic law -/
namespace PaperC.Prel8.PrimeWeightedLimit
open Finset Filter Topology PrimeWeightedWitness WeightedActivityWitness
open PrimeWindowScales PrimeWindowErrors PrimeWindowIntensity PrimeWindowGeometry PrimeRetainedDensity
open PrimeActivityDivergence ArithmeticLowCategory ArithmeticLowMarginals MicroscopicFiniteLedger
open ConditionalStartProbability CategoricalOccupancyEnvelope ArratiaGoldsteinGordonInput IndependentThinning
open V282.PrimeEulerPNT
noncomputable section

def logPolynomial (t : ℝ) (q : ℕ) (G : Finset ℕ) : ℝ :=
  Real.log (polynomial (FinitePMF.uniform (SampleSpace (cylinder q)))
    (retainedCategory (cylinder q) (q-1) (excess q) G) t)

theorem referenceRate_tendsto : Tendsto referenceRate atTop (𝓝 0) := by
  have hh : Tendsto (fun q : ℕ ↦ 2/(q:ℝ)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using inverse_prime.const_mul 2
  apply squeeze_zero' (Eventually.of_forall (fun q ↦ by unfold referenceRate; positivity)) _ hh
  filter_upwards [eventually_ge_atTop 2] with q hq
  have hpos : (0:ℝ)<q := by exact_mod_cast (show 0<q by omega)
  apply (le_div_iff₀ hpos).mpr
  have hlen := length_mass_le_one q
  have hqle : (q:ℝ)≤2*((q-1:ℕ):ℝ) := by exact_mod_cast (show q≤2*(q-1) by omega)
  have hr : 0≤referenceRate q := by unfold referenceRate; positivity
  have hm := mul_le_mul_of_nonneg_right hqle hr
  nlinarith only [hm,hlen]

/-- The true low-type mean eventually satisfies every fixed weighted positivity condition. -/
theorem weighted_mean_small {t : ℝ} (ht : 0≤t) :
    ∀ᶠ q : ℕ in atTop, t*retainedRate (q-1) (excess q)≤1/2 := by
  have hh := (referenceRate_tendsto.const_mul t).eventually (gt_mem_nhds (by norm_num : t*0<(1/2:ℝ)))
  filter_upwards [hh] with q hq
  exact (mul_le_mul_of_nonneg_left (retainedRate_le_base (q-1) (excess q)).2 ht).trans hq.le

/-- The leading normalized exponent is beta*(log(1+t)-1), with beta=log 2. -/
theorem good_subsets_lower (hPNT : PrimeNumberTheoremRemainder) {t : ℝ} (ht : 0≤t)
    (G : ℕ → Finset ℕ) (hG : ∀ q, G q⊆original q)
    (hD : Tendsto (fun q ↦ (((Icc 1 (window q))\G q).card:ℝ)*Real.log (window q)/(window q:ℝ)) atTop (𝓝 0))
    {epsilon : ℝ} (hepsilon : 0<epsilon) :
    ∀ᶠ q : ℕ in atTop, q.Prime → Real.log 2*(Real.log (1+t)-1)-epsilon≤
      Real.log (window q)/(window q:ℝ)*logPolynomial t q (G q) := by
  let r := fun q ↦ retainedRate (q-1) (excess q)
  have hcard (q : ℕ) : (G q).card≤window q := by
    have hc := card_le_card ((hG q).trans (original_subset q))
    simp only [Nat.card_Icc] at hc; omega
  have hB := marginal_error_tendsto (fun q ↦ (G q).card) r (Eventually.of_forall (fun q ↦
    ⟨hcard q,(retainedRate_le_base (q-1) (excess q)).1,(retainedRate_le_base (q-1) (excess q)).2⟩))
  have hl := lowerEnvelope_tendsto hPNT t support
    (fun q ↦ (((Icc 1 (window q))\G q).card:ℝ)) (fun q ↦ (G q).card*r q) support_ratio hD hB
  have he := hl.eventually (eventually_gt_nhds (show Real.log 2*(Real.log (1+t)-1)-epsilon<
    Real.log 2*(Real.log (1+t)-1) by linarith))
  filter_upwards [he,weighted_mean_small ht,original_geometry] with q hq hm hg hp
  exact hq.le.trans (normalized_lower hp (G q) ht (retainedRate_le_base (q-1) (excess q)).1 hm
    (fun i ↦ occupancy_expectation (geometry_subset hg (hG q)) i))

theorem retained_lower (hPNT : PrimeNumberTheoremRemainder) {t theta : ℝ} (ht : 0≤t) (htheta : 0≤theta)
    {epsilon : ℝ} (hepsilon : 0<epsilon) :
    ∀ᶠ q : ℕ in atTop, q.Prime → Real.log 2*(Real.log (1+t)-1)-epsilon≤
      Real.log (window q)/(window q:ℝ)*logPolynomial t q (retained q theta) :=
  good_subsets_lower hPNT ht (fun q ↦ retained q theta) (fun q ↦ retained_subset_original q theta)
    (retained_density hPNT htheta) hepsilon

theorem original_lower (hPNT : PrimeNumberTheoremRemainder) {t : ℝ} (ht : 0≤t)
    {epsilon : ℝ} (hepsilon : 0<epsilon) :
    ∀ᶠ q : ℕ in atTop, q.Prime → Real.log 2*(Real.log (1+t)-1)-epsilon≤
      Real.log (window q)/(window q:ℝ)*logPolynomial t q (original q) :=
  good_subsets_lower hPNT ht original (fun _ ↦ Subset.refl _) (original_density hPNT) hepsilon

/-- The witness grows without bound for t>e-1; no optimality assertion is made. -/
theorem witness_divergence {t : ℝ} (ht : 0≤t) (hthreshold : Real.exp 1-1<t)
    (G : ℕ → Finset ℕ)
    (hlo : ∀ epsilon>0, ∀ᶠ q : ℕ in atTop, q.Prime → Real.log 2*(Real.log (1+t)-1)-epsilon≤
      Real.log (window q)/(window q:ℝ)*logPolynomial t q (G q))
    (qs : ℕ → ℕ) (hqs : Tendsto qs atTop atTop) (hp : ∀ᶠ n in atTop, (qs n).Prime) :
    Tendsto (fun n ↦ logPolynomial t (qs n) (G (qs n))) atTop atTop := by
  let K := Real.log 2*(Real.log (1+t)-1)
  have hK : 0<K := mul_pos (Real.log_pos (by norm_num)) ((positive_leading_iff ht).mpr hthreshold)
  have hh := hlo (K/2) (by positivity)
  have hg := (inverse_normalization_atTop.const_mul_atTop (show 0<K/2 by positivity)).comp hqs
  apply tendsto_atTop_mono' atTop _ hg
  filter_upwards [hqs.eventually hh,hp,hqs.eventually
    (PrimeWindowBudget.log_window_atTop.eventually (eventually_gt_atTop (0:ℝ)))] with n hn hp hlog
  have hw : (0:ℝ)<window (qs n) := by exact_mod_cast window_pos (qs n)
  have hx := (div_le_iff₀ (div_pos hlog hw)).mpr
    (show K/2≤logPolynomial t (qs n) (G (qs n))*(Real.log (window (qs n))/(window (qs n):ℝ)) by
      have := hn hp; dsimp [K] at *; nlinarith)
  convert hx using 1
  dsimp only [Function.comp_def]
  field_simp

theorem retained_log_diverges (hPNT : PrimeNumberTheoremRemainder) {t theta : ℝ}
    (ht : 0≤t) (htheta : 0≤theta) (hthreshold : Real.exp 1-1<t)
    (qs : ℕ → ℕ) (hqs : Tendsto qs atTop atTop) (hp : ∀ᶠ n in atTop, (qs n).Prime) :
    Tendsto (fun n ↦ logPolynomial t (qs n) (retained (qs n) theta)) atTop atTop :=
  witness_divergence ht hthreshold (fun q ↦ retained q theta)
    (fun _ he ↦ retained_lower hPNT ht htheta he) qs hqs hp

theorem original_log_diverges (hPNT : PrimeNumberTheoremRemainder) {t : ℝ}
    (ht : 0≤t) (hthreshold : Real.exp 1-1<t)
    (qs : ℕ → ℕ) (hqs : Tendsto qs atTop atTop) (hp : ∀ᶠ n in atTop, (qs n).Prime) :
    Tendsto (fun n ↦ logPolynomial t (qs n) (original (qs n))) atTop atTop :=
  witness_divergence ht hthreshold original (fun _ he ↦ original_lower hPNT ht he) qs hqs hp

end
end PaperC.Prel8.PrimeWeightedLimit
