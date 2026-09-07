import PaperCV282.SoftRateLedger
import PaperCV282.FreeCutoffAdmissibility
import PaperCV282.BadStartRankinFreeCutoff

/-!
# The actual soft error ledger at every free cutoff in the square-root band

The initial ledger retains the intensity envelope explicitly. Under
lambda at least one and log lambda at most A*w, a uniform elementary
absorption proves the printed three-term estimate (4.10). Every threshold
precedes both the moving real cutoff and the natural run length.
-/

namespace PaperC.V282.FreeCutoffSoftRates

open MeasureTheory Set Filter Topology
open InfiniteRademacher InfiniteConditionalWords InfiniteCylinderTransfer
open ScalarSteinInput PrimeEulerPNT SaddleParameters
open MaskedArithmeticGeometry AllStartSoftPoisson FullBandArithmetic
open DyadicPoissonDistance SoftPoissonRates SoftRateLedger
open CutoffGraphFreeCutoff BadStartRankinFreeCutoff FreeCutoffAdmissibility PrimeEulerFreeScales
open CutoffGraphDegree TouchingPairMass TwoWindowParity SectionTwelveMoments

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

noncomputable section

/-- The ledger before absorbing the intensity envelope into a small power. -/
def freeSoftLedger (N L : ℕ) (w epsilon eta : ℝ) : ℝ :=
  2 * Real.sqrt (intensityEnvelope (fullRate N L)) *
      Real.exp (-saddleCost (Real.log N / w) + eta * (Real.log N / w)) +
    3 * intensityEnvelope (fullRate N L) * Real.exp (-w + eta * (Real.log N / w)) +
    6 * intensityEnvelope (fullRate N L) * (N : ℝ) ^ (-(1 / (3 : ℝ)) + epsilon)

/-- The printed three-term rate, with the polynomial remainder explicitly absorbed. -/
def freeSoftRate (N L : ℕ) (w epsilon eta : ℝ) : ℝ :=
  2 * Real.exp (Real.log (fullRate N L : ℝ) / 2 - saddleCost (Real.log N / w) + eta * (Real.log N / w)) +
    3 * Real.exp (Real.log (fullRate N L : ℝ) - w + eta * (Real.log N / w)) +
    6 * (N : ℝ) ^ (-(1 / (3 : ℝ)) + epsilon)

/-- The genuine conditional and unconditional laws obey the free-cutoff ledger. -/
theorem free_soft_ledger_eventually
    (hStein : ScalarSteinFactorsStatement) (hPNT : PrimeNumberTheoremRemainder)
    (c C betaMin betaMax epsilon eta : ℝ) (hc : 0 < c) (hC : 0 < C)
    (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax)
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon < 1 / 3) (heta : 0 < eta) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ w : ℝ,
      c * Real.sqrt (Real.log N * Real.log (Real.log N)) ≤ w →
      w ≤ C * Real.sqrt (Real.log N * Real.log (Real.log N)) →
      ∀ L : ℕ, betaMin * Real.log N ≤ (L + 1 : ℝ) →
      (L + 1 : ℝ) ≤ betaMax * Real.log N →
      smallPrimeSigmaAlgebra (dyadicCutoff N L) ⌊Real.exp w⌋₊ =
          MeasurableSpace.comap (restrictToFinite ⌊Real.exp w⌋₊) inferInstance ∧
      conditionalDistance N L ⌊Real.exp w⌋₊ ≤ freeSoftLedger N L w epsilon eta ∧
      countDistance N L ≤ freeSoftLedger N L w epsilon eta := by
  have hbetaMax : 0 < betaMax := hbetaMin.trans hbeta
  obtain ⟨Nm, hm⟩ := fullDefectMass_div_block_le_eventually
    betaMin betaMax epsilon hbetaMin hbeta hepsilon
  obtain ⟨Nr, hr⟩ := normalized_relation_mass_le_eventually
    betaMin betaMax epsilon hbetaMin hbeta hepsilon
  obtain ⟨Nt, ht⟩ := touching_mass_le_eventually
    betaMin betaMax epsilon hbetaMin hbeta hepsilon
  obtain ⟨Na, ha⟩ := free_cutoff_admissible_eventually c C betaMax hc hC hbetaMax
  obtain ⟨Nd, hd⟩ := normalized_fullBadMask_free_cutoff_le_eventually
    hPNT c C betaMax eta hc hC hbetaMax heta
  obtain ⟨Ne, he⟩ := normalized_degree_and_edges_free_cutoff_le_eventually
    c C betaMax eta hc hC hbetaMax heta
  obtain ⟨Nl, hl⟩ := length_pos_eventually betaMin hbetaMin
  refine ⟨max Nm (max Nr (max Nt (max Na (max Nd (max Ne (max Nl 2)))))), ?_⟩
  intro N hN w hwlo hwhi L hlo hhi
  have hNtwo : 2 ≤ N := by omega
  have hNone : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL := hl N (by omega) L hlo
  obtain ⟨_,hYlo,hYhi⟩ := ha N (by omega) w hwlo hwhi L hhi
  have hm' : (fullDefectMass L (dyadicBlock N) : ℝ) / N ≤
      (N : ℝ) ^ (-(1 / (3 : ℝ)) + epsilon) :=
    (hm N (by omega) L hlo hhi _ (Finset.Subset.refl _)).trans
      (Real.rpow_le_rpow_of_exponent_le hNone (by linarith))
  have hd' := hd N (by omega) w hwlo hwhi L hhi (dyadicBlock N)
  have hmask : fullBadMask N L ⌊Real.exp w⌋₊ (dyadicBlock N) = fullBadStarts N L ⌊Real.exp w⌋₊ :=
    Finset.inter_eq_right.mpr (fullBadStarts_subset_block N L _)
  rw [hmask] at hd'
  have he' := (he N (by omega) w hwlo hwhi L hhi _ (Finset.Subset.refl _)).1
  have hu : 1 / (N : ℝ) ≤ (N : ℝ) ^ (-(1 / (3 : ℝ)) + epsilon) := by
    calc
      _ = (N : ℝ) ^ (-1 : ℝ) := by rw [Real.rpow_neg_one, one_div]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hNone (by linarith)
  have ht' : homogeneousTouchingMass (dyadicCutoff N L) L (dyadicBlock N) / (N : ℝ) ^ 2 ≤
      (N : ℝ) ^ (-(1 / (3 : ℝ)) + epsilon) := by
    calc
      _ ≤ (N : ℝ) ^ (1 + epsilon) / (N : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right (ht N (by omega) L hlo hhi) (by positivity)
      _ = (N : ℝ) ^ (-1 + epsilon) := by
        rw [← Real.rpow_natCast (N : ℝ) 2, ← Real.rpow_sub hNpos]
        congr 1
        norm_num
        ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hNone (by linarith)
  have hPone : (N : ℝ) ^ (-(1 / (3 : ℝ)) + epsilon) ≤ 1 := by
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_le hNone (show -(1 / (3 : ℝ)) + epsilon ≤ 0 by linarith)
  have hbound := conditionalDistance_le_independent_costs hStein hNtwo hL
    (show L + 1 ≤ ⌊Real.exp w⌋₊ by omega)
    (Real.rpow_nonneg hNpos.le _) hPone (Real.exp_nonneg _) hu hm' ht'
    (hr N (by omega) L hlo hhi) he' hd'
  change conditionalDistance N L ⌊Real.exp w⌋₊ ≤ freeSoftLedger N L w epsilon eta at hbound
  exact ⟨conditioningSigma_eq_full_FY hYhi, hbound,
    (countDistance_le_conditionalDistance N L ⌊Real.exp w⌋₊).trans hbound⟩

/-- Uniform sublinear growth of A*w on the entire moving cutoff band. -/
theorem multiple_free_cutoff_le_log_eventually (c C A delta : ℝ)
    (hc : 0 < c) (hC : 0 < C) (hA : 0 ≤ A) (hdelta : 0 < delta) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ w : ℝ,
      c * Real.sqrt (Real.log N * Real.log (Real.log N)) ≤ w →
      w ≤ C * Real.sqrt (Real.log N * Real.log (Real.log N)) →
      A * w ≤ delta * Real.log N := by
  obtain ⟨Hband,hband⟩ := sqrt_log_band_eventually_in_power_band c C hc hC
  have hsmall : Tendsto (fun H : ℝ => A * H ^ (-(1 / 4 : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).const_mul A
  obtain ⟨Hsmall,hsmall⟩ := eventually_atTop.1 (hsmall.eventually (gt_mem_nhds hdelta))
  have hnatlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨Nzero,hzero⟩ := eventually_atTop.1
    (hnatlog.eventually (eventually_ge_atTop (max Hband (max Hsmall 1))))
  refine ⟨Nzero, ?_⟩
  intro N hN w hlo hhi
  have hH := hzero N hN
  have hHone : (1 : ℝ) ≤ Real.log N := by order
  have hHpos : 0 < Real.log N := by linarith
  have hp := (hband (Real.log N) (by order) w hlo hhi).2
  have hs := mul_le_mul_of_nonneg_right (hsmall (Real.log N) (by order)).le hHpos.le
  have hprod : (Real.log N) ^ (-(1 / 4 : ℝ)) * Real.log N = (Real.log N) ^ (3 / 4 : ℝ) := by
    conv_lhs => rhs; rw [← Real.rpow_one (Real.log N)]
    rw [← Real.rpow_add hHpos]
    norm_num
  rw [mul_assoc, hprod] at hs
  exact (mul_le_mul_of_nonneg_left hp hA).trans hs

/-- Absorbing the intensity for log lambda bounded by A*w gives the printed equation (4.10). -/
theorem equation_four_ten
    (hStein : ScalarSteinFactorsStatement) (hPNT : PrimeNumberTheoremRemainder)
    (c C A betaMin betaMax epsilon eta : ℝ) (hc : 0 < c) (hC : 0 < C) (hA : 0 ≤ A)
    (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax)
    (hepsilon : 0 < epsilon) (heta : 0 < eta) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ w : ℝ,
      c * Real.sqrt (Real.log N * Real.log (Real.log N)) ≤ w →
      w ≤ C * Real.sqrt (Real.log N * Real.log (Real.log N)) →
      ∀ L : ℕ, betaMin * Real.log N ≤ (L + 1 : ℝ) →
      (L + 1 : ℝ) ≤ betaMax * Real.log N →
      1 ≤ (fullRate N L : ℝ) → Real.log (fullRate N L : ℝ) ≤ A * w →
      smallPrimeSigmaAlgebra (dyadicCutoff N L) ⌊Real.exp w⌋₊ =
          MeasurableSpace.comap (restrictToFinite ⌊Real.exp w⌋₊) inferInstance ∧
      conditionalDistance N L ⌊Real.exp w⌋₊ ≤ freeSoftRate N L w epsilon eta ∧
      countDistance N L ≤ freeSoftRate N L w epsilon eta := by
  let epsmall : ℝ := min epsilon (1 / 6)
  have hepspos : 0 < epsmall := lt_min hepsilon (by norm_num)
  have hepsle : epsmall ≤ epsilon := min_le_left _ _
  have hepssmall : epsmall < 1 / 3 := (min_le_right _ _).trans_lt (by norm_num)
  obtain ⟨Nb,hb⟩ := free_soft_ledger_eventually hStein hPNT c C betaMin betaMax (epsmall / 2) eta
    hc hC hbetaMin hbeta (by positivity) (by linarith) heta
  obtain ⟨Na,ha⟩ := multiple_free_cutoff_le_log_eventually c C A (epsmall / 2) hc hC hA (by positivity)
  refine ⟨max Nb (max Na 1), ?_⟩
  intro N hN w hwlo hwhi L hlo hhi hrate hlog
  obtain ⟨hY,hcond,hcount⟩ := hb N (by omega) w hwlo hwhi L hlo hhi
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNone : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hlogpos : positiveLog (fullRate N L) = Real.log (fullRate N L : ℝ) :=
    max_eq_right (Real.log_nonneg hrate)
  have hK : intensityEnvelope (fullRate N L) ≤ (N : ℝ) ^ (epsmall / 2) := by
    apply intensityEnvelope_le_rpow_of_positiveLog_le hn (ha N (by omega) w hwlo hwhi)
    simpa only [hlogpos] using hlog
  have hpoly : intensityEnvelope (fullRate N L) * (N : ℝ) ^ (-(1 / (3 : ℝ)) + epsmall / 2) ≤
      (N : ℝ) ^ (-(1 / (3 : ℝ)) + epsilon) := by
    calc
      _ ≤ (N : ℝ) ^ (epsmall / 2) * (N : ℝ) ^ (-(1 / (3 : ℝ)) + epsmall / 2) := by
        exact mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg hn.le _)
      _ = (N : ℝ) ^ (-(1 / (3 : ℝ)) + epsmall) := by rw [← Real.rpow_add hn]; congr 1; ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hNone (by linarith)
  have hsqrt : Real.sqrt (intensityEnvelope (fullRate N L)) *
      Real.exp (-saddleCost (Real.log N / w) + eta * (Real.log N / w)) =
      Real.exp (Real.log (fullRate N L : ℝ) / 2 - saddleCost (Real.log N / w) + eta * (Real.log N / w)) := by
    rw [sqrt_intensityEnvelope_eq_exp, hlogpos, ← Real.exp_add]
    congr 1
    ring
  have hdegree := envelope_mul_exp (fullRate N L) w (eta * (Real.log N / w))
  rw [hlogpos] at hdegree
  have hledger : freeSoftLedger N L w (epsmall / 2) eta ≤ freeSoftRate N L w epsilon eta := by
    unfold freeSoftLedger freeSoftRate
    nlinarith
  exact ⟨hY, hcond.trans hledger, hcount.trans hledger⟩

end
end PaperC.V282.FreeCutoffSoftRates
