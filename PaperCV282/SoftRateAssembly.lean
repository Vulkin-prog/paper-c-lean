import PaperCV282.SoftPoissonRates
import PaperCV282.FullBandArithmetic
import PaperCV282.DyadicPoissonDistance
import PaperCV282.InfiniteSoftTransfer
import PaperCV282.SaddleArithmeticBounds

/-!
# Soft Poisson rates for the actual count on the whole logarithmic band

The numerical reduction retains both Stein factors. Only the nontrivial
branch of the final minimum forces log-positive intensity below the soft
cutoff; no global small-intensity hypothesis is imposed. The ordinary PNT
premise supplies the bad-start estimate, and the scalar Stein premise
supplies the actual-law arithmetic ledger.
-/

namespace PaperC.V282.SoftRateAssembly

open MeasureTheory Set Filter Topology
open InfiniteRademacher InfiniteConditionalWords InfiniteCylinderTransfer
open ConditionalStartProbability ConditionalAGGAverage SectionTwelveMoments
open ScalarSteinInput PrimeEulerPNT SaddleParameters SaddleScales
open SaddleCutoffAdmissibility SaddleArithmeticBounds
open MaskedArithmeticGeometry MaskedPairGeometry AllStartSoftPoisson
open FullBandArithmetic DyadicPoissonDistance SoftPoissonRates SoftArithmeticTransfer
open CutoffGraphDegree TouchingPairMass TwoWindowParity

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

noncomputable section

/-- The literal rounded cutoff from the second saddle. -/
def softCutoff (N : ℕ) : ℕ := ⌊Real.exp (saddleCutoff 2 (Real.log N))⌋₊

/-- The two terms inside the minimum in equation (4.9). -/
def softRate (N L : ℕ) (epsilon eta : ℝ) : ℝ :=
  Real.exp (-(saddleCutoff 2 (Real.log N) - max 0 (Real.log (fullRate N L : ℝ))) / 2 +
    eta * saddleNu 2 (Real.log N)) + (N : ℝ) ^ (-(1 / (3 : ℝ)) + epsilon)

/-- Exact denominator normalization of the genuine soft ledger. -/
theorem softArithmeticBudget_eq_normalized (N L Y : ℕ) (hN : 0 < N) :
    softArithmeticBudget N L Y = softBudget (fullRate N L)
      (1 / (N : ℝ)) ((fullDefectMass L (dyadicBlock N) : ℝ) / N)
      ((cutoffMaxDegree L Y (dyadicBlock N) : ℝ) / N)
      ((jointDefectMass N L (separatedPairs (dyadicBlock N) L) : ℝ) / (2 : ℝ) ^ (2 * L))
      (homogeneousTouchingMass (dyadicCutoff N L) L (dyadicBlock N) / (N : ℝ) ^ 2)
      (((fullBadStarts N L Y).card : ℝ) / N) := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hN)
  have hp : (2 : ℝ) ^ L ≠ 0 := by positivity
  unfold softArithmeticBudget softBudget
  rw [fullRate_coe, show 2 * L = L * 2 by omega, pow_mul]
  field_simp
  ring

/-- The second saddle is eventually below every fixed positive multiple of log N. -/
theorem softCutoff_exponent_le_log_eventually (delta : ℝ) (hdelta : 0 < delta) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero,
      saddleCutoff 2 (Real.log N) ≤ delta * Real.log N := by
  have hnatlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall := (tendsto_saddleCutoff_div_height (a := 2) (by norm_num)).eventually
    (gt_mem_nhds hdelta)
  have hevent : ∀ᶠ N : ℕ in atTop,
      saddleCutoff 2 (Real.log N) ≤ delta * Real.log N := by
    filter_upwards [hnatlog.eventually hsmall,
      hnatlog.eventually (eventually_gt_atTop (0 : ℝ))] with N hs hlog
    exact (div_le_iff₀ hlog).mp hs.le
  exact eventually_atTop.1 hevent

/-- Actual-law soft transfer from normalized arithmetic estimates.
The intensity restriction is proved only inside the nontrivial minimum branch. -/
theorem conditionalDistance_soft_le_of_arithmetic (hStein : ScalarSteinFactorsStatement)
    {N L Y : ℕ} {power delta w error : ℝ} (hN : 2 ≤ N) (hL : 0 < L) (hY : L + 1 ≤ Y)
    (hw : w ≤ delta * Real.log N) (herror : 0 ≤ error)
    (hu : 1 / (N : ℝ) ≤ (N : ℝ) ^ power)
    (hm : (fullDefectMass L (dyadicBlock N) : ℝ) / N ≤ (N : ℝ) ^ power)
    (ht : homogeneousTouchingMass (dyadicCutoff N L) L (dyadicBlock N) / (N : ℝ) ^ 2 ≤
      (N : ℝ) ^ power)
    (hr : (jointDefectMass N L (separatedPairs (dyadicBlock N) L) : ℝ) / (2 : ℝ) ^ (2 * L) ≤
      (N : ℝ) ^ power * ((fullRate N L : ℝ) ^ 2 + 2 * (fullRate N L : ℝ)))
    (he : (cutoffMaxDegree L Y (dyadicBlock N) : ℝ) / N ≤ Real.exp (-w + error))
    (hd : ((fullBadStarts N L Y).card : ℝ) / N ≤ Real.exp (-w / 2 + error)) :
    conditionalDistance N L Y ≤
      6 * min 1 (softExponential (fullRate N L) w error + (N : ℝ) ^ (power + delta)) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hb := average_conditionalMaskedLaw_soft_le hStein hN hL hY
  change conditionalDistance N L Y ≤ _ at hb
  rw [softArithmeticBudget_eq_normalized N L Y (by omega)] at hb
  exact soft_rate_rpow_of_budget hn hw (conditionalDistance_le_one N L Y) herror
    (by positivity) hu hm ht hr he hd hb

/-- Equation (4.9) for the mean conditional distance, with its exact saddle and floor. -/
theorem soft_conditional_rate_eventually
    (hStein : ScalarSteinFactorsStatement) (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax epsilon eta : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hepsilon : 0 < epsilon) (heta : 0 < eta) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      betaMin * Real.log N ≤ (L + 1 : ℝ) → (L + 1 : ℝ) ≤ betaMax * Real.log N →
      softCutoff N ≤ dyadicCutoff N L ∧
        conditionalDistance N L (softCutoff N) ≤ 6 * min 1 (softRate N L epsilon eta) := by
  have hbetaMax : 0 < betaMax := hbetaMin.trans hbeta
  obtain ⟨Nm, hm⟩ := fullDefectMass_div_block_le_eventually
    betaMin betaMax (epsilon / 2) hbetaMin hbeta (by positivity)
  obtain ⟨Nr, hr⟩ := normalized_relation_mass_le_eventually
    betaMin betaMax (epsilon / 2) hbetaMin hbeta (by positivity)
  obtain ⟨Nt, ht⟩ := touching_mass_le_eventually
    betaMin betaMax (epsilon / 2) hbetaMin hbeta (by positivity)
  obtain ⟨Na, ha⟩ := saddleCutoff_nat_admissible_eventually 2 betaMax (by norm_num) hbetaMax
  obtain ⟨Nd, hd⟩ := normalized_fullBadMask_saddle_cost_le_eventually
    hPNT 2 betaMax eta (by norm_num) hbetaMax heta
  obtain ⟨Ne, he⟩ := normalized_degree_and_edges_saddle_le_eventually
    2 betaMax eta (by norm_num) hbetaMax heta
  obtain ⟨Nl, hl⟩ := length_pos_eventually betaMin hbetaMin
  obtain ⟨Nw, hw⟩ := softCutoff_exponent_le_log_eventually (epsilon / 2) (by positivity)
  refine ⟨max Nm (max Nr (max Nt (max Na (max Nd (max Ne (max Nl (max Nw 2))))))), ?_⟩
  intro N hN L hlo hhi
  have hNtwo : 2 ≤ N := by omega
  have hNone : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL := hl N (by omega) L hlo
  obtain ⟨_,hcutpos,hYlo,hYhi⟩ := ha N (by omega) L hhi
  refine ⟨hYhi, ?_⟩
  have hm' : (fullDefectMass L (dyadicBlock N) : ℝ) / N ≤
      (N : ℝ) ^ (-(1 / (3 : ℝ)) + epsilon / 2) :=
    (hm N (by omega) L hlo hhi _ (Finset.Subset.refl _)).trans
      (Real.rpow_le_rpow_of_exponent_le hNone (by linarith))
  have hd' := hd N (by omega) L hhi (dyadicBlock N)
  have hmask : fullBadMask N L (softCutoff N) (dyadicBlock N) = fullBadStarts N L (softCutoff N) :=
    Finset.inter_eq_right.mpr (fullBadStarts_subset_block N L _)
  change ((fullBadMask N L (softCutoff N) (dyadicBlock N)).card : ℝ) / N ≤ _ at hd'
  rw [hmask] at hd'
  have he' := (he N (by omega) L hhi _ (Finset.Subset.refl _)).1
  have hu : 1 / (N : ℝ) ≤ (N : ℝ) ^ (-(1 / (3 : ℝ)) + epsilon / 2) := by
    calc
      _ = (N : ℝ) ^ (-1 : ℝ) := by rw [Real.rpow_neg_one, one_div]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hNone (by linarith)
  have ht' : homogeneousTouchingMass (dyadicCutoff N L) L (dyadicBlock N) / (N : ℝ) ^ 2 ≤
      (N : ℝ) ^ (-(1 / (3 : ℝ)) + epsilon / 2) := by
    calc
      _ ≤ (N : ℝ) ^ (1 + epsilon / 2) / (N : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right (ht N (by omega) L hlo hhi) (by positivity)
      _ = (N : ℝ) ^ (-1 + epsilon / 2) := by
        rw [← Real.rpow_natCast (N : ℝ) 2, ← Real.rpow_sub hNpos]
        congr 1
        norm_num
        ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hNone (by linarith)
  have herr : 0 ≤ eta * saddleNu 2 (Real.log N) := by
    unfold saddleNu
    exact mul_nonneg heta.le (div_nonneg (Real.log_nonneg hNone) hcutpos.le)
  have hbound := conditionalDistance_soft_le_of_arithmetic hStein hNtwo hL
    (show L + 1 ≤ softCutoff N by change L + 1 ≤ ⌊Real.exp (saddleCutoff 2 (Real.log N))⌋₊; omega)
    (hw N (by omega)) herr hu hm' ht' (hr N (by omega) L hlo hhi) he' hd'
  have hpower : -(1 / (3 : ℝ)) + epsilon / 2 + epsilon / 2 = -(1 / (3 : ℝ)) + epsilon := by ring
  simpa only [hpower, softRate, softExponential, positiveLog] using hbound

/-- Equation (4.9), simultaneously for actual F_Y fibres and the infinite count law. -/
theorem theorem_four_three_soft
    (hStein : ScalarSteinFactorsStatement) (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax epsilon eta : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hepsilon : 0 < epsilon) (heta : 0 < eta) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      betaMin * Real.log N ≤ (L + 1 : ℝ) → (L + 1 : ℝ) ≤ betaMax * Real.log N →
      smallPrimeSigmaAlgebra (dyadicCutoff N L) (softCutoff N) =
          MeasurableSpace.comap (restrictToFinite (softCutoff N)) inferInstance ∧
      conditionalDistance N L (softCutoff N) ≤ 6 * min 1 (softRate N L epsilon eta) ∧
      countDistance N L ≤ 6 * min 1 (softRate N L epsilon eta) := by
  obtain ⟨Nzero,hzero⟩ := soft_conditional_rate_eventually
    hStein hPNT betaMin betaMax epsilon eta hbetaMin hbeta hepsilon heta
  refine ⟨Nzero, ?_⟩
  intro N hN L hlo hhi
  obtain ⟨hY, hbound⟩ := hzero N hN L hlo hhi
  exact ⟨conditioningSigma_eq_full_FY hY, hbound,
    (countDistance_le_conditionalDistance N L (softCutoff N)).trans hbound⟩

end
end PaperC.V282.SoftRateAssembly
