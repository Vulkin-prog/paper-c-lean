import PaperCV282.MesoscopicCutoff

/-! # Deep-start negligibility in the rare regime -/
namespace PaperC.V282.MesoscopicRareLimit

open Filter MeasureTheory InfiniteRademacher InfiniteStartProbabilityTransfer
open DeepStartEvents PostQuadraticLiterature BalasubramanianShoreyInput PostQuadraticDecay
open scoped Topology

noncomputable section

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

local instance instProbabilityInfiniteRademacher : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

/-- Negligibility of the actual deep event relative to the border mass plus the bulk mean.
This stronger fixed-band conclusion does not require the bulk mean itself to vanish. -/
theorem deep_probability_negligible_in_band
    (betaMin betaMax delta : ℝ) (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax)
    (hdelta : 0 < delta) (hdeltaOne : delta < 1)
    (hShorey : ShoreySquareProductStatement)
    (hPNT : PrimeEulerPNT.PrimeNumberTheoremRemainder)
    (hNR : PellInput.NicolasRobinDivisorLogBoundStatement)
    (sizes lengths : ℕ → ℕ) (hsizes : Tendsto sizes atTop atTop)
    (hlengths : Tendsto lengths atTop atTop)
    (hband : ∀ᶠ n : ℕ in atTop,
      betaMin * Real.log (sizes n) ≤ (lengths n + 1 : ℕ) ∧
      (lengths n + 1 : ℕ) ≤ betaMax * Real.log (sizes n)) :
    Tendsto (fun n : ℕ =>
      infiniteRademacherMeasure.real
        {omega | ∃ x : ℕ, 2 * (lengths n) ^ 2 < x ∧ (x : ℝ) < (sizes n : ℝ) ^ delta ∧
          omega ∈ infiniteStartEvent x (lengths n)} /
        (((2 : ℝ)⁻¹) ^ Nat.primeCounting (lengths n) + (sizes n : ℝ) / (2 : ℝ) ^ lengths n))
      atTop (𝓝 0) := by
  obtain ⟨theta, K, hK, Mzero, h⟩ := equation_seven_eight
    betaMin betaMax hbetaMin hbeta hShorey hPNT hNR
  have hpower : Tendsto (fun n : ℕ => (sizes n : ℝ) ^ (delta - 1)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_sub] using
      (tendsto_rpow_neg_atTop (by linarith : 0 < 1 - delta)).comp
        (tendsto_natCast_atTop_atTop.comp hsizes)
  have htail := (exceptional_relative_to_border_tendsto_zero hPNT theta K hK).comp hlengths
  have hsum := hpower.add htail
  apply squeeze_zero' (Eventually.of_forall (fun n => by positivity)) _
    (by simpa only [Function.comp_def, add_zero] using hsum)
  filter_upwards [hband, hsizes.eventually (eventually_ge_atTop (max Mzero 1))] with n hn hN
  let M := sizes n
  let L := lengths n
  let b : ℝ := ((2 : ℝ)⁻¹) ^ Nat.primeCounting L
  let lambda : ℝ := (M : ℝ) / (2 : ℝ) ^ L
  let E : ℝ := Real.exp (K * ((L : ℝ) / Real.log L)) * (2 : ℝ) ^ (-gap (L + 1) theta)
  have hM : 0 < (M : ℝ) := by exact_mod_cast (show 0 < M by dsimp [M]; omega)
  have hb : 0 < b := by dsimp [b]; positivity
  have hlambda : 0 < lambda := by dsimp [lambda]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hp := h M (by dsimp [M]; omega) L hn.1 hn.2 delta hdelta hdeltaOne
  calc
    _ ≤ ((M : ℝ) ^ delta / (2 : ℝ) ^ L + E) / (b + lambda) :=
      div_le_div_of_nonneg_right hp (by positivity)
    _ = ((M : ℝ) ^ delta / (2 : ℝ) ^ L) / (b + lambda) + E / (b + lambda) := add_div _ _ _
    _ ≤ ((M : ℝ) ^ delta / (2 : ℝ) ^ L) / lambda + E / b := by
      exact add_le_add (div_le_div_of_nonneg_left (by positivity) hlambda (by linarith))
        (div_le_div_of_nonneg_left hE hb (by linarith))
    _ = (M : ℝ) ^ (delta - 1) + E / b := by
      congr 1
      dsimp [lambda]
      rw [Real.rpow_sub hM, Real.rpow_one]
      field_simp

/-- The rare-mean assumption supplies the lower logarithmic band; no lower band is
added to the hypotheses of the final assertion of Proposition 7.3. -/
theorem rare_mean_supplies_lower_band
    (sizes lengths : ℕ → ℕ)
    (hrare : Tendsto (fun n => (sizes n : ℝ) / (2 : ℝ) ^ lengths n) atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop,
      1 / (2 * Real.log 2) * Real.log (sizes n) ≤ (lengths n + 1 : ℕ) := by
  filter_upwards [hrare.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with n hn
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  by_cases hs : sizes n = 0
  · simp only [hs, Nat.cast_zero, Real.log_zero, mul_zero]
    positivity
  have hspos : 0 < (sizes n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hs)
  have hm : (sizes n : ℝ) ≤ (2 : ℝ) ^ lengths n := (div_lt_one (by positivity)).mp hn |>.le
  have hl := Real.log_le_log hspos hm
  rw [Real.log_pow] at hl
  have hmul := mul_le_mul_of_nonneg_left hl (show 0 ≤ 1 / (2 * Real.log 2) by positivity)
  have he : 1 / (2 * Real.log 2) * ((lengths n : ℝ) * Real.log 2) = (lengths n : ℝ) / 2 := by field_simp
  rw [he] at hmul
  push_cast
  linarith [show 0 ≤ (lengths n : ℝ) by positivity]

/-- The final rare-regime assertion of Proposition 7.3, first with the smaller exact
border-plus-bulk denominator.  Any microscopic non-vacancy probability dominates it. -/
theorem proposition_seven_three_rare_negligibility
    (betaMax delta : ℝ) (hbetaMax : 0 < betaMax) (hdelta : 0 < delta) (hdeltaOne : delta < 1)
    (hShorey : ShoreySquareProductStatement)
    (hPNT : PrimeEulerPNT.PrimeNumberTheoremRemainder)
    (hNR : PellInput.NicolasRobinDivisorLogBoundStatement)
    (sizes lengths : ℕ → ℕ) (hsizes : Tendsto sizes atTop atTop)
    (hlengths : Tendsto lengths atTop atTop)
    (hupper : ∀ᶠ n : ℕ in atTop, (lengths n + 1 : ℕ) ≤ betaMax * Real.log (sizes n))
    (hrare : Tendsto (fun n => (sizes n : ℝ) / (2 : ℝ) ^ lengths n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
      infiniteRademacherMeasure.real
        {omega | ∃ x : ℕ, 2 * (lengths n) ^ 2 < x ∧ (x : ℝ) < (sizes n : ℝ) ^ delta ∧
          omega ∈ infiniteStartEvent x (lengths n)} /
        (((2 : ℝ)⁻¹) ^ Nat.primeCounting (lengths n) + (sizes n : ℝ) / (2 : ℝ) ^ lengths n))
      atTop (𝓝 0) := by
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hbb : 1 / (2 * Real.log 2) < betaMax + 2 / Real.log 2 := by
    have hc : 1 / (2 * Real.log 2) < 2 / Real.log 2 := by
      apply (div_lt_div_iff₀ (by positivity) hlog).mpr
      nlinarith
    linarith
  apply deep_probability_negligible_in_band (1 / (2 * Real.log 2))
    (betaMax + 2 / Real.log 2) delta (by positivity) hbb hdelta hdeltaOne
    hShorey hPNT hNR sizes lengths hsizes hlengths
  filter_upwards [rare_mean_supplies_lower_band sizes lengths hrare, hupper,
    hsizes.eventually (eventually_ge_atTop 1)] with n hlo hup hN
  refine ⟨hlo, hup.trans ?_⟩
  have hp : 0 ≤ Real.log (sizes n : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity : 0 ≤ 2 / Real.log 2)) hp

end
end PaperC.V282.MesoscopicRareLimit
