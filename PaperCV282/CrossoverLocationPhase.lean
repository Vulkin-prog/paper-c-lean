import PaperCV282.RarePrefixMass

/-! # Exact phases and limiting weights for the rare crossover -/
namespace PaperC.V282.CrossoverLocationPhase

open Filter Topology BulkPopulation RarePrefixMass AllStartSoftPoisson MicroscopicNonvacancy
open MicroscopicBoundaryDominance LaishramUniformInput PostQuadraticLiterature PrimeEulerPNT
open scoped NNReal

noncomputable section

/-- The printed logarithm is base two; the prime count belongs to the same base length. -/
def crossoverPhase (M L : ℕ) : ℝ :=
  (L : ℝ)-Real.log M/Real.log 2-Nat.primeCounting L

theorem rate_div_border_eq {M : ℕ} (hM : 0 < M) (L : ℕ) :
    (fullRate M L : ℝ)/((2 : ℝ)⁻¹)^Nat.primeCounting L =
      Real.exp (-crossoverPhase M L*Real.log 2) := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hlog : Real.log (2 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have he : -crossoverPhase M L*Real.log 2 = Real.log M+
      ((Nat.primeCounting L : ℝ)*Real.log 2-(L : ℝ)*Real.log 2) := by
    unfold crossoverPhase
    field_simp
    ring
  rw [he,Real.exp_add,Real.exp_sub,Real.exp_log hMr,Real.exp_nat_mul,Real.exp_nat_mul,
    Real.exp_log (by norm_num : (0 : ℝ)<2)]
  change ((M : ℝ)/(2 : ℝ)^L)/((2 : ℝ)⁻¹)^Nat.primeCounting L = _
  rw [inv_pow]
  field_simp

theorem rate_div_border_tendsto
    (sizes lengths : ℕ → ℕ) (hsizes : Tendsto sizes atTop atTop) (s : ℝ)
    (hphase : Tendsto (fun n => crossoverPhase (sizes n) (lengths n)) atTop (𝓝 s)) :
    Tendsto (fun n => (fullRate (sizes n) (lengths n) : ℝ)/
      ((2 : ℝ)⁻¹)^Nat.primeCounting (lengths n)) atTop (𝓝 ((2 : ℝ)^(-s))) := by
  have ht := Real.continuous_exp.continuousAt.tendsto.comp ((hphase.neg).mul_const (Real.log 2))
  have ht' : Tendsto (fun n => Real.exp (-crossoverPhase (sizes n) (lengths n)*Real.log 2))
      atTop (𝓝 ((2 : ℝ)^(-s))) := by
    simpa only [Real.rpow_def_of_pos (by norm_num : (0 : ℝ)<2), mul_comm, Function.comp_def] using ht
  apply ht'.congr'
  filter_upwards [hsizes.eventually (eventually_ge_atTop 1)] with n hn
  exact (rate_div_border_eq (by omega : 0 < sizes n) (lengths n)).symm

/-- The exact microscopic probability and the border have the same phase-dependent crossover. -/
theorem rate_div_microscopic_tendsto
    (hLS : UniformPrimeDivisorStatement) (hShorey : ShoreySquareProductStatement)
    (hPNT : PrimeNumberTheoremRemainder)
    (sizes lengths : ℕ → ℕ) (hsizes : Tendsto sizes atTop atTop) (hlengths : Tendsto lengths atTop atTop)
    (s : ℝ) (hphase : Tendsto (fun n => crossoverPhase (sizes n) (lengths n)) atTop (𝓝 s)) :
    Tendsto (fun n => (fullRate (sizes n) (lengths n) : ℝ)/microscopicProbability (lengths n))
      atTop (𝓝 ((2 : ℝ)^(-s))) := by
  have ht := (rate_div_border_tendsto sizes lengths hsizes s hphase).div
    ((microscopic_probability_ratio_tendsto_one hLS hShorey hPNT).comp hlengths) (by norm_num : (1 : ℝ)≠0)
  apply (show Tendsto _ atTop (𝓝 ((2 : ℝ)^(-s))) from by simpa only [div_one] using ht).congr
  intro n
  dsimp only [Pi.div_apply, Function.comp_def]
  have ha : ((2 : ℝ)⁻¹)^Nat.primeCounting (lengths n) ≠ 0 := by positivity
  field_simp

/-- The actual finite contained population gives the same bulk mixing weight. -/
theorem bulk_div_border_tendsto
    (sizes lengths : ℕ → ℕ) (hsizes : Tendsto sizes atTop atTop)
    (beta delta : ℝ) (hdelta : 0 < delta) (hdeltaOne : delta < 1)
    (hupper : ∀ᶠ n in atTop, (lengths n : ℝ) ≤ beta*Real.log (sizes n))
    (hpositive : ∀ᶠ n in atTop, 1 ≤ lengths n)
    (s : ℝ) (hphase : Tendsto (fun n => crossoverPhase (sizes n) (lengths n)) atTop (𝓝 s)) :
    Tendsto (fun n => (bulkRate (sizes n) (lengths n) delta : ℝ)/
      ((2 : ℝ)⁻¹)^Nat.primeCounting (lengths n)) atTop (𝓝 ((2 : ℝ)^(-s))) := by
  have ht := (bulkRate_ratio_tendsto_one sizes lengths hsizes beta delta hdelta hdeltaOne hupper hpositive).mul
    (rate_div_border_tendsto sizes lengths hsizes s hphase)
  apply (show Tendsto _ atTop (𝓝 ((2 : ℝ)^(-s))) from by simpa only [one_mul] using ht).congr'
  filter_upwards [hsizes.eventually (eventually_ge_atTop 1)] with n hn
  have hp : (fullRate (sizes n) (lengths n) : ℝ) ≠ 0 := by
    change (sizes n : ℝ)/(2 : ℝ)^lengths n ≠ 0
    positivity
  field_simp

/-- Both coefficients in (7.19), with the exact moving population before taking the limit. -/
theorem mixture_weights_tendsto
    (sizes lengths : ℕ → ℕ) (hsizes : Tendsto sizes atTop atTop)
    (beta delta : ℝ) (hdelta : 0 < delta) (hdeltaOne : delta < 1)
    (hupper : ∀ᶠ n in atTop, (lengths n : ℝ) ≤ beta*Real.log (sizes n))
    (hpositive : ∀ᶠ n in atTop, 1 ≤ lengths n)
    (s : ℝ) (hphase : Tendsto (fun n => crossoverPhase (sizes n) (lengths n)) atTop (𝓝 s)) :
    Tendsto (fun n => ((2 : ℝ)⁻¹)^Nat.primeCounting (lengths n) /
      (((2 : ℝ)⁻¹)^Nat.primeCounting (lengths n)+(bulkRate (sizes n) (lengths n) delta : ℝ)))
      atTop (𝓝 (1/(1+(2 : ℝ)^(-s)))) ∧
    Tendsto (fun n => (bulkRate (sizes n) (lengths n) delta : ℝ) /
      (((2 : ℝ)⁻¹)^Nat.primeCounting (lengths n)+(bulkRate (sizes n) (lengths n) delta : ℝ)))
      atTop (𝓝 ((2 : ℝ)^(-s)/(1+(2 : ℝ)^(-s)))) := by
  have ht := bulk_div_border_tendsto sizes lengths hsizes beta delta hdelta hdeltaOne hupper hpositive s hphase
  have hd : 1+(2 : ℝ)^(-s) ≠ 0 := by positivity
  constructor
  · convert tendsto_const_nhds.div (ht.const_add 1) hd using 1
    funext n
    dsimp only [Pi.div_apply]
    have ha : ((2 : ℝ)⁻¹)^Nat.primeCounting (lengths n) ≠ 0 := by positivity
    field_simp
  · convert ht.div (ht.const_add 1) hd using 1
    funext n
    dsimp only [Pi.div_apply]
    have ha : ((2 : ℝ)⁻¹)^Nat.primeCounting (lengths n) ≠ 0 := by positivity
    field_simp

end
end PaperC.V282.CrossoverLocationPhase
