import PaperCV282.CrossoverMarkedConvergence
import PaperCV282.CrossoverRightCensor

/-! # The right-censored version of the actual two-clock crossover

Only the bulk excess is clamped at the end of the finite word. The boundary
clock, site and sign are retained, and the comparison target stays unchanged.
-/
namespace PaperC.V282.CrossoverCensored

open Filter Topology MeasureTheory ProbabilityTheory InfiniteRademacher AllStartSoftPoisson
open CrossoverMarkedModel CrossoverMarkedTarget CrossoverMovingTarget CrossoverSparseSource
open CrossoverRightCensor CrossoverBulkOnePoint CrossoverMarkedConvergence CrossoverConditioningTools
open CrossoverRareScaleProbabilities BulkPopulation BulkMarkedGeometry SharpConditioning
open PrimeEulerPNT ProcessAGGInput LaishramUniformInput PostQuadraticLiterature

open scoped NNReal

noncomputable section

/-- R=M-L+1 is the last allowed base start; the censored excess at x is min(e,R-x). -/
def censorRecord (M L : ℕ) : Record → Record
  | some (Sum.inr (x,(e,s))) => some (Sum.inr (x,(min e (M-L+1-x),s)))
  | r => r

theorem censorRecord_border (M L G : ℕ) : censorRecord M L (borderLabel G)=borderLabel G := rfl

theorem censorRecord_bulk (M L : ℕ) (sites : Finset ℕ) (j : BulkMarkedTypes.SpatialMarkedIndex sites) :
    censorRecord M L (bulkLabel sites j)=bulkLabel sites (censorLabel sites (M-L+1) j) := rfl

/-- The clamped excess gives exactly the run length available in the finite word. -/
theorem censored_run_length {M L x : ℕ} (hLM : L≤M) (hx : x≤M-L+1) (e : ℕ) :
    L+min e (M-L+1-x)=min (L+e) (M+1-x) := by omega

theorem censorRecord_position (M L : ℕ) (r : Record) :
    macroPosition M (censorRecord M L r)=macroPosition M r := by
  cases r with
  | none => rfl
  | some r => cases r <;> rfl

theorem censorRecord_sign (M L : ℕ) (r : Record) :
    positiveSign (censorRecord M L r)=positiveSign r := by
  cases r with
  | none => rfl
  | some r => cases r <;> rfl

theorem borderLaw_censor (M L : ℕ) : borderLaw.map (censorRecord M L)=borderLaw := by
  rw [borderLaw,Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  rfl

/-- The full joint site/sign/excess law, after forgetting only the excess beyond the word. -/
theorem bulkLaw_censor_tv_le (M L : ℕ) (sites : Finset ℕ) (hs : sites.Nonempty)
    (hsites : ∀x∈sites,x≤M-L+1) :
    measureTotalVariation ((bulkLaw sites hs).map (censorRecord M L)) (bulkLaw sites hs)≤
      1/(sites.card : ℝ) := by
  letI instProbabilityCensoredLabel : IsProbabilityMeasure
      ((labelMeasure sites hs).map (censorLabel sites (M-L+1))) :=
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
  have hm : (bulkLaw sites hs).map (censorRecord M L)=
      ((labelMeasure sites hs).map (censorLabel sites (M-L+1))).map (bulkLabel sites) := by
    rw [bulkLaw,Measure.map_map (measurable_of_countable _) (measurable_of_countable _),
      Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
    rfl
  rw [hm]
  exact (measureTotalVariation_map_le _ _ (measurable_of_countable (bulkLabel sites))).trans
    (censor_target_tv_le sites hs (M-L+1) hsites)

/-- The mixture weight can only reduce the censoring cost of the bulk branch. -/
theorem mixedLaw_censor_tv_le (M L : ℕ) (sites : Finset ℕ) (hs : sites.Nonempty)
    (hsites : ∀x∈sites,x≤M-L+1) :
    measureTotalVariation ((mixedLaw sites hs L).map (censorRecord M L)) (mixedLaw sites hs L)≤
      1/(sites.card : ℝ) := by
  letI instProbabilityCensoredMixed : IsProbabilityMeasure ((mixedLaw sites hs L).map (censorRecord M L)) :=
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
  letI instProbabilityCensoredBulk : IsProbabilityMeasure ((bulkLaw sites hs).map (censorRecord M L)) :=
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
  apply (measureTotalVariation_le_iff _ _ _).mpr
  intro S hS
  have hb : borderLaw.real (censorRecord M L ⁻¹' S)=borderLaw.real S := by
    rw [← map_measureReal_apply (measurable_of_countable _) hS,borderLaw_censor]
  have hd := (discrepancy_le ((bulkLaw sites hs).map (censorRecord M L)) (bulkLaw sites hs) S hS).trans
    (bulkLaw_censor_tv_le M L sites hs hsites)
  rw [map_measureReal_apply (measurable_of_countable _) hS] at hd
  rw [map_measureReal_apply (measurable_of_countable _) hS,mixedLaw_real,mixedLaw_real,hb]
  have he : (borderWeight sites L : ℝ)*borderLaw.real S+
      (bulkWeight sites L : ℝ)*(bulkLaw sites hs).real (censorRecord M L ⁻¹' S)-
      ((borderWeight sites L : ℝ)*borderLaw.real S+(bulkWeight sites L : ℝ)*(bulkLaw sites hs).real S)=
      (bulkWeight sites L : ℝ)*((bulkLaw sites hs).real (censorRecord M L ⁻¹' S)-(bulkLaw sites hs).real S) := by ring
  rw [he,abs_mul,abs_of_nonneg (by positivity : 0≤(bulkWeight sites L : ℝ))]
  have hw : (bulkWeight sites L : ℝ)≤1 := by
    have hh := congrArg (fun x : ℝ≥0 => (x : ℝ)) (weights_sum sites L)
    push_cast at hh
    have ha : 0≤(borderWeight sites L : ℝ) := by positivity
    linarith
  exact (mul_le_mul_of_nonneg_left hd (by positivity)).trans
    (mul_le_of_le_one_left (by positivity) hw)

/-- Actual source law, censored after reading the genuine least contained departure. -/
def censoredDistance (M L : ℕ) (delta : ℝ) : ℝ :=
  measureTotalVariation ((conditionalGammaLaw M L delta).map (censorRecord M L)) (targetLaw M L delta)

theorem censoredDistance_le {M L : ℕ} (delta : ℝ) (hLM : L≤M)
    (hs : (bulkStarts M L delta).Nonempty) :
    censoredDistance M L delta≤actualDistance M L delta+1/((bulkStarts M L delta).card : ℝ) := by
  letI instProbabilityGamma : IsProbabilityMeasure (conditionalGammaLaw M L delta) :=
    conditionalGammaLaw_probability delta hLM
  letI instProbabilityCensoredGamma : IsProbabilityMeasure
      ((conditionalGammaLaw M L delta).map (censorRecord M L)) :=
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
  letI instProbabilityCensoredTarget : IsProbabilityMeasure ((targetLaw M L delta).map (censorRecord M L)) :=
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
  have htri := variation_triangle ((conditionalGammaLaw M L delta).map (censorRecord M L))
    ((targetLaw M L delta).map (censorRecord M L)) (targetLaw M L delta)
  have hmap := measureTotalVariation_map_le (conditionalGammaLaw M L delta) (targetLaw M L delta)
    (measurable_of_countable (censorRecord M L))
  have htarget : measureTotalVariation ((targetLaw M L delta).map (censorRecord M L)) (targetLaw M L delta)≤
      1/((bulkStarts M L delta).card : ℝ) := by
    rw [targetLaw_eq hs]
    exact mixedLaw_censor_tv_le M L _ hs (fun x hx=>(mem_bulkStarts M L x delta).mp hx |>.2)
  exact htri.trans (add_le_add hmap htarget)

theorem inverse_bulk_card_tendsto_zero
    (sizes lengths : ℕ → ℕ) (hsizes : Tendsto sizes atTop atTop)
    (beta delta : ℝ) (hdelta : 0<delta) (hdeltaOne : delta<1)
    (hupper : ∀ᶠ n in atTop,(lengths n : ℝ)≤beta*Real.log (sizes n))
    (hpositive : ∀ᶠ n in atTop,1≤lengths n) :
    Tendsto (fun n=>1/((bulkStarts (sizes n) (lengths n) delta).card : ℝ)) atTop (𝓝 0) := by
  have hr := (population_ratio_tendsto_one sizes lengths hsizes beta delta hdelta hdeltaOne hupper hpositive).inv₀
    (by norm_num : (1 : ℝ)≠0)
  have hi : Tendsto (fun n=>1/(sizes n : ℝ)) atTop (𝓝 0) := by
    simpa only [one_div,Function.comp_def] using
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hsizes)
  have ht := hr.mul hi
  simp only [mul_zero] at ht
  apply ht.congr'
  filter_upwards [hsizes.eventually (eventually_ge_atTop 1),
    bulk_nonempty_eventually sizes lengths hsizes beta delta hdelta hdeltaOne hupper hpositive] with n hn hs
  have hM : (sizes n : ℝ)≠0 := by exact_mod_cast (show sizes n≠0 by omega)
  have hc : ((bulkStarts (sizes n) (lengths n) delta).card : ℝ)≠0 := by
    exact_mod_cast (Finset.card_pos.mpr hs).ne'
  field_simp

/-- The right-censored variant of Theorem 7.9, with the same uncensored moving target. -/
theorem theorem_seven_nine_censored
    (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (hLS : UniformPrimeDivisorStatement) (hShorey : ShoreySquareProductStatement)
    (hNR : PellInput.NicolasRobinDivisorLogBoundStatement)
    (sizes lengths : ℕ → ℕ) (hsizes : Tendsto sizes atTop atTop) (hlengths : Tendsto lengths atTop atTop)
    (beta delta : ℝ) (hbeta : 0<beta) (hdelta : 0<delta) (hdeltaOne : delta<1)
    (hupper : ∀ᶠ n in atTop,(lengths n : ℝ)≤beta*Real.log (sizes n))
    (hrare : Tendsto (fun n=>(fullRate (sizes n) (lengths n) : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n=>censoredDistance (sizes n) (lengths n) delta) atTop (𝓝 0) := by
  have ht := theorem_seven_nine hAGG hPNT hLS hShorey hNR sizes lengths hsizes hlengths
    beta delta hbeta hdelta hdeltaOne hupper hrare
  have hi := inverse_bulk_card_tendsto_zero sizes lengths hsizes beta delta hdelta hdeltaOne hupper
    (hlengths.eventually (eventually_ge_atTop 1))
  have hc := RarePrefixMass.logarithmic_lengths_eventually_contained sizes lengths hsizes beta hupper
  apply squeeze_zero' ?_ ?_ (by simpa only [add_zero] using ht.add hi)
  · filter_upwards [hc] with n hn
    letI instProbabilityGamma : IsProbabilityMeasure (conditionalGammaLaw (sizes n) (lengths n) delta) :=
      conditionalGammaLaw_probability delta hn
    letI instProbabilityCensoredGamma : IsProbabilityMeasure
        ((conditionalGammaLaw (sizes n) (lengths n) delta).map (censorRecord (sizes n) (lengths n))) :=
      Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
    exact measureTotalVariation_nonneg _ _
  · filter_upwards [hc,bulk_nonempty_eventually sizes lengths hsizes beta delta hdelta hdeltaOne hupper
      (hlengths.eventually (eventually_ge_atTop 1))] with n hn hs
    exact censoredDistance_le delta hn hs

end
end PaperC.V282.CrossoverCensored
