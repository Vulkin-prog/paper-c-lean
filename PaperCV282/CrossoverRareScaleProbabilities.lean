import PaperCV282.CrossoverRareScale
import PaperCV282.CrossoverSparseSource

/-! # True hit, independent sparse product, and actual sparse source at the common rare scale -/
namespace PaperC.V282.CrossoverRareScaleProbabilities

open Filter Topology MeasureTheory InfiniteRademacher AllStartSoftPoisson
open BulkPopulation BulkMarkedGeometry CrossoverMarkedTarget CrossoverBulkAtoms CrossoverRareScale
open CrossoverSparseTarget CrossoverSparseWeights CrossoverSparseSource CrossoverMarkedCandidate
open CrossoverPrimeClockStable CrossoverClockRecordMass RarePrefixMass RarePrefixGeometry
open RarePrefixPoisson
open MicroscopicNonvacancy MicroscopicBoundaryDominance SharpConditioning
open PrimeEulerPNT LaishramUniformInput PostQuadraticLiterature ProcessAGGInput

noncomputable section

/-- The contained bulk is nonempty eventually; no artificial nonemptiness input is needed. -/
theorem bulk_nonempty_eventually
    (sizes lengths : ℕ → ℕ) (hsizes : Tendsto sizes atTop atTop)
    (beta delta : ℝ) (hdelta : 0<delta) (hdeltaOne : delta<1)
    (hupper : ∀ᶠ n in atTop,(lengths n : ℝ)≤beta*Real.log (sizes n))
    (hpositive : ∀ᶠ n in atTop,1≤lengths n) :
    ∀ᶠ n in atTop,(bulkStarts (sizes n) (lengths n) delta).Nonempty := by
  have ht := population_ratio_tendsto_one sizes lengths hsizes beta delta hdelta hdeltaOne hupper hpositive
  filter_upwards [ht.eventually (lt_mem_nhds (by norm_num : (0 : ℝ)<1))] with n hn
  by_contra he
  have hz := Finset.not_nonempty_iff_eq_empty.mp he
  simp only [hz,Finset.card_empty,Nat.cast_zero,zero_div] at hn
  exact (lt_irrefl _ hn)

/-- Equation (7.18) at the actual target's denominator alpha_L+lambda_bulk. -/
theorem hit_probability_ratio_tendsto_one
    (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (hLS : UniformPrimeDivisorStatement) (hShorey : ShoreySquareProductStatement)
    (hNR : PellInput.NicolasRobinDivisorLogBoundStatement)
    (sizes lengths : ℕ → ℕ) (hsizes : Tendsto sizes atTop atTop) (hlengths : Tendsto lengths atTop atTop)
    (beta delta : ℝ) (hbeta : 0<beta) (hdelta : 0<delta) (hdeltaOne : delta<1)
    (hupper : ∀ᶠ n in atTop,(lengths n : ℝ)≤beta*Real.log (sizes n))
    (hrare : Tendsto (fun n=>(fullRate (sizes n) (lengths n) : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n=>hitProbability (sizes n) (lengths n)/rareScale (sizes n) (lengths n) delta)
      atTop (𝓝 1) := by
  have hh := equation_seven_eighteen hAGG hPNT hLS hShorey hNR sizes lengths hsizes hlengths
    beta delta hbeta hdelta hdeltaOne hupper hrare
  have hd := denominator_ratio_tendsto_one hLS hShorey hPNT sizes lengths hsizes hlengths
    beta delta hdelta hdeltaOne hupper
  have ht := hh.mul hd
  simp only [mul_one] at ht
  apply ht.congr'
  filter_upwards [hsizes.eventually (eventually_ge_atTop 1)] with n hn
  have hp : 0<microscopicProbability (lengths n)+(fullRate (sizes n) (lengths n) : ℝ) := by
    have hq : 0≤microscopicProbability (lengths n) := by exact measureReal_nonneg
    have hl : 0<(fullRate (sizes n) (lengths n) : ℝ) := by
      change 0<(sizes n : ℝ)/(2 : ℝ)^lengths n
      positivity
    positivity
  field_simp

/-- The product sparse event has the common rare mass, uniformly in the moving mixture weights. -/
theorem product_sparse_ratio_tendsto_one
    (sizes lengths : ℕ → ℕ) (hsizes : Tendsto sizes atTop atTop) (hlengths : Tendsto lengths atTop atTop)
    (K : ℕ) (beta delta : ℝ) (hdelta : 0<delta) (hdeltaOne : delta<1)
    (hupper : ∀ᶠ n in atTop,(lengths n : ℝ)≤beta*Real.log (sizes n))
    (hrare : Tendsto (fun n=>(fullRate (sizes n) (lengths n) : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n=>(productJoint (bulkStarts (sizes n) (lengths n) delta) (lengths n) K).real
      (sparseEvent (bulkStarts (sizes n) (lengths n) delta))/rareScale (sizes n) (lengths n) delta)
      atTop (𝓝 1) := by
  have hb := bulk_rate_tendsto_zero sizes lengths hsizes beta delta hdelta hdeltaOne hupper
    (hlengths.eventually (eventually_ge_atTop 1)) hrare
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _=>norm_nonneg _) ?_
    (by simpa using hb.const_mul 2)
  filter_upwards [bulk_nonempty_eventually sizes lengths hsizes beta delta hdelta hdeltaOne hupper
    (hlengths.eventually (eventually_ge_atTop 1))] with n hn
  rw [Real.norm_eq_abs,sparse_mass _ hn,rareScale]
  exact sparse_mass_relative_error (by exact_mod_cast borderRate_pos (lengths n))
    (borderRate_le_one _) (by positivity)

/-- Stable factorization is negligible relative to alpha+lambda_bulk, not just lambda_full. -/
theorem truncated_joint_rare_scale_tendsto_zero
    (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (sizes lengths : ℕ → ℕ) (hsizes : Tendsto sizes atTop atTop) (hlengths : Tendsto lengths atTop atTop)
    (K : ℕ) (beta delta : ℝ) (hbeta : 0<beta) (hdelta : 0<delta) (hdeltaOne : delta<1)
    (hupper : ∀ᶠ n in atTop,(lengths n : ℝ)≤beta*Real.log (sizes n))
    (hrare : Tendsto (fun n=>(fullRate (sizes n) (lengths n) : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n=>truncatedJointDistance (sizes n) (lengths n) K delta/
      rareScale (sizes n) (lengths n) delta) atTop (𝓝 0) := by
  apply relative_zero_of_half_le
    (Eventually.of_forall fun _=>truncatedJointDistance_nonneg _ _ _ _) ?_
    (full_rate_half_le_eventually sizes lengths hsizes beta delta hdelta hdeltaOne hupper
      (hlengths.eventually (eventually_ge_atTop 1)))
    (truncated_joint_relative_along_subsequence hAGG hPNT sizes lengths hsizes hlengths K
      beta delta hbeta hdelta hupper hrare)
  filter_upwards [hsizes.eventually (eventually_ge_atTop 1)] with n hn
  change 0<(sizes n : ℝ)/(2 : ℝ)^lengths n
  positivity

/-- The genuine joint source uses the same prime clock and all signed bulk marks. -/
theorem source_sparse_ratio_tendsto_one
    (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (sizes lengths : ℕ → ℕ) (hsizes : Tendsto sizes atTop atTop) (hlengths : Tendsto lengths atTop atTop)
    (K : ℕ) (beta delta : ℝ) (hbeta : 0<beta) (hdelta : 0<delta) (hdeltaOne : delta<1)
    (hupper : ∀ᶠ n in atTop,(lengths n : ℝ)≤beta*Real.log (sizes n))
    (hrare : Tendsto (fun n=>(fullRate (sizes n) (lengths n) : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n=>(sourceJoint (sizes n) (lengths n) K delta).real
      (sparseEvent (bulkStarts (sizes n) (lengths n) delta))/rareScale (sizes n) (lengths n) delta)
      atTop (𝓝 1) := by
  have hp := product_sparse_ratio_tendsto_one sizes lengths hsizes hlengths K beta delta
    hdelta hdeltaOne hupper hrare
  have ht := truncated_joint_rare_scale_tendsto_zero hAGG hPNT sizes lengths hsizes hlengths K
    beta delta hbeta hdelta hdeltaOne hupper hrare
  have hd : Tendsto (fun n=>
      (sourceJoint (sizes n) (lengths n) K delta).real (sparseEvent (bulkStarts (sizes n) (lengths n) delta)) /
        rareScale (sizes n) (lengths n) delta-
      (productJoint (bulkStarts (sizes n) (lengths n) delta) (lengths n) K).real
        (sparseEvent (bulkStarts (sizes n) (lengths n) delta)) /
        rareScale (sizes n) (lengths n) delta) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun _=>norm_nonneg _) ?_ ht
    filter_upwards [] with n
    rw [Real.norm_eq_abs,← sub_div,abs_div,abs_of_pos (rareScale_pos _ _ _)]
    apply div_le_div_of_nonneg_right ?_ (rareScale_pos _ _ _).le
    exact discrepancy_le _ _ _ (Set.to_countable _).measurableSet
  simpa only [sub_add_cancel,zero_add] using hd.add hp

theorem source_sparse_event_ratio_tendsto_one
    (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (sizes lengths : ℕ → ℕ) (hsizes : Tendsto sizes atTop atTop) (hlengths : Tendsto lengths atTop atTop)
    (K : ℕ) (beta delta : ℝ) (hbeta : 0<beta) (hdelta : 0<delta) (hdeltaOne : delta<1)
    (hupper : ∀ᶠ n in atTop,(lengths n : ℝ)≤beta*Real.log (sizes n))
    (hrare : Tendsto (fun n=>(fullRate (sizes n) (lengths n) : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n=>infiniteRademacherMeasure.real (sourceSparseEvent (sizes n) (lengths n) K delta)/
      rareScale (sizes n) (lengths n) delta) atTop (𝓝 1) := by
  simpa only [sourceSparse_mass] using source_sparse_ratio_tendsto_one hAGG hPNT sizes lengths
    hsizes hlengths K beta delta hbeta hdelta hdeltaOne hupper hrare

end
end PaperC.V282.CrossoverRareScaleProbabilities
