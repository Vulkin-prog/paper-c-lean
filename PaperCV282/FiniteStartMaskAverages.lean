import PaperCV282.FiniteStartMaskModel
import PaperCV282.ScalarPoissonBounds

/-! # Exact finite probability identities on arbitrary start masks

The mean over all small-prime assignments is the actual full-cylinder law.
Good marginals are derived from private prime coordinates; no probability
approximation or asymptotic hypothesis appears in these identities.
-/
namespace PaperC.V282.FiniteStartMaskAverages

open Affine ArratiaGoldsteinGordonInput ConditionalDependencyGraph
open ConditionalAGGInstantiation ConditionalAGGAverage ConditionalStartProbability
open LargePrimeDependencyGraph SectionThirteenFiniteBound SectionThirteenCouplings
open FiniteStartMaskModel ScalarSteinInput ScalarPoissonBounds
open scoped BigOperators NNReal

noncomputable section

local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

/-- The source rate assigned to an actual population. -/
def maskRate (L : ℕ) (mask : Finset ℕ) : ℝ≥0 :=
  ⟨(mask.card : ℝ)/(2 : ℝ)^L,by positivity⟩

theorem marginal_eq_baseline {C L Y : ℕ} (mask : Finset ℕ)
    (hL : 0<L) (hLY : L+1≤Y) (sigma : SmallSample C Y) (x : mask)
    (hx : 2≤x.val) (hcut : x.val+L≤C)
    (hgood : ∀ i : Fin L, ¬DefectivePredicate.HDefective Y (x.val+i.val)) :
    marginal (largeUniformPMF C Y) (conditionedIndicator C L Y mask sigma) x =
      (1 : ℝ)/(2 : ℝ)^L := by
  classical
  simp only [marginal,conditionedIndicator_eq_true]
  rw [eventProbability_largeUniformPMF_eq,
    finiteUniformProbability_conditionedStart_eq C Y x.val L hL sigma,
    conditionedStartProbability_eq_baseline hx hL hLY (fun i => by have := i.isLt;omega) hgood sigma]
  norm_num

/-- No positivity or location assumption is needed for the true averaging identity. -/
theorem average_marginal (C L Y : ℕ) (mask : Finset ℕ) (x : mask) :
    finiteUniformAverage (fun sigma : SmallSample C Y =>
      marginal (largeUniformPMF C Y) (conditionedIndicator C L Y mask sigma) x) =
      ((uniformEventProbability (fun omega : SampleSpace C => startAt omega x.val L) : ℚ) : ℝ) := by
  classical
  simpa only [marginal,conditionedIndicator_eq_true] using
    finiteUniformAverage_largeEventProbability_eq_full C Y (fun omega => startAt omega x.val L)

/-- The joint identity holds also for defective or coincident sites. -/
theorem average_joint (C L Y : ℕ) (mask : Finset ℕ) (x y : mask) :
    finiteUniformAverage (fun sigma : SmallSample C Y =>
      jointMarginal (largeUniformPMF C Y) (conditionedIndicator C L Y mask sigma) x y) =
      ((uniformEventProbability (fun omega : SampleSpace C =>
        startAt omega x.val L ∧ startAt omega y.val L) : ℚ) : ℝ) := by
  classical
  simpa only [jointMarginal,conditionedIndicator_eq_true] using
    finiteUniformAverage_largeEventProbability_eq_full C Y
      (fun omega => startAt omega x.val L ∧ startAt omega y.val L)

/-- For a genuinely good population the exact mean is independent of the exposed signs. -/
theorem poissonRate_eq_maskRate {C L Y : ℕ} (mask : Finset ℕ)
    (hL : 0<L) (hLY : L+1≤Y) (hpos : ∀ x∈mask,2≤x)
    (hcut : ∀ x∈mask,x+L≤C)
    (hgood : ∀ x∈mask,∀ i : Fin L, ¬DefectivePredicate.HDefective Y (x+i.val))
    (sigma : SmallSample C Y) :
    poissonRate (largeUniformPMF C Y) (conditionedIndicator C L Y mask sigma) = maskRate L mask := by
  apply NNReal.eq
  change poissonParameter _ _ = _
  unfold poissonParameter
  simp_rw [marginal_eq_baseline mask hL hLY sigma _ (hpos _ (Subtype.mem _))
    (hcut _ (Subtype.mem _)) (hgood _ (Subtype.mem _))]
  simp [maskRate,div_eq_mul_inv]
  rfl

/-- Finite scalar Stein comparison for any actual good population. -/
theorem good_scalar_bound (hStein : ScalarSteinFactorsStatement) {C L Y : ℕ}
    (mask : Finset ℕ) (hL : 0<L) (hLY : L+1≤Y) (hpos : ∀ x∈mask,2≤x)
    (hcut : ∀ x∈mask,x+L≤C)
    (hgood : ∀ x∈mask,∀ i : Fin L, ¬DefectivePredicate.HDefective Y (x+i.val))
    (sigma : SmallSample C Y) :
    natTotalVariation (conditionalLaw C L Y mask sigma) (poissonMass (maskRate L mask)) ≤
      firstSteinFactor (maskRate L mask) *
        (bOne (largeUniformPMF C Y) (conditionedIndicator C L Y mask sigma) (startMaskGraph L Y mask) +
         bTwo (largeUniformPMF C Y) (conditionedIndicator C L Y mask sigma) (startMaskGraph L Y mask)) := by
  have h := scalar_poisson_bound hStein (largeUniformPMF C Y)
    (conditionedIndicator C L Y mask sigma) (startMaskGraph L Y mask)
    (hasExactDependencyGraph_conditionedIndicator mask hL sigma)
  rwa [poissonRate_eq_maskRate mask hL hLY hpos hcut hgood sigma] at h

/-- Every conditional mass is the actual event probability of the conditioned count. -/
theorem conditionalLaw_apply (C L Y : ℕ) (mask : Finset ℕ) (sigma : SmallSample C Y) (k : ℕ) :
    conditionalLaw C L Y mask sigma k = eventProbability (largeUniformPMF C Y)
      (fun eta => finiteStartCount C L mask (assemble C Y sigma eta)=k) := by
  classical
  simp only [conditionalLaw,finiteNatLaw,eventProbability,indicatorSum_eq_count]
  apply Finset.sum_congr rfl
  intro eta _
  by_cases h : finiteStartCount C L mask (assemble C Y sigma eta)=k <;> simp [h]

/-- Every unconditional mass is the actual full-cylinder count event. -/
theorem finiteLaw_apply (C L : ℕ) (mask : Finset ℕ) (k : ℕ) :
    finiteLaw C L mask k = ((uniformEventProbability
      (fun omega : SampleSpace C => finiteStartCount C L mask omega=k) : ℚ) : ℝ) := by
  classical
  rw [← finiteUniformProbability_eq_uniformEventProbability,← eventProbability_fullUniformPMF_eq]
  simp only [finiteLaw,finiteNatLaw,eventProbability]
  apply Finset.sum_congr rfl
  intro omega _
  by_cases h : finiteStartCount C L mask omega=k <;> simp [h]

/-- The law of total probability, without replacing the actual random variable. -/
theorem average_conditionalLaw_eq_finiteLaw (C L Y : ℕ) (mask : Finset ℕ) :
    (fun k => finiteUniformAverage (fun sigma : SmallSample C Y => conditionalLaw C L Y mask sigma k)) =
      finiteLaw C L mask := by
  funext k
  simp_rw [conditionalLaw_apply]
  rw [finiteLaw_apply]
  exact finiteUniformAverage_largeEventProbability_eq_full C Y
    (fun omega => finiteStartCount C L mask omega=k)

/-- Unconditional mixing contracts the conditional scalar comparison. -/
theorem finite_tv_le_average (C L Y : ℕ) (mask : Finset ℕ) (rate : ℝ≥0) :
    natTotalVariation (finiteLaw C L mask) (poissonMass rate) ≤
      finiteUniformAverage (fun sigma : SmallSample C Y =>
        natTotalVariation (conditionalLaw C L Y mask sigma) (poissonMass rate)) := by
  rw [← average_conditionalLaw_eq_finiteLaw C L Y mask]
  apply natTotalVariation_uniformMixture_le
  intro sigma
  exact summable_abs_sub_of_nonneg (summable_finiteNatLaw _ _) (hasSum_poissonMass _).summable
    (finiteNatLaw_nonneg _ _) (poissonMass_nonneg _)

end
end PaperC.V282.FiniteStartMaskAverages
