import PaperCV282.CrossoverLocationGrid
import PaperCV282.CrossoverLocationPhase
import PaperCV282.CrossoverMarkedTarget

/-! # Weak convergence of the actual moving location mixture -/
namespace PaperC.V282.CrossoverLocationMixture

open MeasureTheory ProbabilityTheory Filter Topology CrossoverLocationGrid CrossoverLocationPhase
open CrossoverMarkedTarget CrossoverBulkAtoms BulkMarkedGeometry BulkPopulation
open scoped NNReal ENNReal BoundedContinuousFunction

noncomputable section

/-- Convex mixture of genuine probability laws, with its normalization proved. -/
def mixtureLaw (a b : ℝ≥0) (hab : a+b=1) (p q : ProbabilityMeasure ℝ) : ProbabilityMeasure ℝ :=
  ⟨(a : ℝ≥0∞) • (p : Measure ℝ)+(b : ℝ≥0∞) • (q : Measure ℝ),by
    constructor
    simp only [Measure.add_apply,Measure.smul_apply,smul_eq_mul,measure_univ,mul_one]
    exact_mod_cast hab⟩

def zeroLocationLaw : ProbabilityMeasure ℝ := ⟨Measure.dirac 0,inferInstance⟩

theorem integral_mixtureLaw (a b : ℝ≥0) (hab : a+b=1) (p q : ProbabilityMeasure ℝ) (F : ℝ→ᵇℝ) :
    (∫ x,F x ∂(mixtureLaw a b hab p q : Measure ℝ)) =
      (a : ℝ)*(∫ x,F x ∂(p : Measure ℝ))+(b : ℝ)*(∫ x,F x ∂(q : Measure ℝ)) := by
  have hp : Integrable F (a • (p : Measure ℝ)) :=
    ⟨F.continuous.measurable.aestronglyMeasurable,HasFiniteIntegral.of_bounded
      (Eventually.of_forall fun x => F.norm_coe_le_norm x)⟩
  have hq : Integrable F (b • (q : Measure ℝ)) :=
    ⟨F.continuous.measurable.aestronglyMeasurable,HasFiniteIntegral.of_bounded
      (Eventually.of_forall fun x => F.norm_coe_le_norm x)⟩
  rw [show (mixtureLaw a b hab p q : Measure ℝ)=a • (p : Measure ℝ)+b • (q : Measure ℝ) from rfl,
    integral_add_measure hp hq,integral_smul_nnreal_measure,integral_smul_nnreal_measure]
  rfl

theorem mixtureLaw_tendsto (a b : ℕ→ℝ≥0) (hab : ∀n,a n+b n=1)
    (a0 b0 : ℝ≥0) (hzero : a0+b0=1) (p q : ℕ→ProbabilityMeasure ℝ) (p0 q0 : ProbabilityMeasure ℝ)
    (ha : Tendsto (fun n => (a n : ℝ)) atTop (𝓝 (a0 : ℝ)))
    (hb : Tendsto (fun n => (b n : ℝ)) atTop (𝓝 (b0 : ℝ)))
    (hp : Tendsto p atTop (𝓝 p0)) (hq : Tendsto q atTop (𝓝 q0)) :
    Tendsto (fun n => mixtureLaw (a n) (b n) (hab n) (p n) (q n)) atTop
      (𝓝 (mixtureLaw a0 b0 hzero p0 q0)) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto] at hp hq ⊢
  intro F
  simpa only [integral_mixtureLaw] using (ha.mul (hp F)).add (hb.mul (hq F))

def phaseBorderWeight (s : ℝ) : ℝ≥0 := ⟨1/(1+(2 : ℝ)^(-s)),by positivity⟩
def phaseBulkWeight (s : ℝ) : ℝ≥0 := ⟨(2 : ℝ)^(-s)/(1+(2 : ℝ)^(-s)),by positivity⟩

theorem phase_weights_sum (s : ℝ) : phaseBorderWeight s+phaseBulkWeight s=1 := by
  apply NNReal.coe_injective
  change 1/(1+(2 : ℝ)^(-s))+(2 : ℝ)^(-s)/(1+(2 : ℝ)^(-s))=1
  rw [← add_div,div_self (by positivity : 1+(2 : ℝ)^(-s)≠0)]

/-- The exact measure on the right of (7.19). -/
def crossoverLimitLaw (s : ℝ) : ProbabilityMeasure ℝ :=
  mixtureLaw (phaseBorderWeight s) (phaseBulkWeight s) (phase_weights_sum s) zeroLocationLaw unitIntervalLaw

/-- The weights use the actual contained population, and the border location is zero at this scale. -/
def locationMixtureLaw (M L : ℕ) (delta : ℝ) : ProbabilityMeasure ℝ :=
  mixtureLaw (borderWeight (bulkStarts M L delta) L) (bulkWeight (bulkStarts M L delta) L)
    (weights_sum _ L) zeroLocationLaw (bulkLocationLaw M L delta)

/-- Limit of the genuine moving mixture; the source approximation is supplied separately by (7.9). -/
theorem locationMixtureLaw_tendsto
    (sizes lengths : ℕ→ℕ) (hsizes : Tendsto sizes atTop atTop)
    (beta delta : ℝ) (hdelta : 0<delta) (hdeltaOne : delta<1)
    (hupper : ∀ᶠ n in atTop,(lengths n : ℝ)≤beta*Real.log (sizes n))
    (hpositive : ∀ᶠ n in atTop,1≤lengths n)
    (s : ℝ) (hphase : Tendsto (fun n => crossoverPhase (sizes n) (lengths n)) atTop (𝓝 s)) :
    Tendsto (fun n => locationMixtureLaw (sizes n) (lengths n) delta) atTop (𝓝 (crossoverLimitLaw s)) := by
  obtain ⟨ha,hb⟩ := mixture_weights_tendsto sizes lengths hsizes beta delta hdelta hdeltaOne hupper hpositive s hphase
  apply mixtureLaw_tendsto _ _ _ _ _ _ _ _ _ _ _ _ tendsto_const_nhds
    (bulkLocationLaw_tendsto sizes lengths hsizes beta delta hdelta hdeltaOne hupper hpositive)
  · change Tendsto _ atTop (𝓝 (1/(1+(2 : ℝ)^(-s))))
    convert ha using 1
    funext n
    simp only [borderWeight,borderRate,totalRate,bulkRate,FiniteStartMaskAverages.maskRate,
      NNReal.coe_div,NNReal.coe_add,NNReal.coe_pow,NNReal.coe_ofNat,inv_pow,one_div]
    rfl
  · change Tendsto _ atTop (𝓝 ((2 : ℝ)^(-s)/(1+(2 : ℝ)^(-s))))
    convert hb using 1
    funext n
    simp only [bulkWeight,borderRate,totalRate,bulkRate,FiniteStartMaskAverages.maskRate,
      NNReal.coe_div,NNReal.coe_add,NNReal.coe_pow,NNReal.coe_ofNat,inv_pow,one_div]
    rfl

end
end PaperC.V282.CrossoverLocationMixture
