import PaperCV282.PoissonCLT

/-! # Joint weak limits of independent finite Poisson families

The probability laws below are actual finite products, placed in Euclidean
space. Some coordinates may be centered large Poisson variables and others
may remain unscaled Poisson variables.
-/
namespace PaperC.V282.FinitePoissonCLT

open MeasureTheory ProbabilityTheory Filter WithLp PoissonCLT
open scoped Topology NNReal

noncomputable section

variable {I : Type*} [Fintype I]

def euclideanProductLaw (laws : I → ProbabilityMeasure ℝ) :
    ProbabilityMeasure (EuclideanSpace ℝ I) :=
  ⟨(Measure.pi (fun i => (laws i : Measure ℝ))).map (toLp 2),
    Measure.isProbabilityMeasure_map (by fun_prop)⟩

theorem charFun_euclideanProductLaw (laws : I → ProbabilityMeasure ℝ)
    (t : EuclideanSpace ℝ I) :
    charFun (euclideanProductLaw laws : Measure (EuclideanSpace ℝ I)) t =
      ∏ i, charFun (laws i : Measure ℝ) (t i) :=
  charFun_pi t

/-- Coordinatewise weak limits of true independent laws give a joint weak limit. -/
theorem euclideanProductLaw_tendsto (laws : ℕ → I → ProbabilityMeasure ℝ)
    (limit : I → ProbabilityMeasure ℝ)
    (h : ∀ i, Tendsto (fun n => laws n i) atTop (𝓝 (limit i))) :
    Tendsto (fun n => euclideanProductLaw (laws n)) atTop
      (𝓝 (euclideanProductLaw limit)) := by
  apply ProbabilityMeasure.tendsto_iff_tendsto_charFun.mpr
  intro t
  simp only [charFun_euclideanProductLaw]
  exact tendsto_finsetProd _ fun i _ =>
    ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp (h i) (t i)

/-- A mixed target with genuinely independent Gaussian and Poisson coordinates. -/
def poissonGaussianLaw (normal : I → Bool) (variances criticalRates : I → ℝ≥0) :
    ProbabilityMeasure (EuclideanSpace ℝ I) :=
  euclideanProductLaw (fun i => if normal i then centeredGaussianLaw (variances i)
    else realPoissonLaw (criticalRates i))

def mixedPoissonLaw (normal : I → Bool) (rates : I → ℝ≥0) (base : ℝ) :
    ProbabilityMeasure (EuclideanSpace ℝ I) :=
  euclideanProductLaw (fun i => if normal i then centeredScaledPoissonLaw (rates i) (Real.sqrt base)
    else realPoissonLaw (rates i))

/-- A multivariate Poisson CLT jointly with independent unscaled Poisson limits. -/
theorem mixedPoissonLaw_tendsto (normal : I → Bool) (rates : ℕ → I → ℝ≥0)
    (base : ℕ → ℝ) (variances criticalRates : I → ℝ≥0)
    (hbase : Tendsto base atTop atTop)
    (hnormal : ∀ i, normal i = true →
      Tendsto (fun n => (rates n i : ℝ) / base n) atTop (𝓝 (variances i : ℝ)))
    (hcritical : ∀ i, normal i = false →
      Tendsto (fun n => (rates n i : ℝ)) atTop (𝓝 (criticalRates i : ℝ))) :
    Tendsto (fun n => mixedPoissonLaw normal (rates n) (base n)) atTop
      (𝓝 (poissonGaussianLaw normal variances criticalRates)) := by
  apply euclideanProductLaw_tendsto
  intro i
  cases hi : normal i
  · simpa only [hi, Bool.false_eq_true, if_false] using
      realPoissonLaw_tendsto (fun n => rates n i) (criticalRates i) (hcritical i hi)
  · simpa only [hi, if_true] using
      centeredPoisson_tendsto_of_rate_ratio (fun n => rates n i) base (variances i)
        hbase (hnormal i hi)

/-- Center and scale a finite vector of genuine Poisson counts. -/
def normalizedPoissonVector (rates : I → ℝ≥0) (base : ℝ) (k : I → ℕ) :
    EuclideanSpace ℝ I :=
  toLp 2 (fun i => ((k i : ℝ) - (rates i : ℝ)) / Real.sqrt base)

theorem hasLaw_normalizedPoissonVector (rates : I → ℝ≥0) (base : ℝ) :
    HasLaw (normalizedPoissonVector rates base)
      (euclideanProductLaw (fun i => centeredScaledPoissonLaw (rates i) (Real.sqrt base)))
      (Measure.pi (fun i => poissonMeasure (rates i))) := by
  letI (i : I) : IsProbabilityMeasure ((poissonMeasure (rates i)).map
      (fun k : ℕ => ((k : ℝ) - (rates i : ℝ)) / Real.sqrt base)) :=
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
  refine ⟨(measurable_of_countable _).aemeasurable, ?_⟩
  change (Measure.pi (fun i => poissonMeasure (rates i))).map
    ((toLp 2) ∘ (fun k i => ((k i : ℝ) - (rates i : ℝ)) / Real.sqrt base)) = _
  rw [← Measure.map_map (by fun_prop) (measurable_of_countable _),
    Measure.pi_map_pi (f := fun i (k : ℕ) => ((k : ℝ) - (rates i : ℝ)) / Real.sqrt base)
      (fun _ => (measurable_of_countable _).aemeasurable)]
  rfl

end
end PaperC.V282.FinitePoissonCLT
