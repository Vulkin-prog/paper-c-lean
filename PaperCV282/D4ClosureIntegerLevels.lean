import PaperCV282.D4ClosureThreshold
import Mathlib.Probability.Independence.InfinitePi

/-! # A single genuine target on all integer levels

Every half-line is identified in law with a finite-support geometric
configuration. The independence is that of the actual countable product.
-/
namespace PaperC.V282.D4ClosureIntegerLevels

open MeasureTheory ProbabilityTheory
open GeometricMarkedConfiguration GeometricClusterTruncation PoissonFieldMeasure
open scoped BigOperators NNReal ENNReal

noncomputable section

theorem hasLaw_configuration_coordinate (rate : ℝ≥0) (e : ℕ) :
    HasLaw (fun c : ℕ →₀ ℕ => c e) (poissonMeasure (rate / 2^(e+1)))
      (configurationMeasure rate) := by
  have h := (hasLaw_coordinate (geometricCoordinateRates rate e) (Fin.last e)).fun_comp
    (hasLaw_finite_configuration rate e)
  simpa [geometricCoordinateRates] using h

theorem hasLaw_configuration_restrict (rate : ℝ≥0) (s : Finset ℕ) :
    HasLaw (fun c : ℕ →₀ ℕ => fun e : s => c e.val)
      (Measure.pi (fun e : s => poissonMeasure (rate / 2^(e.val+1))))
      (configurationMeasure rate) := by
  classical
  let E := s.sup id
  let f : s → Fin (E+1) := fun e => ⟨e.val, Nat.lt_succ_of_le (Finset.le_sup (f := id) e.property)⟩
  have hf : Function.Injective f := by
    intro i j hij
    exact Subtype.ext (congrArg Fin.val hij)
  have hind := (independent_coordinates (geometricCoordinateRates rate E)).precomp hf
  have hfinite := hind.hasLaw_pi (fun e =>
    hasLaw_coordinate (geometricCoordinateRates rate E) (f e))
  have h := hfinite.fun_comp (hasLaw_finite_configuration rate E)
  simpa [f, geometricCoordinateRates] using h

theorem independent_configuration_coordinates (rate : ℝ≥0) :
    iIndepFun (fun e (c : ℕ →₀ ℕ) => c e) (configurationMeasure rate) := by
  rw [iIndepFun_iff_finset]
  intro s
  exact (iIndepFun_iff_hasLaw_pi_pi (fun e : s =>
    hasLaw_configuration_coordinate rate e.val)).2 (hasLaw_configuration_restrict rate s)

/-- The function-valued law has all independent exact-level coordinates. -/
theorem configuration_function_law (rate : ℝ≥0) :
    HasLaw (fun c : ℕ →₀ ℕ => (c : ℕ → ℕ))
      (Measure.infinitePi (fun e : ℕ => poissonMeasure (rate / 2^(e+1))))
      (configurationMeasure rate) :=
  (independent_configuration_coordinates rate).hasLaw_infinitePi
    (hasLaw_configuration_coordinate rate) (measurable_of_countable _).aemeasurable

def integerLevelRate (theta : ℝ) (r : ℤ) : ℝ≥0 :=
  ⟨(2 : ℝ)^(theta - (r : ℝ) - 1), by positivity⟩

def integerHalfRate (theta : ℝ) (m : ℤ) : ℝ≥0 :=
  ⟨(2 : ℝ)^(theta - (m : ℝ)), by positivity⟩

def integerCountMeasure (theta : ℝ) : Measure (ℤ → ℕ) :=
  Measure.infinitePi (fun r => poissonMeasure (integerLevelRate theta r))

instance instProbabilityIntegerCounts (theta : ℝ) :
    IsProbabilityMeasure (integerCountMeasure theta) := by
  unfold integerCountMeasure
  infer_instance

def halfLineCounts (m : ℤ) (counts : ℤ → ℕ) (e : ℕ) : ℕ := counts (m + e)

theorem measurable_halfLineCounts (m : ℤ) : Measurable (halfLineCounts m) := by
  exact measurable_pi_lambda _ (fun e => measurable_pi_apply (m+e))

theorem integerLevelRate_shift (theta : ℝ) (m : ℤ) (e : ℕ) :
    integerLevelRate theta (m + e) = integerHalfRate theta m / 2^(e+1) := by
  apply NNReal.coe_injective
  change (2 : ℝ)^(theta - ((m + (e : ℤ) : ℤ) : ℝ) - 1) =
    (2 : ℝ)^(theta - (m : ℝ)) / 2^(e+1)
  push_cast
  rw [show theta - ((m : ℝ) + e) - 1 = theta - (m : ℝ) - (e+1 : ℕ) by push_cast; ring,
    Real.rpow_sub (by norm_num), Real.rpow_natCast]

theorem independent_integer_counts (theta : ℝ) :
    iIndepFun (fun r (counts : ℤ → ℕ) => counts r) (integerCountMeasure theta) :=
  iIndepFun_infinitePi (fun _ => measurable_id)

theorem hasLaw_integer_coordinate (theta : ℝ) (r : ℤ) :
    HasLaw (fun counts : ℤ → ℕ => counts r) (poissonMeasure (integerLevelRate theta r))
      (integerCountMeasure theta) :=
  (measurePreserving_eval_infinitePi (fun r => poissonMeasure (integerLevelRate theta r)) r).hasLaw

/-- Each complete half-line has exactly the function-valued geometric configuration law. -/
theorem halfLineCounts_law (theta : ℝ) (m : ℤ) :
    (integerCountMeasure theta).map (halfLineCounts m) =
      (configurationMeasure (integerHalfRate theta m)).map (fun c : ℕ →₀ ℕ => (c : ℕ → ℕ)) := by
  rw [(configuration_function_law _).map_eq]
  unfold integerCountMeasure halfLineCounts
  rw [Measure.map_infinitePi_infinitePi_of_inj (f := fun e : ℕ => m + (e : ℤ))
    (fun i j h => by exact_mod_cast add_left_cancel h)]
  simp_rw [integerLevelRate_shift]

end
end PaperC.V282.D4ClosureIntegerLevels
