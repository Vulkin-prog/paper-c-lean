import PaperCPrel8.EmpiricalFiniteSupport
import PaperCPrel8.EmpiricalSupportScales
import PaperCPrel8.EmpiricalStartField
import Mathlib.Topology.Order.LiminfLimsup

/-! # Remark 7.8b: the empirical full vector cannot approach the product target

The observation space changes with k. The finite-support estimate applies
separately at each k, so no identification of these spaces is needed.
The final result holds for every fixed arithmetic realization.
-/
namespace PaperC.Prel8.EmpiricalSupportTheorem
open MeasureTheory ProbabilityTheory Filter Topology
open PaperC.InfiniteRademacher
open PaperC.Prel8.EmpiricalFiniteSupport PaperC.Prel8.EmpiricalSupportScales
open PaperC.Prel8.EmpiricalSupportTarget PaperC.Prel8.EmpiricalPaperScales
open PaperC.V282.PoissonFieldMeasure PaperC.V282.SharpConditioning
open scoped NNReal
noncomputable section

/-- Site intensities are at most one even before entering the eventual regime. -/
theorem site_rate_le_one (L : ℕ) : (1:ℝ≥0)/2^L ≤ 1 := by
  exact (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))

/-- Any deterministic collection of N_k vectors has the same positive liminf obstruction. -/
theorem deterministic_vector_liminf (alpha tau : ℝ) (ha : 0 ≤ alpha) (ht : 0 ≤ tau)
    (v : (k : ℕ) → Fin (origins alpha tau k) → Fin (windowSize alpha tau k) → ℕ) :
    1-Real.exp (-tau)*(1+tau) ≤
      liminf (fun k => measureTotalVariation
        (empiricalMeasure (origins alpha tau k) (origins_pos alpha tau k) (v k))
        (fieldMeasure (fun _ : Fin (windowSize alpha tau k) => (1:ℝ≥0)/2^(length alpha k)))) atTop := by
  have hb := support_lower_bound_tendsto alpha tau ha ht
  have hle := Eventually.of_forall (f := atTop) (fun k => empirical_poisson_obstruction
    (origins alpha tau k) (windowSize alpha tau k) (origins_pos alpha tau k)
    ((1:ℝ≥0)/2^(length alpha k)) (site_rate_le_one _) (v k))
  simp only [NNReal.coe_div,NNReal.coe_one,NNReal.coe_pow,NNReal.coe_ofNat] at hle
  have hu := isBoundedUnder_of_eventually_le (Eventually.of_forall (f := atTop) (fun k =>
    measureTotalVariation_le_one
      (empiricalMeasure (origins alpha tau k) (origins_pos alpha tau k) (v k))
      (fieldMeasure (fun _ : Fin (windowSize alpha tau k) => (1:ℝ≥0)/2^(length alpha k)))))
  have hh := liminf_le_liminf hle hb.isBoundedUnder_ge hu.isCoboundedUnder_ge
  rwa [hb.liminf_eq] at hh

/-- Relative coordinates of the actual start vector: origin u, coordinate i, start u+i+2. -/
def actualLocalVector (alpha tau : ℝ) (k : ℕ) (omega : InfiniteSample)
    (u : Fin (origins alpha tau k)) (i : Fin (windowSize alpha tau k)) : ℕ :=
  PaperC.V282.ExactMarkedModel.baseStartValue (infiniteValueBit omega)
    (u.val+i.val+2) (length alpha k)

/-- The paper's contained-origin convention gives a genuine interior coordinate. -/
theorem local_coordinate_lt (alpha tau : ℝ) {k : ℕ}
    (hfit : windowSize alpha tau k ≤ sites alpha k)
    (u : Fin (origins alpha tau k)) (i : Fin (windowSize alpha tau k)) :
    u.val+i.val < sites alpha k := by
  have hu := u.isLt
  have hi := i.isLt
  unfold origins at hu
  omega

/-- The relative vector is exactly the previously formalized arithmetic start field. -/
theorem actualLocalVector_eq_actualStarts (alpha tau : ℝ) {k : ℕ}
    (hfit : windowSize alpha tau k ≤ sites alpha k) (omega : InfiniteSample)
    (u : Fin (origins alpha tau k)) (i : Fin (windowSize alpha tau k)) :
    actualLocalVector alpha tau k omega u i =
      PaperC.Prel8.EmpiricalStartField.actualStarts (size k) (length alpha k) omega
        ⟨u.val+i.val,local_coordinate_lt alpha tau hfit u i⟩ := rfl

/-- The literal empirical full-vector law is the pushforward of a uniform origin. -/
def actualEmpiricalVectorMeasure (alpha tau : ℝ) (k : ℕ) (omega : InfiniteSample) :
    Measure (Fin (windowSize alpha tau k) → ℕ) :=
  empiricalMeasure (origins alpha tau k) (origins_pos alpha tau k)
    (actualLocalVector alpha tau k omega)

/-- The displayed finite lower bound for the actual arithmetic empirical vectors. -/
theorem actual_empirical_vector_bound (alpha tau : ℝ) (k : ℕ) (omega : InfiniteSample) :
    1-Real.exp (-(windowSize alpha tau k:ℝ)*((1:ℝ)/2^(length alpha k)))*
      (1+(windowSize alpha tau k:ℝ)*((1:ℝ)/2^(length alpha k)))-
      (origins alpha tau k:ℝ)*((1:ℝ)/2^(length alpha k))^2 ≤
      measureTotalVariation (actualEmpiricalVectorMeasure alpha tau k omega)
        (fieldMeasure (fun _ : Fin (windowSize alpha tau k) => (1:ℝ≥0)/2^(length alpha k))) := by
  exact_mod_cast empirical_poisson_obstruction (origins alpha tau k) (windowSize alpha tau k)
    (origins_pos alpha tau k) ((1:ℝ≥0)/2^(length alpha k)) (site_rate_le_one _)
    (actualLocalVector alpha tau k omega)

/-- Paper 7.8b, for every realization and with the paper's floors and endpoints retained. -/
theorem paper_empirical_vector_obstruction (alpha tau : ℝ) (ha : 0 < alpha)
    (_ha1 : alpha < 1) (ht : 0 < tau) (omega : InfiniteSample) :
    (1-Real.exp (-tau)*(1+tau) ≤
      liminf (fun k => measureTotalVariation (actualEmpiricalVectorMeasure alpha tau k omega)
        (fieldMeasure (fun _ : Fin (windowSize alpha tau k) => (1:ℝ≥0)/2^(length alpha k)))) atTop) ∧
    0 < 1-Real.exp (-tau)*(1+tau) := by
  exact ⟨deterministic_vector_liminf alpha tau ha.le ht.le
    (fun k => actualLocalVector alpha tau k omega), obstruction_positive ht⟩

end
end PaperC.Prel8.EmpiricalSupportTheorem
