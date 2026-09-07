import PaperCV282.CompoundPoissonTarget
import Mathlib.Probability.Distributions.Geometric

/-!
# The positive geometric cluster target of Corollary 5.7

The mark is one plus a geometric variable with success probability one half.
Its law is supported on positive integers with mass 2^(-h). The compound
law is the actual independent random sum constructed in CompoundPoissonTarget.
-/

namespace PaperC.V282.GeometricClusterTarget

open MeasureTheory ProbabilityTheory CompoundPoissonTarget
open scoped BigOperators NNReal ENNReal

noncomputable section

def halfSuccess : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩

theorem halfSuccess_ne_zero : halfSuccess ≠ 0 := by
  intro h
  have := congrArg (fun p : unitInterval => (p : ℝ)) h
  norm_num [halfSuccess] at this

def geometricClusterMeasure : Measure ℕ :=
  (geometricMeasure halfSuccess).map Nat.succ

instance instProbabilityGeometricCluster : IsProbabilityMeasure geometricClusterMeasure := by
  unfold geometricClusterMeasure
  exact Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable

theorem geometricClusterMeasure_zero : geometricClusterMeasure {0} = 0 := by
  rw [geometricClusterMeasure, Measure.map_apply (measurable_of_countable _)
    (measurableSet_singleton _)]
  have hpre : Nat.succ ⁻¹' {(0 : ℕ)} = ∅ := by ext n; simp
  rw [hpre, measure_empty]

theorem geometricClusterMeasure_succ (n : ℕ) :
    geometricClusterMeasure {n + 1} = ENNReal.ofReal (1 / (2 : ℝ) ^ (n + 1)) := by
  rw [geometricClusterMeasure, Measure.map_apply (measurable_of_countable _)
    (measurableSet_singleton _)]
  have hpre : Nat.succ ⁻¹' {n + 1} = {n} := by ext k; simp
  rw [hpre, geometricMeasure_singleton halfSuccess_ne_zero]
  congr 1
  simp only [halfSuccess, Subtype.coe_mk]
  norm_num
  rw [pow_succ, div_pow]
  ring

theorem geometricClusterMeasure_real_succ (n : ℕ) :
    geometricClusterMeasure.real {n + 1} = 1 / (2 : ℝ) ^ (n + 1) := by
  rw [Measure.real, geometricClusterMeasure_succ, ENNReal.toReal_ofReal (by positivity)]

theorem geometricClusterMeasure_positive :
    ∀ᵐ h ∂geometricClusterMeasure, 1 ≤ h := by
  rw [ae_iff]
  have heq : {h : ℕ | ¬ 1 ≤ h} = {0} := by ext h; simp
  rw [heq, geometricClusterMeasure_zero]

theorem geometricCluster_partial_mass (n : ℕ) :
    (∑ h ∈ Finset.range (n + 1), geometricClusterMeasure.real {h}) =
      1 - 1 / (2 : ℝ) ^ n := by
  induction n with
  | zero => simp [Measure.real, geometricClusterMeasure_zero]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, geometricClusterMeasure_real_succ]
    rw [pow_succ]
    field_simp
    ring

/-- The mass of deleted marks e>E, where the positive cluster size is e+1. -/
theorem geometricCluster_tail_real (E : ℕ) :
    geometricClusterMeasure.real {h : ℕ | E + 1 < h} = 1 / (2 : ℝ) ^ (E + 1) := by
  have heq : {h : ℕ | E + 1 < h} = (Finset.range ((E + 1) + 1) : Set ℕ)ᶜ := by
    ext h
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Finset.mem_coe, Finset.mem_range]
    omega
  rw [heq, measureReal_compl (Finset.measurableSet _), probReal_univ,
    ← sum_measureReal_singleton, geometricCluster_partial_mass]
  ring

theorem geometricCluster_pgf {z : ℝ} (hz : 0 ≤ z) (hzOne : z ≤ 1) :
    (∫ h, z ^ h ∂geometricClusterMeasure) = z / (2 - z) := by
  rw [geometricClusterMeasure, integral_map (measurable_of_countable _).aemeasurable
    (measurable_of_countable (fun n : ℕ => z ^ n)).aestronglyMeasurable,
    integral_geometricMeasure halfSuccess_ne_zero]
  simp only [halfSuccess, Subtype.coe_mk, smul_eq_mul, Nat.succ_eq_add_one]
  have hr : z / 2 < 1 := by linarith
  have hsum := (hasSum_geometric_of_lt_one (div_nonneg hz (by norm_num)) hr).mul_left (z / 2)
  calc
    (∑' n : ℕ, (1 - 1 / 2 : ℝ) ^ n * (1 / 2) * z ^ (n + 1)) =
        ∑' n : ℕ, (z / 2) * (z / 2) ^ n := by
      congr 1
      funext n
      simp only [pow_succ, div_eq_mul_inv, mul_pow]
      ring
    _ = (z / 2) * (1 - z / 2)⁻¹ := hsum.tsum_eq
    _ = z / (2 - z) := by field_simp

def geometricCompoundMeasure (rate : ℝ≥0) : Measure ℕ :=
  compoundMeasure rate geometricClusterMeasure

instance instProbabilityGeometricCompound (rate : ℝ≥0) :
    IsProbabilityMeasure (geometricCompoundMeasure rate) := by
  unfold geometricCompoundMeasure
  infer_instance

def geometricCompoundPMF (rate : ℝ≥0) : PMF ℕ :=
  compoundPMF rate geometricClusterMeasure

theorem hasLaw_geometric_random_sum (rate : ℝ≥0) :
    HasLaw stoppedMarkSum (geometricCompoundMeasure rate)
      (compoundSampleMeasure rate geometricClusterMeasure) :=
  hasLaw_stoppedMarkSum rate geometricClusterMeasure

/-- The displayed probability generating function in Corollary 5.7. -/
theorem geometricCompound_pgf (rate : ℝ≥0) {z : ℝ} (hz : 0 ≤ z) (hzOne : z ≤ 1) :
    (∫ n, z ^ n ∂geometricCompoundMeasure rate) =
      Real.exp ((rate : ℝ) * (z / (2 - z) - 1)) := by
  rw [geometricCompoundMeasure, compound_pgf rate geometricClusterMeasure hz hzOne,
    geometricCluster_pgf hz hzOne]

end
end PaperC.V282.GeometricClusterTarget
