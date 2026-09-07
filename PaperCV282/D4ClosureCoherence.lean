import PaperCV282.D4ClosureHalfLines
import PaperCV282.PoissonResolvedPast

/-! # Coherent integer thresholds and their exact finite generating functions -/
namespace PaperC.V282.D4ClosureCoherence

open MeasureTheory ProbabilityTheory
open D4ClosureIntegerLevels D4ClosureHalfLines D4ClosureThreshold
open GeometricMarkedConfiguration GeometricConfigurationCounts ThresholdPathEquivalence
open PoissonConfigurationSplit PoissonResolvedPast
open scoped BigOperators NNReal

noncomputable section

theorem ae_halfLineConfiguration_shift (theta : ℝ) (m : ℤ) (k : ℕ) :
    ∀ᵐ counts ∂integerCountMeasure theta,
      halfLineConfiguration (m+k) counts = shiftedConfiguration k (halfLineConfiguration m counts) := by
  filter_upwards [ae_halfLineConfiguration_coordinates theta m,
    ae_halfLineConfiguration_coordinates theta (m+k)] with counts hm hk
  apply Finsupp.ext
  intro e
  rw [hk, shiftedConfiguration_apply, hm]
  congr 1
  push_cast
  ring

theorem ae_integerThreshold_shift (theta : ℝ) (m : ℤ) (k : ℕ) :
    ∀ᵐ counts ∂integerCountMeasure theta,
      integerThreshold (m+k) counts = tailCount (halfLineConfiguration m counts) k := by
  filter_upwards [ae_halfLineConfiguration_shift theta m k] with counts hc
  change configurationSize (halfLineConfiguration (m+k) counts) = _
  rw [hc, size_shifted_eq_tail]

/-- All finite threshold vectors refer to the same two-sided probability space. -/
theorem integer_threshold_joint_pgf (theta : ℝ) (m : ℤ) (J : ℕ) (z : Fin (J+1) → ℂ) :
    (∫ counts, ∏ j : Fin (J+1), z j ^ integerThreshold (m+j.val) counts
      ∂integerCountMeasure theta) =
      Complex.exp ((∑ i : Fin J,
        (integerHalfRate theta m : ℂ) / 2^(i.val+1) * (prefixProduct J z i.castSucc - 1)) +
          (integerHalfRate theta m : ℂ) / 2^J * ((∏ j : Fin (J+1), z j) - 1)) := by
  have hall := ae_all_iff.mpr (fun j : Fin (J+1) => ae_integerThreshold_shift theta m j.val)
  have heq : (∫ counts, ∏ j : Fin (J+1), z j ^ integerThreshold (m+j.val) counts
      ∂integerCountMeasure theta) =
      ∫ counts, ∏ j : Fin (J+1), z j ^ tailCount (halfLineConfiguration m counts) j.val
        ∂integerCountMeasure theta := by
    apply integral_congr_ae
    filter_upwards [hall] with counts hc
    simp_rw [hc]
  rw [heq]
  exact ((hasLaw_halfLineConfiguration theta m).integral_comp
    (measurable_of_countable (fun c : ℕ →₀ ℕ =>
      ∏ j : Fin (J+1), z j ^ tailCount c j.val)).aestronglyMeasurable).trans
        (threshold_joint_pgf_explicit _ _ _)

/-- The first and next threshold differ by exactly the corresponding Poisson level. -/
theorem ae_integerThreshold_succ (theta : ℝ) (m : ℤ) :
    ∀ᵐ counts ∂integerCountMeasure theta,
      counts m + integerThreshold (m+1) counts = integerThreshold m counts := by
  filter_upwards [ae_halfLineConfiguration_coordinates theta m,
    ae_integerThreshold_shift theta m 1, ae_integerThreshold_shift theta m 0] with counts hc h1 h0
  have hc0 := hc 0
  simp only [Int.natCast_zero, add_zero] at hc0 h0
  simp only [Int.natCast_one] at h1
  rw [h1, h0, ← hc0]
  exact (tailCount_succ _ 0).symm

end
end PaperC.V282.D4ClosureCoherence
