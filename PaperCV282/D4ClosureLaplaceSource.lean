import PaperCV282.MovingMarkedSource
import PaperCV282.D4ClosureLaplaceParameters
import Mathlib.MeasureTheory.Measure.GiryMonad

/-! # The literal centered source measure and its compact-level tests -/
namespace PaperC.V282.D4ClosureLaplaceSource

open MeasureTheory InfiniteRademacher InfiniteCylinderTransfer SpatialMarkedTypes
open SpatialMarkedSource MovingMarkedSource GrowingLevelParameters ExactMarkedModel
open scoped BigOperators ENNReal

noncomputable section

def configurationPointMeasure (N d : ℕ) (config : SpatialMarkedConfig N) : Measure (ℝ × ℤ) :=
  config.sum (fun j n => (n : ℝ≥0∞) •
    Measure.dirac (((N+j.1.val : ℕ) : ℝ)/N, (j.2.1 : ℤ)-d))

def centeredSourceMeasure (N : ℕ) (omega : InfiniteSample) : Measure (ℝ × ℤ) :=
  configurationPointMeasure N (criticalBase N) (spatialMarkedSource N 0 omega)

def configurationPairing (N d : ℕ) (g : ℝ × ℤ → ℝ) (config : SpatialMarkedConfig N) : ℝ :=
  config.sum (fun j n => g (((N+j.1.val : ℕ) : ℝ)/N, (j.2.1 : ℤ)-d)*(n : ℝ))

theorem integral_configurationPointMeasure (N d : ℕ) (g : ℝ × ℤ → ℝ)
    (config : SpatialMarkedConfig N) :
    (∫ z, g z ∂configurationPointMeasure N d config) = configurationPairing N d g config := by
  classical
  unfold configurationPointMeasure configurationPairing Finsupp.sum
  rw [integral_finsetSum_measure (fun j hj =>
    (integrable_dirac (by simp)).smul_measure (by simp))]
  apply Finset.sum_congr rfl
  intro j hj
  simp [integral_smul_measure,mul_comm]

theorem measurable_centeredSourceMeasure (N : ℕ) : Measurable (centeredSourceMeasure N) :=
  (measurable_of_countable (configurationPointMeasure N (criticalBase N))).comp
    (measurable_spatialMarkedSource N 0)

theorem configurationPairing_nonneg (N d : ℕ) (g : ℝ × ℤ → ℝ)
    (hg : ∀ z, 0 ≤ g z) (config : SpatialMarkedConfig N) :
    0 ≤ configurationPairing N d g config := by
  exact Finset.sum_nonneg fun j hj => mul_nonneg (hg _) (Nat.cast_nonneg _)

theorem pairing_filter_eq (N d : ℕ) (g : ℝ × ℤ → ℝ) (config : SpatialMarkedConfig N)
    (p : SpatialMarkedIndex N → Prop) [DecidablePred p]
    (hp : ∀ j, ¬p j → g (((N+j.1.val : ℕ) : ℝ)/N, (j.2.1 : ℤ)-d) = 0) :
    configurationPairing N d g (config.filter p) = configurationPairing N d g config := by
  classical
  unfold configurationPairing
  rw [Finsupp.sum_filter_index,Finsupp.support_filter,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs with h
  · rfl
  · dsimp only
    rw [hp j h]
    simp

/-- A lower-level truncation is an exact source identity, before taking any probability. -/
theorem centered_pairing_eq_shifted {N d : ℕ} (hd : d ≤ criticalBase N)
    (g : ℝ × ℤ → ℝ) (hg : ∀ t r, r < -(d : ℤ) → g (t,r) = 0)
    (omega : InfiniteSample) :
    (∫ z, g z ∂centeredSourceMeasure N omega) =
      configurationPairing N d g (spatialMarkedSource N (movingLength N d) omega) := by
  classical
  rw [centeredSourceMeasure,integral_configurationPointMeasure]
  rw [← pairing_filter_eq N (criticalBase N) g (spatialMarkedSource N 0 omega)
    (fun j => movingLength N d ≤ j.2.1) (fun j hj => hg _ _ (by
      dsimp [movingLength] at hj
      omega))]
  rw [← shifted_source_embeds_as_filtered N 0 (movingLength N d)]
  simp only [Nat.zero_add,configurationPairing,Finsupp.sum_embDomain]
  apply Finset.sum_congr rfl
  intro j hj
  dsimp only
  congr 2
  apply Prod.ext
  · rfl
  · dsimp [excessShift,movingLength]
    omega

/-- Finite projection evaluates the test exactly when all higher levels vanish. -/
theorem configurationPairing_eq_finite (N d E : ℕ) (g : ℝ × ℤ → ℝ)
    (hg : ∀ t r, (E : ℤ)-d < r → g (t,r) = 0) (config : SpatialMarkedConfig N) :
    configurationPairing N d g config =
      ∑ i : SignedMarkIndex N E,
        g ((i.1.val : ℝ)/N, (i.2.1.val : ℤ)-d)*(projectConfiguration N E config i : ℝ) := by
  classical
  rw [← pairing_filter_eq N d g config (fun j => j.2.1 ≤ E)
    (fun j hj => hg _ _ (by omega))]
  change configurationPairing N d g (truncateConfiguration N E config) = _
  rw [← embed_project_configuration]
  unfold configurationPairing embedConfiguration
  rw [Finsupp.sum_embDomain,Finsupp.sum_fintype _ _ (fun _ => by simp)]
  apply Finset.sum_congr rfl
  intro i hi
  congr 2
  apply Prod.ext
  swap
  · rfl
  change ((N+((dyadicSiteEquiv N).symm i.1).val : ℕ) : ℝ)/N = (i.1.val : ℝ)/N
  have hx := congrArg Subtype.val ((dyadicSiteEquiv N).apply_symm_apply i.1)
  change N+((dyadicSiteEquiv N).symm i.1).val=i.1.val at hx
  rw [hx]

/-- Literal integration against the centered source is the finite exact-mark test on a compact level band. -/
theorem centered_source_compact_pairing {N d : ℕ} (hd : d ≤ criticalBase N)
    (E : ℕ) (g : ℝ × ℤ → ℝ)
    (hlo : ∀ t r, r < -(d : ℤ) → g (t,r) = 0)
    (hhi : ∀ t r, (E : ℤ)-d < r → g (t,r) = 0) (omega : InfiniteSample) :
    (∫ z, g z ∂centeredSourceMeasure N omega) =
      ∑ i : SignedMarkIndex N E, g ((i.1.val : ℝ)/N, (i.2.1.val : ℤ)-d)*
        (projectConfiguration N E (spatialMarkedSource N (movingLength N d) omega) i : ℝ) := by
  rw [centered_pairing_eq_shifted hd g hlo,configurationPairing_eq_finite N d E g hhi]

end
end PaperC.V282.D4ClosureLaplaceSource
