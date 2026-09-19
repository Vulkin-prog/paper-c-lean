import PaperCPrel8.RegularTargetPresence
import PaperCPrel8.MicroscopicConditionalSpatial

/-! # Exact regular-plant presence in the original infinite arithmetic law -/
namespace PaperC.Prel8.InfinitePlantPresence
open MeasureTheory ProbabilityTheory InfiniteRademacher InfiniteCylinderTransfer
open InfiniteExactLengthProbabilityTransfer ConditionalStartProbability ArratiaGoldsteinGordonInput
open V282.ExactMarkedModel V282.SpatialMarkedSource V282.ExactMarkedInfinite
open MicroscopicConditionalSpatial MicroscopicInfiniteField RegularTargetPresence RegularPlantPresence
open RoughKernelRegularity V282.SharpConditioning
noncomputable section
local instance : MeasurableSpace F₂ := ⊤

/-- The actual occurrence event for all prescribed signed words. -/
def occurrence {k : ℕ} (L : ℕ) (j e : Fin k → ℕ) (s : Fin k → F₂) : Set InfiniteSample :=
  {w | ∀ i, SignedExactMark (infiniteValueBit w) (j i+1) L (e i) (s i)}

theorem measurableSet_occurrence {k : ℕ} (L : ℕ) (j e : Fin k → ℕ) (s : Fin k → F₂) :
    MeasurableSet (occurrence L j e s) := by
  have he : occurrence L j e s = ⋂ i, {w | SignedExactMark (infiniteValueBit w) (j i+1) L (e i) (s i)} := by ext w; simp [occurrence]
  rw [he]
  exact MeasurableSet.iInter (fun i ↦ measurableSet_signed_exact _ _ _ _)

/-- Joint presence and the small-prime event have exactly factored probabilities
in the original infinite product, not merely in its finite cylinder. -/
theorem joint_presence {C k L E Y : ℕ} (hL : 1≤L) (j e : Fin k → ℕ) (s : Fin k → F₂)
    (hj : ∀ i, 0<j i) (he : ∀ i, e i≤E) (hC : ∀ i, j i+(L+E+1)≤C)
    (hr : Regular (L+E+1) Y j) (A : SmallSample C Y → Prop) :
    infiniteRademacherMeasure.real (traceEvent C Y A ∩ occurrence L j e s) =
      infiniteRademacherMeasure.real (traceEvent C Y A)*∏ i, (signedMarkRate L (e i):ℝ) := by
  obtain ⟨q,hqY,hodd,hprivate⟩ := exists_private_raw j e hj he hC hr
  have hfinite := presence_small_event hL j e s q hqY hodd hprivate A
  have heq : traceEvent C Y A ∩ occurrence L j e s =
      {w | A (restrictSmall C Y (restrictToFinite C w)) ∧
        ∀ i, SignedExactMark (valueBit (restrictToFinite C w)) (j i+1) L (e i) (s i)} := by
    ext w
    change (_ ∧ _) ↔ (_ ∧ _)
    apply and_congr_right
    intro _
    apply forall_congr'
    intro i
    exact (signedExactMark_restrictToFinite_iff (by have := hC i; have := he i; omega) (s i) w).symm
  rw [heq]
  change (infiniteRademacherMeasure {w | A (restrictSmall C Y (restrictToFinite C w)) ∧
      ∀ i, SignedExactMark (valueBit (restrictToFinite C w)) (j i+1) L (e i) (s i)}).toReal = _
  rw [cylinder_probability C (fun w ↦ A (restrictSmall C Y w) ∧ ∀ i, SignedExactMark (valueBit w) (j i+1) L (e i) (s i)),traceEvent_probability]
  exact hfinite

/-- Conditioning the full infinite source leaves the same product of elementary
intensities on every positive event of the represented small-prime algebra. -/
theorem conditional_presence {C k L E Y : ℕ} (hL : 1≤L) (j e : Fin k → ℕ) (s : Fin k → F₂)
    (hj : ∀ i, 0<j i) (he : ∀ i, e i≤E) (hC : ∀ i, j i+(L+E+1)≤C)
    (hr : Regular (L+E+1) Y j) (A : SmallSample C Y → Prop)
    (hA : 0 < infiniteRademacherMeasure.real (traceEvent C Y A)) :
    (cond infiniteRademacherMeasure (traceEvent C Y A)).real (occurrence L j e s) =
      ∏ i, (signedMarkRate L (e i):ℝ) := by
  rw [cond_real_apply _ _ (measurableSet_traceEvent C Y A),joint_presence hL j e s hj he hC hr A]
  exact mul_div_cancel_left₀ _ hA.ne'

end
end PaperC.Prel8.InfinitePlantPresence
