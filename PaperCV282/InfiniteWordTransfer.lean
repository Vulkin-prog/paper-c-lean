import PaperCV282.WindowValues
import PaperC.Probability.InfiniteExactLengthProbabilityTransfer

/-!
# Prescribed words under the infinite Rademacher law

The actual word event at the vertices `x - 1 + j`, `j < B`, is the preimage
of its event on every finite prime cylinder containing those vertices.
The retained restriction theorem identifies its measure with the exact
rational affine probability. This transports the pointwise estimate of
Corollary 2.6 to the source infinite product model.

The infinite conditional-kernel statement and the uniform asymptotic sum
over masks and dictionaries are separate from this unconditional transfer.
-/

namespace PaperC.V282.InfiniteWordTransfer

open MeasureTheory Set
open Affine InfiniteRademacher InfiniteCylinderTransfer
open InfiniteExactLengthProbabilityTransfer
open PrescribedValues WindowValues

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

noncomputable section

/-- The prescribed binary word on the finite prime cylinder at `M`. -/
def finiteWordEvent (M x B : ℕ) (b : Fin B → F₂) : Set (SampleSpace M) :=
  {ω | ∀ i : Fin B, valueBit ω (vertex x B i) = b i}

/-- The same word, evaluated in the source infinite product model. -/
def infiniteWordEvent (x B : ℕ) (b : Fin B → F₂) : Set InfiniteSample :=
  {ω | ∀ i : Fin B, infiniteValueBit ω (vertex x B i) = b i}

/-- The displayed cylinder condition contains every word vertex. -/
theorem vertex_le_cutoff
    {M x B : ℕ} (hcut : x - 1 + B ≤ M + 1) (i : Fin B) :
    vertex x B i ≤ M := by
  have hi := i.isLt
  unfold vertex
  omega

/-- Restriction preserves every prescribed bit in an adequate cylinder. -/
theorem finiteWordEvent_restrictToFinite_iff
    {M x B : ℕ} (hcut : x - 1 + B ≤ M + 1)
    (b : Fin B → F₂) (ω : InfiniteSample) :
    restrictToFinite M ω ∈ finiteWordEvent M x B b ↔
      ω ∈ infiniteWordEvent x B b := by
  simp only [finiteWordEvent, infiniteWordEvent, Set.mem_setOf_eq]
  constructor <;> intro h i
  · simpa only [valueBit_restrictToFinite_eq_infiniteValueBit
      ω (vertex_le_cutoff hcut i)] using h i
  · simpa only [valueBit_restrictToFinite_eq_infiniteValueBit
      ω (vertex_le_cutoff hcut i)] using h i

/-- The infinite word event is the preimage of its finite-cylinder event. -/
theorem infiniteWordEvent_eq_preimage
    {M x B : ℕ} (hcut : x - 1 + B ≤ M + 1) (b : Fin B → F₂) :
    infiniteWordEvent x B b =
      restrictToFinite M ⁻¹' finiteWordEvent M x B b := by
  ext ω
  exact (finiteWordEvent_restrictToFinite_iff hcut b ω).symm

/-- All finite-cylinder word events are measurable. -/
theorem measurableSet_finiteWordEvent
    (M x B : ℕ) (b : Fin B → F₂) :
    MeasurableSet (finiteWordEvent M x B b) :=
  Set.toFinite (finiteWordEvent M x B b) |>.measurableSet

/-- Prescribed word events are measurable in the infinite source model. -/
theorem measurableSet_infiniteWordEvent
    (x B : ℕ) (b : Fin B → F₂) :
    MeasurableSet (infiniteWordEvent x B b) := by
  let M := x - 1 + B
  rw [infiniteWordEvent_eq_preimage
    (M := M) (x := x) (B := B) (by dsimp [M]; omega) b]
  exact (measurable_restrictToFinite M)
    (measurableSet_finiteWordEvent M x B b)

/-- Exact source measure of a word as its rational finite affine probability. -/
theorem infiniteWordEvent_measure_eq_uniformSolutionProbability
    {M x B : ℕ} (hcut : x - 1 + B ≤ M + 1) (b : Fin B → F₂) :
    infiniteRademacherMeasure (infiniteWordEvent x B b) =
      ENNReal.ofReal
        ((uniformSolutionProbability (valueSystem M (vertex x B)) b : ℚ) : ℝ) := by
  classical
  rw [infiniteWordEvent_eq_preimage hcut b,
    ← Measure.map_apply (measurable_restrictToFinite M)
      (measurableSet_finiteWordEvent M x B b),
    map_infiniteRademacherMeasure_restrictToFinite,
    probability_eq_uniform_event]
  convert finiteRademacherMeasure_event_eq_uniformEventProbability
      (fun ω : SampleSpace M => ∀ i : Fin B, valueBit ω (vertex x B i) = b i)
    using 1
  · rfl
  · congr 3

/-- Real-valued probability of a prescribed word in the infinite model. -/
def infiniteWordProbability (x B : ℕ) (b : Fin B → F₂) : ℝ :=
  (infiniteRademacherMeasure (infiniteWordEvent x B b)).toReal

/-- The real source probability equals its exact rational affine probability. -/
theorem infiniteWordProbability_eq_uniformSolutionProbability
    {M x B : ℕ} (hcut : x - 1 + B ≤ M + 1) (b : Fin B → F₂) :
    infiniteWordProbability x B b =
      ((uniformSolutionProbability (valueSystem M (vertex x B)) b : ℚ) : ℝ) := by
  classical
  unfold infiniteWordProbability
  rw [infiniteWordEvent_measure_eq_uniformSolutionProbability hcut b,
    ENNReal.toReal_ofReal]
  apply Rat.cast_nonneg.mpr
  rw [probability_eq_uniform_event]
  unfold uniformEventProbability
  positivity

/-- Equation (2.6) for the actual infinite-product word probability. -/
theorem corollary_two_six_pointwise_infinite
    {x B : ℕ} (hx : 2 ≤ x) (b : Fin B → F₂) :
    |infiniteWordProbability x B b - 1 / (2 : ℝ) ^ B| ≤
      ((2 : ℝ) ^ (defectIndices B x B).card - 1) / (2 : ℝ) ^ B := by
  let M := x - 1 + B
  have hcut : x - 1 + B ≤ M + 1 := by dsimp [M]; omega
  rw [infiniteWordProbability_eq_uniformSolutionProbability hcut b]
  have h := WindowValues.corollary_two_six_pointwise hx hcut b
  have hcast := (Rat.cast_le (K := ℝ)).mpr h
  simpa only [Rat.cast_abs, Rat.cast_sub, Rat.cast_div, Rat.cast_one,
    Rat.cast_pow, Rat.cast_ofNat] using hcast

end
end PaperC.V282.InfiniteWordTransfer
