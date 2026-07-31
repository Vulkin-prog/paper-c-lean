import PaperC.Probability.InfiniteExactLengthProbabilityTransfer

/-!
# Exact transfer of Laplace functionals to the infinite source model

The point-process statements of Section 14 live under the unrestricted
Rademacher product law, whereas the finite Stein--Chen calculation is carried
out on `SampleSpace M`.  This module proves that the spatial and truncated
marked exponential functionals are genuine cylinder observables and that
their expectations transfer exactly through `restrictToFinite`.

There is no limiting argument here.  The proof uses only:

* pointwise agreement of finite and infinite start/exact-length predicates;
* measurability of the finite restriction;
* the exact image-law identity
  `map_infiniteRademacherMeasure_restrictToFinite`.
-/

namespace PaperC
namespace InfiniteLaplaceTransfer

open scoped BigOperators

open MeasureTheory Set
open InfiniteRademacher
open InfiniteCylinderTransfer
open InfiniteExactLengthProbabilityTransfer
open MixedLengthAffine

noncomputable section

/- Keep the measurable structure definitionally identical to the source
model and its cylinder-transfer modules. -/
local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

local instance (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-! ## Spatial process -/

/-- Spatial Laplace functional on a finite prime cylinder. -/
def finiteSpatialLaplaceFunctional
    (M N L : ℕ) (g : ℝ → ℝ)
    (σ : SampleSpace M) : ℝ :=
  Real.exp
    (-(∑ x ∈ dyadicBlock N,
      if startAt σ x L then
        g ((x : ℝ) / (N : ℝ))
      else 0))

/-- Literal spatial Laplace functional under the infinite source model. -/
def infiniteSpatialLaplaceFunctional
    (N L : ℕ) (g : ℝ → ℝ)
    (ω : InfiniteSample) : ℝ :=
  Real.exp
    (-(∑ x ∈ dyadicBlock N,
      if StartEvent (infiniteValueBit ω) x L then
        g ((x : ℝ) / (N : ℝ))
      else 0))

/--
Pointwise cylinder identity at every cutoff covering the complete dyadic
family of start windows.
-/
theorem finiteSpatialLaplaceFunctional_restrictToFinite
    {M N L : ℕ} (hcut : 2 * N + L ≤ M)
    (g : ℝ → ℝ) (ω : InfiniteSample) :
    finiteSpatialLaplaceFunctional M N L g
        (restrictToFinite M ω) =
      infiniteSpatialLaplaceFunctional N L g ω := by
  unfold finiteSpatialLaplaceFunctional
    infiniteSpatialLaplaceFunctional
  congr 2
  apply Finset.sum_congr rfl
  intro x hx
  have hxUpper : x < 2 * N :=
    (Finset.mem_Ico.mp (by simpa only [dyadicBlock] using hx)).2
  have hxcut : x + L ≤ M := by omega
  have hevent :=
    startAt_restrictToFinite_iff
      (M := M) (x := x) (L := L) ω hxcut
  by_cases hfinite : startAt (restrictToFinite M ω) x L
  · have hinfinite :
        StartEvent (infiniteValueBit ω) x L :=
      hevent.mp hfinite
    simp [hfinite, hinfinite]
  · have hinfinite :
        ¬StartEvent (infiniteValueBit ω) x L := by
      exact fun h ↦ hfinite (hevent.mpr h)
    simp [hfinite, hinfinite]

/-- Canonical cutoff identity at `dyadicCutoff N L = 2N+L`. -/
theorem finiteSpatialLaplaceFunctional_restrictToFinite_dyadicCutoff
    (N L : ℕ) (g : ℝ → ℝ) (ω : InfiniteSample) :
    finiteSpatialLaplaceFunctional (dyadicCutoff N L) N L g
        (restrictToFinite (dyadicCutoff N L) ω) =
      infiniteSpatialLaplaceFunctional N L g ω := by
  exact finiteSpatialLaplaceFunctional_restrictToFinite
    (M := dyadicCutoff N L) (N := N) (L := L)
    (by rfl) g ω

theorem measurable_finiteSpatialLaplaceFunctional
    (M N L : ℕ) (g : ℝ → ℝ) :
    Measurable (finiteSpatialLaplaceFunctional M N L g) := by
  exact measurable_of_finite _

/-- The infinite spatial functional is a measurable cylinder observable. -/
theorem measurable_infiniteSpatialLaplaceFunctional
    (N L : ℕ) (g : ℝ → ℝ) :
    Measurable (infiniteSpatialLaplaceFunctional N L g) := by
  let M := dyadicCutoff N L
  have hfun :
      infiniteSpatialLaplaceFunctional N L g =
        finiteSpatialLaplaceFunctional M N L g ∘
          restrictToFinite M := by
    funext ω
    exact
      (finiteSpatialLaplaceFunctional_restrictToFinite_dyadicCutoff
        N L g ω).symm
  rw [hfun]
  exact (measurable_finiteSpatialLaplaceFunctional M N L g).comp
    (measurable_restrictToFinite M)

/-- Spatial expectation under the literal infinite Rademacher law. -/
def infiniteSpatialLaplaceExpectation
    (N L : ℕ) (g : ℝ → ℝ) : ℝ :=
  ∫ ω, infiniteSpatialLaplaceFunctional N L g ω
    ∂infiniteRademacherMeasure

/-- The corresponding expectation on a finite prime cylinder. -/
def finiteSpatialLaplaceExpectation
    (M N L : ℕ) (g : ℝ → ℝ) : ℝ :=
  ∫ σ, finiteSpatialLaplaceFunctional M N L g σ
    ∂finiteRademacherMeasure M

/--
Exact expectation transfer from any adequate finite cylinder to the
infinite source law.
-/
theorem infiniteSpatialLaplaceExpectation_eq_finite
    {M N L : ℕ} (hcut : 2 * N + L ≤ M)
    (g : ℝ → ℝ) :
    infiniteSpatialLaplaceExpectation N L g =
      finiteSpatialLaplaceExpectation M N L g := by
  unfold infiniteSpatialLaplaceExpectation
    finiteSpatialLaplaceExpectation
  calc
    (∫ ω, infiniteSpatialLaplaceFunctional N L g ω
        ∂infiniteRademacherMeasure) =
        ∫ ω,
          finiteSpatialLaplaceFunctional M N L g
            (restrictToFinite M ω)
          ∂infiniteRademacherMeasure := by
      apply integral_congr_ae
      filter_upwards [] with ω
      exact
        (finiteSpatialLaplaceFunctional_restrictToFinite
          hcut g ω).symm
    _ = ∫ σ, finiteSpatialLaplaceFunctional M N L g σ
          ∂finiteRademacherMeasure M := by
      rw [← map_infiniteRademacherMeasure_restrictToFinite M]
      exact
        (integral_map_of_stronglyMeasurable
          (measurable_restrictToFinite M)
          (measurable_finiteSpatialLaplaceFunctional M N L g
            |>.stronglyMeasurable)).symm

/-- Canonical-cutoff form of the exact spatial expectation transfer. -/
theorem infiniteSpatialLaplaceExpectation_eq_finite_dyadicCutoff
    (N L : ℕ) (g : ℝ → ℝ) :
    infiniteSpatialLaplaceExpectation N L g =
      finiteSpatialLaplaceExpectation (dyadicCutoff N L) N L g := by
  exact infiniteSpatialLaplaceExpectation_eq_finite
    (M := dyadicCutoff N L) (N := N) (L := L)
    (by rfl) g

/-! ## Truncated marked process -/

/-- Common maximum row count `Q = L+E+1`. -/
def markedLaplaceRowCutoff (L E : ℕ) : ℕ :=
  excessRowCount L E

/-- Finite-cylinder Laplace functional for exact marks `0 ≤ e ≤ E`. -/
def finiteMarkedLaplaceFunctional
    (M N L E : ℕ) (g : ℝ → ℕ → ℝ)
    (σ : SampleSpace M) : ℝ :=
  Real.exp
    (-(∑ x ∈ dyadicBlock N,
      ∑ e ∈ Finset.range (E + 1),
        if exactLengthAt σ x (excessRowCount L e) then
          g ((x : ℝ) / (N : ℝ)) e
        else 0))

/--
Literal truncated marked Laplace functional under the infinite source law.
-/
def infiniteMarkedLaplaceFunctional
    (N L E : ℕ) (g : ℝ → ℕ → ℝ)
    (ω : InfiniteSample) : ℝ :=
  Real.exp
    (-(∑ x ∈ dyadicBlock N,
      ∑ e ∈ Finset.range (E + 1),
        if ExactLengthEvent (infiniteValueBit ω) x
            (excessRowCount L e) then
          g ((x : ℝ) / (N : ℝ)) e
        else 0))

/--
Pointwise marked-cylinder identity.  One common cutoff covers all marks
`e ≤ E`.
-/
theorem finiteMarkedLaplaceFunctional_restrictToFinite
    {M N L E : ℕ}
    (hcut : 2 * N + markedLaplaceRowCutoff L E ≤ M)
    (g : ℝ → ℕ → ℝ) (ω : InfiniteSample) :
    finiteMarkedLaplaceFunctional M N L E g
        (restrictToFinite M ω) =
      infiniteMarkedLaplaceFunctional N L E g ω := by
  unfold finiteMarkedLaplaceFunctional
    infiniteMarkedLaplaceFunctional
  congr 2
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro e he
  have hxUpper : x < 2 * N :=
    (Finset.mem_Ico.mp (by simpa only [dyadicBlock] using hx)).2
  have heE : e ≤ E :=
    Nat.le_of_lt_succ (Finset.mem_range.mp he)
  have hrows :
      excessRowCount L e ≤ markedLaplaceRowCutoff L E := by
    simp only [markedLaplaceRowCutoff, excessRowCount]
    omega
  have heventCut :
      x + (excessRowCount L e - 1) ≤ M := by
    omega
  have hevent :=
    exactLengthAt_restrictToFinite_iff
      (M := M) (x := x) (q := excessRowCount L e)
      ω heventCut
  by_cases hfinite :
      exactLengthAt (restrictToFinite M ω) x
        (excessRowCount L e)
  · have hinfinite :
        ExactLengthEvent (infiniteValueBit ω) x
          (excessRowCount L e) :=
      hevent.mp hfinite
    simp [hfinite, hinfinite]
  · have hinfinite :
        ¬ExactLengthEvent (infiniteValueBit ω) x
          (excessRowCount L e) := by
      exact fun h ↦ hfinite (hevent.mpr h)
    simp [hfinite, hinfinite]

/-- Canonical common-cutoff identity for all marks `e ≤ E`. -/
theorem finiteMarkedLaplaceFunctional_restrictToFinite_dyadicCutoff
    (N L E : ℕ) (g : ℝ → ℕ → ℝ)
    (ω : InfiniteSample) :
    finiteMarkedLaplaceFunctional
        (dyadicCutoff N (markedLaplaceRowCutoff L E))
        N L E g
        (restrictToFinite
          (dyadicCutoff N (markedLaplaceRowCutoff L E)) ω) =
      infiniteMarkedLaplaceFunctional N L E g ω := by
  exact finiteMarkedLaplaceFunctional_restrictToFinite
    (M := dyadicCutoff N (markedLaplaceRowCutoff L E))
    (N := N) (L := L) (E := E)
    (by rfl) g ω

theorem measurable_finiteMarkedLaplaceFunctional
    (M N L E : ℕ) (g : ℝ → ℕ → ℝ) :
    Measurable (finiteMarkedLaplaceFunctional M N L E g) := by
  exact measurable_of_finite _

/-- The truncated marked source functional is measurable. -/
theorem measurable_infiniteMarkedLaplaceFunctional
    (N L E : ℕ) (g : ℝ → ℕ → ℝ) :
    Measurable (infiniteMarkedLaplaceFunctional N L E g) := by
  let M := dyadicCutoff N (markedLaplaceRowCutoff L E)
  have hfun :
      infiniteMarkedLaplaceFunctional N L E g =
        finiteMarkedLaplaceFunctional M N L E g ∘
          restrictToFinite M := by
    funext ω
    exact
      (finiteMarkedLaplaceFunctional_restrictToFinite_dyadicCutoff
        N L E g ω).symm
  rw [hfun]
  exact (measurable_finiteMarkedLaplaceFunctional M N L E g).comp
    (measurable_restrictToFinite M)

/-- Truncated marked expectation under the infinite source law. -/
def infiniteMarkedLaplaceExpectation
    (N L E : ℕ) (g : ℝ → ℕ → ℝ) : ℝ :=
  ∫ ω, infiniteMarkedLaplaceFunctional N L E g ω
    ∂infiniteRademacherMeasure

/-- Truncated marked expectation on a finite prime cylinder. -/
def finiteMarkedLaplaceExpectation
    (M N L E : ℕ) (g : ℝ → ℕ → ℝ) : ℝ :=
  ∫ σ, finiteMarkedLaplaceFunctional M N L E g σ
    ∂finiteRademacherMeasure M

/-- Exact expectation transfer for every adequate common marked cutoff. -/
theorem infiniteMarkedLaplaceExpectation_eq_finite
    {M N L E : ℕ}
    (hcut : 2 * N + markedLaplaceRowCutoff L E ≤ M)
    (g : ℝ → ℕ → ℝ) :
    infiniteMarkedLaplaceExpectation N L E g =
      finiteMarkedLaplaceExpectation M N L E g := by
  unfold infiniteMarkedLaplaceExpectation
    finiteMarkedLaplaceExpectation
  calc
    (∫ ω, infiniteMarkedLaplaceFunctional N L E g ω
        ∂infiniteRademacherMeasure) =
        ∫ ω,
          finiteMarkedLaplaceFunctional M N L E g
            (restrictToFinite M ω)
          ∂infiniteRademacherMeasure := by
      apply integral_congr_ae
      filter_upwards [] with ω
      exact
        (finiteMarkedLaplaceFunctional_restrictToFinite
          hcut g ω).symm
    _ = ∫ σ, finiteMarkedLaplaceFunctional M N L E g σ
          ∂finiteRademacherMeasure M := by
      rw [← map_infiniteRademacherMeasure_restrictToFinite M]
      exact
        (integral_map_of_stronglyMeasurable
          (measurable_restrictToFinite M)
          (measurable_finiteMarkedLaplaceFunctional M N L E g
            |>.stronglyMeasurable)).symm

/-- Canonical-cutoff form of the marked expectation transfer. -/
theorem infiniteMarkedLaplaceExpectation_eq_finite_dyadicCutoff
    (N L E : ℕ) (g : ℝ → ℕ → ℝ) :
    infiniteMarkedLaplaceExpectation N L E g =
      finiteMarkedLaplaceExpectation
        (dyadicCutoff N (markedLaplaceRowCutoff L E))
        N L E g := by
  exact infiniteMarkedLaplaceExpectation_eq_finite
    (M := dyadicCutoff N (markedLaplaceRowCutoff L E))
    (N := N) (L := L) (E := E)
    (by rfl) g

end

end InfiniteLaplaceTransfer
end PaperC
