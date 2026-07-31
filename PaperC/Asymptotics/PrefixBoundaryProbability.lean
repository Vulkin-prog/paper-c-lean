import PaperC.Asymptotics.CorollaryPrefixLaw
import PaperC.Asymptotics.DependencyEdgesCritical

/-!
# Probability of the left-boundary prefix event

The special boundary term in the finite-prefix count is the event that the
values at `1, ..., L` are all equal.  Complete multiplicativity makes the
value at `1` zero in additive coordinates, and testing the event at every
prime `p ≤ L` shows that it is exactly the zero assignment on the finite
prime cylinder `SampleSpace L`.  Projection of the infinite product law to
that cylinder therefore gives the exact mass

`2 ^ (-Nat.primeCounting L)`.

The final theorem records that this mass is uniformly `o(1)` in the literal
critical run-length window.
-/

open scoped ENNReal Topology
open MeasureTheory Set Filter

namespace PaperC
namespace PrefixBoundaryProbability

open CorollaryPrefixLaw
open InfiniteCylinderTransfer
open InfiniteExactLengthProbabilityTransfer
open InfiniteRademacher

/- Keep the measurable structure definitionally identical to the infinite
product model and its finite projections. -/
local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

noncomputable section

/-! ## The boundary event is the zero finite assignment -/

/-- Primes represented by `PrimeUpTo L` are exactly `Nat.primesLE L`. -/
noncomputable def primeUpToEquivPrimesLE (L : ℕ) :
    PrimeUpTo L ≃ {p : ℕ // p ∈ Nat.primesLE L} where
  toFun p :=
    ⟨p.1.1, Nat.mem_primesLE.mpr
      ⟨Nat.le_of_lt_succ p.1.2, p.2⟩⟩
  invFun p :=
    ⟨⟨p.1, Nat.lt_succ_iff.mpr
      (Nat.mem_primesLE.mp p.2).1⟩,
      (Nat.mem_primesLE.mp p.2).2⟩
  left_inv p := by
    apply Subtype.ext
    apply Fin.ext
    rfl
  right_inv p := by
    apply Subtype.ext
    rfl

/-- The number of coordinates in `SampleSpace L` is `π(L)`. -/
theorem card_primeUpTo_eq_primeCounting (L : ℕ) :
    Fintype.card (PrimeUpTo L) = Nat.primeCounting L := by
  calc
    Fintype.card (PrimeUpTo L) =
        Fintype.card {p : ℕ // p ∈ Nat.primesLE L} :=
      Fintype.card_congr (primeUpToEquivPrimesLE L)
    _ = (Nat.primesLE L).card := Fintype.card_coe _
    _ = Nat.primeCounting L := Nat.primesLE_card_eq_primeCounting L

/-- On a represented prime, `valueBit` reads exactly that prime coordinate. -/
@[simp]
theorem valueBit_primeUpTo
    {L : ℕ} (sigma : SampleSpace L) (p : PrimeUpTo L) :
    valueBit sigma p.1.1 = sigma p := by
  classical
  simp only [valueBit, parityVec, p.2.factorization,
    Finsupp.mapRange_single]
  rw [Fintype.sum_eq_single p]
  · simp
  · intro q hqp
    have hval : q.1.1 ≠ p.1.1 := by
      intro h
      apply hqp
      apply Subtype.ext
      apply Fin.ext
      exact h
    simp [hval]

/-- The additive value at `1` is always zero. -/
@[simp]
theorem valueBit_one {L : ℕ} (sigma : SampleSpace L) :
    valueBit sigma 1 = 0 := by
  simp [valueBit]

/--
The finite boundary predicate is equivalent to the zero assignment on all
prime coordinates at most `L`.
-/
theorem prefixBoundaryEvent_valueBit_iff_eq_zero
    {L : ℕ} (sigma : SampleSpace L) :
    prefixBoundaryEvent (valueBit sigma) L ↔ sigma = 0 := by
  constructor
  · intro hboundary
    funext p
    have hpOne : 1 ≤ p.1.1 := p.2.one_le
    have hpL : p.1.1 ≤ L := Nat.le_of_lt_succ p.1.2
    have hvalue := hboundary (p.1.1 - 1) (by omega)
    have hindex : 1 + (p.1.1 - 1) = p.1.1 := by omega
    rw [hindex, valueBit_primeUpTo, valueBit_one] at hvalue
    simpa using hvalue
  · intro hsigma
    subst sigma
    intro j hj
    simp [valueBit]

/-- The boundary event in the finite prime cylinder. -/
def finitePrefixBoundaryEvent (L : ℕ) : Set (SampleSpace L) :=
  {sigma | prefixBoundaryEvent (valueBit sigma) L}

/-- The boundary event under the infinite Rademacher product law. -/
def infinitePrefixBoundaryEvent (L : ℕ) : Set InfiniteSample :=
  {omega | prefixBoundaryEvent (infiniteValueBit omega) L}

/-- The finite event is literally the singleton containing the zero sample. -/
theorem finitePrefixBoundaryEvent_eq_singleton_zero (L : ℕ) :
    finitePrefixBoundaryEvent L = ({0} : Set (SampleSpace L)) := by
  ext sigma
  exact prefixBoundaryEvent_valueBit_iff_eq_zero sigma

/-- Restriction to primes at most `L` preserves the boundary predicate. -/
theorem prefixBoundaryEvent_restrictToFinite_iff
    (L : ℕ) (omega : InfiniteSample) :
    prefixBoundaryEvent (valueBit (restrictToFinite L omega)) L ↔
      prefixBoundaryEvent (infiniteValueBit omega) L := by
  unfold prefixBoundaryEvent
  constructor <;> intro hboundary j hj
  · simpa only [
        valueBit_restrictToFinite_eq_infiniteValueBit omega
          (show 1 + j ≤ L by omega),
        valueBit_restrictToFinite_eq_infiniteValueBit omega
          (show 1 ≤ L by omega)] using
      hboundary j hj
  · simpa only [
        valueBit_restrictToFinite_eq_infiniteValueBit omega
          (show 1 + j ≤ L by omega),
        valueBit_restrictToFinite_eq_infiniteValueBit omega
          (show 1 ≤ L by omega)] using
      hboundary j hj

/-- The source event is the preimage of the zero finite assignment. -/
theorem infinitePrefixBoundaryEvent_eq_preimage (L : ℕ) :
    infinitePrefixBoundaryEvent L =
      restrictToFinite L ⁻¹' finitePrefixBoundaryEvent L := by
  ext omega
  exact (prefixBoundaryEvent_restrictToFinite_iff L omega).symm

theorem measurableSet_finitePrefixBoundaryEvent (L : ℕ) :
    MeasurableSet (finitePrefixBoundaryEvent L) :=
  Set.toFinite (finitePrefixBoundaryEvent L) |>.measurableSet

theorem measurableSet_infinitePrefixBoundaryEvent (L : ℕ) :
    MeasurableSet (infinitePrefixBoundaryEvent L) := by
  rw [infinitePrefixBoundaryEvent_eq_preimage]
  exact
    (measurable_restrictToFinite L)
      (measurableSet_finitePrefixBoundaryEvent L)

/-! ## Exact probability and uniform decay -/

/-- Exact `ENNReal` mass of the left-boundary event. -/
theorem measure_infinitePrefixBoundaryEvent (L : ℕ) :
    infiniteRademacherMeasure (infinitePrefixBoundaryEvent L) =
      ((2 : ℝ≥0∞)⁻¹) ^ Nat.primeCounting L := by
  rw [infinitePrefixBoundaryEvent_eq_preimage,
    ← Measure.map_apply (measurable_restrictToFinite L)
      (measurableSet_finitePrefixBoundaryEvent L),
    map_infiniteRademacherMeasure_restrictToFinite,
    finitePrefixBoundaryEvent_eq_singleton_zero,
    finiteRademacherMeasure_singleton,
    card_primeUpTo_eq_primeCounting]

/-- Literal event formulation used in the finite-prefix coupling. -/
theorem measure_prefixBoundaryEvent_infiniteValueBit (L : ℕ) :
    infiniteRademacherMeasure
        {omega | prefixBoundaryEvent (infiniteValueBit omega) L} =
      ((2 : ℝ≥0∞)⁻¹) ^ Nat.primeCounting L := by
  simpa only [infinitePrefixBoundaryEvent] using
    measure_infinitePrefixBoundaryEvent L

/-- Real-valued probability of the left-boundary event. -/
noncomputable def infinitePrefixBoundaryProbability (L : ℕ) : ℝ :=
  (infiniteRademacherMeasure (infinitePrefixBoundaryEvent L)).toReal

/-- Exact real form `2 ^ (-π(L))`. -/
theorem infinitePrefixBoundaryProbability_eq (L : ℕ) :
    infinitePrefixBoundaryProbability L =
      ((2 : ℝ)⁻¹) ^ Nat.primeCounting L := by
  unfold infinitePrefixBoundaryProbability
  rw [measure_infinitePrefixBoundaryEvent]
  simp

/-- The explicit boundary probability tends to zero with `L`. -/
theorem infinitePrefixBoundaryProbability_tendsto_zero :
    Tendsto infinitePrefixBoundaryProbability atTop (nhds 0) := by
  have hpow :
      Tendsto (fun n : ℕ ↦ ((2 : ℝ)⁻¹) ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : 0 ≤ (2 : ℝ)⁻¹)
      (by norm_num : (2 : ℝ)⁻¹ < 1)
  rw [show infinitePrefixBoundaryProbability =
      (fun L : ℕ ↦ ((2 : ℝ)⁻¹) ^ Nat.primeCounting L) by
    funext L
    exact infinitePrefixBoundaryProbability_eq L]
  exact hpow.comp Nat.tendsto_primeCounting

/--
Uniform `o(1)` form in the manuscript window `|L - log₂ M| ≤ C`.
-/
theorem infinitePrefixBoundaryProbability_uniformLittleOOne
    {C : ℝ} (hC : 0 ≤ C) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun _ L ↦ infinitePrefixBoundaryProbability L)
      (fun _ _ ↦ 1) := by
  intro epsilon hepsilon
  obtain ⟨L₀, hL₀⟩ :=
    Metric.tendsto_atTop.mp
      infinitePrefixBoundaryProbability_tendsto_zero epsilon hepsilon
  obtain ⟨M₀, hM₀⟩ :=
    DependencyEdgesCritical.runLengthAddOne_tends_to_infinity
      hC (L₀ + 1)
  refine ⟨M₀, ?_⟩
  intro M hM L hrun
  have hL : L₀ ≤ L := by
    have hLadd := hM₀ M hM L hrun
    omega
  have hdist := hL₀ L hL
  rw [Real.dist_eq] at hdist
  simpa using hdist.le

end

end PrefixBoundaryProbability
end PaperC
