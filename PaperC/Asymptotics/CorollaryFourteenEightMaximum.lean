import PaperC.Asymptotics.MarkedDetruncationCritical
import PaperC.Asymptotics.MaskedPoissonCanonical
import PaperC.Probability.PoissonVoidApproximation

/-!
# Corollary 14.8: law of the maximum exact excess

The exact de-truncation identity says that

`{maximum excess ≤ m} = {there is no start of length L + m + 1}`

almost surely.  This module transfers the latter void event to the audited
finite-cylinder count law and applies canonical Proposition 14.2 at the
shifted length.  Along `N / 2^L → λ`, the shifted Poisson parameter tends to
`λ / 2^(m+1)`, yielding

`P(maximum excess ≤ m) → exp (-λ / 2^(m+1))`.

The empty configuration is included on the left, exactly matching the
manuscript convention `maximum ∅ = -∞`.
-/

open scoped BigOperators ENNReal Topology
open MeasureTheory Set Filter

namespace PaperC
namespace CorollaryFourteenEightMaximum

open InfiniteRademacher
open InfiniteCylinderTransfer
open InfiniteExactLengthProbabilityTransfer
open InfiniteStartProbabilityTransfer
open MarkedDetruncation
open MarkedDetruncationCritical
open ConditionalAGGAverage
open SectionThirteenCouplings
open SectionThirteenFiniteBound
open MaskedPoissonCritical
open ArratiaGoldsteinGordonInput
open ProbabilityTheory

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

noncomputable section

local instance (P : Prop) : Decidable P :=
  Classical.propDecidable P

noncomputable local instance instIsProbabilityMeasureInfiniteRademacher :
    IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

/-- No ordinary start of length `q` occurs on the finite dyadic cylinder. -/
def finiteNoDyadicStartEvent (N q : ℕ) :
    Set (DyadicSample N q) :=
  {σ | ∀ x ∈ dyadicBlock N, ¬ startAt σ x q}

/-- The finite no-start event is measurable. -/
theorem measurableSet_finiteNoDyadicStartEvent (N q : ℕ) :
    MeasurableSet (finiteNoDyadicStartEvent N q) :=
  Set.toFinite (finiteNoDyadicStartEvent N q) |>.measurableSet

/--
The source no-start event is exactly the preimage of the finite no-start
event at the canonical dyadic cutoff.
-/
theorem infiniteNoDyadicStartEvent_eq_preimage
    (N q : ℕ) :
    (infiniteDyadicStartEvent N q)ᶜ =
      restrictToFinite (dyadicCutoff N q) ⁻¹'
        finiteNoDyadicStartEvent N q := by
  ext ω
  constructor
  · intro hnone
    have hnone' :
        ∀ x ∈ dyadicBlock N,
          ¬ StartEvent (infiniteValueBit ω) x q := by
      simpa [infiniteDyadicStartEvent] using hnone
    intro x hx hfinite
    have hxUpper : x < 2 * N :=
      (Finset.mem_Ico.mp (by simpa [dyadicBlock] using hx)).2
    have hcut : x + q ≤ dyadicCutoff N q := by
      unfold dyadicCutoff
      omega
    exact hnone' x hx
      ((startAt_restrictToFinite_iff ω hcut).mp hfinite)
  · intro hfinite
    have hfinite' :
        ∀ x ∈ dyadicBlock N,
          ¬ startAt (restrictToFinite (dyadicCutoff N q) ω) x q :=
      hfinite
    have hnone :
        ∀ x ∈ dyadicBlock N,
          ¬ StartEvent (infiniteValueBit ω) x q := by
      intro x hx hinfinite
      have hxUpper : x < 2 * N :=
        (Finset.mem_Ico.mp (by simpa [dyadicBlock] using hx)).2
      have hcut : x + q ≤ dyadicCutoff N q := by
        unfold dyadicCutoff
        omega
      exact hfinite' x hx
        ((startAt_restrictToFinite_iff ω hcut).mpr hinfinite)
    simpa [infiniteDyadicStartEvent] using hnone

/-- Exact source/cylinder equality for the dyadic void probability. -/
theorem infiniteNoDyadicStartProbability_eq_finiteUniform
    (N q : ℕ) :
    (infiniteRademacherMeasure
      (infiniteDyadicStartEvent N q)ᶜ).toReal =
        (((uniformEventProbability
          (M := dyadicCutoff N q)
          (fun σ => ∀ x ∈ dyadicBlock N,
            ¬ startAt σ x q) : ℚ) : ℝ)) := by
  classical
  rw [infiniteNoDyadicStartEvent_eq_preimage,
    ← Measure.map_apply
      (measurable_restrictToFinite (dyadicCutoff N q))
      (measurableSet_finiteNoDyadicStartEvent N q),
    map_infiniteRademacherMeasure_restrictToFinite]
  simp only [finiteNoDyadicStartEvent]
  rw [finiteRademacherMeasure_event_eq_uniformEventProbability,
    ENNReal.toReal_ofReal]
  apply Rat.cast_nonneg.mpr
  unfold uniformEventProbability
  positivity

/-- A finite masked count vanishes exactly when every masked start is absent. -/
theorem fullMaskedDyadicCount_eq_zero_iff
    (N q : ℕ) (σ : DyadicSample N q) :
    fullMaskedDyadicCount N q (dyadicBlock N) σ = 0 ↔
      ∀ x ∈ dyadicBlock N, ¬ startAt σ x q := by
  classical
  unfold fullMaskedDyadicCount
  simp
  rw [Finset.filter_eq_empty_iff]

/-- The zero atom of the finite count law is the finite no-start probability. -/
theorem fullMaskedDyadicStartLaw_zero_eq_finiteUniform
    (N q : ℕ) :
    fullMaskedDyadicStartLaw N q (dyadicBlock N) 0 =
      (((uniformEventProbability
        (M := dyadicCutoff N q)
        (fun σ => ∀ x ∈ dyadicBlock N,
          ¬ startAt σ x q) : ℚ) : ℝ)) := by
  classical
  unfold fullMaskedDyadicStartLaw
  have hLaw :
      finiteNatLaw (fullUniformPMF (dyadicCutoff N q))
          (fullMaskedDyadicCount N q (dyadicBlock N)) 0 =
        eventProbability (fullUniformPMF (dyadicCutoff N q))
          (fun σ =>
            fullMaskedDyadicCount N q (dyadicBlock N) σ = 0) := by
    unfold finiteNatLaw eventProbability
    apply Finset.sum_congr rfl
    intro σ _
    by_cases hzero :
        fullMaskedDyadicCount N q (dyadicBlock N) σ = 0 <;>
      simp [hzero]
  rw [hLaw, eventProbability_fullUniformPMF_eq,
    finiteUniformProbability_eq_uniformEventProbability]
  have hPred :
      (fun σ : DyadicSample N q =>
        fullMaskedDyadicCount N q (dyadicBlock N) σ = 0) =
      (fun σ : DyadicSample N q =>
        ∀ x ∈ dyadicBlock N, ¬ startAt σ x q) := by
    funext σ
    exact propext (fullMaskedDyadicCount_eq_zero_iff N q σ)
  simp only [hPred]

/--
Exact identification of the source maximum probability with the zero atom
of the finite longer-start count.
-/
theorem infiniteMaximumAtMostProbability_eq_finiteLaw_zero
    {N L m : ℕ} (hN : 2 ≤ N) :
    infiniteMaximumAtMostProbability N L m =
      fullMaskedDyadicStartLaw
        N (L + m + 1) (dyadicBlock N) 0 := by
  unfold infiniteMaximumAtMostProbability
  rw [measure_infiniteMaximumAtMostEvent_eq_no_longStart hN,
    infiniteNoDyadicStartProbability_eq_finiteUniform,
    fullMaskedDyadicStartLaw_zero_eq_finiteUniform]

/-- Zero atom of the target Poisson law at the shifted length. -/
theorem shiftedMaskedTargetPoissonLaw_zero
    (N L m : ℕ) :
    maskedTargetPoissonLaw (L + m + 1) (dyadicBlock N) 0 =
      Real.exp
        (-((N : ℝ) / (2 : ℝ) ^ (L + m + 1))) := by
  unfold maskedTargetPoissonLaw poissonPMFReal
    maskedTargetPoissonRate
  simp only [TouchingPairs.card_dyadicBlock, NNReal.coe_mk,
    pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, div_one]

/--
The maximum probability differs from its finite-`N` geometric Poisson
prediction by at most twice the canonical masked total-variation error.
-/
theorem abs_infiniteMaximumAtMostProbability_sub_exp_le
    {N L m : ℕ} (hN : 2 ≤ N) :
    |infiniteMaximumAtMostProbability N L m -
        Real.exp
          (-((N : ℝ) / (2 : ℝ) ^ (L + m + 1)))| ≤
      2 *
        maskedPoissonTotalVariation
          N (L + m + 1) (dyadicBlock N) := by
  rw [infiniteMaximumAtMostProbability_eq_finiteLaw_zero hN,
    ← shiftedMaskedTargetPoissonLaw_zero]
  exact
    PoissonVoidApproximation.abs_mass_zero_sub_le_two_mul_natTotalVariation
      (by
        unfold fullMaskedDyadicStartLaw
        exact
          (hasSum_finiteNatLaw
            (fullUniformPMF (dyadicCutoff N (L + m + 1)))
            (fullMaskedDyadicCount N (L + m + 1)
              (dyadicBlock N))).summable)
      (by
        unfold maskedTargetPoissonLaw
        exact (poissonPMFRealSum _).summable)
      (fun k => by
        unfold fullMaskedDyadicStartLaw
        exact finiteNatLaw_nonneg _ _ k)
      (fun _ => poissonPMFReal_nonneg)

/--
Corollary 14.8, maximum part, through the canonical arithmetic route.
-/
theorem corollary_fourteen_eight_maximum
    {C lam : ℝ} (hC : 0 ≤ C)
    (hAGG : ArratiaGoldsteinGordonStatement)
    (hES :
      EvertseSilvermanInput.EvertseSilvermanAbscissaStatement)
    (hConductor :
      PellInput.QuadraticOrderConductorFiberBoundStatement)
    (hDivisor :
      PellInput.NicolasRobinDivisorLogBoundStatement)
    (Lseq : ℕ → ℕ)
    (hwindow :
      ∀ᶠ N : ℕ in atTop,
        CriticalRunWindow.InRunLengthWindow C N (Lseq N))
    (hbalance :
      Tendsto
        (fun N : ℕ => (N : ℝ) / (2 : ℝ) ^ (Lseq N))
        atTop (𝓝 lam))
    (m : ℕ) :
    Tendsto
      (fun N : ℕ =>
        infiniteMaximumAtMostProbability N (Lseq N) m)
      atTop
      (𝓝 (Real.exp (-(lam / (2 : ℝ) ^ (m + 1))))) := by
  let Cshift : ℝ := C + ((m + 1 : ℕ) : ℝ)
  have hCshift : 0 ≤ Cshift := by
    dsimp only [Cshift]
    positivity
  have htv :=
    MaskedPoissonCanonical.maskedPoissonTotalVariation_uniformLittleOOne
      hCshift hAGG hES hConductor hDivisor
  have htvSeq :
      Tendsto
        (fun N : ℕ =>
          maskedPoissonTotalVariation
            N (Lseq N + m + 1) (dyadicBlock N))
        atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨Ntv, hNtv⟩ := htv (ε / 2) (by linarith)
    obtain ⟨Nwindow, hNwindow⟩ := eventually_atTop.1 hwindow
    refine ⟨max Ntv Nwindow, ?_⟩
    intro N hN
    have hbound :=
      hNtv N ((le_max_left _ _).trans hN)
        (Lseq N + m + 1)
        (by
          simpa only [Cshift] using
            shifted_runLength_mem (E := m)
              (hNwindow N ((le_max_right _ _).trans hN)))
        (dyadicBlock N) (by rfl)
    rw [Real.dist_eq]
    have hbound' :
        maskedPoissonTotalVariation
            N (Lseq N + m + 1) (dyadicBlock N) < ε :=
      hbound.trans_lt (by linarith)
    simpa only [sub_zero,
      abs_of_nonneg
        (maskedPoissonTotalVariation_nonneg
          N (Lseq N + m + 1) (dyadicBlock N))] using hbound'
  have hrate :
      Tendsto
        (fun N : ℕ =>
          (N : ℝ) / (2 : ℝ) ^ (Lseq N + m + 1))
        atTop
        (𝓝 (lam / (2 : ℝ) ^ (m + 1))) := by
    have hdiv := hbalance.div_const ((2 : ℝ) ^ (m + 1))
    convert hdiv using 1
    · funext N
      rw [show Lseq N + m + 1 = Lseq N + (m + 1) by omega,
        pow_add]
      ring
  have hexp :
      Tendsto
        (fun N : ℕ =>
          Real.exp
            (-((N : ℝ) / (2 : ℝ) ^ (Lseq N + m + 1))))
        atTop
        (𝓝 (Real.exp (-(lam / (2 : ℝ) ^ (m + 1))))) :=
    (Real.continuous_exp.continuousAt.tendsto).comp hrate.neg
  let approx : ℕ → ℝ := fun N =>
    Real.exp (-((N : ℝ) / (2 : ℝ) ^ (Lseq N + m + 1)))
  let err : ℕ → ℝ := fun N =>
    infiniteMaximumAtMostProbability N (Lseq N) m - approx N
  have herrAbs :
      Tendsto (fun N : ℕ => |err N|) atTop (𝓝 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall fun _ => abs_nonneg _
    · have hNtwo : ∀ᶠ N : ℕ in atTop, 2 ≤ N :=
        eventually_ge_atTop 2
      filter_upwards [hNtwo] with N hN
      exact
        abs_infiniteMaximumAtMostProbability_sub_exp_le
          (L := Lseq N) (m := m) hN
    · simpa only [mul_zero] using htvSeq.const_mul 2
  have herr : Tendsto err atTop (𝓝 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa only [sub_zero, Real.norm_eq_abs] using herrAbs
  have hsum := herr.add hexp
  convert hsum using 1
  · funext N
    dsimp only [err, approx]
    ring
  · simp

end

end CorollaryFourteenEightMaximum
end PaperC
