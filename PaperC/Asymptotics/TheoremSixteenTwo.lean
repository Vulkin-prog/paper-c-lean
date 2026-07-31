import PaperC.Asymptotics.PropositionFifteenFiveClosure
import PaperC.Asymptotics.PropositionFifteenFivePartition
import PaperC.Asymptotics.PropositionSixteenOne
import PaperC.Asymptotics.BoundedRatioSteinChen
import PaperC.Asymptotics.BoundedRatioPoissonAssembly
import PaperC.Asymptotics.BoundedRatioSteinChenSecondTermCritical
import PaperC.Asymptotics.BoundedRatioFixedJBadStarts
import PaperC.Diophantine.EvertseSilvermanInput
import PaperC.Diophantine.GeneralizedPell
import PaperC.Probability.FiniteCylinderCountTransport
import PaperC.Probability.SectionThirteenCouplings
import PaperC.Probability.CriticalRunWindow

set_option maxHeartbeats 1600000

/-!
# Theorem 16.2: the global interior Poisson law

This file separates the finite probability bookkeeping in Theorem 16.2 from
the one genuinely new fixed-ratio estimate of Section 16.  The global count
is literal: it counts every start `2 ≤ x < M` on one finite prime cylinder
large enough to contain all its windows.  Its parameter is the exact
expectation of this count.

For a truncation depth `j₀`, the retained count uses
`M / 2^j₀ ≤ x < M`.  Proposition 15.5 controls the complementary starts.
The intermediate proposition `BoundedRangePoissonConclusion` records what
is needed at each *fixed* `j₀`:

* a Poisson approximation for the retained count;
* its first-moment asymptotic with factor `1 - 2⁻ʲ⁰`.

The proof below performs, in Lean, the order of limits required by the
manuscript: choose `j₀` first, and only then choose the threshold in `M`.
It also proves the coupling truncation bound, Poisson recentering, the
asymptotic for the exact mean, and the probability-of-zero conclusion.

The intermediate fixed-ratio proposition is discharged below from the
certified bounded-ratio Stein--Chen estimates and the exact transport between
the local and global finite cylinders.

The finite-model compatibility needed here is proved below: a one-start event
computed on the common global cylinder has the same probability as on the
local cylinder already used by Proposition 15.5.  The proof splits off the
unused prime coordinates above the local window and therefore introduces no
bridge hypothesis.
-/

namespace PaperC
namespace TheoremSixteenTwo

open scoped BigOperators Topology NNReal
open Filter

open ArratiaGoldsteinGordonInput
open BoundedRatioFixedJBadStarts
open BoundedRatioPoissonAssembly
open BoundedRatioSteinChenRates
open BoundedRatioSteinChenSecondTermCritical
open ConditionalAGGAverage
open ConditionalStartProbability
open FiniteCylinderCountTransport
open PropositionFifteenFiveClosure
open PropositionSixteenOne
open ProbabilityTheory
open SectionThirteenCouplings
open SectionThirteenFiniteBound

noncomputable section

open BoundedRatioCanonicalTerminalPopulation

local instance (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-! ## The literal global count and its law -/

/--
The common prime cutoff for all windows beginning at `2 ≤ x < M`.

The slightly generous value `2M+L` reuses the canonical dyadic cutoff and,
in particular, includes windows which cross the right endpoint `M`.
-/
def globalCylinderCutoff (M L : ℕ) : ℕ :=
  dyadicCutoff M L

/-- Interior starts in the exact manuscript range `2 ≤ x < M`. -/
def globalStartIndices (M : ℕ) : Finset ℕ :=
  Finset.Ico 2 M

/-- Starts retained after truncation at depth `j₀`. -/
def retainedStartIndices (M j₀ : ℕ) : Finset ℕ :=
  Finset.Ico (M / 2 ^ j₀) M

/-- Starts discarded at depth `j₀`. -/
def discardedStartIndices (M j₀ : ℕ) : Finset ℕ :=
  Finset.Ico 2 (M / 2 ^ j₀)

/-- The literal global count `Z_M = ∑_{2≤x<M} J_{x,L}`. -/
noncomputable def globalStartCount
    (M L : ℕ)
    (ω : SampleSpace (globalCylinderCutoff M L)) : ℕ :=
  ∑ x ∈ globalStartIndices M,
    if startAt ω x L then 1 else 0

/-- The count on the fixed-ratio range retained after truncation. -/
noncomputable def retainedStartCount
    (M L j₀ : ℕ)
    (ω : SampleSpace (globalCylinderCutoff M L)) : ℕ :=
  ∑ x ∈ retainedStartIndices M j₀,
    if startAt ω x L then 1 else 0

/-- Uniform law on the common global finite cylinder. -/
noncomputable def globalUniformPMF (M L : ℕ) :
    FinitePMF (SampleSpace (globalCylinderCutoff M L)) :=
  fullUniformPMF (globalCylinderCutoff M L)

/-- Law of the literal global count. -/
noncomputable def globalStartLaw (M L : ℕ) : ℕ → ℝ :=
  finiteNatLaw (globalUniformPMF M L) (globalStartCount M L)

/-- Law of the retained fixed-ratio count. -/
noncomputable def retainedStartLaw
    (M L j₀ : ℕ) : ℕ → ℝ :=
  finiteNatLaw (globalUniformPMF M L)
    (retainedStartCount M L j₀)

/-- One-start probability on the common global cylinder. -/
noncomputable def commonCylinderStartProbability
    (M L x : ℕ) : ℝ :=
  eventProbability (globalUniformPMF M L)
    (fun ω ↦ startAt ω x L)

/--
The exact parameter `Λ_M = E Z_M`, written as the sum of its one-point
marginals.
-/
noncomputable def globalStartMean (M L : ℕ) : ℝ :=
  ∑ x ∈ globalStartIndices M,
    commonCylinderStartProbability M L x

/-- Exact mean of the retained fixed-ratio count. -/
noncomputable def retainedStartMean (M L j₀ : ℕ) : ℝ :=
  ∑ x ∈ retainedStartIndices M j₀,
    commonCylinderStartProbability M L x

/-- Probability mass removed by truncation, on the common cylinder. -/
noncomputable def discardedStartMass (M L j₀ : ℕ) : ℝ :=
  ∑ x ∈ discardedStartIndices M j₀,
    commonCylinderStartProbability M L x

/-- The global parameter packaged as a nonnegative Poisson rate. -/
noncomputable def globalStartRate (M L : ℕ) : ℝ≥0 :=
  ⟨globalStartMean M L, by
    unfold globalStartMean commonCylinderStartProbability
    exact Finset.sum_nonneg fun x _ ↦
      eventProbability_nonneg _ _⟩

/-- The retained parameter packaged as a nonnegative Poisson rate. -/
noncomputable def retainedStartRate (M L j₀ : ℕ) : ℝ≥0 :=
  ⟨retainedStartMean M L j₀, by
    unfold retainedStartMean commonCylinderStartProbability
    exact Finset.sum_nonneg fun x _ ↦
      eventProbability_nonneg _ _⟩

/-- The critical first-moment scale `M 2⁻ᴸ`. -/
noncomputable def criticalScale (M L : ℕ) : ℝ :=
  (M : ℝ) / (2 : ℝ) ^ L

/-- Probability that the literal global count is zero. -/
noncomputable def globalEmptyProbability (M L : ℕ) : ℝ :=
  globalStartLaw M L 0

theorem globalStartMean_nonneg (M L : ℕ) :
    0 ≤ globalStartMean M L :=
  (globalStartRate M L).2

theorem retainedStartMean_nonneg (M L j₀ : ℕ) :
    0 ≤ retainedStartMean M L j₀ :=
  (retainedStartRate M L j₀).2

theorem discardedStartMass_nonneg (M L j₀ : ℕ) :
    0 ≤ discardedStartMass M L j₀ := by
  unfold discardedStartMass commonCylinderStartProbability
  exact Finset.sum_nonneg fun x _ ↦
    eventProbability_nonneg _ _

theorem summable_globalStartLaw (M L : ℕ) :
    Summable (globalStartLaw M L) :=
  summable_finiteNatLaw _ _

theorem summable_retainedStartLaw (M L j₀ : ℕ) :
    Summable (retainedStartLaw M L j₀) :=
  summable_finiteNatLaw _ _

theorem globalStartLaw_nonneg (M L k : ℕ) :
    0 ≤ globalStartLaw M L k :=
  finiteNatLaw_nonneg _ _ _

theorem retainedStartLaw_nonneg (M L j₀ k : ℕ) :
    0 ≤ retainedStartLaw M L j₀ k :=
  finiteNatLaw_nonneg _ _ _

/-! ## `Λ_M` really is the expectation -/

/-- Real expectation of the literal global count on its finite cylinder. -/
noncomputable def globalStartCountExpectation (M L : ℕ) : ℝ :=
  ∑ ω : SampleSpace (globalCylinderCutoff M L),
    (globalUniformPMF M L).prob ω * (globalStartCount M L ω : ℝ)

/-- Real expectation of the retained count on the same cylinder. -/
noncomputable def retainedStartCountExpectation
    (M L j₀ : ℕ) : ℝ :=
  ∑ ω : SampleSpace (globalCylinderCutoff M L),
    (globalUniformPMF M L).prob ω *
      (retainedStartCount M L j₀ ω : ℝ)

/-- Exact identity `Λ_M = E Z_M`. -/
theorem globalStartMean_eq_expectation (M L : ℕ) :
    globalStartMean M L =
      globalStartCountExpectation M L := by
  classical
  unfold globalStartMean globalStartCountExpectation
    commonCylinderStartProbability globalStartCount eventProbability
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  calc
    (∑ x ∈ globalStartIndices M,
        ∑ ω : SampleSpace (globalCylinderCutoff M L),
          if startAt ω x L then
            (globalUniformPMF M L).prob ω else 0) =
        ∑ ω : SampleSpace (globalCylinderCutoff M L),
          ∑ x ∈ globalStartIndices M,
            if startAt ω x L then
              (globalUniformPMF M L).prob ω else 0 := by
      rw [Finset.sum_comm]
    _ =
        ∑ ω : SampleSpace (globalCylinderCutoff M L),
          (globalUniformPMF M L).prob ω *
            ∑ x ∈ globalStartIndices M,
              if startAt ω x L then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro ω _hω
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _hx
      by_cases hstart : startAt ω x L <;>
        simp [hstart]

/-- The analogous exact expectation identity for the retained count. -/
theorem retainedStartMean_eq_expectation (M L j₀ : ℕ) :
    retainedStartMean M L j₀ =
      retainedStartCountExpectation M L j₀ := by
  classical
  unfold retainedStartMean retainedStartCountExpectation
    commonCylinderStartProbability retainedStartCount eventProbability
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  calc
    (∑ x ∈ retainedStartIndices M j₀,
        ∑ ω : SampleSpace (globalCylinderCutoff M L),
          if startAt ω x L then
            (globalUniformPMF M L).prob ω else 0) =
        ∑ ω : SampleSpace (globalCylinderCutoff M L),
          ∑ x ∈ retainedStartIndices M j₀,
            if startAt ω x L then
              (globalUniformPMF M L).prob ω else 0 := by
      rw [Finset.sum_comm]
    _ =
        ∑ ω : SampleSpace (globalCylinderCutoff M L),
          (globalUniformPMF M L).prob ω *
            ∑ x ∈ retainedStartIndices M j₀,
              if startAt ω x L then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro ω _hω
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _hx
      by_cases hstart : startAt ω x L <;>
        simp [hstart]

/-! ## Exact finite truncation bookkeeping -/

theorem globalStartIndices_eq_discarded_union_retained
    {M j₀ : ℕ} (hcut : 2 ≤ M / 2 ^ j₀) :
    globalStartIndices M =
      discardedStartIndices M j₀ ∪ retainedStartIndices M j₀ := by
  ext x
  simp only [globalStartIndices, discardedStartIndices,
    retainedStartIndices, Finset.mem_Ico, Finset.mem_union]
  constructor
  · intro hx
    by_cases hdiscard : x < M / 2 ^ j₀
    · exact Or.inl ⟨hx.1, hdiscard⟩
    · exact Or.inr ⟨Nat.le_of_not_gt hdiscard, hx.2⟩
  · rintro (hx | hx)
    · exact
        ⟨hx.1,
          hx.2.trans_le (Nat.div_le_self M (2 ^ j₀))⟩
    · exact ⟨hcut.trans hx.1, hx.2⟩

theorem discarded_retained_disjoint (M j₀ : ℕ) :
    Disjoint (discardedStartIndices M j₀)
      (retainedStartIndices M j₀) := by
  rw [Finset.disjoint_left]
  intro x hxDiscard hxRetained
  have hd :=
    Finset.mem_Ico.mp
      (by simpa only [discardedStartIndices] using hxDiscard)
  have hr :=
    Finset.mem_Ico.mp
      (by simpa only [retainedStartIndices] using hxRetained)
  omega

theorem globalStartCount_eq_discarded_add_retained
    {M L j₀ : ℕ} (hcut : 2 ≤ M / 2 ^ j₀)
    (ω : SampleSpace (globalCylinderCutoff M L)) :
    globalStartCount M L ω =
      (∑ x ∈ discardedStartIndices M j₀,
          if startAt ω x L then 1 else 0) +
        retainedStartCount M L j₀ ω := by
  classical
  unfold globalStartCount retainedStartCount
  rw [globalStartIndices_eq_discarded_union_retained hcut,
    Finset.sum_union (discarded_retained_disjoint M j₀)]

theorem globalStartMean_eq_discarded_add_retained
    {M L j₀ : ℕ} (hcut : 2 ≤ M / 2 ^ j₀) :
    globalStartMean M L =
      discardedStartMass M L j₀ +
        retainedStartMean M L j₀ := by
  classical
  unfold globalStartMean discardedStartMass retainedStartMean
  rw [globalStartIndices_eq_discarded_union_retained hcut,
    Finset.sum_union (discarded_retained_disjoint M j₀)]

/--
If the global and retained counts differ, a discarded start actually
occurs.  This is the event-level core of the truncation coupling.
-/
theorem exists_discarded_start_of_counts_ne
    {M L j₀ : ℕ} (hcut : 2 ≤ M / 2 ^ j₀)
    {ω : SampleSpace (globalCylinderCutoff M L)}
    (hne :
      globalStartCount M L ω ≠
        retainedStartCount M L j₀ ω) :
    ∃ x ∈ discardedStartIndices M j₀,
      startAt ω x L := by
  by_contra hnone
  push_neg at hnone
  apply hne
  rw [globalStartCount_eq_discarded_add_retained hcut]
  have hzero :
      (∑ x ∈ discardedStartIndices M j₀,
        if startAt ω x L then 1 else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    simp only [if_neg (hnone x hx)]
  rw [hzero, zero_add]

/-- Finite union bound for the truncation disagreement event. -/
theorem disagreementProbability_global_retained_le_discardedMass
    {M L j₀ : ℕ} (hcut : 2 ≤ M / 2 ^ j₀) :
    disagreementProbability
        (globalUniformPMF M L)
        (globalStartCount M L)
        (retainedStartCount M L j₀) ≤
      discardedStartMass M L j₀ := by
  classical
  have hpoint :
      ∀ ω : SampleSpace (globalCylinderCutoff M L),
        (if globalStartCount M L ω ≠
              retainedStartCount M L j₀ ω then
            (globalUniformPMF M L).prob ω
          else 0) ≤
          ∑ x ∈ discardedStartIndices M j₀,
            if startAt ω x L then
              (globalUniformPMF M L).prob ω
            else 0 := by
    intro ω
    by_cases hne :
        globalStartCount M L ω ≠
          retainedStartCount M L j₀ ω
    · rw [if_pos hne]
      obtain ⟨x, hx, hstart⟩ :=
        exists_discarded_start_of_counts_ne hcut hne
      calc
        (globalUniformPMF M L).prob ω =
            (if startAt ω x L then
              (globalUniformPMF M L).prob ω else 0) := by
              rw [if_pos hstart]
        _ ≤
            ∑ y ∈ discardedStartIndices M j₀,
              if startAt ω y L then
                (globalUniformPMF M L).prob ω else 0 := by
          apply Finset.single_le_sum
              (s := discardedStartIndices M j₀)
              (f := fun y ↦
                if startAt ω y L then
                  (globalUniformPMF M L).prob ω else 0)
          · intro y _hy
            split_ifs
            · exact (globalUniformPMF M L).nonneg ω
            · exact le_rfl
          · exact hx
    · rw [if_neg hne]
      exact Finset.sum_nonneg fun x _hx ↦ by
        split_ifs
        · exact (globalUniformPMF M L).nonneg ω
        · exact le_rfl
  unfold disagreementProbability discardedStartMass
    commonCylinderStartProbability eventProbability
  calc
    (∑ ω,
        if globalStartCount M L ω ≠
              retainedStartCount M L j₀ ω then
          (globalUniformPMF M L).prob ω else 0) ≤
        ∑ ω, ∑ x ∈ discardedStartIndices M j₀,
          if startAt ω x L then
            (globalUniformPMF M L).prob ω else 0 :=
      Finset.sum_le_sum fun ω _ ↦ hpoint ω
    _ =
        ∑ x ∈ discardedStartIndices M j₀, ∑ ω,
          if startAt ω x L then
            (globalUniformPMF M L).prob ω else 0 := by
      rw [Finset.sum_comm]

/-- Coupling form of the truncation estimate. -/
theorem natTotalVariation_global_retained_le_discardedMass
    {M L j₀ : ℕ} (hcut : 2 ≤ M / 2 ^ j₀) :
    natTotalVariation
        (globalStartLaw M L)
        (retainedStartLaw M L j₀) ≤
      discardedStartMass M L j₀ := by
  exact
    (natTotalVariation_finiteNatLaw_le_disagreement
      (globalUniformPMF M L)
      (globalStartCount M L)
      (retainedStartCount M L j₀)).trans
        (disagreementProbability_global_retained_le_discardedMass hcut)

/-! ## Alignment with Proposition 15.5 -/

/-!
### Cylinder enlargement for a single start

The common cylinder is split at the cutoff of the local one-start cylinder.
The small prime coordinates are canonically the local sample space, whereas
the remaining coordinates do not occur in any integer label of the start
window.  The following finite equivalences make this elementary marginal
invariance explicit.
-/

/--
Prime coordinates at most `H` inside a larger cutoff `G` are canonically the
prime coordinates of the cutoff-`H` cylinder.
-/
def smallPrimeCoordinateEquiv
    {G H : ℕ} (hHG : H ≤ G) :
    SmallPrimeCoordinate G H ≃ PrimeUpTo H where
  toFun p :=
    ⟨⟨p.1.1, Nat.lt_succ_of_le p.2⟩, p.1.2⟩
  invFun p :=
    ⟨⟨⟨p.1.1,
        Nat.lt_succ_of_le
          ((Nat.le_of_lt_succ p.1.2).trans hHG)⟩,
      p.2⟩,
      Nat.le_of_lt_succ p.1.2⟩
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv p := by
    apply Subtype.ext
    apply Fin.ext
    rfl

/-- Assignment-level form of `smallPrimeCoordinateEquiv`. -/
def smallSampleEquiv
    {G H : ℕ} (hHG : H ≤ G) :
    SmallSample G H ≃ SampleSpace H where
  toFun σ p := σ ((smallPrimeCoordinateEquiv hHG).symm p)
  invFun ω p := ω (smallPrimeCoordinateEquiv hHG p)
  left_inv σ := by
    funext p
    simp
  right_inv ω := by
    funext p
    simp

/--
Zero-extension of a small-coordinate assignment evaluates `valueBit` exactly
as the corresponding assignment on the genuinely smaller cylinder.
-/
theorem valueBit_extendSmall_eq_local
    {G H : ℕ} (hHG : H ≤ G)
    (σ : SmallSample G H) (n : ℕ) :
    valueBit (extendSmall G H σ) n =
      valueBit (smallSampleEquiv hHG σ) n := by
  classical
  unfold valueBit
  rw [← Fintype.sum_subtype_add_sum_subtype
    (fun p : PrimeUpTo G ↦ p.1.1 ≤ H)
    (fun p ↦
      extendSmall G H σ p * parityVec n p.1)]
  have hlarge :
      (∑ p : {p : PrimeUpTo G // ¬p.1.1 ≤ H},
        extendSmall G H σ p.1 * parityVec n p.1.1) = 0 := by
    apply Finset.sum_eq_zero
    intro p _hp
    simp [extendSmall, p.2]
  rw [hlarge, add_zero]
  calc
    (∑ p : SmallPrimeCoordinate G H,
        extendSmall G H σ p.1 * parityVec n p.1.1) =
        ∑ p : SmallPrimeCoordinate G H,
          σ p * parityVec n p.1.1 := by
      apply Finset.sum_congr rfl
      intro p _hp
      simp [extendSmall, p.2]
    _ =
        ∑ p : PrimeUpTo H,
          smallSampleEquiv hHG σ p * parityVec n p.1 :=
      Fintype.sum_equiv
        (smallPrimeCoordinateEquiv hHG)
        (fun p : SmallPrimeCoordinate G H ↦
          σ p * parityVec n p.1.1)
        (fun p : PrimeUpTo H ↦
          smallSampleEquiv hHG σ p * parityVec n p.1)
        (fun p ↦ by
          have hsigma :
              smallSampleEquiv hHG σ
                  (smallPrimeCoordinateEquiv hHG p) =
                σ p := by
            change
              σ ((smallPrimeCoordinateEquiv hHG).symm
                (smallPrimeCoordinateEquiv hHG p)) = σ p
            rw [Equiv.symm_apply_apply]
          have hindex :
              (smallPrimeCoordinateEquiv hHG p).1.1 =
                p.1.1 := rfl
          calc
            σ p * parityVec n p.1.1 =
                smallSampleEquiv hHG σ
                    (smallPrimeCoordinateEquiv hHG p) *
                  parityVec n p.1.1 := by
              rw [hsigma]
            _ =
                smallSampleEquiv hHG σ
                    (smallPrimeCoordinateEquiv hHG p) *
                  parityVec n
                    (smallPrimeCoordinateEquiv hHG p).1 := by
              rw [hindex])

/--
Coordinates strictly above `H` do not affect `valueBit n` when
`0 < n ≤ H`.
-/
theorem valueBit_assemble_eq_local
    {G H : ℕ} (hHG : H ≤ G)
    (σ : SmallSample G H) (η : LargeSample G H)
    {n : ℕ} (hn : 0 < n) (hnH : n ≤ H) :
    valueBit (assemble G H σ η) n =
      valueBit (smallSampleEquiv hHG σ) n := by
  classical
  have hlarge :
      valueBit (extendLarge G H η) n = 0 := by
    unfold valueBit
    apply Finset.sum_eq_zero
    intro p _hp
    by_cases hp : H < p.1.1
    · have hpNotDvd : ¬p.1.1 ∣ n := by
        intro hpDvd
        have hpLe : p.1.1 ≤ n := Nat.le_of_dvd hn hpDvd
        omega
      rw [parityVec_apply,
        Nat.factorization_eq_zero_of_not_dvd hpNotDvd]
      simp
    · simp [extendLarge, hp]
  calc
    valueBit (assemble G H σ η) n =
        valueBit (extendSmall G H σ) n +
          valueBit (extendLarge G H η) n := by
      unfold assemble valueBit
      simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    _ =
        valueBit (smallSampleEquiv hHG σ) n +
          valueBit (extendLarge G H η) n := by
      rw [valueBit_extendSmall_eq_local hHG]
    _ = valueBit (smallSampleEquiv hHG σ) n := by
      rw [hlarge, add_zero]

/--
On an adequate cutoff, a one-start event on the assembled large cylinder is
the corresponding event on its local small-coordinate assignment.
-/
theorem startAt_assemble_iff_local
    {G H x L : ℕ} (hHG : H ≤ G)
    (hx : 2 ≤ x) (hwindow : x + L ≤ H)
    (σ : SmallSample G H) (η : LargeSample G H) :
    startAt (assemble G H σ η) x L ↔
      startAt (smallSampleEquiv hHG σ) x L := by
  unfold startAt StartEvent
  have hleft :
      valueBit (assemble G H σ η) (x - 1) =
        valueBit (smallSampleEquiv hHG σ) (x - 1) :=
    valueBit_assemble_eq_local hHG σ η
      (by omega) (by omega)
  have hbase :
      valueBit (assemble G H σ η) x =
        valueBit (smallSampleEquiv hHG σ) x :=
    valueBit_assemble_eq_local hHG σ η
      (by omega) (by omega)
  constructor
  · rintro ⟨hboundary, hrun⟩
    constructor
    · simpa only [hleft, hbase] using hboundary
    · intro j hj
      have hjValue :
          valueBit (assemble G H σ η) (x + j) =
            valueBit (smallSampleEquiv hHG σ) (x + j) :=
        valueBit_assemble_eq_local hHG σ η
          (by omega) (by omega)
      simpa only [hjValue, hbase] using hrun j hj
  · rintro ⟨hboundary, hrun⟩
    constructor
    · simpa only [hleft, hbase] using hboundary
    · intro j hj
      have hjValue :
          valueBit (assemble G H σ η) (x + j) =
            valueBit (smallSampleEquiv hHG σ) (x + j) :=
        valueBit_assemble_eq_local hHG σ η
          (by omega) (by omega)
      simpa only [hjValue, hbase] using hrun j hj

/--
The large prime cylinder is the product of the local one-start cylinder and
the unused coordinates above its cutoff.
-/
def sampleSpaceEquivLocalProd
    {G H : ℕ} (hHG : H ≤ G) :
    SampleSpace G ≃ SampleSpace H × LargeSample G H :=
  (sampleSplitEquiv G H).trans
    (Equiv.prodCongr (smallSampleEquiv hHG) (Equiv.refl _))

theorem startAt_sampleSpaceEquivLocalProd_iff
    {G H x L : ℕ} (hHG : H ≤ G)
    (hx : 2 ≤ x) (hwindow : x + L ≤ H)
    (ω : SampleSpace G) :
    startAt ω x L ↔
      startAt (sampleSpaceEquivLocalProd hHG ω).1 x L := by
  let σ := restrictSmall G H ω
  let η := restrictLarge G H ω
  have hassemble : assemble G H σ η = ω :=
    assemble_restrictions G H ω
  have hlocal :=
    startAt_assemble_iff_local hHG hx hwindow σ η
  rw [hassemble] at hlocal
  simpa [sampleSpaceEquivLocalProd, sampleSplitEquiv, σ, η] using hlocal

/-- Event-level equivalence induced by the cylinder product decomposition. -/
def startEventEquivLocalProd
    {G H x L : ℕ} (hHG : H ≤ G)
    (hx : 2 ≤ x) (hwindow : x + L ≤ H) :
    {ω : SampleSpace G // startAt ω x L} ≃
      {ω : SampleSpace H // startAt ω x L} ×
        LargeSample G H where
  toFun ω :=
    let pieces := sampleSpaceEquivLocalProd hHG ω.1
    (⟨pieces.1,
      (startAt_sampleSpaceEquivLocalProd_iff
        hHG hx hwindow ω.1).mp ω.2⟩,
      pieces.2)
  invFun pieces :=
    let ω :=
      (sampleSpaceEquivLocalProd hHG).symm
        (pieces.1.1, pieces.2)
    ⟨ω, (startAt_sampleSpaceEquivLocalProd_iff
      hHG hx hwindow ω).mpr (by
        have hfst :
            (sampleSpaceEquivLocalProd hHG ω).1 =
              pieces.1.1 :=
          congrArg Prod.fst
            ((sampleSpaceEquivLocalProd hHG).apply_symm_apply
              (pieces.1.1, pieces.2))
        rw [hfst]
        exact pieces.1.2)⟩
  left_inv ω := by
    apply Subtype.ext
    exact (sampleSpaceEquivLocalProd hHG).symm_apply_apply ω.1
  right_inv pieces := by
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst
        ((sampleSpaceEquivLocalProd hHG).apply_symm_apply
          (pieces.1.1, pieces.2))
    · change
        ((sampleSpaceEquivLocalProd hHG)
          ((sampleSpaceEquivLocalProd hHG).symm
            (pieces.1.1, pieces.2))).2 = pieces.2
      exact congrArg Prod.snd
        ((sampleSpaceEquivLocalProd hHG).apply_symm_apply
          (pieces.1.1, pieces.2))

/--
Uniform one-start probabilities are invariant under enlarging an adequate
finite prime cylinder.
-/
theorem uniformEventProbability_startAt_cutoff_invariant
    {G H x L : ℕ} (hHG : H ≤ G)
    (hx : 2 ≤ x) (hwindow : x + L ≤ H) :
    uniformEventProbability
        (M := G) (fun ω ↦ startAt ω x L) =
      uniformEventProbability
        (M := H) (fun ω ↦ startAt ω x L) := by
  classical
  unfold uniformEventProbability
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  have hEventCard :
      Fintype.card {ω : SampleSpace G // startAt ω x L} =
        Fintype.card {ω : SampleSpace H // startAt ω x L} *
          Fintype.card (LargeSample G H) := by
    rw [Fintype.card_congr
      (startEventEquivLocalProd hHG hx hwindow)]
    exact Fintype.card_prod _ _
  have hSampleCard :
      Fintype.card (SampleSpace G) =
        Fintype.card (SampleSpace H) *
          Fintype.card (LargeSample G H) := by
    rw [Fintype.card_congr (sampleSpaceEquivLocalProd hHG)]
    exact Fintype.card_prod _ _
  rw [hEventCard, hSampleCard]
  have hLarge :
      (Fintype.card (LargeSample G H) : ℚ) ≠ 0 := by
    exact_mod_cast
      (Fintype.card_ne_zero :
        Fintype.card (LargeSample G H) ≠ 0)
  push_cast
  field_simp [hLarge]
  <;> ring

/--
Finite-cylinder marginal compatibility, proved by the explicit product
decomposition above.  The event on the common global cylinder observes
exactly the same prime coordinates as the local one-start cylinder used in
`PropositionFifteenFive.globalStartProbability`.
-/
theorem commonCylinderStartProbability_eq_globalStartProbability
    {M L x : ℕ} (hx : x ∈ globalStartIndices M) :
    commonCylinderStartProbability M L x =
      PropositionFifteenFive.globalStartProbability L x := by
  have hxBounds :
      2 ≤ x ∧ x < M := by
    simpa only [globalStartIndices, Finset.mem_Ico] using hx
  have hcutoff :
      dyadicCutoff x L ≤ globalCylinderCutoff M L := by
    unfold globalCylinderCutoff dyadicCutoff
    omega
  have hwindow : x + L ≤ dyadicCutoff x L := by
    unfold dyadicCutoff
    omega
  unfold commonCylinderStartProbability globalUniformPMF
    PropositionFifteenFive.globalStartProbability
  rw [eventProbability_fullUniformPMF_eq,
    finiteUniformProbability_eq_uniformEventProbability]
  norm_cast
  exact
    uniformEventProbability_startAt_cutoff_invariant
      hcutoff hxBounds.1 hwindow

theorem discardedStartMass_eq_deepStartProbabilityMass
    {M L j₀ : ℕ} (hcut : 2 ≤ M / 2 ^ j₀) :
    discardedStartMass M L j₀ =
      deepStartProbabilityMass M L j₀ := by
  unfold discardedStartMass deepStartProbabilityMass
    discardedStartIndices
  apply Finset.sum_congr rfl
  intro x hx
  apply commonCylinderStartProbability_eq_globalStartProbability
  rw [globalStartIndices, Finset.mem_Ico]
  have hx' := Finset.mem_Ico.mp hx
  exact ⟨hx'.1, hx'.2.trans_le (Nat.div_le_self M _)⟩

theorem natTotalVariation_global_retained_le_deepMass
    {M L j₀ : ℕ} (hcut : 2 ≤ M / 2 ^ j₀) :
    natTotalVariation
        (globalStartLaw M L)
        (retainedStartLaw M L j₀) ≤
      deepStartProbabilityMass M L j₀ := by
  rw [← discardedStartMass_eq_deepStartProbabilityMass
    hcut]
  exact natTotalVariation_global_retained_le_discardedMass hcut

theorem abs_globalMean_sub_retainedMean_eq_deepMass
    {M L j₀ : ℕ} (hcut : 2 ≤ M / 2 ^ j₀) :
    |globalStartMean M L - retainedStartMean M L j₀| =
      deepStartProbabilityMass M L j₀ := by
  rw [globalStartMean_eq_discarded_add_retained hcut]
  rw [add_sub_cancel_right]
  rw [abs_of_nonneg (discardedStartMass_nonneg M L j₀)]
  exact discardedStartMass_eq_deepStartProbabilityMass hcut

/-! ## Intermediate fixed-ratio conclusion -/

/--
The retained count is asymptotically Poisson on every fixed-ratio range.

The quantifier over `j₀` is outside both little-oh statements.  Thus the
threshold in `M` may depend on `j₀`, exactly as in the proof of Theorem 16.2;
no uniformity for a growing ratio is asserted.
-/
def BoundedRangePoissonConclusion (C : ℝ) : Prop :=
  ∀ j₀ : ℕ, 2 ≤ j₀ →
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun M L ↦
        natTotalVariation
          (retainedStartLaw M L j₀)
          (poissonPMFReal (retainedStartRate M L j₀)))
      (fun _ _ ↦ 1) ∧
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun M L ↦
        retainedStartMean M L j₀ -
          (1 - (1 / 2 : ℝ) ^ j₀) * criticalScale M L)
      (fun _ _ ↦ 1)

/-! ## Exact transport from the local bounded-ratio cylinder -/

theorem boundedRatioBlock_div_eq_retainedStartIndices
    (M j : ℕ) :
    boundedRatioBlock (M / 2 ^ j) M =
      retainedStartIndices M j := by
  ext x
  simp only [mem_boundedRatioBlock,
    retainedStartIndices, Finset.mem_Ico]

theorem boundedRatioCutoff_le_globalCylinderCutoff
    (M L : ℕ) :
    boundedRatioCutoff M L ≤ globalCylinderCutoff M L := by
  unfold boundedRatioCutoff globalCylinderCutoff dyadicCutoff
  omega

theorem two_le_of_mem_retainedStartIndices
    {M j x : ℕ} (hcut : 2 ≤ M / 2 ^ j)
    (hx : x ∈ retainedStartIndices M j) :
    2 ≤ x := by
  have hx' :
      M / 2 ^ j ≤ x ∧ x < M := by
    simpa only [retainedStartIndices, Finset.mem_Ico] using hx
  exact hcut.trans hx'.1

theorem retained_window_le_boundedRatioCutoff
    {M L j x : ℕ}
    (hx : x ∈ retainedStartIndices M j) :
    x + L ≤ boundedRatioCutoff M L := by
  have hx' :
      M / 2 ^ j ≤ x ∧ x < M := by
    simpa only [retainedStartIndices, Finset.mem_Ico] using hx
  unfold boundedRatioCutoff
  omega

/-- The local full law is exactly the retained law on the global cylinder. -/
theorem boundedFullStartLaw_eq_retainedStartLaw
    {M L j : ℕ} (hcut : 2 ≤ M / 2 ^ j) :
    boundedFullStartLaw (M / 2 ^ j) M L =
      retainedStartLaw M L j := by
  have htransport :=
    FiniteCylinderCountTransport.finiteNatLaw_startCountOn_cutoff_invariant
      (boundedRatioCutoff_le_globalCylinderCutoff M L)
      (retainedStartIndices M j)
      (fun x hx ↦ two_le_of_mem_retainedStartIndices hcut hx)
      (fun x hx ↦ retained_window_le_boundedRatioCutoff hx)
  simpa only [boundedFullStartLaw, boundedFullStartCount,
    FiniteCylinderCountTransport.startCountOn,
    retainedStartLaw, globalUniformPMF, retainedStartCount,
    boundedRatioBlock_div_eq_retainedStartIndices] using htransport.symm

/-- The local exact mean is the retained mean on the global cylinder. -/
theorem boundedFullStartMean_eq_retainedStartMean
    {M L j : ℕ} (hcut : 2 ≤ M / 2 ^ j) :
    boundedFullStartMean (M / 2 ^ j) M L =
      retainedStartMean M L j := by
  classical
  unfold boundedFullStartMean retainedStartMean
  rw [boundedRatioBlock_div_eq_retainedStartIndices]
  apply Finset.sum_congr rfl
  intro x hx
  have hxBlock :
      x ∈ boundedRatioBlock (M / 2 ^ j) M := by
    rw [boundedRatioBlock_div_eq_retainedStartIndices]
    exact hx
  have hxGlobal : x ∈ globalStartIndices M := by
    have hxRetained :
        M / 2 ^ j ≤ x ∧ x < M := by
      simpa only [retainedStartIndices, Finset.mem_Ico] using hx
    simp only [globalStartIndices, Finset.mem_Ico]
    exact ⟨hcut.trans hxRetained.1, hxRetained.2⟩
  rw [boundedStartProbability_eq_selfStartProbability hcut hxBlock,
    commonCylinderStartProbability_eq_globalStartProbability hxGlobal]
  rfl

theorem boundedFullStartRate_eq_retainedStartRate
    {M L j : ℕ} (hcut : 2 ≤ M / 2 ^ j) :
    boundedFullStartRate (M / 2 ^ j) M L =
      retainedStartRate M L j := by
  apply NNReal.eq
  change
    boundedFullStartMean (M / 2 ^ j) M L =
      retainedStartMean M L j
  exact boundedFullStartMean_eq_retainedStartMean hcut

/-! ## Certified fixed-ratio conclusion -/

private theorem retainedStartLaw_poisson_uniformLittleOOne
    {C : ℝ} (hC : 0 ≤ C) {j : ℕ} (hj : 1 ≤ j)
    (hAGG : ArratiaGoldsteinGordonStatement)
    (hR2 :
      PropositionSixteenOneStatement
        (fixedJWindowConstant C j) (2 ^ (j + 1))) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun M L ↦
        natTotalVariation
          (retainedStartLaw M L j)
          (poissonPMFReal (retainedStartRate M L j)))
      (fun _ _ ↦ 1) := by
  have hCfixed :
      0 ≤ fixedJWindowConstant C j :=
    fixedJWindowConstant_nonneg hC j
  have hbTwo :
      BoundedRatioBadStarts.UniformLittleOOneInBoundedRatioWindow
        (fixedJWindowConstant C j) (2 ^ (j + 1))
        (fun N M L ↦
          BoundedRatioSteinChenSecondTerm.boundedConditionalBTwoAverage
            N M L (TerminalPrimeCutoff.terminalPrimeCutoff (L + 1))) := by
    simpa only [terminalBoundedConditionalBTwoAverage] using
      (terminalBoundedConditionalBTwoAverage_uniformLittleOOne
        hCfixed (2 ^ (j + 1)) hR2)
  have hbounded :=
    boundedFullStartLaw_poisson_uniformLittleOOne
      hCfixed (2 ^ (j + 1)) hAGG hbTwo
  have hlocal :=
    fixedJ_uniformLittleOOne_of_boundedRatio hj hbounded
  intro ε hε
  obtain ⟨Mlocal, hMlocal⟩ := hlocal ε hε
  refine ⟨max (2 ^ (j + 1)) Mlocal, ?_⟩
  intro M hM L hrun
  have hcut : 2 ≤ M / 2 ^ j := by
    rw [Nat.le_div_iff_mul_le (pow_pos (by norm_num) j)]
    calc
      2 * 2 ^ j = 2 ^ (j + 1) := by
        rw [pow_succ]
        ring
      _ ≤ M := (le_max_left _ _).trans hM
  have hbound :=
    hMlocal M ((le_max_right _ _).trans hM) L hrun
  change
    |natTotalVariation
        (boundedFullStartLaw (M / 2 ^ j) M L)
        (poissonPMFReal
          (boundedFullStartRate (M / 2 ^ j) M L))| ≤
      ε * |(1 : ℝ)| at hbound
  change
    |natTotalVariation
        (retainedStartLaw M L j)
        (poissonPMFReal (retainedStartRate M L j))| ≤
      ε * |(1 : ℝ)|
  rw [boundedFullStartLaw_eq_retainedStartLaw hcut,
    boundedFullStartRate_eq_retainedStartRate hcut] at hbound
  exact hbound

private theorem retainedStartMean_mainTerm_uniformLittleOOne
    {C : ℝ} (hC : 0 ≤ C) {j : ℕ} (hj : 1 ≤ j) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun M L ↦
        retainedStartMean M L j -
          (1 - (1 / 2 : ℝ) ^ j) * criticalScale M L)
      (fun _ _ ↦ 1) := by
  have hmean :=
    retainedFullStartMean_sub_lengthParameter_uniformLittleOOne
      hC hj
  have hround :=
    retainedLength_mainTerm_uniformLittleOOne hC j
  have hsum :=
    PropositionElevenTwo.uniformLittleOOn_add hmean hround
  have hlocal :
      UniformLittleOOn
        (CriticalRunWindow.InRunLengthWindow C)
        (fun M L ↦
          boundedFullStartMean (M / 2 ^ j) M L -
            (1 - (1 / 2 : ℝ) ^ j) * criticalScale M L)
        (fun _ _ ↦ 1) := by
    have hfun :
        (fun M L ↦
          boundedFullStartMean (M / 2 ^ j) M L -
            (1 - (1 / 2 : ℝ) ^ j) * criticalScale M L) =
        (fun M L ↦
          (boundedFullStartMean (M / 2 ^ j) M L -
            ((M - M / 2 ^ j : ℕ) : ℝ) / (2 : ℝ) ^ L) +
          (((M - M / 2 ^ j : ℕ) : ℝ) / (2 : ℝ) ^ L -
            (1 - (1 / 2 : ℝ) ^ j) *
              (M : ℝ) / (2 : ℝ) ^ L)) := by
      funext M L
      unfold criticalScale
      ring
    rw [hfun]
    exact hsum
  intro ε hε
  obtain ⟨Mlocal, hMlocal⟩ := hlocal ε hε
  refine ⟨max (2 ^ (j + 1)) Mlocal, ?_⟩
  intro M hM L hrun
  have hcut : 2 ≤ M / 2 ^ j := by
    rw [Nat.le_div_iff_mul_le (pow_pos (by norm_num) j)]
    calc
      2 * 2 ^ j = 2 ^ (j + 1) := by
        rw [pow_succ]
        ring
      _ ≤ M := (le_max_left _ _).trans hM
  have hbound :=
    hMlocal M ((le_max_right _ _).trans hM) L hrun
  change
    |boundedFullStartMean (M / 2 ^ j) M L -
        (1 - (1 / 2 : ℝ) ^ j) * criticalScale M L| ≤
      ε * |(1 : ℝ)| at hbound
  change
    |retainedStartMean M L j -
        (1 - (1 / 2 : ℝ) ^ j) * criticalScale M L| ≤
      ε * |(1 : ℝ)|
  rw [boundedFullStartMean_eq_retainedStartMean hcut] at hbound
  exact hbound

private theorem boundedRangePoissonConclusion
    {C : ℝ} (hC : 0 ≤ C)
    (hAGG : ArratiaGoldsteinGordonStatement)
    (hR2 :
      ∀ C' : ℝ, 0 < C' →
        ∀ κ₀ : ℕ, 2 ≤ κ₀ →
          PropositionSixteenOneStatement C' κ₀) :
    BoundedRangePoissonConclusion C := by
  intro j hj
  have hjOne : 1 ≤ j := hj.trans' (by norm_num)
  have hfixedPos :
      0 < fixedJWindowConstant C j := by
    unfold fixedJWindowConstant
    positivity
  have hratio :
      2 ≤ 2 ^ (j + 1) := by
    calc
      2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (j + 1) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
  have hR2fixed :=
    hR2 (fixedJWindowConstant C j) hfixedPos
      (2 ^ (j + 1)) hratio
  exact
    ⟨retainedStartLaw_poisson_uniformLittleOOne
        hC hjOne hAGG hR2fixed,
      retainedStartMean_mainTerm_uniformLittleOOne hC hjOne⟩

/-! ## Analytic tools for the double passage -/

theorem two_pow_le_of_two_le_div
    {M j₀ : ℕ} (hM : 2 ^ (j₀ + 1) ≤ M) :
    2 ≤ M / 2 ^ j₀ := by
  rw [Nat.le_div_iff_mul_le (pow_pos (by norm_num) j₀)]
  calc
    2 * 2 ^ j₀ = 2 ^ (j₀ + 1) := by
      rw [pow_succ]
      ring
    _ ≤ M := hM

/-- Uniform upper bound for `M 2⁻ᴸ` in the critical window. -/
theorem criticalScale_le_balanceConstant
    {C : ℝ} (hC : 0 ≤ C) :
    ∃ M₀ : ℕ, ∀ M ≥ M₀, ∀ L,
      CriticalRunWindow.InRunLengthWindow C M L →
      criticalScale M L ≤ CriticalRunWindow.balanceConstant C := by
  obtain ⟨M₀, hM₀⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  refine ⟨M₀, ?_⟩
  intro M hM L hrun
  exact (hM₀ M hM L hrun).2.2

/-- Positive lower balance constant used to convert absolute to relative error. -/
noncomputable def lowerBalanceConstant (C : ℝ) : ℝ :=
  Real.exp (-C * Real.log 2)

theorem lowerBalanceConstant_pos (C : ℝ) :
    0 < lowerBalanceConstant C := by
  unfold lowerBalanceConstant
  positivity

/-- Uniform lower bound for `M 2⁻ᴸ` in the literal critical window. -/
theorem lowerBalanceConstant_le_criticalScale
    {C : ℝ} {M L : ℕ}
    (hM : 1 ≤ M)
    (hrun : CriticalRunWindow.InRunLengthWindow C M L) :
    lowerBalanceConstant C ≤ criticalScale M L := by
  have hlogTwo : 0 < Real.log (2 : ℝ) :=
    Real.log_pos (by norm_num)
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hright :
      (L : ℝ) - Real.log M / Real.log 2 ≤ C :=
    (le_abs_self _).trans hrun
  have hlog :
      (L : ℝ) * Real.log 2 - Real.log M ≤
        C * Real.log 2 := by
    have := mul_le_mul_of_nonneg_right hright hlogTwo.le
    field_simp at this
    linarith
  have hexp :
      Real.exp
          ((L : ℝ) * Real.log 2 - Real.log M) ≤
        Real.exp (C * Real.log 2) :=
    Real.exp_le_exp.mpr hlog
  have hpow :
      Real.exp ((L : ℝ) * Real.log 2) = (2 : ℝ) ^ L := by
    rw [Real.exp_nat_mul,
      Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hquotient :
      (2 : ℝ) ^ L / (M : ℝ) ≤
        Real.exp (C * Real.log 2) := by
    calc
      (2 : ℝ) ^ L / (M : ℝ) =
          Real.exp
            ((L : ℝ) * Real.log 2 - Real.log M) := by
        rw [← hpow, Real.exp_sub, Real.exp_log hMpos]
      _ ≤ Real.exp (C * Real.log 2) := hexp
  have hpowLe :
      (2 : ℝ) ^ L ≤
        Real.exp (C * Real.log 2) * (M : ℝ) :=
    (div_le_iff₀ hMpos).mp hquotient
  have hcancel :
      Real.exp (-C * Real.log 2) *
          Real.exp (C * Real.log 2) = 1 := by
    rw [← Real.exp_add]
    simp
  unfold lowerBalanceConstant criticalScale
  apply (le_div_iff₀ (pow_pos (by norm_num) L)).2
  calc
    Real.exp (-C * Real.log 2) * (2 : ℝ) ^ L ≤
        Real.exp (-C * Real.log 2) *
          (Real.exp (C * Real.log 2) * (M : ℝ)) :=
      mul_le_mul_of_nonneg_left hpowLe (Real.exp_pos _).le
    _ = (M : ℝ) := by
      rw [← mul_assoc, hcancel, one_mul]

theorem criticalScale_nonneg (M L : ℕ) :
    0 ≤ criticalScale M L := by
  unfold criticalScale
  positivity

/--
A single atom difference is bounded by twice total variation.  This factor
is harmless for convergence and avoids importing a separate event-level TV
API.
-/
theorem abs_mass_zero_sub_le_two_mul_natTotalVariation
    {p q : ℕ → ℝ}
    (hp : Summable p) (hq : Summable q)
    (hp0 : ∀ k, 0 ≤ p k) (hq0 : ∀ k, 0 ≤ q k) :
    |p 0 - q 0| ≤ 2 * natTotalVariation p q := by
  have hs :
      Summable fun k ↦ |p k - q k| :=
    summable_abs_sub_of_nonneg hp hq hp0 hq0
  have hsingle :
      |p 0 - q 0| ≤ ∑' k : ℕ, |p k - q k| := by
    let g : ℕ → ℝ :=
      fun k ↦ if k = 0 then |p k - q k| else 0
    have hmono :
        g ≤ (fun k : ℕ ↦ |p k - q k|) := by
      intro k
      dsimp only [g]
      split_ifs
      · exact le_rfl
      · exact abs_nonneg _
    have hg : HasSum g |p 0 - q 0| := by
      have hfun :
          g =
            fun k : ℕ ↦
              if k = 0 then |p 0 - q 0| else 0 := by
        funext k
        by_cases hk : k = 0
        · subst k
          simp [g]
        · simp [g, hk]
      rw [hfun]
      exact hasSum_ite_eq 0 (|p 0 - q 0| : ℝ)
    calc
      |p 0 - q 0| = ∑' k : ℕ, g k := hg.tsum_eq.symm
      _ ≤ ∑' k : ℕ, |p k - q k| :=
        hg.summable.tsum_le_tsum hmono hs
  unfold natTotalVariation
  linarith

theorem poissonPMFReal_zero_eq_exp_neg (r : ℝ≥0) :
    poissonPMFReal r 0 = Real.exp (-(r : ℝ)) := by
  unfold poissonPMFReal
  norm_num

/-! ## The global total-variation limit -/

/--
The two-stage truncation argument proving the first conclusion of Theorem
16.2.  The witness `j₀` is fixed before either fixed-ratio threshold in `M`
is requested.
-/
private theorem global_totalVariation_uniformLittleOOne_of_truncation
    {C : ℝ}
    (htrunc : PropositionFifteenFiveStatement C)
    (hbounded : BoundedRangePoissonConclusion C) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun M L ↦
        natTotalVariation
          (globalStartLaw M L)
          (poissonPMFReal (globalStartRate M L)))
      (fun _ _ ↦ 1) := by
  intro ε hε
  obtain ⟨Jtail, hJtail⟩ :=
    htrunc (ε / 8) (by positivity)
  let j₀ := max 2 Jtail
  have hjTwo : 2 ≤ j₀ := le_max_left _ _
  have hjTail : Jtail ≤ j₀ := le_max_right _ _
  obtain ⟨Mtail, hMtail⟩ := hJtail j₀ hjTail
  obtain ⟨hfixedTV, _hfixedMean⟩ :=
    hbounded j₀ hjTwo
  obtain ⟨Mfixed, hMfixed⟩ :=
    hfixedTV (ε / 2) (by positivity)
  refine ⟨max (2 ^ (j₀ + 1)) (max Mtail Mfixed), ?_⟩
  intro M hM L hrun
  have hcut : 2 ≤ M / 2 ^ j₀ :=
    two_pow_le_of_two_le_div
      ((le_max_left _ _).trans hM)
  have htail :
      deepStartProbabilityMass M L j₀ ≤ ε / 8 := by
    have habs :=
      hMtail M
        ((le_trans (le_max_left Mtail Mfixed)
          (le_max_right (2 ^ (j₀ + 1))
            (max Mtail Mfixed))).trans hM)
        L hrun
    rw [abs_of_nonneg
      (deepStartProbabilityMass_nonneg M L j₀)] at habs
    simpa using habs
  have hfixed :
      natTotalVariation
          (retainedStartLaw M L j₀)
          (poissonPMFReal (retainedStartRate M L j₀)) ≤
        ε / 2 := by
    have :=
      hMfixed M
        ((le_trans (le_max_right Mtail Mfixed)
          (le_max_right (2 ^ (j₀ + 1))
            (max Mtail Mfixed))).trans hM)
        L hrun
    rw [abs_of_nonneg
      (natTotalVariation_nonneg _ _)] at this
    simpa using this
  have hmean :
      |globalStartMean M L -
        retainedStartMean M L j₀| ≤ ε / 8 := by
    rw [abs_globalMean_sub_retainedMean_eq_deepMass
      hcut]
    exact htail
  have hrecenter :
      natTotalVariation
          (poissonPMFReal (retainedStartRate M L j₀))
          (poissonPMFReal (globalStartRate M L)) ≤
        ε / 8 := by
    exact
      (natTotalVariation_poisson_le_abs_rate_sub
        (retainedStartRate M L j₀)
        (globalStartRate M L)).trans
        (by
          simpa only [retainedStartRate, globalStartRate,
            NNReal.coe_mk, abs_sub_comm] using hmean)
  have hglobalLaw := summable_globalStartLaw M L
  have hretainedLaw := summable_retainedStartLaw M L j₀
  have hretainedPois :=
    (poissonPMFRealSum (retainedStartRate M L j₀)).summable
  have hglobalPois :=
    (poissonPMFRealSum (globalStartRate M L)).summable
  have htriangleOne :=
    natTotalVariation_triangle
      hglobalLaw hretainedLaw hretainedPois
      (globalStartLaw_nonneg M L)
      (retainedStartLaw_nonneg M L j₀)
      (fun _ ↦ poissonPMFReal_nonneg)
  have htriangleTwo :=
    natTotalVariation_triangle
      hglobalLaw hretainedPois hglobalPois
      (globalStartLaw_nonneg M L)
      (fun _ ↦ poissonPMFReal_nonneg)
      (fun _ ↦ poissonPMFReal_nonneg)
  have htruncate :=
    natTotalVariation_global_retained_le_deepMass
      (M := M) (L := L) (j₀ := j₀)
      hcut
  rw [abs_of_nonneg
    (natTotalVariation_nonneg _ _)]
  simp only [abs_one, mul_one]
  calc
    natTotalVariation
        (globalStartLaw M L)
        (poissonPMFReal (globalStartRate M L)) ≤
      natTotalVariation
          (globalStartLaw M L)
          (poissonPMFReal (retainedStartRate M L j₀)) +
        natTotalVariation
          (poissonPMFReal (retainedStartRate M L j₀))
          (poissonPMFReal (globalStartRate M L)) :=
      htriangleTwo
    _ ≤
        (natTotalVariation
            (globalStartLaw M L)
            (retainedStartLaw M L j₀) +
          natTotalVariation
            (retainedStartLaw M L j₀)
            (poissonPMFReal (retainedStartRate M L j₀))) +
          natTotalVariation
            (poissonPMFReal (retainedStartRate M L j₀))
            (poissonPMFReal (globalStartRate M L)) := by
      exact add_le_add_right htriangleOne _
    _ ≤ (ε / 8 + ε / 2) + ε / 8 := by
      gcongr
      exact htruncate.trans htail
    _ ≤ ε := by linarith

/-! ## The exact-mean asymptotic -/

/--
The exact global mean satisfies
`Λ_M = (1 + o_C(1)) M 2⁻ᴸ`, uniformly in the literal critical window.
-/
private theorem global_mean_asymptotic_of_truncation
    {C : ℝ} (hC : 0 ≤ C)
    (htrunc : PropositionFifteenFiveStatement C)
    (hbounded : BoundedRangePoissonConclusion C) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun M L ↦ globalStartMean M L - criticalScale M L)
      criticalScale := by
  intro ε hε
  let a := lowerBalanceConstant C
  have ha : 0 < a := lowerBalanceConstant_pos C
  obtain ⟨Mbalance, hMbalance⟩ :=
    criticalScale_le_balanceConstant hC
  let b := CriticalRunWindow.balanceConstant C
  have hb : 0 ≤ b := CriticalRunWindow.balanceConstant_nonneg C
  obtain ⟨Jmass, hJmass⟩ :=
    htrunc (ε * a / 4) (by positivity)
  have hdyadic :
      Tendsto (fun j : ℕ ↦ b * (1 / 2 : ℝ) ^ j)
        atTop (𝓝 0) := by
    simpa using
      tendsto_const_nhds.mul
        (tendsto_pow_atTop_nhds_zero_of_lt_one
          (by norm_num : 0 ≤ (1 / 2 : ℝ))
          (by norm_num : (1 / 2 : ℝ) < 1))
  obtain ⟨Jratio, hJratio⟩ :=
    Metric.tendsto_atTop.mp hdyadic
      (ε * a / 4) (by positivity)
  let j₀ := max 2 (max Jmass Jratio)
  have hjTwo : 2 ≤ j₀ :=
    le_max_left _ _
  have hjMass : Jmass ≤ j₀ :=
    (le_max_left Jmass Jratio).trans
      (le_max_right 2 (max Jmass Jratio))
  have hjRatio : Jratio ≤ j₀ :=
    (le_max_right Jmass Jratio).trans
      (le_max_right 2 (max Jmass Jratio))
  obtain ⟨Mmass, hMmass⟩ := hJmass j₀ hjMass
  obtain ⟨_hfixedTV, hfixedMean⟩ :=
    hbounded j₀ hjTwo
  obtain ⟨Mfixed, hMfixed⟩ :=
    hfixedMean (ε * a / 4) (by positivity)
  refine ⟨max 1
    (max (2 ^ (j₀ + 1))
      (max Mbalance (max Mmass Mfixed))), ?_⟩
  intro M hM L hrun
  have hMone : 1 ≤ M := (le_max_left _ _).trans hM
  have hcut : 2 ≤ M / 2 ^ j₀ := by
    apply two_pow_le_of_two_le_div
    exact
      (le_trans
        (le_max_left (2 ^ (j₀ + 1))
          (max Mbalance (max Mmass Mfixed)))
        (le_max_right 1
          (max (2 ^ (j₀ + 1))
            (max Mbalance (max Mmass Mfixed))))).trans hM
  have hscaleLower : a ≤ criticalScale M L :=
    lowerBalanceConstant_le_criticalScale hMone hrun
  have hscaleUpper : criticalScale M L ≤ b :=
    hMbalance M
      ((le_trans
        (le_trans
          (le_max_left Mbalance (max Mmass Mfixed))
          (le_max_right (2 ^ (j₀ + 1))
            (max Mbalance (max Mmass Mfixed))))
        (le_max_right 1
          (max (2 ^ (j₀ + 1))
            (max Mbalance (max Mmass Mfixed))))).trans hM)
      L hrun
  have hmass :
      deepStartProbabilityMass M L j₀ ≤ ε * a / 4 := by
    have :=
      hMmass M
        ((le_trans
          (le_trans
            (le_trans
              (le_max_left Mmass Mfixed)
              (le_max_right Mbalance (max Mmass Mfixed)))
            (le_max_right (2 ^ (j₀ + 1))
              (max Mbalance (max Mmass Mfixed))))
          (le_max_right 1
            (max (2 ^ (j₀ + 1))
              (max Mbalance (max Mmass Mfixed))))).trans hM)
        L hrun
    rw [abs_of_nonneg
      (deepStartProbabilityMass_nonneg M L j₀)] at this
    simpa using this
  have hfixed :
      |retainedStartMean M L j₀ -
        (1 - (1 / 2 : ℝ) ^ j₀) *
          criticalScale M L| ≤ ε * a / 4 := by
    have :=
      hMfixed M
        ((le_trans
          (le_trans
            (le_trans
              (le_max_right Mmass Mfixed)
              (le_max_right Mbalance (max Mmass Mfixed)))
            (le_max_right (2 ^ (j₀ + 1))
              (max Mbalance (max Mmass Mfixed))))
          (le_max_right 1
            (max (2 ^ (j₀ + 1))
              (max Mbalance (max Mmass Mfixed))))).trans hM)
        L hrun
    simpa using this
  have hratioDist :
      dist (b * (1 / 2 : ℝ) ^ j₀) 0 <
        ε * a / 4 :=
    hJratio j₀ hjRatio
  have hratio :
      (1 / 2 : ℝ) ^ j₀ * criticalScale M L ≤
        ε * a / 4 := by
    have htailNonneg : 0 ≤ b * (1 / 2 : ℝ) ^ j₀ :=
      mul_nonneg hb (by positivity)
    have htail :
        b * (1 / 2 : ℝ) ^ j₀ ≤ ε * a / 4 := by
      rw [Real.dist_eq] at hratioDist
      have habs :
          |b * (1 / 2 : ℝ) ^ j₀| ≤ ε * a / 4 := by
        simpa only [sub_zero] using hratioDist.le
      rw [abs_of_nonneg htailNonneg] at habs
      exact habs
    calc
      (1 / 2 : ℝ) ^ j₀ * criticalScale M L ≤
          (1 / 2 : ℝ) ^ j₀ * b := by
        exact mul_le_mul_of_nonneg_left hscaleUpper (by positivity)
      _ = b * (1 / 2 : ℝ) ^ j₀ := by ring
      _ ≤ ε * a / 4 := htail
  have hmeanDiff :
      |globalStartMean M L -
        retainedStartMean M L j₀| ≤ ε * a / 4 := by
    rw [abs_globalMean_sub_retainedMean_eq_deepMass
      hcut]
    exact hmass
  calc
    |globalStartMean M L - criticalScale M L| =
        |(globalStartMean M L -
              retainedStartMean M L j₀) +
          (retainedStartMean M L j₀ -
            (1 - (1 / 2 : ℝ) ^ j₀) *
              criticalScale M L) -
          (1 / 2 : ℝ) ^ j₀ * criticalScale M L| := by
      congr 1
      ring
    _ ≤
        |globalStartMean M L -
            retainedStartMean M L j₀| +
          |retainedStartMean M L j₀ -
            (1 - (1 / 2 : ℝ) ^ j₀) *
              criticalScale M L| +
          |(1 / 2 : ℝ) ^ j₀ * criticalScale M L| := by
      calc
        |(globalStartMean M L -
              retainedStartMean M L j₀) +
            (retainedStartMean M L j₀ -
              (1 - (1 / 2 : ℝ) ^ j₀) *
                criticalScale M L) -
            (1 / 2 : ℝ) ^ j₀ * criticalScale M L| ≤
          |(globalStartMean M L -
              retainedStartMean M L j₀) +
            (retainedStartMean M L j₀ -
              (1 - (1 / 2 : ℝ) ^ j₀) *
                criticalScale M L)| +
            |(1 / 2 : ℝ) ^ j₀ * criticalScale M L| :=
          abs_sub _ _
        _ ≤ _ := by
          gcongr
          exact abs_add _ _
    _ ≤ ε * a / 4 + ε * a / 4 + ε * a / 4 := by
      gcongr
      rw [abs_of_nonneg
        (mul_nonneg (by positivity)
          (criticalScale_nonneg M L))]
      exact hratio
    _ ≤ ε * |criticalScale M L| := by
      rw [abs_of_nonneg (criticalScale_nonneg M L)]
      have : ε * a ≤ ε * criticalScale M L :=
        mul_le_mul_of_nonneg_left hscaleLower hε.le
      nlinarith

/-! ## The probability of no interior start -/

/--
Total-variation convergence gives the manuscript's zero-count formula
`P(Z_M=0) = exp(-Λ_M) + o_C(1)`.
-/
private theorem global_empty_probability_asymptotic_of_totalVariation
    {C : ℝ}
    (hTV :
      UniformLittleOOn
        (CriticalRunWindow.InRunLengthWindow C)
        (fun M L ↦
          natTotalVariation
            (globalStartLaw M L)
            (poissonPMFReal (globalStartRate M L)))
        (fun _ _ ↦ 1)) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun M L ↦
        globalEmptyProbability M L -
          Real.exp (-globalStartMean M L))
      (fun _ _ ↦ 1) := by
  intro ε hε
  obtain ⟨M₀, hM₀⟩ := hTV (ε / 2) (by positivity)
  refine ⟨M₀, ?_⟩
  intro M hM L hrun
  have htv :
      natTotalVariation
          (globalStartLaw M L)
          (poissonPMFReal (globalStartRate M L)) ≤
        ε / 2 := by
    have := hM₀ M hM L hrun
    rw [abs_of_nonneg
      (natTotalVariation_nonneg _ _)] at this
    simpa using this
  have hpoint :=
    abs_mass_zero_sub_le_two_mul_natTotalVariation
      (summable_globalStartLaw M L)
      ((poissonPMFRealSum (globalStartRate M L)).summable)
      (globalStartLaw_nonneg M L)
      (fun _ ↦ poissonPMFReal_nonneg)
  rw [poissonPMFReal_zero_eq_exp_neg] at hpoint
  have hpoint' :
      |globalStartLaw M L 0 -
          Real.exp (-globalStartMean M L)| ≤
        2 *
          natTotalVariation
            (globalStartLaw M L)
            (poissonPMFReal (globalStartRate M L)) := by
    simpa only [globalStartRate, NNReal.coe_mk] using hpoint
  simp only [globalEmptyProbability, abs_one, mul_one]
  exact hpoint'.trans (by linarith)

/-! ## Exact packaged statement and theorem -/

/--
The complete exact statement of Theorem 16.2 for the literal global count.
-/
def TheoremSixteenTwoStatement (C : ℝ) : Prop :=
  UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun M L ↦
        natTotalVariation
          (globalStartLaw M L)
          (poissonPMFReal (globalStartRate M L)))
      (fun _ _ ↦ 1) ∧
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun M L ↦ globalStartMean M L - criticalScale M L)
      criticalScale ∧
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun M L ↦
        globalEmptyProbability M L -
          Real.exp (-globalStartMean M L))
      (fun _ _ ↦ 1)

/--
Theorem 16.2, conditional exactly on the published inputs and the three deep
registered sector estimates still used by Proposition 16.1.  The first three
bounded-ratio sectors and the former aggregate fixed-ratio bridge have been
completely discharged.
-/
theorem theorem_sixteen_two
    {C : ℝ} (hC : 0 < C)
    (hpnt :
      PrimeNumberTheoremInput.PrimeNumberTheoremStatement)
    (hLS :
      LaishramShoreyInput.LaishramShoreyStatement)
    (hPell :
      PellInput.GeneralizedPellPolynomialBoxStatement)
    (hBS :
      BalasubramanianShoreyInput.BalasubramanianShoreyStatement)
    (hAGG :
      ArratiaGoldsteinGordonInput.ArratiaGoldsteinGordonStatement)
    (hES :
      EvertseSilvermanInput.EvertseSilvermanAbscissaStatement)
    (terminal :
      ℝ → ℕ → PropositionSixteenOne.TerminalPredicateFamily)
    (hmany :
      ∀ C' : ℝ, 0 < C' →
        ∀ κ₀ : ℕ, 2 ≤ κ₀ →
          PropositionSixteenOne.ManyDefectsSectorStabilityStatement
            C' κ₀ 3 (terminal C' κ₀))
    (hnonterminal :
      ∀ C' : ℝ, 0 < C' →
        ∀ κ₀ : ℕ, 2 ≤ κ₀ →
          PropositionSixteenOne.NonterminalSectorStabilityStatement
            C' κ₀ 3 (terminal C' κ₀))
    (hterminal :
      ∀ C' : ℝ, 0 < C' →
        ∀ κ₀ : ℕ, 2 ≤ κ₀ →
          PropositionSixteenOne.TerminalSectorStabilityStatement
            C' κ₀ 3 (terminal C' κ₀)) :
    TheoremSixteenTwoStatement C := by
  have htrunc : PropositionFifteenFiveStatement C :=
    PropositionFifteenFivePartition.proposition_fifteen_five
      hC.le hpnt hLS hPell hBS
  have hpropositionSixteenOne :
      ∀ C' : ℝ, 0 < C' →
        ∀ κ₀ : ℕ, 2 ≤ κ₀ →
          PropositionSixteenOneStatement C' κ₀ := by
    intro C' hC' κ₀ hκ₀
    exact
      PropositionSixteenOne.proposition_sixteen_one
        hC'.le hκ₀ (terminal C' κ₀)
        (hmany C' hC' κ₀ hκ₀)
        (hnonterminal C' hC' κ₀ hκ₀)
        (hterminal C' hC' κ₀ hκ₀)
        hES hPell
  have hbounded :
      BoundedRangePoissonConclusion C :=
    boundedRangePoissonConclusion hC.le hAGG
      hpropositionSixteenOne
  have hTV :=
    global_totalVariation_uniformLittleOOne_of_truncation
      htrunc hbounded
  exact ⟨hTV,
    global_mean_asymptotic_of_truncation
      hC.le htrunc hbounded,
    global_empty_probability_asymptotic_of_totalVariation hTV⟩

/--
Theorem 16.2 with the canonical intrinsic `T_K` family from Section 17.

The function `K` may depend on the fixed ratio bound `κ₀`, exactly as the
constant `Cterm(κ₀)` in Lemmas 17.23 and 17.28.  Unlike the more general
assembly theorem above, callers cannot substitute an unrelated terminal
predicate.
-/
theorem theorem_sixteen_two_canonical_of_sector_estimates
    {C : ℝ} (hC : 0 < C)
    (hpnt :
      PrimeNumberTheoremInput.PrimeNumberTheoremStatement)
    (hLS :
      LaishramShoreyInput.LaishramShoreyStatement)
    (hPell :
      PellInput.GeneralizedPellPolynomialBoxStatement)
    (hBS :
      BalasubramanianShoreyInput.BalasubramanianShoreyStatement)
    (hAGG :
      ArratiaGoldsteinGordonInput.ArratiaGoldsteinGordonStatement)
    (hES :
      EvertseSilvermanInput.EvertseSilvermanAbscissaStatement)
    (K : ℕ → ℝ)
    (hmany :
      ∀ C' : ℝ, 0 < C' →
        ∀ κ₀ : ℕ, 2 ≤ κ₀ →
          PropositionSixteenOne.ManyDefectsSectorStabilityStatement
            C' κ₀ 3
              (boundedIntrinsicTerminalPredicate 3 (K κ₀)))
    (hnonterminal :
      ∀ C' : ℝ, 0 < C' →
        ∀ κ₀ : ℕ, 2 ≤ κ₀ →
          PropositionSixteenOne.NonterminalSectorStabilityStatement
            C' κ₀ 3
              (boundedIntrinsicTerminalPredicate 3 (K κ₀)))
    (hterminal :
      ∀ C' : ℝ, 0 < C' →
        ∀ κ₀ : ℕ, 2 ≤ κ₀ →
          PropositionSixteenOne.TerminalSectorStabilityStatement
            C' κ₀ 3
              (boundedIntrinsicTerminalPredicate 3 (K κ₀))) :
    TheoremSixteenTwoStatement C :=
  theorem_sixteen_two hC hpnt hLS hPell hBS hAGG hES
    (fun _C' κ₀ =>
      boundedIntrinsicTerminalPredicate 3 (K κ₀))
    hmany hnonterminal hterminal

/--
Historical canonical wrapper with an explicit family of Lemma 17.26
many-defects estimates.

The terminal-sector argument is constructed uniformly for every bounded
ratio from generalized Pell; the source-exact Lemma 9.10 equivalence is
proved internally.  This wrapper is retained for callers that already
provide the many-defects estimates; the principal canonical theorem below
constructs them from Evertse--Silverman and Pell.
-/
theorem theorem_sixteen_two_canonical_of_manyDefectsEstimates
    {C : ℝ} (hC : 0 < C)
    (hpnt :
      PrimeNumberTheoremInput.PrimeNumberTheoremStatement)
    (hLS :
      LaishramShoreyInput.LaishramShoreyStatement)
    (hPell :
      PellInput.GeneralizedPellPolynomialBoxStatement)
    (hBS :
      BalasubramanianShoreyInput.BalasubramanianShoreyStatement)
    (hAGG :
      ArratiaGoldsteinGordonInput.ArratiaGoldsteinGordonStatement)
    (hES :
      EvertseSilvermanInput.EvertseSilvermanAbscissaStatement)
    (K : ℕ → ℝ)
    (hK :
      ∀ κ₀ : ℕ, 2 ≤ κ₀ → 0 ≤ K κ₀)
    (hmany :
      ∀ C' : ℝ, 0 < C' →
        ∀ κ₀ : ℕ, 2 ≤ κ₀ →
          PropositionSixteenOne.ManyDefectsSectorStabilityStatement
            C' κ₀ 3
              (boundedIntrinsicTerminalPredicate 3 (K κ₀)))
    (hnonterminal :
      ∀ C' : ℝ, 0 < C' →
        ∀ κ₀ : ℕ, 2 ≤ κ₀ →
          PropositionSixteenOne.NonterminalSectorStabilityStatement
            C' κ₀ 3
              (boundedIntrinsicTerminalPredicate 3 (K κ₀))) :
    TheoremSixteenTwoStatement C := by
  apply
    theorem_sixteen_two_canonical_of_sector_estimates
      hC hpnt hLS hPell hBS hAGG hES K hmany hnonterminal
  intro C' hC' κ₀ hκ₀
  exact
    BoundedRatioTerminalSummation.intrinsicTerminalSectorStability
      hC'.le κ₀ 3 (K κ₀) hκ₀ (by norm_num)
      (hK κ₀ hκ₀)

/--
Historical canonical wrapper with an explicit family of Lemma 17.28
nonterminal estimates.  Lemmas 17.26 and 17.30 are constructed internally.
It is retained for callers that already provide the sixth-sector estimate.
-/
theorem theorem_sixteen_two_canonical_of_nonterminalEstimates
    {C : ℝ} (hC : 0 < C)
    (hpnt :
      PrimeNumberTheoremInput.PrimeNumberTheoremStatement)
    (hLS :
      LaishramShoreyInput.LaishramShoreyStatement)
    (hPell :
      PellInput.GeneralizedPellPolynomialBoxStatement)
    (hBS :
      BalasubramanianShoreyInput.BalasubramanianShoreyStatement)
    (hAGG :
      ArratiaGoldsteinGordonInput.ArratiaGoldsteinGordonStatement)
    (hES :
      EvertseSilvermanInput.EvertseSilvermanAbscissaStatement)
    (K : ℕ → ℝ)
    (hK :
      ∀ κ₀ : ℕ, 2 ≤ κ₀ → 0 ≤ K κ₀)
    (hnonterminal :
      ∀ C' : ℝ, 0 < C' →
        ∀ κ₀ : ℕ, 2 ≤ κ₀ →
          PropositionSixteenOne.NonterminalSectorStabilityStatement
            C' κ₀ 3
              (boundedIntrinsicTerminalPredicate 3 (K κ₀))) :
    TheoremSixteenTwoStatement C := by
  exact
    theorem_sixteen_two_canonical_of_manyDefectsEstimates
      hC hpnt hLS hPell hBS hAGG hES K hK
      (fun C' hC' κ₀ _hκ₀ =>
        BoundedRatioManyDefectsAssembly.manyDefectsSectorStability
          hC'.le κ₀ 3
          (boundedIntrinsicTerminalPredicate 3 (K κ₀)))
      hnonterminal

/--
Theorem 16.2 with the canonical intrinsic terminal populations.

For every critical-window constant and fixed ratio bound, Proposition 16.1
now constructs all three deep-sector estimates internally.  In particular,
the nonterminal Lemma 17.28 chooses its own admissible threshold `K`; no
family of terminal predicates or Section 17 estimates remains in this
principal API.
-/
theorem theorem_sixteen_two_canonical_of_generalizedPell
    {C : ℝ} (hC : 0 < C)
    (hpnt :
      PrimeNumberTheoremInput.PrimeNumberTheoremStatement)
    (hLS :
      LaishramShoreyInput.LaishramShoreyStatement)
    (hPell :
      PellInput.GeneralizedPellPolynomialBoxStatement)
    (hBS :
      BalasubramanianShoreyInput.BalasubramanianShoreyStatement)
    (hAGG :
      ArratiaGoldsteinGordonInput.ArratiaGoldsteinGordonStatement)
    (hES :
      EvertseSilvermanInput.EvertseSilvermanAbscissaStatement) :
    TheoremSixteenTwoStatement C := by
  have htrunc : PropositionFifteenFiveStatement C :=
    PropositionFifteenFivePartition.proposition_fifteen_five
      hC.le hpnt hLS hPell hBS
  have hpropositionSixteenOne :
      ∀ C' : ℝ, 0 < C' →
        ∀ κ₀ : ℕ, 2 ≤ κ₀ →
          PropositionSixteenOneStatement C' κ₀ := by
    intro C' hC' κ₀ hκ₀
    exact
      PropositionSixteenOne.proposition_sixteen_one_canonical_of_generalizedPell
        hC'.le hκ₀ hES hPell
  have hbounded :
      BoundedRangePoissonConclusion C :=
    boundedRangePoissonConclusion hC.le hAGG
      hpropositionSixteenOne
  have hTV :=
    global_totalVariation_uniformLittleOOne_of_truncation
      htrunc hbounded
  exact
    ⟨hTV,
      global_mean_asymptotic_of_truncation
        hC.le htrunc hbounded,
      global_empty_probability_asymptotic_of_totalVariation hTV⟩

/--
Compatibility wrapper for the former specialized Nicolas--Robin Pell
envelope.
-/
theorem theorem_sixteen_two_canonical_of_pellEnvelope
    {C : ℝ} (hC : 0 < C)
    (hpnt :
      PrimeNumberTheoremInput.PrimeNumberTheoremStatement)
    (hLS :
      LaishramShoreyInput.LaishramShoreyStatement)
    (hConductor :
      PellInput.QuadraticOrderConductorFiberBoundStatement)
    (hDivisor :
      PellInput.NicolasRobinPellEnvelopeStatement)
    (hBS :
      BalasubramanianShoreyInput.BalasubramanianShoreyStatement)
    (hAGG :
      ArratiaGoldsteinGordonInput.ArratiaGoldsteinGordonStatement)
    (hES :
      EvertseSilvermanInput.EvertseSilvermanAbscissaStatement) :
    TheoremSixteenTwoStatement C :=
  theorem_sixteen_two_canonical_of_generalizedPell
    hC hpnt hLS
      (PellInput.generalizedPellPolynomialBox_of_quadraticOrder_nicolasRobin
        hConductor hDivisor)
      hBS hAGG hES

/--
Canonical Theorem 16.2 with no manuscript-internal generalized-Pell
antecedent.  The latter is reconstructed from the conductor comparison and
the source-shaped Nicolas--Robin logarithmic divisor inequality.
-/
theorem theorem_sixteen_two_canonical
    {C : ℝ} (hC : 0 < C)
    (hpnt :
      PrimeNumberTheoremInput.PrimeNumberTheoremStatement)
    (hLS :
      LaishramShoreyInput.LaishramShoreyStatement)
    (hConductor :
      PellInput.QuadraticOrderConductorFiberBoundStatement)
    (hDivisor :
      PellInput.NicolasRobinDivisorLogBoundStatement)
    (hBS :
      BalasubramanianShoreyInput.BalasubramanianShoreyStatement)
    (hAGG :
      ArratiaGoldsteinGordonInput.ArratiaGoldsteinGordonStatement)
    (hES :
      EvertseSilvermanInput.EvertseSilvermanAbscissaStatement) :
    TheoremSixteenTwoStatement C :=
  theorem_sixteen_two_canonical_of_generalizedPell
    hC hpnt hLS
      (PellInput.generalizedPellPolynomialBox_of_quadraticOrder_divisorLogBound
        hConductor hDivisor)
      hBS hAGG hES

end
end TheoremSixteenTwo
end PaperC
