import PaperC.Asymptotics.TheoremSixteenTwoRecentered
import PaperC.Asymptotics.TheoremSixteenTwoInfiniteModel
import PaperC.Asymptotics.MaskedFirstMomentCritical
import PaperC.Probability.ExactLengthDecomposition

/-!
# The finite-prefix constant-stretch law

This module isolates the finite-prefix observable used in `cor:prefix-law`.
The boundary at `x = 1` is counted separately; every later constant stretch
has a unique left-maximal start and is therefore detected by `StartEvent`.
-/

namespace PaperC
namespace CorollaryPrefixLaw

open scoped BigOperators ENNReal NNReal
open MeasureTheory Set

open ArratiaGoldsteinGordonInput
open ConditionalAGGAverage
open InfiniteCylinderTransfer
open InfiniteExactLengthProbabilityTransfer
open InfiniteRademacher
open SectionThirteenCouplings
open SectionThirteenFiniteBound
open TheoremSixteenTwo

noncomputable section

local instance (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- A constant stretch of length `L`, contained in the finite prefix
`{1, ..., M}` and beginning at `x`. -/
def PrefixConstantStretch
    (g : ℕ → F₂) (M x L : ℕ) : Prop :=
  1 ≤ x ∧ x + L ≤ M + 1 ∧
    ∀ j : ℕ, j < L → g (x + j) = g x

/-- The finite prefix contains a constant stretch of length `L`. -/
def prefixHasConstantStretch
    (g : ℕ → F₂) (M L : ℕ) : Prop :=
  ∃ x : ℕ, PrefixConstantStretch g M x L

/-- The admissible lengths of constant stretches in the first `M` values. -/
def prefixConstantStretchLengths
    (g : ℕ → F₂) (M : ℕ) : Finset ℕ :=
  (Finset.range (M + 1)).filter (prefixHasConstantStretch g M)

theorem prefixConstantStretchLengths_nonempty
    (g : ℕ → F₂) (M : ℕ) :
    (prefixConstantStretchLengths g M).Nonempty := by
  refine ⟨0, ?_⟩
  simp only [prefixConstantStretchLengths, Finset.mem_filter,
    Finset.mem_range, Nat.zero_lt_succ, true_and]
  exact ⟨1, by simp [PrefixConstantStretch]⟩

/-- Length of the longest constant stretch in the finite prefix. -/
def prefixLongestConstantStretch
    (g : ℕ → F₂) (M : ℕ) : ℕ :=
  (prefixConstantStretchLengths g M).max'
    (prefixConstantStretchLengths_nonempty g M)

theorem prefixConstantStretch_length_le
    {g : ℕ → F₂} {M x L : ℕ}
    (h : PrefixConstantStretch g M x L) :
    L ≤ M := by
  unfold PrefixConstantStretch at h
  omega

theorem prefixHasConstantStretch_mono
    {g : ℕ → F₂} {M q L : ℕ}
    (hq : prefixHasConstantStretch g M q) (hLq : L ≤ q) :
    prefixHasConstantStretch g M L := by
  obtain ⟨x, hx, hxq, hconst⟩ := hq
  refine ⟨x, hx, ?_, ?_⟩
  · omega
  · intro j hj
    exact hconst j (hj.trans_le hLq)

/-- The longest-stretch event is the negation of the existence of a stretch
at the tested length. -/
theorem prefixLongestConstantStretch_lt_iff
    {g : ℕ → F₂} {M L : ℕ} :
    prefixLongestConstantStretch g M < L ↔
      ¬ prefixHasConstantStretch g M L := by
  rw [prefixLongestConstantStretch, Finset.max'_lt_iff]
  constructor
  · intro hall hL
    have hLM : L ≤ M := by
      obtain ⟨x, hx⟩ := hL
      exact prefixConstantStretch_length_le hx
    have hmem : L ∈ prefixConstantStretchLengths g M := by
      simp only [prefixConstantStretchLengths, Finset.mem_filter,
        Finset.mem_range]
      exact ⟨Nat.lt_succ_of_le hLM, hL⟩
    exact (Nat.lt_irrefl L) (hall L hmem)
  · intro hnone q hq
    simp only [prefixConstantStretchLengths, Finset.mem_filter,
      Finset.mem_range] at hq
    by_contra hnlt
    have hLq : L ≤ q := Nat.le_of_not_gt hnlt
    exact hnone (prefixHasConstantStretch_mono hq.2 hLq)

/-- The special left-boundary indicator in `W_{M,L}`. -/
def prefixBoundaryEvent (g : ℕ → F₂) (L : ℕ) : Prop :=
  ∀ j : ℕ, j < L → g (1 + j) = g 1

/-- Interior starts fully contained in the prefix. -/
def prefixInteriorStartIndices (M L : ℕ) : Finset ℕ :=
  Finset.Ico 2 (M - L + 2)

/--
The prefix count
`W_{M,L} = 1_{f(1)=...=f(L)} + ∑_{2≤x≤M-L+1} J_{x,L}`.
-/
def prefixStartCount (g : ℕ → F₂) (M L : ℕ) : ℕ :=
  (if prefixBoundaryEvent g L then 1 else 0) +
    ∑ x ∈ prefixInteriorStartIndices M L,
      if StartEvent g x L then 1 else 0

private def leftCandidates
    (g : ℕ → F₂) (M L x : ℕ) : Finset ℕ :=
  (Finset.Icc 1 x).filter (fun y ↦ PrefixConstantStretch g M y L)

private theorem leftCandidates_nonempty
    {g : ℕ → F₂} {M L x : ℕ}
    (hx : PrefixConstantStretch g M x L) :
    (leftCandidates g M L x).Nonempty := by
  refine ⟨x, ?_⟩
  simp only [leftCandidates, Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨hx.1, le_rfl⟩, hx⟩

/-- Every constant stretch in the prefix either starts at the left boundary,
or has a left-maximal representative detected by `StartEvent`. -/
theorem prefixHasConstantStretch_iff_boundary_or_start
    {g : ℕ → F₂} {M L : ℕ} (hLM : L ≤ M) :
    prefixHasConstantStretch g M L ↔
      prefixBoundaryEvent g L ∨
        ∃ x ∈ prefixInteriorStartIndices M L, StartEvent g x L := by
  constructor
  · rintro ⟨x, hx⟩
    let s := leftCandidates g M L x
    have hs : s.Nonempty := leftCandidates_nonempty hx
    let y := s.min' hs
    have hyMem : y ∈ s := Finset.min'_mem s hs
    have hyData :
        1 ≤ y ∧ y ≤ x ∧ PrefixConstantStretch g M y L := by
      have hraw :
          (1 ≤ y ∧ y ≤ x) ∧ PrefixConstantStretch g M y L := by
        simpa only [s, leftCandidates, Finset.mem_filter,
          Finset.mem_Icc] using hyMem
      exact ⟨hraw.1.1, hraw.1.2, hraw.2⟩
    have hyPrefix : PrefixConstantStretch g M y L := hyData.2.2
    rcases eq_or_lt_of_le hyData.1 with hyEq | hygt
    · left
      intro j hj
      simpa only [hyEq] using hyPrefix.2.2 j hj
    · right
      have hleftNe : g (y - 1) ≠ g y := by
        intro heq
        have hshift : PrefixConstantStretch g M (y - 1) L := by
          refine ⟨by omega, ?_, ?_⟩
          · have hyBound := hyPrefix.2.1
            omega
          intro j hj
          by_cases hj0 : j = 0
          · subst j
            simp
          · have horiginal := hyPrefix.2.2 (j - 1) (by omega)
            have hindex : y - 1 + j = y + (j - 1) := by omega
            rw [hindex, horiginal]
            exact heq.symm
        have hshiftMem : y - 1 ∈ s := by
          simp only [s, leftCandidates, Finset.mem_filter,
            Finset.mem_Icc]
          exact ⟨⟨by omega, by omega⟩, hshift⟩
        have hmin := Finset.min'_le s (y - 1) hshiftMem
        omega
      refine ⟨y, ?_, ?_⟩
      · simp only [prefixInteriorStartIndices, Finset.mem_Ico]
        constructor
        · omega
        · have hyBound := hyPrefix.2.1
          omega
      · refine ⟨(ExactLengthDecomposition.add_eq_one_iff_ne _ _).2 hleftNe, ?_⟩
        exact hyPrefix.2.2
  · rintro (hboundary | ⟨x, hxmem, hxstart⟩)
    · exact ⟨1, by
        refine ⟨by omega, by omega, ?_⟩
        exact hboundary⟩
    · have hxBounds : 2 ≤ x ∧ x < M - L + 2 := by
        simpa only [prefixInteriorStartIndices, Finset.mem_Ico] using hxmem
      refine ⟨x, ?_⟩
      refine ⟨by omega, by omega, ?_⟩
      exact hxstart.2

private theorem sum_indicator_eq_zero_iff
    (s : Finset ℕ) (P : ℕ → Prop) [DecidablePred P] :
    (∑ x ∈ s, if P x then 1 else 0) = 0 ↔
      ∀ x ∈ s, ¬ P x := by
  classical
  simp only [Finset.sum_eq_zero_iff,
    ite_eq_right_iff, one_ne_zero, imp_false]

/-- Exact event identity required by the prefix-law proof. -/
theorem prefixStartCount_eq_zero_iff_longest_lt
    {g : ℕ → F₂} {M L : ℕ} (hLM : L ≤ M) :
    prefixStartCount g M L = 0 ↔
      prefixLongestConstantStretch g M < L := by
  rw [prefixLongestConstantStretch_lt_iff,
    prefixHasConstantStretch_iff_boundary_or_start hLM]
  unfold prefixStartCount
  rw [Nat.add_eq_zero_iff, sum_indicator_eq_zero_iff]
  by_cases hb : prefixBoundaryEvent g L
  · simp [hb]
  · simp [hb]

/-- `W_{M,L}` as a random variable on the infinite product law. -/
def infinitePrefixStartCount (M L : ℕ) (ω : InfiniteSample) : ℕ :=
  prefixStartCount (infiniteValueBit ω) M L

/-- `R_M`, the longest constant stretch of the first `M` values, on the
infinite product law. -/
def infinitePrefixLongestConstantStretch
    (M : ℕ) (ω : InfiniteSample) : ℕ :=
  prefixLongestConstantStretch (infiniteValueBit ω) M

/-- Infinite-model specialization of the exact void/longest-stretch event. -/
theorem infinitePrefixStartCount_eq_zero_iff_longest_lt
    {M L : ℕ} (hLM : L ≤ M) (ω : InfiniteSample) :
    infinitePrefixStartCount M L ω = 0 ↔
      infinitePrefixLongestConstantStretch M ω < L :=
  prefixStartCount_eq_zero_iff_longest_lt hLM

/-! ## Exact finite-cylinder representation of the prefix count -/

/-- The prefix count evaluated on the same common cylinder as the global
count of Theorem 16.2. -/
def finitePrefixStartCount
    (M L : ℕ) (σ : SampleSpace (globalCylinderCutoff M L)) : ℕ :=
  prefixStartCount (valueBit σ) M L

/-- Restriction to the common cylinder preserves the prefix observable. -/
theorem finitePrefixStartCount_restrictToFinite_eq_infinitePrefixStartCount
    (M L : ℕ) (ω : InfiniteSample) :
    finitePrefixStartCount M L
        (restrictToFinite (globalCylinderCutoff M L) ω) =
      infinitePrefixStartCount M L ω := by
  classical
  have hboundary :
      prefixBoundaryEvent
          (valueBit (restrictToFinite (globalCylinderCutoff M L) ω)) L ↔
        prefixBoundaryEvent (infiniteValueBit ω) L := by
    unfold prefixBoundaryEvent
    constructor <;> intro h j hj
    · simpa only [
          valueBit_restrictToFinite_eq_infiniteValueBit ω
            (show 1 + j ≤ globalCylinderCutoff M L by
              unfold globalCylinderCutoff dyadicCutoff
              omega),
          valueBit_restrictToFinite_eq_infiniteValueBit ω
            (show 1 ≤ globalCylinderCutoff M L by
              unfold globalCylinderCutoff dyadicCutoff
              omega)] using h j hj
    · simpa only [
          valueBit_restrictToFinite_eq_infiniteValueBit ω
            (show 1 + j ≤ globalCylinderCutoff M L by
              unfold globalCylinderCutoff dyadicCutoff
              omega),
          valueBit_restrictToFinite_eq_infiniteValueBit ω
            (show 1 ≤ globalCylinderCutoff M L by
              unfold globalCylinderCutoff dyadicCutoff
              omega)] using h j hj
  unfold finitePrefixStartCount infinitePrefixStartCount prefixStartCount
  have hindicator :
      (if prefixBoundaryEvent
            (valueBit (restrictToFinite (globalCylinderCutoff M L) ω)) L
        then 1 else 0) =
      (if prefixBoundaryEvent (infiniteValueBit ω) L then 1 else 0) :=
    if_congr hboundary rfl rfl
  rw [hindicator]
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  have hxBounds : 2 ≤ x ∧ x < M - L + 2 := by
    simpa only [prefixInteriorStartIndices, Finset.mem_Ico] using hx
  have hcut : x + L ≤ globalCylinderCutoff M L := by
    unfold globalCylinderCutoff dyadicCutoff
    omega
  have hiff :=
    startAt_restrictToFinite_iff
      (M := globalCylinderCutoff M L) (x := x) (L := L) ω hcut
  by_cases hstart : StartEvent (infiniteValueBit ω) x L
  · have hfinite :
        StartEvent
          (valueBit (restrictToFinite (globalCylinderCutoff M L) ω)) x L := by
      change startAt
        (restrictToFinite (globalCylinderCutoff M L) ω) x L
      exact hiff.mpr hstart
    simp [hstart, hfinite]
  · have hfinite :
        ¬ StartEvent
          (valueBit (restrictToFinite (globalCylinderCutoff M L) ω)) x L :=
      fun h ↦ hstart (hiff.mp h)
    simp [hstart, hfinite]

/-- One atom of the finite prefix-count law. -/
def finitePrefixStartCountEvent (M L k : ℕ) :
    Set (SampleSpace (globalCylinderCutoff M L)) :=
  {σ | finitePrefixStartCount M L σ = k}

/-- One atom of the infinite prefix-count law. -/
def infinitePrefixStartCountEvent (M L k : ℕ) : Set InfiniteSample :=
  {ω | infinitePrefixStartCount M L ω = k}

theorem infinitePrefixStartCountEvent_eq_preimage (M L k : ℕ) :
    infinitePrefixStartCountEvent M L k =
      restrictToFinite (globalCylinderCutoff M L) ⁻¹'
        finitePrefixStartCountEvent M L k := by
  ext ω
  change
    infinitePrefixStartCount M L ω = k ↔
      finitePrefixStartCount M L
        (restrictToFinite (globalCylinderCutoff M L) ω) = k
  exact iff_of_eq
    (congrArg (fun count ↦ count = k)
      (finitePrefixStartCount_restrictToFinite_eq_infinitePrefixStartCount
        M L ω)).symm

theorem measurableSet_finitePrefixStartCountEvent (M L k : ℕ) :
    MeasurableSet (finitePrefixStartCountEvent M L k) :=
  Set.toFinite (finitePrefixStartCountEvent M L k) |>.measurableSet

theorem measurableSet_infinitePrefixStartCountEvent (M L k : ℕ) :
    MeasurableSet (infinitePrefixStartCountEvent M L k) := by
  rw [infinitePrefixStartCountEvent_eq_preimage]
  exact
    (measurable_restrictToFinite (globalCylinderCutoff M L))
      (measurableSet_finitePrefixStartCountEvent M L k)

/-- Finite-cylinder mass function of `W_{M,L}`. -/
def prefixStartLaw (M L : ℕ) : ℕ → ℝ :=
  finiteNatLaw (globalUniformPMF M L) (finitePrefixStartCount M L)

/-- Mass function of `W_{M,L}` on the infinite product law. -/
def infinitePrefixStartLaw (M L k : ℕ) : ℝ :=
  (infiniteRademacherMeasure
    (infinitePrefixStartCountEvent M L k)).toReal

/-- The infinite and common-cylinder versions of `W_{M,L}` have exactly the
same law. -/
theorem infinitePrefixStartCount_law_eq_prefixStartLaw (M L : ℕ) :
    infinitePrefixStartLaw M L = prefixStartLaw M L := by
  funext k
  classical
  unfold infinitePrefixStartLaw
  rw [infinitePrefixStartCountEvent_eq_preimage,
    ← Measure.map_apply
      (measurable_restrictToFinite (globalCylinderCutoff M L))
      (measurableSet_finitePrefixStartCountEvent M L k),
    map_infiniteRademacherMeasure_restrictToFinite]
  simp only [finitePrefixStartCountEvent]
  rw [finiteRademacherMeasure_event_eq_uniformEventProbability,
    ENNReal.toReal_ofReal]
  · rw [← finiteUniformProbability_eq_uniformEventProbability,
      ← eventProbability_fullUniformPMF_eq]
    unfold prefixStartLaw globalUniformPMF finiteNatLaw eventProbability
    apply Finset.sum_congr rfl
    intro σ _hσ
    by_cases hcount : finitePrefixStartCount M L σ = k <;>
      simp [hcount]
  · apply Rat.cast_nonneg.mpr
    unfold uniformEventProbability
    positivity

/-! ## Coupling to the global interior count -/

/-- Starts in the global count whose length-`L` stretch crosses the right
edge of the prefix. -/
def prefixOverflowStartIndices (M L : ℕ) : Finset ℕ :=
  Finset.Ico (M - L + 2) M

theorem globalStartIndices_eq_prefixInterior_union_overflow
    {M L : ℕ} (hLtwo : 2 ≤ L) (hLM : L ≤ M) :
    globalStartIndices M =
      prefixInteriorStartIndices M L ∪ prefixOverflowStartIndices M L := by
  ext x
  simp only [globalStartIndices, prefixInteriorStartIndices,
    prefixOverflowStartIndices, Finset.mem_Ico, Finset.mem_union]
  omega

theorem prefixInterior_overflow_disjoint (M L : ℕ) :
    Disjoint (prefixInteriorStartIndices M L)
      (prefixOverflowStartIndices M L) := by
  rw [Finset.disjoint_left]
  intro x hxInterior hxOverflow
  have hi := Finset.mem_Ico.mp
    (by simpa only [prefixInteriorStartIndices] using hxInterior)
  have ho := Finset.mem_Ico.mp
    (by simpa only [prefixOverflowStartIndices] using hxOverflow)
  omega

/-- If the two counts disagree, either the left-boundary indicator occurs or
one of the starts crossing the right edge occurs. -/
theorem boundary_or_exists_overflow_start_of_counts_ne
    {M L : ℕ} (hLtwo : 2 ≤ L) (hLM : L ≤ M)
    {σ : SampleSpace (globalCylinderCutoff M L)}
    (hne : finitePrefixStartCount M L σ ≠ globalStartCount M L σ) :
    prefixBoundaryEvent (valueBit σ) L ∨
      ∃ x ∈ prefixOverflowStartIndices M L, startAt σ x L := by
  by_contra hnone
  push Not at hnone
  apply hne
  unfold finitePrefixStartCount prefixStartCount globalStartCount
  rw [if_neg hnone.1,
    globalStartIndices_eq_prefixInterior_union_overflow hLtwo hLM,
    Finset.sum_union (prefixInterior_overflow_disjoint M L)]
  have hoverflowZero :
      (∑ x ∈ prefixOverflowStartIndices M L,
        if startAt σ x L then 1 else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    simp only [if_neg (hnone.2 x hx)]
  rw [hoverflowZero, add_zero, zero_add]
  rfl

/-- Probability of the special left-boundary indicator on the common
cylinder. -/
def prefixBoundaryProbability (M L : ℕ) : ℝ :=
  eventProbability (globalUniformPMF M L)
    (fun σ ↦ prefixBoundaryEvent (valueBit σ) L)

/-- First-moment mass of starts crossing the right edge of the prefix. -/
def prefixOverflowStartMass (M L : ℕ) : ℝ :=
  ∑ x ∈ prefixOverflowStartIndices M L,
    commonCylinderStartProbability M L x

/-- The exact finite coupling bound for the prefix and global counts. -/
theorem disagreementProbability_prefix_global_le
    {M L : ℕ} (hLtwo : 2 ≤ L) (hLM : L ≤ M) :
    disagreementProbability
        (globalUniformPMF M L)
        (finitePrefixStartCount M L)
        (globalStartCount M L) ≤
      prefixBoundaryProbability M L + prefixOverflowStartMass M L := by
  classical
  have hpoint :
      ∀ σ : SampleSpace (globalCylinderCutoff M L),
        (if finitePrefixStartCount M L σ ≠ globalStartCount M L σ then
            (globalUniformPMF M L).prob σ else 0) ≤
          (if prefixBoundaryEvent (valueBit σ) L then
              (globalUniformPMF M L).prob σ else 0) +
            ∑ x ∈ prefixOverflowStartIndices M L,
              if startAt σ x L then
                (globalUniformPMF M L).prob σ else 0 := by
    intro σ
    by_cases hne :
        finitePrefixStartCount M L σ ≠ globalStartCount M L σ
    · rw [if_pos hne]
      rcases boundary_or_exists_overflow_start_of_counts_ne
          hLtwo hLM hne with hboundary | ⟨x, hx, hstart⟩
      · rw [if_pos hboundary]
        exact le_add_of_nonneg_right
          (Finset.sum_nonneg fun y _hy ↦ by
            split_ifs
            · exact (globalUniformPMF M L).nonneg σ
            · exact le_rfl)
      · calc
          (globalUniformPMF M L).prob σ =
              (if startAt σ x L then
                (globalUniformPMF M L).prob σ else 0) := by
            rw [if_pos hstart]
          _ ≤
              ∑ y ∈ prefixOverflowStartIndices M L,
                if startAt σ y L then
                  (globalUniformPMF M L).prob σ else 0 := by
            apply Finset.single_le_sum
                (s := prefixOverflowStartIndices M L)
                (f := fun y ↦ if startAt σ y L then
                  (globalUniformPMF M L).prob σ else 0)
            · intro y _hy
              split_ifs
              · exact (globalUniformPMF M L).nonneg σ
              · exact le_rfl
            · exact hx
          _ ≤
              (if prefixBoundaryEvent (valueBit σ) L then
                  (globalUniformPMF M L).prob σ else 0) +
                ∑ y ∈ prefixOverflowStartIndices M L,
                  if startAt σ y L then
                    (globalUniformPMF M L).prob σ else 0 := by
            apply le_add_of_nonneg_left
            split_ifs
            · exact (globalUniformPMF M L).nonneg σ
            · exact le_rfl
    · rw [if_neg hne]
      exact add_nonneg
        (by split_ifs
            · exact (globalUniformPMF M L).nonneg σ
            · exact le_rfl)
        (Finset.sum_nonneg fun x _hx ↦ by
          split_ifs
          · exact (globalUniformPMF M L).nonneg σ
          · exact le_rfl)
  unfold disagreementProbability prefixBoundaryProbability
    prefixOverflowStartMass commonCylinderStartProbability eventProbability
  calc
    (∑ σ,
        if finitePrefixStartCount M L σ ≠ globalStartCount M L σ then
          (globalUniformPMF M L).prob σ else 0) ≤
      ∑ σ,
        ((if prefixBoundaryEvent (valueBit σ) L then
            (globalUniformPMF M L).prob σ else 0) +
          ∑ x ∈ prefixOverflowStartIndices M L,
            if startAt σ x L then
              (globalUniformPMF M L).prob σ else 0) :=
        Finset.sum_le_sum fun σ _ ↦ hpoint σ
    _ =
      (∑ σ, if prefixBoundaryEvent (valueBit σ) L then
          (globalUniformPMF M L).prob σ else 0) +
        ∑ x ∈ prefixOverflowStartIndices M L, ∑ σ,
          if startAt σ x L then
            (globalUniformPMF M L).prob σ else 0 := by
      rw [Finset.sum_add_distrib, Finset.sum_comm]

/-- Total variation is bounded by the two explicit boundary errors. -/
theorem natTotalVariation_prefix_global_le
    {M L : ℕ} (hLtwo : 2 ≤ L) (hLM : L ≤ M) :
    natTotalVariation (prefixStartLaw M L) (globalStartLaw M L) ≤
      prefixBoundaryProbability M L + prefixOverflowStartMass M L := by
  exact
    (natTotalVariation_finiteNatLaw_le_disagreement
      (globalUniformPMF M L)
      (finitePrefixStartCount M L)
      (globalStartCount M L)).trans
        (disagreementProbability_prefix_global_le hLtwo hLM)

/-! ## Evaluation of the two boundary errors -/

/-- Left endpoint of the overflow mask. -/
def prefixOverflowBase (M L : ℕ) : ℕ :=
  M - L + 2

theorem prefixOverflowStartIndices_eq (M L : ℕ) :
    prefixOverflowStartIndices M L =
      Finset.Ico (prefixOverflowBase M L) M :=
  rfl

theorem prefixOverflowStartIndices_subset_dyadicBlock
    {M L : ℕ} (hMtwo : M ≤ 2 * prefixOverflowBase M L) :
    prefixOverflowStartIndices M L ⊆
      dyadicBlock (prefixOverflowBase M L) := by
  intro x hx
  have hx' := Finset.mem_Ico.mp
    (by simpa only [prefixOverflowStartIndices, prefixOverflowBase] using hx)
  simp only [dyadicBlock, Finset.mem_Ico]
  exact ⟨hx'.1, hx'.2.trans_le hMtwo⟩

theorem prefixOverflowStartIndices_card_le (M L : ℕ) :
    (prefixOverflowStartIndices M L).card ≤ L := by
  simp only [prefixOverflowStartIndices, Nat.card_Ico]
  omega

/-- Cutoff invariance identifies the overflow mass with the masked first
moment on the block whose left endpoint is `M-L+2`. -/
theorem prefixOverflowStartMass_eq_maskedDyadicExpectation
    {M L : ℕ} (hMtwo : M ≤ 2 * prefixOverflowBase M L) :
    prefixOverflowStartMass M L =
      ((MaskedFirstMoment.maskedDyadicExpectation
        (prefixOverflowBase M L) L
        (prefixOverflowStartIndices M L) : ℚ) : ℝ) := by
  classical
  unfold prefixOverflowStartMass
    MaskedFirstMoment.maskedDyadicExpectation
  push_cast
  apply Finset.sum_congr rfl
  intro x hx
  have hxOverflow :
      prefixOverflowBase M L ≤ x ∧ x < M := by
    simpa only [prefixOverflowStartIndices, prefixOverflowBase,
      Finset.mem_Ico] using hx
  have hxGlobal : x ∈ globalStartIndices M := by
    simp only [globalStartIndices, Finset.mem_Ico]
    constructor
    · have hbase : 2 ≤ prefixOverflowBase M L := by
        unfold prefixOverflowBase
        omega
      exact hbase.trans hxOverflow.1
    · exact hxOverflow.2
  rw [commonCylinderStartProbability_eq_globalStartProbability hxGlobal]
  unfold PropositionFifteenFive.globalStartProbability
  have hxMask : x ∈ dyadicBlock (prefixOverflowBase M L) :=
    prefixOverflowStartIndices_subset_dyadicBlock hMtwo hx
  have hxSelf : x ∈ dyadicBlock x := by
    simp only [dyadicBlock, Finset.mem_Ico]
    have hxTwo : 2 ≤ x :=
      (Finset.mem_Ico.mp
        (by simpa only [globalStartIndices] using hxGlobal)).1
    omega
  exact
    (InfiniteStartProbabilityTransfer.infiniteStartProbability_eq_startProbability
      hxSelf).symm.trans
      (InfiniteStartProbabilityTransfer.infiniteStartProbability_eq_startProbability
        hxMask)

/-- Source event corresponding to the special prefix boundary. -/
def infinitePrefixBoundaryEvent (L : ℕ) : Set InfiniteSample :=
  {ω | prefixBoundaryEvent (infiniteValueBit ω) L}

theorem infinitePrefixBoundaryEvent_eq_preimage (M L : ℕ) :
    infinitePrefixBoundaryEvent L =
      restrictToFinite (globalCylinderCutoff M L) ⁻¹'
        {σ | prefixBoundaryEvent (valueBit σ) L} := by
  ext ω
  change
    prefixBoundaryEvent (infiniteValueBit ω) L ↔
      prefixBoundaryEvent
        (valueBit (restrictToFinite (globalCylinderCutoff M L) ω)) L
  unfold prefixBoundaryEvent
  constructor <;> intro h j hj
  · simpa only [
        valueBit_restrictToFinite_eq_infiniteValueBit ω
          (show 1 + j ≤ globalCylinderCutoff M L by
            unfold globalCylinderCutoff dyadicCutoff
            omega),
        valueBit_restrictToFinite_eq_infiniteValueBit ω
          (show 1 ≤ globalCylinderCutoff M L by
            unfold globalCylinderCutoff dyadicCutoff
            omega)] using h j hj
  · simpa only [
        valueBit_restrictToFinite_eq_infiniteValueBit ω
          (show 1 + j ≤ globalCylinderCutoff M L by
            unfold globalCylinderCutoff dyadicCutoff
            omega),
        valueBit_restrictToFinite_eq_infiniteValueBit ω
          (show 1 ≤ globalCylinderCutoff M L by
            unfold globalCylinderCutoff dyadicCutoff
            omega)] using h j hj

theorem measurableSet_infinitePrefixBoundaryEvent (L : ℕ) :
    MeasurableSet (infinitePrefixBoundaryEvent L) := by
  rw [infinitePrefixBoundaryEvent_eq_preimage (M := L)]
  exact
    (measurable_restrictToFinite (globalCylinderCutoff L L))
      (Set.toFinite
        ({σ : SampleSpace (globalCylinderCutoff L L) |
          prefixBoundaryEvent (valueBit σ) L}) |>.measurableSet)

/-- Exact transfer of the left-boundary probability to the source law. -/
theorem prefixBoundaryProbability_eq_measure (M L : ℕ) :
    prefixBoundaryProbability M L =
      (infiniteRademacherMeasure
        (infinitePrefixBoundaryEvent L)).toReal := by
  classical
  rw [infinitePrefixBoundaryEvent_eq_preimage M L,
    ← Measure.map_apply
      (measurable_restrictToFinite (globalCylinderCutoff M L))
      (Set.toFinite
        ({σ : SampleSpace (globalCylinderCutoff M L) |
          prefixBoundaryEvent (valueBit σ) L}) |>.measurableSet),
    map_infiniteRademacherMeasure_restrictToFinite]
  rw [finiteRademacherMeasure_event_eq_uniformEventProbability,
    ENNReal.toReal_ofReal]
  · rw [← finiteUniformProbability_eq_uniformEventProbability,
      ← eventProbability_fullUniformPMF_eq]
    rfl
  · apply Rat.cast_nonneg.mpr
    unfold uniformEventProbability
    positivity

/-- Fixing a constant prefix forces every prime coordinate represented below
that prefix to be zero.  The finite `K`-coordinate form is sufficient for
the uniform vanishing argument. -/
theorem infinitePrefixBoundaryEvent_subset_zeroPrefix
    {L K : ℕ} (hK : 0 < K)
    (hprime : Nat.nth Nat.Prime (K - 1) ≤ L) :
    infinitePrefixBoundaryEvent L ⊆ zeroPrefix 0 K := by
  intro ω hω
  rw [zeroPrefix, Set.mem_pi]
  intro k hk
  have hkBounds := Finset.mem_Ico.mp hk
  simp only [Set.mem_singleton_iff]
  have hkLast : k ≤ K - 1 := by omega
  have hpMono :
      Nat.nth Nat.Prime k ≤ Nat.nth Nat.Prime (K - 1) :=
    Nat.nth_monotone Nat.infinite_setOf_prime hkLast
  have hpL : Nat.nth Nat.Prime k ≤ L := hpMono.trans hprime
  have hpTwo : 2 ≤ Nat.nth Nat.Prime k := by
    exact (Nat.add_two_le_nth_prime k).trans' (by omega)
  have hj : Nat.nth Nat.Prime k - 1 < L := by omega
  change prefixBoundaryEvent (infiniteValueBit ω) L at hω
  have hvalue := hω (Nat.nth Nat.Prime k - 1) hj
  have hindex :
      1 + (Nat.nth Nat.Prime k - 1) = Nat.nth Nat.Prime k := by
    omega
  rw [hindex, infiniteValueBit_nth_prime] at hvalue
  have hone : infiniteValueBit ω 1 = 0 := by
    unfold infiniteValueBit
    rw [parityVec_one]
    simp
  exact hvalue.trans hone

/-- Explicit geometric upper bound for the special left-boundary event. -/
theorem prefixBoundaryProbability_le_geometric
    {M L K : ℕ} (hK : 0 < K)
    (hprime : Nat.nth Nat.Prime (K - 1) ≤ L) :
    prefixBoundaryProbability M L ≤ (1 / 2 : ℝ) ^ K := by
  rw [prefixBoundaryProbability_eq_measure]
  have hmeasure :
      infiniteRademacherMeasure (infinitePrefixBoundaryEvent L) ≤
        infiniteRademacherMeasure (zeroPrefix 0 K) :=
    measure_mono
      (infinitePrefixBoundaryEvent_subset_zeroPrefix hK hprime)
  have hnotTop :
      infiniteRademacherMeasure (zeroPrefix 0 K) ≠ ∞ := by
    rw [measure_zeroPrefix]
    simp
  have hreal := ENNReal.toReal_mono hnotTop hmeasure
  rw [measure_zeroPrefix] at hreal
  norm_num at hreal
  exact hreal

/-- Replacing `M` by `M-L+2` enlarges the fixed critical window by at most
one whenever the two scales differ by at most a factor two. -/
theorem prefixOverflowBase_in_runLengthWindow
    {C : ℝ} {M L : ℕ}
    (hrun : CriticalRunWindow.InRunLengthWindow C M L)
    (hLtwo : 2 ≤ L) (hLM : L ≤ M)
    (hMtwo : M ≤ 2 * prefixOverflowBase M L) :
    CriticalRunWindow.InRunLengthWindow (C + 1)
      (prefixOverflowBase M L) L := by
  let N := prefixOverflowBase M L
  have hNtwo : 2 ≤ N := by
    dsimp only [N, prefixOverflowBase]
    omega
  have hNM : N ≤ M := by
    dsimp only [N, prefixOverflowBase]
    omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hlogTwo : (0 : ℝ) < Real.log 2 :=
    Real.log_pos (by norm_num)
  have hlogNM : Real.log N ≤ Real.log M :=
    Real.log_le_log hNpos (by exact_mod_cast hNM)
  have hMtwoReal : (M : ℝ) ≤ 2 * (N : ℝ) := by
    exact_mod_cast hMtwo
  have hlogMtwoN : Real.log M ≤ Real.log (2 * N) :=
    Real.log_le_log hMpos hMtwoReal
  have hlogUpper : Real.log M ≤ Real.log 2 + Real.log N := by
    calc
      Real.log M ≤ Real.log (2 * N) := hlogMtwoN
      _ = Real.log 2 + Real.log N := by
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
          (ne_of_gt hNpos)]
  have hdeltaNonneg :
      0 ≤ Real.log M / Real.log 2 - Real.log N / Real.log 2 := by
    apply sub_nonneg.mpr
    exact div_le_div_of_nonneg_right hlogNM hlogTwo.le
  have hdeltaOne :
      Real.log M / Real.log 2 - Real.log N / Real.log 2 ≤ 1 := by
    apply (sub_le_iff_le_add).2
    apply (div_le_iff₀ hlogTwo).2
    have := hlogUpper
    field_simp
    linarith
  unfold CriticalRunWindow.InRunLengthWindow at hrun ⊢
  have hdecomp :
      (L : ℝ) - Real.log N / Real.log 2 =
        ((L : ℝ) - Real.log M / Real.log 2) +
          (Real.log M / Real.log 2 - Real.log N / Real.log 2) := by
    ring
  rw [hdecomp]
  calc
    |(L : ℝ) - Real.log M / Real.log 2 +
        (Real.log M / Real.log 2 - Real.log N / Real.log 2)| ≤
      |(L : ℝ) - Real.log M / Real.log 2| +
        |Real.log M / Real.log 2 - Real.log N / Real.log 2| :=
          abs_add_le _ _
    _ = |(L : ℝ) - Real.log M / Real.log 2| +
        (Real.log M / Real.log 2 - Real.log N / Real.log 2) := by
      rw [abs_of_nonneg hdeltaNonneg]
    _ ≤ C + 1 := add_le_add hrun hdeltaOne

/-- Probability of the longest-stretch event, read from the prefix law. -/
def prefixLongestStretchBelowProbability (M L : ℕ) : ℝ :=
  prefixStartLaw M L 0

/-- Exact identification of the atom at zero with `P(R_M < L)`. -/
theorem prefixLongestStretchBelowProbability_eq_measure
    {M L : ℕ} (hLM : L ≤ M) :
    prefixLongestStretchBelowProbability M L =
      (infiniteRademacherMeasure
        {ω | infinitePrefixLongestConstantStretch M ω < L}).toReal := by
  rw [prefixLongestStretchBelowProbability,
    ← congrFun (infinitePrefixStartCount_law_eq_prefixStartLaw M L) 0]
  unfold infinitePrefixStartLaw infinitePrefixStartCountEvent
  congr 2
  ext ω
  exact infinitePrefixStartCount_eq_zero_iff_longest_lt hLM ω

end

end CorollaryPrefixLaw
end PaperC
