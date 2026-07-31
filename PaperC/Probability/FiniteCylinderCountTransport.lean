import PaperC.Asymptotics.BoundedRatioSteinChen
import PaperC.Probability.SectionThirteenCouplings

set_option maxHeartbeats 1200000

/-!
# Transport and coupling for bounded-ratio start counts

This module contains two finite facts used in the assembly of Lemma 17.37.

* A count of start events supported below a cutoff `H` has exactly the same
  law on the uniform cylinders of cutoffs `H` and `G ≥ H`.
* On the local bounded-ratio cylinder, replacing all starts by the good
  starts costs at most the probability mass of the terminal bad starts.

Both statements are exact.  No asymptotic estimate and no bridge hypothesis
is used here.
-/

namespace PaperC
namespace FiniteCylinderCountTransport

open scoped BigOperators NNReal

open ArratiaGoldsteinGordonInput
open BadStartCount
open BadStartMass
open BoundedRatioSteinChen
open ConditionalAGGInstantiation
open ConditionalAGGAverage
open ConditionalDependencyGraph
open ConditionalStartProbability
open ProbabilityTheory
open PropositionSixteenOne
open SectionThirteenCouplings
open SectionThirteenFiniteBound

noncomputable section

local instance (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-! ## A generic finite-cylinder transport theorem -/

/--
Prime coordinates at most `H` inside a larger cutoff `G` are canonically
the prime coordinates of the cutoff-`H` cylinder.
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
Zero-extension of a small assignment evaluates `valueBit` exactly as the
corresponding assignment on the smaller cylinder.
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

/-- Coordinates strictly above `H` do not affect values below `H`. -/
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

/-- A supported start event depends only on the local cylinder factor. -/
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

/-- The large cylinder is the local cylinder times unused coordinates. -/
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

/-- Uniform one-start probabilities are invariant under cutoff enlargement. -/
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
    let eventEquiv :
        {ω : SampleSpace G // startAt ω x L} ≃
          {ω : SampleSpace H // startAt ω x L} ×
            LargeSample G H :=
      { toFun := fun ω ↦
          let pieces := sampleSpaceEquivLocalProd hHG ω.1
          (⟨pieces.1,
            (startAt_sampleSpaceEquivLocalProd_iff
              hHG hx hwindow ω.1).mp ω.2⟩,
            pieces.2)
        invFun := fun pieces ↦
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
        left_inv := by
          intro ω
          apply Subtype.ext
          exact (sampleSpaceEquivLocalProd hHG).symm_apply_apply ω.1
        right_inv := by
          intro pieces
          apply Prod.ext
          · apply Subtype.ext
            exact congrArg Prod.fst
              ((sampleSpaceEquivLocalProd hHG).apply_symm_apply
                (pieces.1.1, pieces.2))
          · change
              (sampleSpaceEquivLocalProd hHG
                ((sampleSpaceEquivLocalProd hHG).symm
                  (pieces.1.1, pieces.2))).2 = pieces.2
            exact congrArg Prod.snd
              ((sampleSpaceEquivLocalProd hHG).apply_symm_apply
                (pieces.1.1, pieces.2)) }
    rw [Fintype.card_congr eventEquiv]
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

/-- Number of starts from a fixed finite population on a prime cylinder. -/
noncomputable def startCountOn
    (s : Finset ℕ) (L H : ℕ)
    (ω : SampleSpace H) : ℕ :=
  ∑ x ∈ s, if startAt ω x L then 1 else 0

/--
Under the canonical product decomposition of a large cylinder, a count
whose windows are supported below `H` is its count on the local factor.
-/
theorem startCountOn_sampleSpaceEquivLocalProd
    {G H L : ℕ} (hHG : H ≤ G)
    (s : Finset ℕ)
    (hleft : ∀ x ∈ s, 2 ≤ x)
    (hright : ∀ x ∈ s, x + L ≤ H)
    (ω : SampleSpace G) :
    startCountOn s L G ω =
      startCountOn s L H
        (sampleSpaceEquivLocalProd hHG ω).1 := by
  classical
  unfold startCountOn
  apply Finset.sum_congr rfl
  intro x hx
  rw [startAt_sampleSpaceEquivLocalProd_iff
    hHG (hleft x hx) (hright x hx) ω]

/-- Event-level equivalence for a transported finite start count. -/
def startCountEventEquivLocalProd
    {G H L : ℕ} (hHG : H ≤ G)
    (s : Finset ℕ)
    (hleft : ∀ x ∈ s, 2 ≤ x)
    (hright : ∀ x ∈ s, x + L ≤ H)
    (k : ℕ) :
    {ω : SampleSpace G // startCountOn s L G ω = k} ≃
      {ω : SampleSpace H // startCountOn s L H ω = k} ×
        LargeSample G H where
  toFun ω :=
    let pieces :=
      sampleSpaceEquivLocalProd hHG ω.1
    (⟨pieces.1, by
      rw [← startCountOn_sampleSpaceEquivLocalProd
        hHG s hleft hright ω.1]
      exact ω.2⟩,
      pieces.2)
  invFun pieces :=
    let ω :=
      (sampleSpaceEquivLocalProd hHG).symm
        (pieces.1.1, pieces.2)
    ⟨ω, by
      rw [startCountOn_sampleSpaceEquivLocalProd
        hHG s hleft hright ω]
      have hfst :
          (sampleSpaceEquivLocalProd hHG ω).1 =
            pieces.1.1 :=
        congrArg Prod.fst
          ((sampleSpaceEquivLocalProd hHG).apply_symm_apply
            (pieces.1.1, pieces.2))
      rw [hfst]
      exact pieces.1.2⟩
  left_inv ω := by
    apply Subtype.ext
    exact
      (sampleSpaceEquivLocalProd hHG).symm_apply_apply
        ω.1
  right_inv pieces := by
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst
        ((sampleSpaceEquivLocalProd hHG).apply_symm_apply
          (pieces.1.1, pieces.2))
    · change
        (sampleSpaceEquivLocalProd hHG
          ((sampleSpaceEquivLocalProd hHG).symm
            (pieces.1.1, pieces.2))).2 = pieces.2
      exact congrArg Prod.snd
        ((sampleSpaceEquivLocalProd hHG).apply_symm_apply
          (pieces.1.1, pieces.2))

/--
The full pushforward law of a supported count is invariant under enlarging
the finite prime cylinder.
-/
theorem finiteNatLaw_startCountOn_cutoff_invariant
    {G H L : ℕ} (hHG : H ≤ G)
    (s : Finset ℕ)
    (hleft : ∀ x ∈ s, 2 ≤ x)
    (hright : ∀ x ∈ s, x + L ≤ H) :
    finiteNatLaw
        (fullUniformPMF G)
        (startCountOn s L G) =
      finiteNatLaw
        (fullUniformPMF H)
        (startCountOn s L H) := by
  funext k
  have hG :
      finiteNatLaw
          (fullUniformPMF G)
          (startCountOn s L G) k =
        eventProbability
          (fullUniformPMF G)
          (fun ω ↦ startCountOn s L G ω = k) := by
    unfold finiteNatLaw eventProbability
    apply Finset.sum_congr rfl
    intro ω _hω
    by_cases h : startCountOn s L G ω = k <;> simp [h]
  have hH :
      finiteNatLaw
          (fullUniformPMF H)
          (startCountOn s L H) k =
        eventProbability
          (fullUniformPMF H)
          (fun ω ↦ startCountOn s L H ω = k) := by
    unfold finiteNatLaw eventProbability
    apply Finset.sum_congr rfl
    intro ω _hω
    by_cases h : startCountOn s L H ω = k <;> simp [h]
  rw [hG, hH]
  rw [eventProbability_fullUniformPMF_eq,
    eventProbability_fullUniformPMF_eq]
  norm_cast
  classical
  unfold finiteUniformProbability
  simp only [Nat.card_eq_fintype_card]
  have hEventCard :
      Fintype.card
          {ω : SampleSpace G // startCountOn s L G ω = k} =
        Fintype.card
            {ω : SampleSpace H // startCountOn s L H ω = k} *
          Fintype.card (LargeSample G H) := by
    rw [Fintype.card_congr
      (startCountEventEquivLocalProd
        hHG s hleft hright k)]
    exact Fintype.card_prod _ _
  have hSampleCard :
      Fintype.card (SampleSpace G) =
        Fintype.card (SampleSpace H) *
          Fintype.card (LargeSample G H) := by
    rw [Fintype.card_congr
      (sampleSpaceEquivLocalProd hHG)]
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

/-! ## Exact bounded-ratio good/full coupling -/

/-- Good-start count on the complete local bounded-ratio cylinder. -/
noncomputable def boundedFullGoodStartCount
    (N M L Y : ℕ)
    (ω : SampleSpace (boundedRatioCutoff M L)) : ℕ :=
  ∑ x ∈ boundedGoodStarts N M L Y,
    if startAt ω x L then 1 else 0

/-- Complete start count on the same local cylinder. -/
noncomputable def boundedFullStartCount
    (N M L : ℕ)
    (ω : SampleSpace (boundedRatioCutoff M L)) : ℕ :=
  startCountOn (boundedRatioBlock N M) L
    (boundedRatioCutoff M L) ω

/-- Law of the local good-start count. -/
noncomputable def boundedFullGoodStartLaw
    (N M L Y : ℕ) : ℕ → ℝ :=
  finiteNatLaw
    (fullUniformPMF (boundedRatioCutoff M L))
    (boundedFullGoodStartCount N M L Y)

/-- Law of the complete local bounded-ratio count. -/
noncomputable def boundedFullStartLaw
    (N M L : ℕ) : ℕ → ℝ :=
  finiteNatLaw
    (fullUniformPMF (boundedRatioCutoff M L))
    (boundedFullStartCount N M L)

/-- Probability mass of terminal bad starts on the local full cylinder. -/
noncomputable def boundedStartProbability
    (M L x : ℕ) : ℝ :=
  eventProbability
    (fullUniformPMF (boundedRatioCutoff M L))
    (fun ω ↦ startAt ω x L)

/-- Probability mass of terminal bad starts on the local full cylinder. -/
noncomputable def boundedBadStartProbabilityMass
    (N M L Y : ℕ) : ℝ :=
  ∑ x ∈ boundedTerminalBadStarts N M L Y,
    boundedStartProbability M L x

/--
The local bounded-ratio probability of one supported start is the usual
exact rational one-start probability, evaluated on any adequate dyadic
cylinder and cast to `ℝ`.
-/
theorem boundedStartProbability_eq_selfStartProbability
    {N M L x : ℕ} (hN : 2 ≤ N)
    (hx : x ∈ boundedRatioBlock N M) :
    boundedStartProbability M L x =
      ((startProbability x L x : ℚ) : ℝ) := by
  have hxTwo : 2 ≤ x :=
    hN.trans (mem_boundedRatioBlock.mp hx).1
  have hlocal :
      x + L ≤ boundedRatioCutoff M L :=
    startWindow_le_boundedRatioCutoff hx le_rfl
  have hdyadic :
      x + L ≤ dyadicCutoff x L := by
    unfold dyadicCutoff
    omega
  unfold boundedStartProbability
  rw [eventProbability_fullUniformPMF_eq,
    finiteUniformProbability_eq_uniformEventProbability]
  norm_cast
  unfold startProbability
  calc
    uniformEventProbability
        (M := boundedRatioCutoff M L)
        (fun ω ↦ startAt ω x L) =
      uniformEventProbability
        (M := x + L)
        (fun ω ↦ startAt ω x L) :=
      uniformEventProbability_startAt_cutoff_invariant
        hlocal hxTwo le_rfl
    _ =
      uniformEventProbability
        (M := dyadicCutoff x L)
        (fun ω ↦ startAt ω x L) :=
      (uniformEventProbability_startAt_cutoff_invariant
        hdyadic hxTwo le_rfl).symm

/-- Bounded-ratio bad-start sets are monotone in the prime cutoff. -/
theorem boundedTerminalBadStarts_mono
    {N M L B Y : ℕ} (hBY : B ≤ Y) :
    boundedTerminalBadStarts N M L B ⊆
      boundedTerminalBadStarts N M L Y := by
  intro x hx
  obtain ⟨hxBlock, j, hj, hkernel⟩ :=
    mem_boundedTerminalBadStarts.mp hx
  exact mem_boundedTerminalBadStarts.mpr
    ⟨hxBlock, j, hj,
      largeOddKernel_eq_one_mono hBY hkernel⟩

/-- Weighted base-cutoff defect mass on `[N,M)`. -/
noncomputable def boundedTerminalDefectWeightMass
    (N M L B : ℕ) : ℝ :=
  ∑ x ∈ boundedRatioBlock N M,
    (((2 : ℕ) ^
      (startDefectIndicesAt B x L).card - 1 : ℕ) : ℝ)

/-- Exact first moment of all starts on the local bounded-ratio cylinder. -/
noncomputable def boundedFullStartMean
    (N M L : ℕ) : ℝ :=
  ∑ x ∈ boundedRatioBlock N M,
    boundedStartProbability M L x

/-- Pointwise weighted defect bound on a bounded-ratio bad start. -/
theorem boundedStartProbability_le_two_mul_defectWeight_div
    {N M L B x : ℕ}
    (hN : 2 ≤ N) (hL : 0 < L) (hLB : L + 1 ≤ B)
    (hx : x ∈ boundedRatioBlock N M)
    (hbad : x ∈ boundedTerminalBadStarts N M L B) :
    boundedStartProbability M L x ≤
      (2 : ℝ) *
          (((2 : ℕ) ^
            (startDefectIndicesAt B x L).card - 1 : ℕ) : ℝ) /
        (2 : ℝ) ^ L := by
  have hxTwo : 2 ≤ x :=
    hN.trans (mem_boundedRatioBlock.mp hx).1
  have hxDyadic : x ∈ dyadicBlock x := by
    simp only [dyadicBlock, Finset.mem_Ico]
    omega
  have hbadSelf : x ∈ terminalBadStarts x L B := by
    obtain ⟨_hxBlock, j, hj, hkernel⟩ :=
      mem_boundedTerminalBadStarts.mp hbad
    exact mem_terminalBadStarts.mpr
      ⟨hxDyadic, j, hj, hkernel⟩
  have hq :=
    BadStartMass.startProbability_le_two_mul_defectWeight_div
      hxTwo hxDyadic hL hLB hbadSelf
  have hcast := (Rat.cast_le (K := ℝ)).mpr hq
  push_cast at hcast
  rw [boundedStartProbability_eq_selfStartProbability hN hx]
  simpa using hcast

/-- Outside the base bad set, the bounded-ratio marginal is exactly `2⁻ᴸ`. -/
theorem boundedStartProbability_eq_baseline_of_not_bad
    {N M L B x : ℕ}
    (hN : 2 ≤ N) (hL : 0 < L) (hLB : L + 1 ≤ B)
    (hx : x ∈ boundedRatioBlock N M)
    (hgood : x ∉ boundedTerminalBadStarts N M L B) :
    boundedStartProbability M L x =
      (1 : ℝ) / (2 : ℝ) ^ L := by
  have hxTwo : 2 ≤ x :=
    hN.trans (mem_boundedRatioBlock.mp hx).1
  have hxDyadic : x ∈ dyadicBlock x := by
    simp only [dyadicBlock, Finset.mem_Ico]
    omega
  have hgoodSelf : x ∉ terminalBadStarts x L B := by
    intro hbadSelf
    obtain ⟨_hxDyadic, j, hj, hkernel⟩ :=
      mem_terminalBadStarts.mp hbadSelf
    exact hgood
      (mem_boundedTerminalBadStarts.mpr
        ⟨hx, j, hj, hkernel⟩)
  have hq :=
    BadStartMass.startProbability_eq_baseline_of_not_bad
      hxTwo hxDyadic hL hLB hgoodSelf
  rw [boundedStartProbability_eq_selfStartProbability hN hx]
  have hcast :=
    congrArg (fun q : ℚ ↦ (q : ℝ)) hq
  push_cast at hcast
  simpa using hcast

/--
The complete bounded-ratio mean is the deterministic good-start parameter
plus the exact probability mass of the bad starts.
-/
theorem boundedFullStartMean_eq_goodParameter_add_badMass
    {N M L Y : ℕ}
    (hN : 2 ≤ N) (hL : 0 < L) (hLY : L + 1 ≤ Y) :
    boundedFullStartMean N M L =
      ((boundedGoodStarts N M L Y).card : ℝ) /
          (2 : ℝ) ^ L +
        boundedBadStartProbabilityMass N M L Y := by
  let block := boundedRatioBlock N M
  let bad := boundedTerminalBadStarts N M L Y
  have hsubset : bad ⊆ block := by
    intro x hx
    exact (mem_boundedTerminalBadStarts.mp hx).1
  have hgood :
      (∑ x ∈ block \ bad, boundedStartProbability M L x) =
        ((block \ bad).card : ℝ) / (2 : ℝ) ^ L := by
    calc
      (∑ x ∈ block \ bad, boundedStartProbability M L x) =
          ∑ _x ∈ block \ bad, (1 : ℝ) / (2 : ℝ) ^ L := by
        apply Finset.sum_congr rfl
        intro x hx
        have hx' := Finset.mem_sdiff.mp hx
        exact boundedStartProbability_eq_baseline_of_not_bad
          hN hL hLY hx'.1 hx'.2
      _ = ((block \ bad).card : ℝ) / (2 : ℝ) ^ L := by
        rw [Finset.sum_const, nsmul_eq_mul]
        push_cast
        ring
  unfold boundedFullStartMean boundedBadStartProbabilityMass
  change
    (∑ x ∈ block, boundedStartProbability M L x) =
      ((boundedGoodStarts N M L Y).card : ℝ) /
          (2 : ℝ) ^ L +
        ∑ x ∈ bad, boundedStartProbability M L x
  rw [← Finset.sum_sdiff hsubset]
  rw [hgood]
  rfl

/--
Exact two-cutoff bound on the bounded-ratio bad-start probability mass:

`mass(D_Y) ≤ 2 M_{B,[N,M)} / 2^L + #D_Y / 2^L`.

Thus the probabilistic part of Lemma 17.34 reduces to the two explicit
arithmetic estimates for the weighted base-defect mass and the terminal
bad-start cardinal.
-/
theorem boundedBadStartProbabilityMass_le_two_cutoffs
    {N M L B Y : ℕ}
    (hN : 2 ≤ N) (hL : 0 < L)
    (hLB : L + 1 ≤ B) (hBY : B ≤ Y) :
    boundedBadStartProbabilityMass N M L Y ≤
      2 * boundedTerminalDefectWeightMass N M L B /
          (2 : ℝ) ^ L +
        ((boundedTerminalBadStarts N M L Y).card : ℝ) /
          (2 : ℝ) ^ L := by
  let DB := boundedTerminalBadStarts N M L B
  let DY := boundedTerminalBadStarts N M L Y
  let w : ℕ → ℝ := fun x ↦
    (((2 : ℕ) ^ (startDefectIndicesAt B x L).card - 1 : ℕ) : ℝ)
  have hsubset : DB ⊆ DY :=
    boundedTerminalBadStarts_mono hBY
  have hsplit :
      boundedBadStartProbabilityMass N M L Y =
        (∑ x ∈ DB, boundedStartProbability M L x) +
          ∑ x ∈ DY \ DB, boundedStartProbability M L x := by
    unfold boundedBadStartProbabilityMass
    change
      (∑ x ∈ DY, boundedStartProbability M L x) =
        (∑ x ∈ DB, boundedStartProbability M L x) +
          ∑ x ∈ DY \ DB, boundedStartProbability M L x
    rw [← Finset.sum_sdiff hsubset]
    ac_rfl
  have hDBBlock : DB ⊆ boundedRatioBlock N M := by
    intro x hx
    exact (mem_boundedTerminalBadStarts.mp hx).1
  have hbase :
      (∑ x ∈ DB, boundedStartProbability M L x) ≤
        2 * boundedTerminalDefectWeightMass N M L B /
          (2 : ℝ) ^ L := by
    have hsumSubset :
        (∑ x ∈ DB, w x) ≤
          ∑ x ∈ boundedRatioBlock N M, w x := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hDBBlock
      intro x _hx _hnot
      dsimp only [w]
      positivity
    calc
      (∑ x ∈ DB, boundedStartProbability M L x) ≤
          ∑ x ∈ DB,
            (2 : ℝ) * w x / (2 : ℝ) ^ L := by
        apply Finset.sum_le_sum
        intro x hx
        exact boundedStartProbability_le_two_mul_defectWeight_div
          hN hL hLB (hDBBlock hx) hx
      _ =
          (2 / (2 : ℝ) ^ L) * (∑ x ∈ DB, w x) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _hx
        ring
      _ ≤
          (2 / (2 : ℝ) ^ L) *
            (∑ x ∈ boundedRatioBlock N M, w x) :=
        mul_le_mul_of_nonneg_left hsumSubset (by positivity)
      _ =
          2 * boundedTerminalDefectWeightMass N M L B /
            (2 : ℝ) ^ L := by
        simp only [boundedTerminalDefectWeightMass, w]
        ring
  have hremaining :
      (∑ x ∈ DY \ DB, boundedStartProbability M L x) =
        ((DY \ DB).card : ℝ) / (2 : ℝ) ^ L := by
    calc
      (∑ x ∈ DY \ DB, boundedStartProbability M L x) =
          ∑ _x ∈ DY \ DB, (1 : ℝ) / (2 : ℝ) ^ L := by
        apply Finset.sum_congr rfl
        intro x hx
        have hxDY : x ∈ DY := (Finset.mem_sdiff.mp hx).1
        have hxDB : x ∉ DB := (Finset.mem_sdiff.mp hx).2
        exact boundedStartProbability_eq_baseline_of_not_bad
          hN hL hLB
          (mem_boundedTerminalBadStarts.mp hxDY).1 hxDB
      _ = ((DY \ DB).card : ℝ) / (2 : ℝ) ^ L := by
        rw [Finset.sum_const, nsmul_eq_mul]
        push_cast
        ring
  have hcard :
      ((DY \ DB).card : ℝ) / (2 : ℝ) ^ L ≤
        (DY.card : ℝ) / (2 : ℝ) ^ L := by
    apply div_le_div_of_nonneg_right
    · exact_mod_cast
        Finset.card_le_card (Finset.sdiff_subset : DY \ DB ⊆ DY)
    · positivity
  rw [hsplit, hremaining]
  exact add_le_add hbase hcard

/--
If the good and complete local counts differ, an occurring terminal bad
start witnesses the disagreement.
-/
theorem exists_bad_start_of_boundedGood_ne_full
    {N M L Y : ℕ}
    {ω : SampleSpace (boundedRatioCutoff M L)}
    (hne :
      boundedFullGoodStartCount N M L Y ω ≠
        boundedFullStartCount N M L ω) :
    ∃ x ∈ boundedTerminalBadStarts N M L Y,
      startAt ω x L := by
  classical
  by_contra h
  push_neg at h
  apply hne
  unfold boundedFullGoodStartCount boundedFullStartCount startCountOn
  apply Finset.sum_subset Finset.sdiff_subset
  intro x hxBlock hxNotGood
  have hxBad : x ∈ boundedTerminalBadStarts N M L Y := by
    by_contra hxNotBad
    exact hxNotGood
      (Finset.mem_sdiff.mpr ⟨hxBlock, hxNotBad⟩)
  rw [if_neg (h x hxBad)]

/-- Disagreement probability is bounded by the bad-start union bound. -/
theorem disagreementProbability_boundedGood_full_le_badMass
    (N M L Y : ℕ) :
    disagreementProbability
        (fullUniformPMF (boundedRatioCutoff M L))
        (boundedFullGoodStartCount N M L Y)
        (boundedFullStartCount N M L) ≤
      boundedBadStartProbabilityMass N M L Y := by
  classical
  have hpoint :
      ∀ ω : SampleSpace (boundedRatioCutoff M L),
        (if boundedFullGoodStartCount N M L Y ω ≠
              boundedFullStartCount N M L ω then
            (fullUniformPMF (boundedRatioCutoff M L)).prob ω
          else 0) ≤
          ∑ x ∈ boundedTerminalBadStarts N M L Y,
            if startAt ω x L then
              (fullUniformPMF
                (boundedRatioCutoff M L)).prob ω
            else 0 := by
    intro ω
    by_cases hne :
        boundedFullGoodStartCount N M L Y ω ≠
          boundedFullStartCount N M L ω
    · rw [if_pos hne]
      obtain ⟨x, hxBad, hxStart⟩ :=
        exists_bad_start_of_boundedGood_ne_full hne
      calc
        (fullUniformPMF
            (boundedRatioCutoff M L)).prob ω =
            (if startAt ω x L then
              (fullUniformPMF
                (boundedRatioCutoff M L)).prob ω
            else 0) := by rw [if_pos hxStart]
        _ ≤
            ∑ y ∈ boundedTerminalBadStarts N M L Y,
              if startAt ω y L then
                (fullUniformPMF
                  (boundedRatioCutoff M L)).prob ω
              else 0 := by
          apply Finset.single_le_sum
            (s := boundedTerminalBadStarts N M L Y)
            (f := fun y ↦
              if startAt ω y L then
                (fullUniformPMF
                  (boundedRatioCutoff M L)).prob ω
              else 0)
          · intro y _hy
            split_ifs
            · exact
                (fullUniformPMF
                  (boundedRatioCutoff M L)).nonneg ω
            · exact le_rfl
          · exact hxBad
    · rw [if_neg hne]
      exact Finset.sum_nonneg fun x _hx ↦ by
        split_ifs
        · exact
            (fullUniformPMF
              (boundedRatioCutoff M L)).nonneg ω
        · exact le_rfl
  unfold disagreementProbability boundedBadStartProbabilityMass
  calc
    (∑ ω,
      if boundedFullGoodStartCount N M L Y ω ≠
          boundedFullStartCount N M L ω then
        (fullUniformPMF (boundedRatioCutoff M L)).prob ω
      else 0) ≤
        ∑ ω,
          ∑ x ∈ boundedTerminalBadStarts N M L Y,
            if startAt ω x L then
              (fullUniformPMF
                (boundedRatioCutoff M L)).prob ω
            else 0 :=
      Finset.sum_le_sum fun ω _hω ↦ hpoint ω
    _ =
        ∑ x ∈ boundedTerminalBadStarts N M L Y,
          eventProbability
            (fullUniformPMF (boundedRatioCutoff M L))
            (fun ω ↦ startAt ω x L) := by
      rw [Finset.sum_comm]
      rfl

/-- Total variation form of the exact bounded-ratio coupling. -/
theorem natTotalVariation_boundedGood_full_le_badMass
    (N M L Y : ℕ) :
    natTotalVariation
        (boundedFullGoodStartLaw N M L Y)
        (boundedFullStartLaw N M L) ≤
      boundedBadStartProbabilityMass N M L Y := by
  unfold boundedFullGoodStartLaw boundedFullStartLaw
  exact
    (natTotalVariation_finiteNatLaw_le_disagreement
      (fullUniformPMF (boundedRatioCutoff M L))
      (boundedFullGoodStartCount N M L Y)
      (boundedFullStartCount N M L)).trans
        (disagreementProbability_boundedGood_full_le_badMass
          N M L Y)

end

end FiniteCylinderCountTransport
end PaperC
