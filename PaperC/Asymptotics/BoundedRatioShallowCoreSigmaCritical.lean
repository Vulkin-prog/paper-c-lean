import PaperC.Asymptotics.PropositionSixteenOneCore

set_option maxHeartbeats 1800000

/-!
# The shallow-core systematic exponent on bounded-ratio blocks

For fixed `κ₀`, every interval `[N,M)` with `M ≤ κ₀N` embeds in the single
finite block `[N,κ₀N)`.  This module takes the maximum of the canonical
systematic exponent over the deliberately broad population on that block
defined only by

* absence of a small canonical height; and
* residual core density at most `3/16`.

The third sector of Proposition 16.1 is contained in this population,
independently of the endpoint `M` and of the terminal predicate.  The
height-packing argument from `ShallowCoreSigmaCritical` then applies
pointwise without any dyadic-shell assumption.  Consequently the common
maximum is `o(L+1)`, and its fourth power is `N^{o(1)}` in every fixed
critical run-length window.
-/

namespace PaperC
namespace BoundedRatioShallowCoreSigmaCritical

open Affine.CanonicalRationalCode
open PropositionSixteenOne
open RationalMassFinite
open SectionElevenPartition
open ShallowCorePairs
open SmallHeightLargeProductPairs

noncomputable section

/-! ## A common finite population for every endpoint -/

/--
The broad shallow-core population in the complete bounding block
`[N,κ₀N)`.  The large-prime-product test is intentionally omitted: every
actual third-sector pair satisfies the two displayed predicates, and this
larger set gives an endpoint-independent envelope.
-/
noncomputable def boundedRatioShallowCorePairs
    (κ₀ A N L : ℕ) :
    Finset (SeparatedBoundedRatioPair N (κ₀ * N) L) := by
  classical
  exact Finset.univ.filter fun pair ↦
    ¬ HasSmallCanonicalHeight
        A L pair.1.1 pair.1.2 ∧
      HasCoreDensityAtMostThreeSixteenths
        A L pair.1.1 pair.1.2

@[simp]
theorem mem_boundedRatioShallowCorePairs
    {κ₀ A N L : ℕ}
    {pair : SeparatedBoundedRatioPair N (κ₀ * N) L} :
    pair ∈ boundedRatioShallowCorePairs κ₀ A N L ↔
      ¬ HasSmallCanonicalHeight
          A L pair.1.1 pair.1.2 ∧
        HasCoreDensityAtMostThreeSixteenths
          A L pair.1.1 pair.1.2 := by
  classical
  simp [boundedRatioShallowCorePairs]

/--
Embed a separated pair from `[N,M)` into the complete bounding block
`[N,κ₀N)`.
-/
def embedInBoundingBlock
    {κ₀ N M L : ℕ}
    (hMκ : M ≤ κ₀ * N)
    (pair : SeparatedBoundedRatioPair N M L) :
    SeparatedBoundedRatioPair N (κ₀ * N) L := by
  refine ⟨pair.1, ?_⟩
  have hp := mem_separatedBoundedRatioPairs.mp pair.2
  apply mem_separatedBoundedRatioPairs.mpr
  refine ⟨?_, ?_, hp.2.2⟩
  · have hx := mem_boundedRatioBlock.mp hp.1
    exact mem_boundedRatioBlock.mpr
      ⟨hx.1, hx.2.trans_le hMκ⟩
  · have hy := mem_boundedRatioBlock.mp hp.2.1
    exact mem_boundedRatioBlock.mpr
      ⟨hy.1, hy.2.trans_le hMκ⟩

@[simp]
theorem embedInBoundingBlock_val
    {κ₀ N M L : ℕ}
    (hMκ : M ≤ κ₀ * N)
    (pair : SeparatedBoundedRatioPair N M L) :
    (embedInBoundingBlock hMκ pair).1 = pair.1 :=
  rfl

/--
Every pair classified in the third bounded-ratio sector belongs, after the
canonical endpoint embedding, to the common broad population.
-/
theorem embedInBoundingBlock_mem_of_mem_shallowCoreSector
    {κ₀ N M A L : ℕ} {hN : 2 ≤ N}
    {terminal : TerminalPredicateFamily}
    {pair : SeparatedBoundedRatioPair N M L}
    (hMκ : M ≤ κ₀ * N)
    (hpair :
      pair ∈ boundedRatioSectorPairs
        N M A L hN terminal .shallowCore) :
    embedInBoundingBlock hMκ pair ∈
      boundedRatioShallowCorePairs κ₀ A N L := by
  have hsector :=
    mem_boundedRatioSectorPairs.mp hpair
  unfold boundedRatioSectorOf at hsector
  rw [sectorOf_eq_shallowCore_iff] at hsector
  apply mem_boundedRatioShallowCorePairs.mpr
  change
    ¬ HasSmallCanonicalHeight
        A L pair.1.1 pair.1.2 ∧
      HasCoreDensityAtMostThreeSixteenths
        A L pair.1.1 pair.1.2
  simpa only [boundedRatioSectorTests] using
    (show
      ¬(boundedRatioSectorTests
          N M A L hN terminal).smallCanonicalHeight pair ∧
        (boundedRatioSectorTests
          N M A L hN terminal).shallowCore pair from
      ⟨hsector.2.1, hsector.2.2⟩)

/-! ## The endpoint-independent systematic maximum -/

/--
Largest canonical systematic exponent on the broad population in
`[N,κ₀N)`.
-/
noncomputable def maxBoundedRatioShallowCoreSigma
    (κ₀ A N L : ℕ) : ℕ :=
  (boundedRatioShallowCorePairs κ₀ A N L).sup fun pair ↦
    canonicalPairSigma A L pair.1.1 pair.1.2

/-- Every member of the common population is bounded by its finite maximum. -/
theorem canonicalPairSigma_le_max_of_mem
    {κ₀ A N L : ℕ}
    {pair : SeparatedBoundedRatioPair N (κ₀ * N) L}
    (hpair :
      pair ∈ boundedRatioShallowCorePairs κ₀ A N L) :
    canonicalPairSigma A L pair.1.1 pair.1.2 ≤
      maxBoundedRatioShallowCoreSigma κ₀ A N L := by
  unfold maxBoundedRatioShallowCoreSigma
  exact Finset.le_sup
    (f := fun pair ↦
      canonicalPairSigma A L pair.1.1 pair.1.2)
    hpair

/--
The common maximum dominates every actual shallow-core sector pair for
every endpoint `M ≤ κ₀N`.
-/
theorem canonicalPairSigma_le_max_of_mem_shallowCoreSector
    {κ₀ N M A L : ℕ} {hN : 2 ≤ N}
    {terminal : TerminalPredicateFamily}
    {pair : SeparatedBoundedRatioPair N M L}
    (hMκ : M ≤ κ₀ * N)
    (hpair :
      pair ∈ boundedRatioSectorPairs
        N M A L hN terminal .shallowCore) :
    canonicalPairSigma A L pair.1.1 pair.1.2 ≤
      maxBoundedRatioShallowCoreSigma κ₀ A N L := by
  have hembed :=
    canonicalPairSigma_le_max_of_mem
      (embedInBoundingBlock_mem_of_mem_shallowCoreSector
        hMκ hpair)
  simpa only [embedInBoundingBlock_val] using hembed

/--
A pointwise real bound passes to the finite systematic-exponent maximum,
including when the population is empty.
-/
theorem maxBoundedRatioShallowCoreSigma_cast_le
    {κ₀ A N L : ℕ} {R : ℝ}
    (hR : 0 ≤ R)
    (hpoint :
      ∀ pair ∈ boundedRatioShallowCorePairs κ₀ A N L,
        (canonicalPairSigma A L pair.1.1 pair.1.2 : ℝ) ≤ R) :
    (maxBoundedRatioShallowCoreSigma κ₀ A N L : ℝ) ≤ R := by
  classical
  have aux :
      ∀ s : Finset
          (SeparatedBoundedRatioPair N (κ₀ * N) L),
        (∀ pair ∈ s,
          (canonicalPairSigma
              A L pair.1.1 pair.1.2 : ℝ) ≤ R) →
        ((s.sup fun pair ↦
            canonicalPairSigma
              A L pair.1.1 pair.1.2 : ℕ) : ℝ) ≤ R := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro _h
        simpa using hR
    | @insert pair s hpairNotMem ih =>
        intro hs
        rw [Finset.sup_insert, Nat.cast_max]
        apply max_le
        · exact hs pair (Finset.mem_insert_self pair s)
        · apply ih
          intro other hother
          exact hs other (Finset.mem_insert_of_mem hother)
  exact aux (boundedRatioShallowCorePairs κ₀ A N L) hpoint

/-! ## The height-packing estimate -/

/--
A power-of-four lower bound for a natural threshold puts that threshold
below the logarithmic square root.
-/
private theorem cast_le_sqrt_log_of_four_pow_sq_le
    {T B : ℕ}
    (hpower : 4 ^ (T ^ 2) ≤ B) :
    (T : ℝ) ≤ Real.sqrt (Real.log (B : ℝ)) := by
  have hpowerReal :
      (((4 ^ (T ^ 2) : ℕ) : ℝ)) ≤ (B : ℝ) := by
    exact_mod_cast hpower
  have hlogPower :
      Real.log (((4 ^ (T ^ 2) : ℕ) : ℝ)) ≤
        Real.log (B : ℝ) :=
    Real.log_le_log (by positivity) hpowerReal
  have hlogFour :
      (1 : ℝ) ≤ Real.log 4 := by
    have hfour :
        Real.log (4 : ℝ) =
          Real.log 2 + Real.log 2 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num,
        Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
          (by norm_num : (2 : ℝ) ≠ 0)]
    rw [hfour]
    nlinarith [Real.log_two_gt_d9]
  have hsqLogFour :
      ((T : ℝ) ^ 2) ≤
        ((T : ℝ) ^ 2) * Real.log 4 := by
    simpa only [mul_one] using
      (mul_le_mul_of_nonneg_left hlogFour
        (sq_nonneg (T : ℝ)))
  have hlogPower' :
      ((T : ℝ) ^ 2) * Real.log 4 ≤
        Real.log (B : ℝ) := by
    calc
      ((T : ℝ) ^ 2) * Real.log 4 =
          Real.log (((4 ^ (T ^ 2) : ℕ) : ℝ)) := by
        rw [Nat.cast_pow, Real.log_pow]
        push_cast
        ring
      _ ≤ Real.log (B : ℝ) := hlogPower
  exact Real.le_sqrt_of_sq_le (hsqLogFour.trans hlogPower')

/--
Pointwise height-packing estimate on the broad bounded-ratio population.
The proof depends only on the canonical channel and not on the ambient
shape of the block.
-/
private theorem canonicalPairSigma_cast_le_epsilon_height
    {κ₀ A N L T : ℕ}
    {ε : ℝ} (hε : 0 < ε)
    (hT : 1 / ε < (T : ℝ))
    (hpower : 4 ^ (T ^ 2) ≤ L + 1)
    (pair : SeparatedBoundedRatioPair N (κ₀ * N) L)
    (hpair :
      pair ∈ boundedRatioShallowCorePairs κ₀ A N L) :
    (canonicalPairSigma A L pair.1.1 pair.1.2 : ℝ) ≤
      ε * ((L + 1 : ℕ) : ℝ) := by
  by_cases hsigmaZero :
      canonicalPairSigma A L pair.1.1 pair.1.2 = 0
  · simp only [hsigmaZero, Nat.cast_zero]
    positivity
  · have hsigmaPos :
        0 < canonicalPairSigma
          A L pair.1.1 pair.1.2 :=
      Nat.pos_of_ne_zero hsigmaZero
    have hmultiplicity :
        2 ≤ canonicalMultiplicity
          A L pair.1.1 pair.1.2 :=
      two_le_canonicalMultiplicity_of_sigma_pos hsigmaPos
    obtain ⟨c, hchoice, _hmCandidate⟩ :=
      exists_canonical_candidate_of_two_le_multiplicity
        hmultiplicity
    have hnotSmall :
        ¬ HasSmallCanonicalHeight
          A L pair.1.1 pair.1.2 :=
      (mem_boundedRatioShallowCorePairs.mp hpair).1
    have hheightNotLe :
        ¬ ((Nat.max c.1.1 c.1.2 : ℕ) : ℝ) ≤
            Real.sqrt
              (Real.log ((L + 1 : ℕ) : ℝ)) := by
      intro hheight
      exact hnotSmall ⟨c, hchoice, hheight⟩
    have hsqrtLtHeight :
        Real.sqrt (Real.log ((L + 1 : ℕ) : ℝ)) <
          ((Nat.max c.1.1 c.1.2 : ℕ) : ℝ) :=
      lt_of_not_ge hheightNotLe
    have hTLeSqrt :
        (T : ℝ) ≤
          Real.sqrt (Real.log ((L + 1 : ℕ) : ℝ)) :=
      cast_le_sqrt_log_of_four_pow_sq_le hpower
    have hTltHeight :
        (T : ℝ) <
          ((Nat.max c.1.1 c.1.2 : ℕ) : ℝ) :=
      hTLeSqrt.trans_lt hsqrtLtHeight
    have hpackingNat :
        Nat.max c.1.1 c.1.2 *
            canonicalPairSigma
              A L pair.1.1 pair.1.2 ≤ L := by
      have hpacking :=
        maxStep_mul_channelSigma_le
          L c.1.1 c.1.2
          (candidate_fst_pos c)
          (candidate_snd_pos c)
          (candidate_coprime c)
          (pairChannelError
            pair.1.1 pair.1.2 c.1.1 c.1.2)
      rw [← canonicalPairSigma_eq_channelSigma_of_choice
          hchoice] at hpacking
      exact hpacking
    have hpackingReal :
        ((Nat.max c.1.1 c.1.2 : ℕ) : ℝ) *
            (canonicalPairSigma
              A L pair.1.1 pair.1.2 : ℝ) ≤
          (L : ℝ) := by
      exact_mod_cast hpackingNat
    have hTpacking :
        (T : ℝ) *
            (canonicalPairSigma
              A L pair.1.1 pair.1.2 : ℝ) ≤
          ((L + 1 : ℕ) : ℝ) := by
      calc
        (T : ℝ) *
              (canonicalPairSigma
                A L pair.1.1 pair.1.2 : ℝ) ≤
            ((Nat.max c.1.1 c.1.2 : ℕ) : ℝ) *
              (canonicalPairSigma
                A L pair.1.1 pair.1.2 : ℝ) :=
          mul_le_mul_of_nonneg_right hTltHeight.le
            (by positivity)
        _ ≤ (L : ℝ) := hpackingReal
        _ ≤ ((L + 1 : ℕ) : ℝ) := by
          push_cast
          linarith
    have hscale :
        (1 : ℝ) ≤ ε * (T : ℝ) := by
      have honeLt : (1 : ℝ) < (T : ℝ) * ε :=
        (div_lt_iff₀ hε).1 hT
      nlinarith
    calc
      (canonicalPairSigma
          A L pair.1.1 pair.1.2 : ℝ) =
          1 * (canonicalPairSigma
            A L pair.1.1 pair.1.2 : ℝ) := by ring
      _ ≤
          (ε * (T : ℝ)) *
            (canonicalPairSigma
              A L pair.1.1 pair.1.2 : ℝ) :=
        mul_le_mul_of_nonneg_right hscale (by positivity)
      _ =
          ε * ((T : ℝ) *
            (canonicalPairSigma
              A L pair.1.1 pair.1.2 : ℝ)) := by ring
      _ ≤ ε * ((L + 1 : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hTpacking hε.le

/-! ## Uniform consequences in the critical run-length window -/

/--
The common bounded-ratio shallow-core systematic exponent is uniformly
little-oh of `L+1`.
-/
theorem maxBoundedRatioShallowCoreSigma_uniformLittleO
    {C : ℝ} (hC : 0 ≤ C) (κ₀ A : ℕ) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun N L ↦
        (maxBoundedRatioShallowCoreSigma κ₀ A N L : ℝ))
      (fun _ L ↦ ((L + 1 : ℕ) : ℝ)) := by
  intro ε hε
  obtain ⟨T : ℕ, hT⟩ :=
    exists_nat_gt (1 / ε)
  let B : ℕ := 4 ^ (T ^ 2)
  obtain ⟨Nwindow, hNwindow⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  obtain ⟨Nadm, hNadm⟩ :=
    CriticalWeightedDefect.admissible_eventually
      CriticalRunWindow.lowerConstant_pos
      CriticalRunWindow.lowerConstant_lt_upperConstant
  obtain ⟨Nheight, hNheight⟩ :=
    CriticalWeightedDefect.height_tends_to_infinity
      (c₂ := CriticalRunWindow.upperConstant)
      CriticalRunWindow.lowerConstant_pos B
  refine
    ⟨max Nwindow (max Nadm Nheight), ?_⟩
  intro N hN L hrun
  have hNwindowN : Nwindow ≤ N :=
    (le_max_left _ _).trans hN
  have hNtail : max Nadm Nheight ≤ N :=
    (le_max_right _ _).trans hN
  have hNadmN : Nadm ≤ N :=
    (le_max_left _ _).trans hNtail
  have hNheightN : Nheight ≤ N :=
    (le_max_right _ _).trans hNtail
  have hfirst :=
    hNwindow N hNwindowN L hrun
  have hadmissible :
      CriticalWeightedDefect.Admissible
        CriticalRunWindow.lowerConstant
        CriticalRunWindow.upperConstant N (L + 1) :=
    hNadm N hNadmN (L + 1) hfirst.1
  have hheight : B ≤ L + 1 :=
    hNheight N hNheightN (L + 1) hadmissible
  have hmax :
      (maxBoundedRatioShallowCoreSigma κ₀ A N L : ℝ) ≤
        ε * ((L + 1 : ℕ) : ℝ) := by
    apply maxBoundedRatioShallowCoreSigma_cast_le
    · positivity
    · intro pair hpair
      exact canonicalPairSigma_cast_le_epsilon_height
        hε hT (by simpa only [B] using hheight)
        pair hpair
  rw [abs_of_nonneg
      (show
        0 ≤
          (maxBoundedRatioShallowCoreSigma
            κ₀ A N L : ℝ) by positivity),
    abs_of_nonneg
      (show 0 ≤ ((L + 1 : ℕ) : ℝ) by positivity)]
  exact hmax

/--
Exponentiating the common bounded-ratio systematic maximum produces a
uniformly subpolynomial factor.
-/
theorem four_pow_maxBoundedRatioShallowCoreSigma_uniformSubpolynomial
    {C : ℝ} (hC : 0 ≤ C) (κ₀ A : ℕ) :
    UniformSubpolynomialOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun N L ↦
        (((4 ^
          maxBoundedRatioShallowCoreSigma
            κ₀ A N L : ℕ) : ℝ))) := by
  have hupperNonneg :
      0 ≤ CriticalRunWindow.upperConstant :=
    (CriticalRunWindow.lowerConstant_pos.trans
      CriticalRunWindow.lowerConstant_lt_upperConstant).le
  apply
    FourPowLittleOHeight.uniformSubpolynomialOn_four_pow_of_uniformLittleO_height
      (maxBoundedRatioShallowCoreSigma κ₀ A)
      (fun _ L ↦ ((L + 1 : ℕ) : ℝ))
      CriticalRunWindow.upperConstant hupperNonneg
  · exact
      maxBoundedRatioShallowCoreSigma_uniformLittleO
        hC κ₀ A
  · intro N L _hrun
    positivity
  · obtain ⟨Nwindow, hNwindow⟩ :=
      CriticalRunWindow.firstMomentWindow_eventually hC
    refine ⟨Nwindow, ?_⟩
    intro N hN L hrun
    exact (hNwindow N hN L hrun).1.2.2.2

end

end BoundedRatioShallowCoreSigmaCritical
end PaperC
