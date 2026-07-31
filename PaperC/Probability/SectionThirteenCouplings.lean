import PaperC.Probability.BadStartMass
import PaperC.Probability.ConditionalAGGAverage

set_option maxHeartbeats 1200000

/-!
# Couplings for the final Section 13 assembly

This module identifies the uniform mixture of conditioned good-start laws
with the corresponding law on the full prime cylinder.  On that common
cylinder it couples the good-start count to the complete dyadic start count.
Their disagreement forces at least one start in the terminal bad set, so a
finite union bound controls total variation by the bad-start probability
mass used elsewhere in Section 13.
-/

namespace PaperC
namespace SectionThirteenCouplings

open scoped BigOperators NNReal

open ProbabilityTheory
open ArratiaGoldsteinGordonInput
open BadStartCount
open ConditionalAGGAverage
open ConditionalAGGInstantiation
open ConditionalDependencyGraph
open ConditionalStartProbability
open LargePrimeDependencyGraph
open SectionThirteenFiniteBound
open SteinChenTerms

noncomputable section

local instance (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-! ## Full-cylinder laws -/

/-- Uniform PMF on the complete prime-sign cylinder. -/
noncomputable def fullUniformPMF (M : ℕ) :
    FinitePMF (SampleSpace M) :=
  FinitePMF.uniform _

/-- Good-start indicators viewed directly on the complete cylinder. -/
noncomputable def fullGoodIndicator
    (N L Y : ℕ) :
    {x : ℕ // x ∈ goodStarts N L Y} →
      SampleSpace (dyadicCutoff N L) → Bool := by
  classical
  exact fun x ω ↦ decide (startAt ω x.1 L)

@[simp]
theorem fullGoodIndicator_eq_true_iff
    {N L Y : ℕ}
    {x : {x : ℕ // x ∈ goodStarts N L Y}}
    {ω : SampleSpace (dyadicCutoff N L)} :
    fullGoodIndicator N L Y x ω = true ↔
      startAt ω x.1 L := by
  simp [fullGoodIndicator]

/-- Number of good starts on the complete cylinder. -/
noncomputable def fullGoodStartCount
    (N L Y : ℕ)
    (ω : SampleSpace (dyadicCutoff N L)) : ℕ :=
  indicatorSum (fullGoodIndicator N L Y) ω

/-- Law of the full-cylinder good-start count. -/
noncomputable def fullGoodStartLaw
    (N L Y : ℕ) : ℕ → ℝ :=
  indicatorSumLaw
    (fullUniformPMF (dyadicCutoff N L))
    (fullGoodIndicator N L Y)

/-- Law of the complete dyadic start count on the same cylinder. -/
noncomputable def fullDyadicStartLaw
    (N L : ℕ) : ℕ → ℝ :=
  finiteNatLaw
    (fullUniformPMF (dyadicCutoff N L))
    (dyadicCount N L)

/-- Real cast of the exact bad-start probability mass. -/
noncomputable def badStartProbabilityMassReal
    (N L Y : ℕ) : ℝ :=
  ((BadStartMass.startProbabilityMass N L
    (terminalBadStarts N L Y) : ℚ) : ℝ)

/-! ## Identification of the averaged conditional law -/

/-- Conditional and full good-start counts agree under `assemble`. -/
theorem conditionedGoodIndicatorSum_eq_fullGoodStartCount
    (N L Y : ℕ)
    (σ : SmallSample (dyadicCutoff N L) Y)
    (η : LargeSample (dyadicCutoff N L) Y) :
    indicatorSum (conditionedGoodIndicator N L Y σ) η =
      fullGoodStartCount N L Y
        (assemble (dyadicCutoff N L) Y σ η) := by
  classical
  unfold indicatorSum fullGoodStartCount fullGoodIndicator
    conditionedGoodIndicator
  rfl

/--
Event probabilities for the uniform full-cylinder PMF are the real casts of
the exact rational finite-uniform probabilities.
-/
theorem eventProbability_fullUniformPMF_eq
    {M : ℕ} (event : SampleSpace M → Prop) :
    eventProbability (fullUniformPMF M) event =
      ((finiteUniformProbability event : ℚ) : ℝ) := by
  classical
  unfold eventProbability fullUniformPMF
    FinitePMF.uniform finiteUniformProbability
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Fintype.card_subtype]
  simp only [div_eq_mul_inv, Rat.cast_mul, Rat.cast_natCast,
    Rat.cast_inv, Rat.cast_ofNat]
  rw [← Finset.sum_filter]
  simp

/-- Full good-start law as a finite pushforward law. -/
theorem fullGoodStartLaw_eq_finiteNatLaw
    (N L Y : ℕ) :
    fullGoodStartLaw N L Y =
      finiteNatLaw
        (fullUniformPMF (dyadicCutoff N L))
        (fullGoodStartCount N L Y) := by
  funext k
  unfold fullGoodStartLaw indicatorSumLaw finiteNatLaw
    eventProbability fullGoodStartCount
  apply Finset.sum_congr rfl
  intro ω _hω
  split_ifs <;> rfl

/--
The uniform mixture of the conditioned laws is exactly the good-start law on
the full prime cylinder.
-/
theorem averagedConditionalGoodLaw_eq_fullGoodStartLaw
    (N L Y : ℕ) :
    averagedConditionalGoodLaw N L Y =
      fullGoodStartLaw N L Y := by
  funext k
  let P : SampleSpace (dyadicCutoff N L) → Prop :=
    fun ω ↦ fullGoodStartCount N L Y ω = k
  have htotal :=
    finiteUniformAverage_largeEventProbability_eq_full
      (dyadicCutoff N L) Y P
  have hfull :
      eventProbability
          (fullUniformPMF (dyadicCutoff N L)) P =
        ((uniformEventProbability P : ℚ) : ℝ) := by
    rw [eventProbability_fullUniformPMF_eq,
      finiteUniformProbability_eq_uniformEventProbability]
  rw [← hfull] at htotal
  simpa only [averagedConditionalGoodLaw, conditionalGoodLaw,
    indicatorSumLaw, fullGoodStartLaw, P,
    conditionedGoodIndicatorSum_eq_fullGoodStartCount] using htotal

/-! ## Disagreement and the finite bad-start union bound -/

/-- Literal good-start count as a sum over the natural good-start set. -/
theorem fullGoodStartCount_eq_sum
    (N L Y : ℕ)
    (ω : SampleSpace (dyadicCutoff N L)) :
    fullGoodStartCount N L Y ω =
      ∑ x ∈ goodStarts N L Y,
        if startAt ω x L then 1 else 0 := by
  classical
  unfold fullGoodStartCount indicatorSum
  rw [Finset.card_filter]
  simp only [fullGoodIndicator_eq_true_iff]
  rw [← Finset.sum_subtype
    (goodStarts N L Y) (fun _x ↦ Iff.rfl)
    (fun x ↦ if startAt ω x L then 1 else 0)]

/--
If the good-start count differs from the full dyadic count, at least one
terminal bad start occurs.
-/
theorem exists_bad_start_of_fullGoodStartCount_ne_dyadicCount
    {N L Y : ℕ}
    {ω : SampleSpace (dyadicCutoff N L)}
    (hne :
      fullGoodStartCount N L Y ω ≠ dyadicCount N L ω) :
    ∃ x ∈ terminalBadStarts N L Y, startAt ω x L := by
  classical
  by_contra h
  push_neg at h
  apply hne
  rw [fullGoodStartCount_eq_sum]
  unfold dyadicCount
  apply Finset.sum_subset Finset.sdiff_subset
  intro x hxBlock hxNotGood
  have hxBad : x ∈ terminalBadStarts N L Y := by
    by_contra hxNotBad
    exact hxNotGood
      (Finset.mem_sdiff.mpr ⟨hxBlock, hxNotBad⟩)
  rw [if_neg (h x hxBad)]

/--
The disagreement probability of the two coupled counts is bounded by the
real bad-start probability mass.
-/
theorem disagreementProbability_fullGood_dyadic_le_badMass
    (N L Y : ℕ) :
    disagreementProbability
        (fullUniformPMF (dyadicCutoff N L))
        (fullGoodStartCount N L Y)
        (dyadicCount N L) ≤
      badStartProbabilityMassReal N L Y := by
  classical
  have hpoint :
      ∀ ω : SampleSpace (dyadicCutoff N L),
        (if fullGoodStartCount N L Y ω ≠ dyadicCount N L ω then
            (fullUniformPMF (dyadicCutoff N L)).prob ω
          else 0) ≤
          ∑ x ∈ terminalBadStarts N L Y,
            if startAt ω x L then
              (fullUniformPMF (dyadicCutoff N L)).prob ω
            else 0 := by
    intro ω
    by_cases hne :
        fullGoodStartCount N L Y ω ≠ dyadicCount N L ω
    · rw [if_pos hne]
      obtain ⟨x, hxBad, hxStart⟩ :=
        exists_bad_start_of_fullGoodStartCount_ne_dyadicCount hne
      calc
        (fullUniformPMF (dyadicCutoff N L)).prob ω =
            (if startAt ω x L then
              (fullUniformPMF (dyadicCutoff N L)).prob ω
            else 0) := by rw [if_pos hxStart]
        _ ≤
            ∑ y ∈ terminalBadStarts N L Y,
              if startAt ω y L then
                (fullUniformPMF (dyadicCutoff N L)).prob ω
              else 0 := by
          apply Finset.single_le_sum
            (s := terminalBadStarts N L Y)
            (f := fun y ↦
              if startAt ω y L then
                (fullUniformPMF (dyadicCutoff N L)).prob ω
              else 0)
          · intro y _hy
            split_ifs
            · exact (fullUniformPMF
                (dyadicCutoff N L)).nonneg ω
            · exact le_rfl
          · exact hxBad
    · rw [if_neg hne]
      exact Finset.sum_nonneg fun x _hx ↦ by
        split_ifs
        · exact (fullUniformPMF
            (dyadicCutoff N L)).nonneg ω
        · exact le_rfl
  have hsum :
      (∑ ω,
        if fullGoodStartCount N L Y ω ≠ dyadicCount N L ω then
          (fullUniformPMF (dyadicCutoff N L)).prob ω
        else 0) ≤
        ∑ ω, ∑ x ∈ terminalBadStarts N L Y,
          if startAt ω x L then
            (fullUniformPMF (dyadicCutoff N L)).prob ω
          else 0 :=
    Finset.sum_le_sum fun ω _hω ↦ hpoint ω
  unfold disagreementProbability
  calc
    (∑ ω,
        if fullGoodStartCount N L Y ω ≠ dyadicCount N L ω then
          (fullUniformPMF (dyadicCutoff N L)).prob ω
        else 0) ≤
      ∑ ω, ∑ x ∈ terminalBadStarts N L Y,
        if startAt ω x L then
          (fullUniformPMF (dyadicCutoff N L)).prob ω
        else 0 := hsum
    _ =
        ∑ x ∈ terminalBadStarts N L Y,
          eventProbability
            (fullUniformPMF (dyadicCutoff N L))
            (fun ω ↦ startAt ω x L) := by
      rw [Finset.sum_comm]
      rfl
    _ =
        badStartProbabilityMassReal N L Y := by
      unfold badStartProbabilityMassReal
        BadStartMass.startProbabilityMass startProbability
      simp_rw [eventProbability_fullUniformPMF_eq,
        finiteUniformProbability_eq_uniformEventProbability]
      push_cast
      apply Finset.sum_congr rfl
      intro x _hx
      rfl

/--
First coupling contribution in Corollary 13.9: replacing all starts by good
starts costs at most the bad-start probability mass.
-/
theorem natTotalVariation_averagedGood_fullDyadic_le_badMass
    (N L Y : ℕ) :
    natTotalVariation
        (averagedConditionalGoodLaw N L Y)
        (fullDyadicStartLaw N L) ≤
      badStartProbabilityMassReal N L Y := by
  rw [averagedConditionalGoodLaw_eq_fullGoodStartLaw,
    fullGoodStartLaw_eq_finiteNatLaw]
  exact
    (natTotalVariation_finiteNatLaw_le_disagreement
      (fullUniformPMF (dyadicCutoff N L))
      (fullGoodStartCount N L Y)
      (dyadicCount N L)).trans
        (disagreementProbability_fullGood_dyadic_le_badMass N L Y)

/-! ## Coupling two Poisson parameters -/

/--
After multiplying the smaller-rate Poisson law by
`exp (r - s)`, it is pointwise dominated by the larger-rate law.
-/
theorem scaled_poissonPMFReal_le_of_le
    {r s : ℝ≥0} (hrs : r ≤ s) (k : ℕ) :
    Real.exp ((r : ℝ) - (s : ℝ)) *
        poissonPMFReal r k ≤
      poissonPMFReal s k := by
  have hrsReal : (r : ℝ) ≤ (s : ℝ) := by
    exact_mod_cast hrs
  have hpow : (r : ℝ) ^ k ≤ (s : ℝ) ^ k :=
    pow_le_pow_left₀ (by positivity) hrsReal k
  have hexp :
      Real.exp ((r : ℝ) - (s : ℝ)) *
          Real.exp (-(r : ℝ)) =
        Real.exp (-(s : ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold poissonPMFReal
  calc
    Real.exp ((r : ℝ) - (s : ℝ)) *
          (Real.exp (-(r : ℝ)) * (r : ℝ) ^ k /
            (k.factorial : ℝ)) =
        (Real.exp ((r : ℝ) - (s : ℝ)) *
            Real.exp (-(r : ℝ))) * (r : ℝ) ^ k /
          (k.factorial : ℝ) := by ring
    _ =
        Real.exp (-(s : ℝ)) * (r : ℝ) ^ k /
          (k.factorial : ℝ) := by rw [hexp]
    _ ≤
        Real.exp (-(s : ℝ)) * (s : ℝ) ^ k /
          (k.factorial : ℝ) := by
      apply div_le_div_of_nonneg_right
      · exact mul_le_mul_of_nonneg_left hpow
          (Real.exp_pos _).le
      · positivity

/--
Ordered-rate Poisson comparison:
`dTV(Pois(r), Pois(s)) ≤ 1 - exp(r-s)` for `r ≤ s`.
-/
theorem natTotalVariation_poisson_le_one_sub_exp_of_le
    {r s : ℝ≥0} (hrs : r ≤ s) :
    natTotalVariation
        (poissonPMFReal r) (poissonPMFReal s) ≤
      1 - Real.exp ((r : ℝ) - (s : ℝ)) := by
  let c : ℝ := Real.exp ((r : ℝ) - (s : ℝ))
  have hrsReal : (r : ℝ) ≤ (s : ℝ) := by
    exact_mod_cast hrs
  have hc0 : 0 ≤ c := by
    dsimp only [c]
    positivity
  have hc1 : c ≤ 1 := by
    dsimp only [c]
    exact Real.exp_le_one_iff.mpr (sub_nonpos.mpr hrsReal)
  have hp := (poissonPMFRealSum r).summable
  have hq := (poissonPMFRealSum s).summable
  have hcp : Summable fun k ↦ c * poissonPMFReal r k :=
    hp.mul_left c
  have hfirst :
      natTotalVariation
          (poissonPMFReal r)
          (fun k ↦ c * poissonPMFReal r k) =
        (2 : ℝ)⁻¹ * (1 - c) := by
    unfold natTotalVariation
    have habs :
        ∀ k : ℕ,
          |poissonPMFReal r k -
              c * poissonPMFReal r k| =
            (1 - c) * poissonPMFReal r k := by
      intro k
      rw [abs_of_nonneg]
      · ring
      · have hp0 : 0 ≤ poissonPMFReal r k :=
          poissonPMFReal_nonneg
        nlinarith
    rw [tsum_congr habs]
    rw [hp.tsum_mul_left]
    rw [(poissonPMFRealSum r).tsum_eq]
    ring
  have hsecond :
      natTotalVariation
          (fun k ↦ c * poissonPMFReal r k)
          (poissonPMFReal s) =
        (2 : ℝ)⁻¹ * (1 - c) := by
    unfold natTotalVariation
    have habs :
        ∀ k : ℕ,
          |c * poissonPMFReal r k -
              poissonPMFReal s k| =
            poissonPMFReal s k -
              c * poissonPMFReal r k := by
      intro k
      rw [abs_of_nonpos]
      · ring
      · dsimp only [c]
        linarith [scaled_poissonPMFReal_le_of_le hrs k]
    rw [tsum_congr habs]
    rw [hq.tsum_sub hcp]
    rw [(poissonPMFRealSum s).tsum_eq,
      hp.tsum_mul_left,
      (poissonPMFRealSum r).tsum_eq]
    ring
  have htriangle :=
    natTotalVariation_triangle
      hp hcp hq
      (fun _k ↦ poissonPMFReal_nonneg)
      (fun _k ↦ mul_nonneg hc0 poissonPMFReal_nonneg)
      (fun _k ↦ poissonPMFReal_nonneg)
  rw [hfirst, hsecond] at htriangle
  linarith

/--
Total variation between two Poisson laws is at most the absolute difference
of their rates.
-/
theorem natTotalVariation_poisson_le_abs_rate_sub
    (r s : ℝ≥0) :
    natTotalVariation
        (poissonPMFReal r) (poissonPMFReal s) ≤
      |(r : ℝ) - (s : ℝ)| := by
  rcases le_total r s with hrs | hsr
  · have hbase :=
      natTotalVariation_poisson_le_one_sub_exp_of_le hrs
    have hexp :=
      Real.add_one_le_exp ((r : ℝ) - (s : ℝ))
    rw [abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast hrs))]
    linarith
  · rw [natTotalVariation_comm]
    have hbase :=
      natTotalVariation_poisson_le_one_sub_exp_of_le hsr
    have hexp :=
      Real.add_one_le_exp ((s : ℝ) - (r : ℝ))
    rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hsr))]
    linarith

/-! ## The good and target Poisson parameters -/

/-- Manuscript target rate `λ_N = N / 2^L`. -/
noncomputable def targetPoissonRate
    (N L : ℕ) : ℝ≥0 :=
  ⟨(N : ℝ) / (2 : ℝ) ^ L, by positivity⟩

/-- Poisson law at the manuscript target rate. -/
noncomputable def targetPoissonLaw
    (N L : ℕ) : ℕ → ℝ :=
  poissonPMFReal (targetPoissonRate N L)

/-- Exact closed form of the conditional good-start Poisson rate. -/
theorem commonConditionalGoodPoissonRate_eq
    {N L Y : ℕ}
    (hN : 2 ≤ N) (hL : 0 < L) (hLY : L + 1 ≤ Y) :
    ((poissonRate
        (largeUniformPMF (dyadicCutoff N L) Y)
        (conditionedGoodIndicator N L Y 0) : ℝ≥0) : ℝ) =
      ((goodStarts N L Y).card : ℝ) /
        (2 : ℝ) ^ L := by
  unfold poissonRate poissonParameter
  simp only [NNReal.coe_mk]
  simp_rw [marginal_conditionedGoodIndicator_eq_baseline
    hN hL hLY 0]
  simp only [Finset.sum_const, nsmul_eq_mul,
    Finset.card_univ, Fintype.card_coe]
  ring

/-- Terminal bad starts are contained in the dyadic block. -/
theorem terminalBadStarts_subset_dyadicBlock
    (N L Y : ℕ) :
    terminalBadStarts N L Y ⊆ dyadicBlock N := by
  intro x hx
  exact (mem_terminalBadStarts.mp hx).1

/-- Good and bad starts partition the dyadic block at the cardinal level. -/
theorem card_goodStarts_add_card_terminalBadStarts
    (N L Y : ℕ) :
    (goodStarts N L Y).card +
        (terminalBadStarts N L Y).card =
      N := by
  unfold goodStarts
  rw [Finset.card_sdiff_add_card_eq_card
    (terminalBadStarts_subset_dyadicBlock N L Y)]
  exact TouchingPairs.card_dyadicBlock N

/--
The rate difference between the good-start Poisson law and the manuscript
target is exactly the normalized number of terminal bad starts.
-/
theorem abs_commonGoodPoissonRate_sub_targetRate_eq
    {N L Y : ℕ}
    (hN : 2 ≤ N) (hL : 0 < L) (hLY : L + 1 ≤ Y) :
    |((poissonRate
        (largeUniformPMF (dyadicCutoff N L) Y)
        (conditionedGoodIndicator N L Y 0) : ℝ≥0) : ℝ) -
      (targetPoissonRate N L : ℝ)| =
        ((terminalBadStarts N L Y).card : ℝ) /
          (2 : ℝ) ^ L := by
  rw [commonConditionalGoodPoissonRate_eq hN hL hLY]
  unfold targetPoissonRate
  simp only [NNReal.coe_mk]
  have hcard :
      ((goodStarts N L Y).card : ℝ) +
          ((terminalBadStarts N L Y).card : ℝ) =
        (N : ℝ) := by
    exact_mod_cast
      card_goodStarts_add_card_terminalBadStarts N L Y
  have heq :
      ((goodStarts N L Y).card : ℝ) /
            (2 : ℝ) ^ L -
          (N : ℝ) / (2 : ℝ) ^ L =
        -(((terminalBadStarts N L Y).card : ℝ) /
          (2 : ℝ) ^ L) := by
    field_simp
    linarith
  rw [heq, abs_neg, abs_of_nonneg]
  positivity

/--
Second coupling contribution in Corollary 13.9: changing the matching
good-start Poisson parameter to `λ_N` costs at most
`#D_Y / 2^L`.
-/
theorem natTotalVariation_commonGoodPoisson_target_le
    {N L Y : ℕ}
    (hN : 2 ≤ N) (hL : 0 < L) (hLY : L + 1 ≤ Y) :
    natTotalVariation
        (commonConditionalGoodPoissonLaw N L Y)
        (targetPoissonLaw N L) ≤
      ((terminalBadStarts N L Y).card : ℝ) /
        (2 : ℝ) ^ L := by
  change
    natTotalVariation
        (poissonPMFReal
          (poissonRate
            (largeUniformPMF (dyadicCutoff N L) Y)
            (conditionedGoodIndicator N L Y 0)))
        (poissonPMFReal (targetPoissonRate N L)) ≤ _
  exact
    (natTotalVariation_poisson_le_abs_rate_sub _ _).trans_eq
      (abs_commonGoodPoissonRate_sub_targetRate_eq
        hN hL hLY)

/-! ## Finite assembly of Corollary 13.9 -/

/--
The three exact finite contributions in the final Section 13 comparison:

* the coupling which removes terminal bad starts;
* the averaged conditional AGG error;
* the change from the good-start Poisson parameter to `N / 2^L`.

This form is independent of any particular upper bound for the middle
term, and is the convenient interface for the critical-window assembly.
-/
theorem natTotalVariation_fullDyadic_targetPoisson_le_components
    {N L Y : ℕ}
    (hN : 2 ≤ N) (hL : 0 < L) (hLY : L + 1 ≤ Y) :
    natTotalVariation
        (fullDyadicStartLaw N L)
        (targetPoissonLaw N L) ≤
      badStartProbabilityMassReal N L Y +
        natTotalVariation
          (averagedConditionalGoodLaw N L Y)
          (commonConditionalGoodPoissonLaw N L Y) +
        ((terminalBadStarts N L Y).card : ℝ) /
          (2 : ℝ) ^ L := by
  have hfullSum :
      Summable (fullDyadicStartLaw N L) := by
    unfold fullDyadicStartLaw
    exact summable_finiteNatLaw _ _
  have hfullNonneg :
      ∀ k, 0 ≤ fullDyadicStartLaw N L k := by
    intro k
    unfold fullDyadicStartLaw
    exact finiteNatLaw_nonneg _ _ _
  have havgSum :
      Summable (averagedConditionalGoodLaw N L Y) := by
    rw [averagedConditionalGoodLaw_eq_fullGoodStartLaw,
      fullGoodStartLaw_eq_finiteNatLaw]
    exact summable_finiteNatLaw _ _
  have havgNonneg :
      ∀ k, 0 ≤ averagedConditionalGoodLaw N L Y k := by
    intro k
    rw [averagedConditionalGoodLaw_eq_fullGoodStartLaw,
      fullGoodStartLaw_eq_finiteNatLaw]
    exact finiteNatLaw_nonneg _ _ _
  have hcommonSum :
      Summable (commonConditionalGoodPoissonLaw N L Y) :=
    summable_commonConditionalGoodPoissonLaw N L Y
  have hcommonNonneg :
      ∀ k, 0 ≤ commonConditionalGoodPoissonLaw N L Y k :=
    commonConditionalGoodPoissonLaw_nonneg N L Y
  have htargetSum :
      Summable (targetPoissonLaw N L) := by
    unfold targetPoissonLaw
    exact (poissonPMFRealSum _).summable
  have htargetNonneg :
      ∀ k, 0 ≤ targetPoissonLaw N L k := by
    intro k
    exact poissonPMFReal_nonneg
  have houter :=
    natTotalVariation_triangle
      hfullSum havgSum htargetSum
      hfullNonneg havgNonneg htargetNonneg
  have hinner :=
    natTotalVariation_triangle
      havgSum hcommonSum htargetSum
      havgNonneg hcommonNonneg htargetNonneg
  have hbad :
      natTotalVariation
          (fullDyadicStartLaw N L)
          (averagedConditionalGoodLaw N L Y) ≤
        badStartProbabilityMassReal N L Y := by
    rw [natTotalVariation_comm]
    exact natTotalVariation_averagedGood_fullDyadic_le_badMass N L Y
  have hparameter :=
    natTotalVariation_commonGoodPoisson_target_le
      hN hL hLY
  linarith

/--
Fully concrete finite Corollary 13.9 bound, conditional only on the
published Arratia--Goldstein--Gordon statement.
-/
theorem natTotalVariation_fullDyadic_targetPoisson_le
    (hAGG : ArratiaGoldsteinGordonStatement)
    {N L Y : ℕ}
    (hN : 2 ≤ N) (hL : 0 < L) (hLY : L + 1 ≤ Y) :
    natTotalVariation
        (fullDyadicStartLaw N L)
        (targetPoissonLaw N L) ≤
      badStartProbabilityMassReal N L Y +
        2 *
          (((steinBOne N L Y : ℚ) : ℝ) +
            ((steinBTwoAverage N L Y : ℚ) : ℝ)) +
        ((terminalBadStarts N L Y).card : ℝ) /
          (2 : ℝ) ^ L := by
  have hcomponents :=
    natTotalVariation_fullDyadic_targetPoisson_le_components
      hN hL hLY
  have hagg :=
    averagedConditionalGood_natTotalVariation_le_steinTerms
      hAGG hN hL hLY
  linarith

end

end SectionThirteenCouplings
end PaperC
