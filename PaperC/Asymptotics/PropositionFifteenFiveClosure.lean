import PaperC.Asymptotics.PropositionFifteenFive
import PaperC.Asymptotics.PropositionFifteenFiveDecay
import PaperC.Asymptotics.DependencyEdgesCritical
import PaperC.Asymptotics.Uniform
import PaperC.Probability.CriticalRunWindow
import Mathlib.Analysis.SpecificLimits.Basic

set_option maxHeartbeats 1600000

/-!
# Proposition 15.5: double-limit closure

This module records the quantifier order in the conclusion of Proposition
15.5 and separates the analytic closure from the finite dyadic-block
estimates.  The truncation depth `j₀` is chosen first; only afterwards may the
threshold in the main parameter `M` be chosen.  Uniformity in the critical
run-length parameter is expressed by the explicit predicate `admissible`.
-/

namespace PaperC
namespace PropositionFifteenFiveClosure

open scoped BigOperators Topology
open Filter

noncomputable section

/--
The literal probability mass below the integer cutoff
`⌊M 2⁻ʲ⁰⌋ = M / 2^j₀` occurring in Proposition 15.5.

The strict upper endpoint of `Finset.Ico` encodes the manuscript range
`2 ≤ x < M 2⁻ʲ⁰`.
-/
noncomputable def deepStartProbabilityMass
    (M L j₀ : ℕ) : ℝ :=
  ∑ x ∈ Finset.Ico 2 (M / 2 ^ j₀),
    PropositionFifteenFive.globalStartProbability L x

/-- The literal deep-start mass is nonnegative. -/
theorem deepStartProbabilityMass_nonneg
    (M L j₀ : ℕ) :
    0 ≤ deepStartProbabilityMass M L j₀ := by
  unfold deepStartProbabilityMass
  exact Finset.sum_nonneg fun x _ ↦
    PropositionFifteenFive.globalStartProbability_nonneg L x

/--
The uniform double-limit conclusion of Proposition 15.5.

For every tolerance, all sufficiently deep truncation levels `j₀` work, and
for each such `j₀` the threshold `M₀` is then allowed to depend on `j₀`.
The final quantifier over `L` makes the conclusion uniform in the critical
window encoded by `admissible`.
-/
def DeepTruncationDoubleLimit
    (admissible : ℕ → ℕ → Prop)
    (mass : ℕ → ℕ → ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ J₀ : ℕ, ∀ j₀ ≥ J₀,
      ∃ M₀ : ℕ, ∀ M ≥ M₀, ∀ L, admissible M L →
        |mass M L j₀| ≤ ε

/--
The exact formal statement of Proposition 15.5 in the manuscript critical
window, for the genuine finite-cylinder start probabilities.
-/
def PropositionFifteenFiveStatement (C : ℝ) : Prop :=
  DeepTruncationDoubleLimit
    (CriticalRunWindow.InRunLengthWindow C)
    deepStartProbabilityMass

/--
Abstract analytic closure for Proposition 15.5.

The finite argument need only provide a nonnegative mass bounded by a
uniform little-oh remainder plus the explicit dyadic tail
`D * (1 / 2)^j₀`.  No sign assumption is imposed on the remainder: its
absolute value is controlled by `UniformLittleOOn`.
-/
theorem deepTruncationDoubleLimit_of_uniformLittleO_remainder
    {admissible : ℕ → ℕ → Prop}
    {mass : ℕ → ℕ → ℕ → ℝ}
    {remainder : ℕ → ℕ → ℝ}
    {D : ℝ}
    (hD : 0 ≤ D)
    (hmass_nonneg :
      ∀ M L j₀, admissible M L → 0 ≤ mass M L j₀)
    (hmass_le :
      ∀ M L j₀, admissible M L →
        mass M L j₀ ≤
          remainder M L + D * (1 / 2 : ℝ) ^ j₀)
    (hremainder :
      UniformLittleOOn admissible remainder (fun _ _ => 1)) :
    DeepTruncationDoubleLimit admissible mass := by
  intro ε hε
  have hdyadic :
      Tendsto (fun j₀ : ℕ => D * (1 / 2 : ℝ) ^ j₀)
        atTop (𝓝 0) := by
    simpa using
      tendsto_const_nhds.mul
        (tendsto_pow_atTop_nhds_zero_of_lt_one
          (by norm_num : 0 ≤ (1 / 2 : ℝ))
          (by norm_num : (1 / 2 : ℝ) < 1))
  obtain ⟨J₀, hJ₀⟩ :=
    Metric.tendsto_atTop.mp hdyadic (ε / 2) (by positivity)
  refine ⟨J₀, ?_⟩
  intro j₀ hj₀
  obtain ⟨M₀, hM₀⟩ :=
    hremainder (ε / 2) (by positivity)
  refine ⟨M₀, ?_⟩
  intro M hM L hML
  have hrem :
      |remainder M L| ≤ ε / 2 := by
    simpa using hM₀ M hM L hML
  have htailDist :
      dist (D * (1 / 2 : ℝ) ^ j₀) 0 < ε / 2 :=
    hJ₀ j₀ hj₀
  have htailNonneg :
      0 ≤ D * (1 / 2 : ℝ) ^ j₀ :=
    mul_nonneg hD (by positivity)
  have htailAbs :
      |D * (1 / 2 : ℝ) ^ j₀| ≤ ε / 2 := by
    rw [Real.dist_eq] at htailDist
    simpa using htailDist.le
  have htail :
      D * (1 / 2 : ℝ) ^ j₀ ≤ ε / 2 := by
    calc
      D * (1 / 2 : ℝ) ^ j₀ =
          |D * (1 / 2 : ℝ) ^ j₀| :=
        (abs_of_nonneg htailNonneg).symm
      _ ≤ ε / 2 := htailAbs
  rw [abs_of_nonneg (hmass_nonneg M L j₀ hML)]
  calc
    mass M L j₀ ≤
        remainder M L + D * (1 / 2 : ℝ) ^ j₀ :=
      hmass_le M L j₀ hML
    _ ≤ |remainder M L| + D * (1 / 2 : ℝ) ^ j₀ := by
      gcongr
      exact le_abs_self (remainder M L)
    _ ≤ ε / 2 + ε / 2 := add_le_add hrem htail
    _ = ε := by ring

/--
A scalar sequence tending to zero with the run length gives a uniform
little-oh in the manuscript critical window.  The threshold in `M` is
obtained from the already proved uniform divergence of `L+1`.
-/
theorem uniformLittleOOn_runLength_of_tendsto_zero
    {C : ℝ} (hC : 0 ≤ C)
    {f : ℕ → ℝ}
    (hf : Tendsto f atTop (𝓝 0)) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun _ L ↦ f L) (fun _ _ ↦ 1) := by
  intro ε hε
  obtain ⟨L₀, hL₀⟩ :=
    Metric.tendsto_atTop.mp hf ε hε
  obtain ⟨M₀, hM₀⟩ :=
    DependencyEdgesCritical.runLengthAddOne_tends_to_infinity
      hC (L₀ + 1)
  refine ⟨M₀, ?_⟩
  intro M hM L hrun
  have hL : L₀ ≤ L := by
    have := hM₀ M hM L hrun
    omega
  have hdist := hL₀ L hL
  rw [Real.dist_eq] at hdist
  simpa using hdist.le

/--
Uniform critical-window form of the exceptional high-zone decay.  This is
the `o_M(1)` term obtained by summing Lemmas 15.3 and 15.4 over at most a
linear number of dyadic blocks.
-/
theorem highZoneExceptionalEnvelope_uniformLittleOOne
    {C θ K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun _ L ↦
        (L : ℝ) *
          Real.exp
            (K * (L : ℝ) / Real.log (L : ℝ)) *
          (2 : ℝ) ^
            (1 -
              BalasubramanianShoreyInput.gap (L + 1) θ))
      (fun _ _ ↦ 1) :=
  uniformLittleOOn_runLength_of_tendsto_zero hC
    (PropositionFifteenFiveDecay.highZoneExceptionalEnvelope_tendsto_zero
      θ K hK)

/--
The linear cutoff `2L` is eventually contained in the power zone
`L^(2-1/2)` of Lemma 15.1.  Together with the band of Lemma 15.2 this
already covers every integer start up to `2L²`.
-/
theorem two_mul_runLength_lowZonePowerAdmissible_eventually :
    ∃ L₀ : ℕ, ∀ L ≥ L₀,
      LowZoneCritical.LowZonePowerAdmissible
        (1 / 2 : ℝ) L (2 * L) := by
  have hroot :
      ∀ᶠ L : ℕ in atTop,
        (2 : ℝ) ≤ (L : ℝ) ^ (1 / 2 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
      tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop 2)
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.mp hroot
  refine ⟨max L₀ 1, ?_⟩
  intro L hL
  have hrootL :
      (2 : ℝ) ≤ (L : ℝ) ^ (1 / 2 : ℝ) :=
    hL₀ L ((le_max_left L₀ 1).trans hL)
  have hLone : 1 ≤ L :=
    (le_max_right L₀ 1).trans hL
  have hLpos : (0 : ℝ) < (L : ℝ) := by positivity
  refine ⟨by norm_num, by norm_num, ?_⟩
  norm_num only [Nat.cast_mul, Nat.cast_ofNat]
  have htarget :
      2 * (L : ℝ) ≤ (L : ℝ) ^ (3 / 2 : ℝ) := by
    calc
      2 * (L : ℝ) ≤
          (L : ℝ) ^ (1 / 2 : ℝ) * (L : ℝ) := by
        gcongr
      _ =
          (L : ℝ) ^ ((1 / 2 : ℝ) + 1) := by
        calc
          (L : ℝ) ^ (1 / 2 : ℝ) * (L : ℝ) =
              (L : ℝ) ^ (1 / 2 : ℝ) *
                (L : ℝ) ^ (1 : ℝ) := by
            rw [Real.rpow_one]
          _ = (L : ℝ) ^ ((1 / 2 : ℝ) + 1) :=
            (Real.rpow_add hLpos _ _).symm
      _ = (L : ℝ) ^ (3 / 2 : ℝ) := by
        congr 1
        norm_num
  exact htarget

/--
Lemma 15.1 at the concrete linear cutoff needed to overlap the polynomial
band.  Its mass tends to zero under exactly the external PNT statement.
-/
theorem lowZoneLinearProbabilityMass_tendsto_zero
    (hpnt : PrimeNumberTheoremInput.PrimeNumberTheoremStatement) :
    Tendsto
      (fun L : ℕ ↦
        LowZoneCritical.lowZoneProbabilityMass L (2 * L))
      atTop (𝓝 0) := by
  have hlittle :=
    LowZoneCritical.lowZoneProbabilityMass_uniformLittleOOne_power
      (ε := (1 / 2 : ℝ)) hpnt
  obtain ⟨Ladmissible, hadmissible⟩ :=
    two_mul_runLength_lowZonePowerAdmissible_eventually
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨Llittle, hlittleEventually⟩ :=
    hlittle (ε / 2) (by positivity)
  refine ⟨max Ladmissible Llittle, ?_⟩
  intro L hL
  have hLadmissible : Ladmissible ≤ L :=
    (le_max_left Ladmissible Llittle).trans hL
  have hLlittle : Llittle ≤ L :=
    (le_max_right Ladmissible Llittle).trans hL
  have hbound :=
    hlittleEventually L hLlittle (2 * L)
      (hadmissible L hLadmissible)
  simp only [sub_zero, abs_one, mul_one] at hbound
  rw [Real.dist_eq, sub_zero]
  calc
    |LowZoneCritical.lowZoneProbabilityMass L (2 * L)| ≤
        ε / 2 := hbound
    _ < ε := by linarith

/-- The two low pieces in the proof of Proposition 15.5. -/
noncomputable def lowPolynomialRemainder (L : ℕ) : ℝ :=
  LowZoneCritical.lowZoneProbabilityMass L (2 * L) +
    PolynomialZoneSum.polynomialZoneProbabilityMass L

/--
The complete low-plus-polynomial remainder tends to zero under precisely
the PNT and Laishram--Shorey source statements.
-/
theorem lowPolynomialRemainder_tendsto_zero
    (hLS : LaishramShoreyInput.LaishramShoreyStatement)
    (hpnt : PrimeNumberTheoremInput.PrimeNumberTheoremStatement) :
    Tendsto lowPolynomialRemainder atTop (𝓝 0) := by
  unfold lowPolynomialRemainder
  simpa only [add_zero] using
    (lowZoneLinearProbabilityMass_tendsto_zero hpnt).add
      (PolynomialZoneSum.polynomialZoneProbabilityMass_tendsto_zero
        hLS hpnt)

/-- Uniform critical-window form of the low-zone remainder. -/
theorem lowPolynomialRemainder_uniformLittleOOne
    {C : ℝ} (hC : 0 ≤ C)
    (hLS : LaishramShoreyInput.LaishramShoreyStatement)
    (hpnt : PrimeNumberTheoremInput.PrimeNumberTheoremStatement) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun _ L ↦ lowPolynomialRemainder L)
      (fun _ _ ↦ 1) :=
  uniformLittleOOn_runLength_of_tendsto_zero hC
    (lowPolynomialRemainder_tendsto_zero hLS hpnt)

/-- Literal probability mass of all starts in the low range
`2 ≤ x ≤ 2L²`. -/
noncomputable def lowHeightProbabilityMass (L : ℕ) : ℝ :=
  ∑ x ∈ Finset.Icc 2 (2 * L ^ 2),
    PropositionFifteenFive.globalStartProbability L x

/--
For `L ≥ 3`, the low range is covered by the overlapping union of the
linear Lemma-15.1 cutoff and the complete Lemma-15.2 band.
-/
theorem lowHeightProbabilityMass_le_lowPolynomialRemainder
    {L : ℕ} (hL : 3 ≤ L) :
    lowHeightProbabilityMass L ≤ lowPolynomialRemainder L := by
  classical
  let target := Finset.Icc 2 (2 * L ^ 2)
  let low := LowZoneCritical.lowZoneStarts (2 * L)
  let polynomial := PolynomialZoneSum.polynomialZoneStarts L
  let probability : ℕ → ℝ :=
    fun x ↦ PropositionFifteenFive.globalStartProbability L x
  have hcover : target ⊆ low ∪ polynomial := by
    intro x hx
    have hxTarget : 2 ≤ x ∧ x ≤ 2 * L ^ 2 := by
      simpa only [target, Finset.mem_Icc] using hx
    by_cases hxLow : x ≤ 2 * L
    · apply Finset.mem_union_left
      simpa only [low, LowZoneCritical.mem_lowZoneStarts] using
        ⟨hxTarget.1, hxLow⟩
    · apply Finset.mem_union_right
      rw [PolynomialZoneSum.mem_polynomialZoneStarts]
      constructor
      · have hcoverGap : L + 2 ≤ 2 * L := by omega
        omega
      · exact hxTarget.2
  have hnonneg (x : ℕ) : 0 ≤ probability x :=
    PropositionFifteenFive.globalStartProbability_nonneg L x
  have htarget :
      (∑ x ∈ target, probability x) ≤
        ∑ x ∈ low ∪ polynomial, probability x :=
    Finset.sum_le_sum_of_subset_of_nonneg hcover
      (fun x _ _ ↦ hnonneg x)
  have hunion :
      (∑ x ∈ low ∪ polynomial, probability x) ≤
        (∑ x ∈ low, probability x) +
          ∑ x ∈ polynomial, probability x := by
    rw [show low ∪ polynomial = low ∪ (polynomial \ low) by
      ext x
      simp]
    rw [Finset.sum_union Finset.disjoint_sdiff]
    exact add_le_add_right
      (Finset.sum_le_sum_of_subset_of_nonneg
        Finset.sdiff_subset (fun x _ _ ↦ hnonneg x)) _
  have hlow :
      (∑ x ∈ low, probability x) =
        LowZoneCritical.lowZoneProbabilityMass L (2 * L) := by
    simp only [low, probability,
      PropositionFifteenFive.globalStartProbability,
      LowZoneCritical.lowZoneProbabilityMass,
      LowZoneCritical.lowZoneProbabilityMassQ]
    push_cast
    rfl
  have hpolynomial :
      (∑ x ∈ polynomial, probability x) =
        PolynomialZoneSum.polynomialZoneProbabilityMass L := by
    simp only [polynomial, probability,
      PropositionFifteenFive.globalStartProbability,
      PolynomialZoneSum.polynomialZoneProbabilityMass,
      PolynomialZoneSum.polynomialZoneProbabilityMassQ]
    push_cast
    rfl
  unfold lowHeightProbabilityMass lowPolynomialRemainder
  change (∑ x ∈ target, probability x) ≤ _
  calc
    (∑ x ∈ target, probability x) ≤
        ∑ x ∈ low ∪ polynomial, probability x := htarget
    _ ≤
        (∑ x ∈ low, probability x) +
          ∑ x ∈ polynomial, probability x := hunion
    _ =
        LowZoneCritical.lowZoneProbabilityMass L (2 * L) +
          PolynomialZoneSum.polynomialZoneProbabilityMass L := by
      rw [hlow, hpolynomial]

/--
Concrete closure criterion for Proposition 15.5.

Once the finite dyadic decomposition bounds the literal deep-start mass by a
uniform `o_M(1)` remainder plus `D 2⁻ʲ⁰`, the manuscript's ordered double
limit follows with no further probabilistic input.
-/
theorem proposition_fifteen_five_of_uniformLittleO_remainder
    {C D : ℝ}
    (hD : 0 ≤ D)
    {remainder : ℕ → ℕ → ℝ}
    (hmass_le :
      ∀ M L j₀,
        CriticalRunWindow.InRunLengthWindow C M L →
        deepStartProbabilityMass M L j₀ ≤
          remainder M L + D * (1 / 2 : ℝ) ^ j₀)
    (hremainder :
      UniformLittleOOn
        (CriticalRunWindow.InRunLengthWindow C)
        remainder (fun _ _ => 1)) :
    PropositionFifteenFiveStatement C := by
  exact
    deepTruncationDoubleLimit_of_uniformLittleO_remainder
      hD
      (fun M L j₀ _ ↦ deepStartProbabilityMass_nonneg M L j₀)
      hmass_le hremainder

/--
Eventual version of the concrete closure criterion.  This is the form used
after the critical-window thresholds for Lemmas 15.3 and 15.4 have been
chosen: the finite prefix in `M` is irrelevant to the ordered double limit.
-/
theorem proposition_fifteen_five_of_eventual_uniformLittleO_remainder
    {C D : ℝ}
    (hD : 0 ≤ D)
    {remainder : ℕ → ℕ → ℝ}
    (hmass_le :
      ∃ Mbound : ℕ, ∀ M ≥ Mbound, ∀ L j₀,
        CriticalRunWindow.InRunLengthWindow C M L →
        deepStartProbabilityMass M L j₀ ≤
          remainder M L + D * (1 / 2 : ℝ) ^ j₀)
    (hremainder :
      UniformLittleOOn
        (CriticalRunWindow.InRunLengthWindow C)
        remainder (fun _ _ => 1)) :
    PropositionFifteenFiveStatement C := by
  obtain ⟨Mbound, hmassEventually⟩ := hmass_le
  intro ε hε
  have hdyadic :
      Tendsto (fun j₀ : ℕ => D * (1 / 2 : ℝ) ^ j₀)
        atTop (𝓝 0) := by
    simpa using
      tendsto_const_nhds.mul
        (tendsto_pow_atTop_nhds_zero_of_lt_one
          (by norm_num : 0 ≤ (1 / 2 : ℝ))
          (by norm_num : (1 / 2 : ℝ) < 1))
  obtain ⟨J₀, hJ₀⟩ :=
    Metric.tendsto_atTop.mp hdyadic (ε / 2) (by positivity)
  refine ⟨J₀, ?_⟩
  intro j₀ hj₀
  obtain ⟨Mrem, hremEventually⟩ :=
    hremainder (ε / 2) (by positivity)
  refine ⟨max Mbound Mrem, ?_⟩
  intro M hM L hrun
  have hmass :=
    hmassEventually M
      ((le_max_left Mbound Mrem).trans hM)
      L j₀ hrun
  have hrem :
      |remainder M L| ≤ ε / 2 := by
    simpa using
      hremEventually M
        ((le_max_right Mbound Mrem).trans hM)
        L hrun
  have htailDist :
      dist (D * (1 / 2 : ℝ) ^ j₀) 0 < ε / 2 :=
    hJ₀ j₀ hj₀
  have htailNonneg :
      0 ≤ D * (1 / 2 : ℝ) ^ j₀ :=
    mul_nonneg hD (by positivity)
  have htail :
      D * (1 / 2 : ℝ) ^ j₀ ≤ ε / 2 := by
    rw [Real.dist_eq] at htailDist
    calc
      D * (1 / 2 : ℝ) ^ j₀ =
          |D * (1 / 2 : ℝ) ^ j₀| :=
        (abs_of_nonneg htailNonneg).symm
      _ ≤ ε / 2 := by simpa using htailDist.le
  rw [abs_of_nonneg (deepStartProbabilityMass_nonneg M L j₀)]
  calc
    deepStartProbabilityMass M L j₀ ≤
        remainder M L + D * (1 / 2 : ℝ) ^ j₀ := hmass
    _ ≤
        |remainder M L| + D * (1 / 2 : ℝ) ^ j₀ := by
      gcongr
      exact le_abs_self (remainder M L)
    _ ≤ ε / 2 + ε / 2 := add_le_add hrem htail
    _ = ε := by ring

/--
Finite dyadic tails have the exact geometric bound used in the
`O(2⁻ʲ⁰)` term of Proposition 15.5.
-/
theorem finite_dyadic_tail_le (J j₀ : ℕ) :
    (∑ k ∈ Finset.range J, (1 / 2 : ℝ) ^ (j₀ + k)) ≤
      2 * (1 / 2 : ℝ) ^ j₀ := by
  calc
    (∑ k ∈ Finset.range J, (1 / 2 : ℝ) ^ (j₀ + k)) =
        (1 / 2 : ℝ) ^ j₀ *
          (∑ k ∈ Finset.range J, (1 / 2 : ℝ) ^ k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [pow_add]
    _ ≤ (1 / 2 : ℝ) ^ j₀ * 2 :=
      mul_le_mul_of_nonneg_left (sum_geometric_two_le J) (by positivity)
    _ = 2 * (1 / 2 : ℝ) ^ j₀ := by ring

/-- The same finite geometric estimate with an explicit nonnegative
manuscript constant. -/
theorem finite_scaled_dyadic_tail_le
    {D : ℝ} (hD : 0 ≤ D) (J j₀ : ℕ) :
    D * (∑ k ∈ Finset.range J, (1 / 2 : ℝ) ^ (j₀ + k)) ≤
      2 * D * (1 / 2 : ℝ) ^ j₀ := by
  calc
    D * (∑ k ∈ Finset.range J, (1 / 2 : ℝ) ^ (j₀ + k)) ≤
        D * (2 * (1 / 2 : ℝ) ^ j₀) :=
      mul_le_mul_of_nonneg_left (finite_dyadic_tail_le J j₀) hD
    _ = 2 * D * (1 / 2 : ℝ) ^ j₀ := by ring

end

end PropositionFifteenFiveClosure
end PaperC
