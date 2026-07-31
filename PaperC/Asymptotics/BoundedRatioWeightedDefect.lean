import PaperC.Asymptotics.BoundedRatioBadStarts
import PaperC.Probability.FiniteCylinderCountTransport

set_option maxHeartbeats 1800000

/-!
# Weighted bad-start defects on bounded-ratio intervals

This module closes the weighted part of Lemma 17.33.  The proof applies the
finite weighted-defect estimate behind Proposition 3.2 directly to the
population `[N,M)`, with ambient cutoff `(κ₀+1)N`.  It does not cover the
interval by separately asymptotic dyadic blocks.

At the base cutoff `B=L+1`, the local defect indices used by the bad-start
probability estimate inject into the canonical local defect set.  The
resulting weighted mass is uniformly `N^(1/2+o_C(1))`; after division by
`2^L` it is uniformly `o(1)`.
-/

namespace PaperC
namespace BoundedRatioWeightedDefect

open scoped BigOperators

open ArratiaGoldsteinGordonInput
open BoundedRatioBadStarts
open BoundedRatioSteinChen
open CriticalWeightedDefect
open FiniteCylinderCountTransport
open PropositionSixteenOne

noncomputable section

/-! ## Finite comparison with Proposition 3.2 -/

/-- Canonical bounded-ratio defect mass with a common ambient cutoff. -/
noncomputable def canonicalBoundedDefectMass
    (N M H X : ℕ) : ℕ :=
  let defects :=
    WeightedDefectCounting.positiveDefectValues
      (DefectCounting.smallPrimesUpTo H) X
  ∑ x ∈ boundedRatioBlock N M,
    (2 ^ IntervalDefectAggregation.localCount defects H x - 1)

/--
The bad-start defect indices at `B=L+1` are bounded pointwise by the
canonical local defect count used in Proposition 3.2.
-/
theorem card_startDefectIndicesAt_le_localCount
    {N M L X x : ℕ}
    (hN : 2 ≤ N)
    (htwo : 2 * (L + 1) ≤ N)
    (hx : x ∈ boundedRatioBlock N M)
    (hxX : x + (L + 1) ≤ X) :
    (BadStartMass.startDefectIndicesAt (L + 1) x L).card ≤
      IntervalDefectAggregation.localCount
        (WeightedDefectCounting.positiveDefectValues
          (DefectCounting.smallPrimesUpTo (L + 1)) X)
        (L + 1) x := by
  have hxLower : N ≤ x := (mem_boundedRatioBlock.mp hx).1
  have hxPos : 0 < x := by omega
  have hlocal :=
    WeightedDefectMass.localCount_positiveDefectValues_eq
      (H := L + 1) (U := x) (X := X) hxPos hxX
  calc
    (BadStartMass.startDefectIndicesAt (L + 1) x L).card =
        (Affine.StartDefectRank.startDefectIndices x L).card := by
      rfl
    _ ≤
        (IntervalDefectBound.defectsInInterval (L + 1) x).card :=
      Affine.StartDefectRank.card_startDefectIndices_le
        (by omega)
    _ =
        IntervalDefectAggregation.localCount
          (WeightedDefectCounting.positiveDefectValues
            (DefectCounting.smallPrimesUpTo (L + 1)) X)
          (L + 1) x :=
      hlocal.symm

/-- Finite comparison of the two weighted masses. -/
theorem boundedTerminalDefectWeightMass_le_canonical
    {N M L X : ℕ}
    (hN : 2 ≤ N)
    (htwo : 2 * (L + 1) ≤ N)
    (hupper :
      ∀ x ∈ boundedRatioBlock N M,
        x + (L + 1) ≤ X) :
    boundedTerminalDefectWeightMass N M L (L + 1) ≤
      (canonicalBoundedDefectMass N M (L + 1) X : ℝ) := by
  unfold boundedTerminalDefectWeightMass canonicalBoundedDefectMass
  dsimp only
  rw [Nat.cast_sum]
  apply Finset.sum_le_sum
  intro x hx
  exact_mod_cast
    Nat.sub_le_sub_right
      (Nat.pow_le_pow_right (by norm_num)
        (card_startDefectIndicesAt_le_localCount
          hN htwo hx (hupper x hx)))
      1

/--
Explicit finite Proposition 3.2 envelope for the bounded-ratio population.
-/
theorem canonicalBoundedDefectMass_cast_le
    {c₁ c₂ : ℝ} {N M H X : ℕ}
    (hAdm : CriticalWeightedDefect.Admissible c₁ c₂ N H)
    (hstartUpper :
      ∀ x ∈ boundedRatioBlock N M, x + H ≤ X) :
    (canonicalBoundedDefectMass N M H X : ℝ) ≤
      (H + 1 : ℝ) * Real.sqrt X *
        Real.exp (2 * Real.sqrt H) *
        ((2 ^ (2 *
          RungeLogarithmicGrowth.cappedRadius N H
            (CriticalWindowParameters.logarithmicCap N) *
          2 ^ (CriticalWindowParameters.codingConstant c₁ c₂ + 1)) :
            ℕ) : ℝ) := by
  have hfinite :=
    CriticalWindowParameters.sum_two_pow_localCount_sub_one_cast_le_of_criticalWindow
      (c₁ := c₁) (c₂ := c₂) (N := N) (H := H) (X := X)
      (boundedRatioBlock N M)
      hAdm.1 hAdm.2.1 hAdm.2.2.1 hAdm.2.2.2.1
      (fun x hx ↦ (mem_boundedRatioBlock.mp hx).1)
      hstartUpper hAdm.2.2.2.2
  simpa only [canonicalBoundedDefectMass] using hfinite

/-! ## A uniform half-power envelope -/

/-- Residual factor after extracting `sqrt N`. -/
noncomputable def boundedWeightedDefectResidual
    (c₁ c₂ : ℝ) (κ₀ N H : ℕ) : ℝ :=
  Real.sqrt (κ₀ + 1) *
    CriticalWeightedDefect.residualFactor c₁ c₂ N H

theorem boundedWeightedDefectResidual_uniformSubpolynomialOnAdmissible
    {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₁c₂ : c₁ < c₂)
    (κ₀ : ℕ) :
    UniformSubpolynomialOn
      (CriticalWeightedDefect.Admissible c₁ c₂)
      (boundedWeightedDefectResidual c₁ c₂ κ₀) := by
  unfold boundedWeightedDefectResidual
  exact
    ExpSqrtLog.uniformSubpolynomialOn_const_mul
      (Real.sqrt (κ₀ + 1))
      (CriticalWeightedDefect.residualFactor_uniformSubpolynomial
        hc₁ hc₁c₂)

/--
The residual remains uniformly subpolynomial in the literal run-length
window after the technical admissibility thresholds are eliminated.
-/
theorem boundedWeightedDefectResidual_uniformSubpolynomial
    {C : ℝ} (hC : 0 ≤ C) (κ₀ : ℕ) :
    UniformSubpolynomialOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun N L ↦
        boundedWeightedDefectResidual
          CriticalRunWindow.lowerConstant
          CriticalRunWindow.upperConstant κ₀ N (L + 1)) := by
  have hres :=
    boundedWeightedDefectResidual_uniformSubpolynomialOnAdmissible
      CriticalRunWindow.lowerConstant_pos
      CriticalRunWindow.lowerConstant_lt_upperConstant κ₀
  obtain ⟨Nwindow, hwindow⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  obtain ⟨Nadm, hadm⟩ :=
    CriticalWeightedDefect.admissible_eventually
      CriticalRunWindow.lowerConstant_pos
      CriticalRunWindow.lowerConstant_lt_upperConstant
  intro k hk
  obtain ⟨Nres, hresBound⟩ := hres k hk
  refine ⟨max Nwindow (max Nadm Nres), ?_⟩
  intro N hN L hrun
  have htail :
      max Nadm Nres ≤ N :=
    (le_max_right Nwindow (max Nadm Nres)).trans hN
  have hw :=
    hwindow N ((le_max_left _ _).trans hN) L hrun
  exact
    hresBound N ((le_max_right Nadm Nres).trans htail) (L + 1)
      (hadm N ((le_max_left Nadm Nres).trans htail)
        (L + 1) hw.1)

/-- A two-parameter envelope uniform in the endpoint `M`. -/
noncomputable def boundedWeightedDefectEnvelope
    (C : ℝ) (κ₀ N L : ℕ) : ℝ :=
  Real.sqrt N *
    boundedWeightedDefectResidual
      CriticalRunWindow.lowerConstant
      CriticalRunWindow.upperConstant κ₀ N (L + 1)

theorem boundedWeightedDefectEnvelope_uniformHalfPower
    {C : ℝ} (hC : 0 ≤ C) (κ₀ : ℕ) :
    UniformHalfPowerSubpolynomialOn
      (CriticalRunWindow.InRunLengthWindow C)
      (boundedWeightedDefectEnvelope C κ₀) := by
  apply UniformHalfPower.of_sqrt_mul_subpolynomial
    (boundedWeightedDefectResidual_uniformSubpolynomial hC κ₀)
  refine ⟨0, ?_⟩
  intro N _hN L _hrun
  unfold boundedWeightedDefectEnvelope
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]

/--
Eventually the literal weighted mass is dominated by the uniform
half-power envelope.
-/
theorem boundedTerminalDefectWeightMass_le_envelope
    {C : ℝ} (hC : 0 ≤ C) (κ₀ : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ M L,
      2 * N ≤ M →
      M ≤ κ₀ * N →
      CriticalRunWindow.InRunLengthWindow C N L →
      boundedTerminalDefectWeightMass N M L (L + 1) ≤
        boundedWeightedDefectEnvelope C κ₀ N L := by
  obtain ⟨Nwindow, hwindow⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  obtain ⟨Nadm, hadm⟩ :=
    CriticalWeightedDefect.admissible_eventually
      CriticalRunWindow.lowerConstant_pos
      CriticalRunWindow.lowerConstant_lt_upperConstant
  refine ⟨max Nwindow Nadm, ?_⟩
  intro N hN M L _hNM hMκ hrun
  have hw :=
    hwindow N ((le_max_left _ _).trans hN) L hrun
  have hAdm :=
    hadm N ((le_max_right _ _).trans hN) (L + 1) hw.1
  have htwo :
      2 * (L + 1) ≤ N :=
    CriticalWindowParameters.two_mul_H_le_N_of_criticalWindow
      hAdm.1 hAdm.2.2.2.1
  let X := (κ₀ + 1) * N
  have hupper :
      ∀ x ∈ boundedRatioBlock N M,
        x + (L + 1) ≤ X := by
    intro x hx
    have hxM := (mem_boundedRatioBlock.mp hx).2
    dsimp only [X]
    calc
      x + (L + 1) ≤ M + (L + 1) := by omega
      _ ≤ κ₀ * N + N := Nat.add_le_add hMκ (by omega)
      _ = (κ₀ + 1) * N := by
        simp only [Nat.add_mul, one_mul]
  have hcompare :=
    boundedTerminalDefectWeightMass_le_canonical
      hAdm.2.1 htwo hupper
  have hfinite :=
    canonicalBoundedDefectMass_cast_le hAdm hupper
  have hsqrtX :
      Real.sqrt X ≤
        Real.sqrt (κ₀ + 1) * Real.sqrt N := by
    dsimp only [X]
    rw [Nat.cast_mul,
      Real.sqrt_mul (Nat.cast_nonneg (κ₀ + 1))]
    norm_num only [Nat.cast_add, Nat.cast_one]
    exact le_rfl
  have hrestNonneg :
      0 ≤
        (L + 2 : ℝ) *
          Real.exp (2 * Real.sqrt (L + 1)) *
          ((2 ^ (2 *
            RungeLogarithmicGrowth.cappedRadius N (L + 1)
              (CriticalWindowParameters.logarithmicCap N) *
            2 ^ (CriticalWindowParameters.codingConstant
              CriticalRunWindow.lowerConstant
              CriticalRunWindow.upperConstant + 1)) : ℕ) : ℝ) := by
    positivity
  calc
    boundedTerminalDefectWeightMass N M L (L + 1) ≤
        (canonicalBoundedDefectMass N M (L + 1) X : ℝ) :=
      hcompare
    _ ≤
        (L + 2 : ℝ) * Real.sqrt X *
          Real.exp (2 * Real.sqrt (L + 1)) *
          ((2 ^ (2 *
            RungeLogarithmicGrowth.cappedRadius N (L + 1)
              (CriticalWindowParameters.logarithmicCap N) *
            2 ^ (CriticalWindowParameters.codingConstant
              CriticalRunWindow.lowerConstant
              CriticalRunWindow.upperConstant + 1)) : ℕ) : ℝ) :=
      by
        convert hfinite using 1 <;>
          norm_num only [Nat.cast_add, Nat.cast_one] <;>
          ring
    _ ≤
        (L + 2 : ℝ) *
          (Real.sqrt (κ₀ + 1) * Real.sqrt N) *
          Real.exp (2 * Real.sqrt (L + 1)) *
          ((2 ^ (2 *
            RungeLogarithmicGrowth.cappedRadius N (L + 1)
              (CriticalWindowParameters.logarithmicCap N) *
            2 ^ (CriticalWindowParameters.codingConstant
              CriticalRunWindow.lowerConstant
              CriticalRunWindow.upperConstant + 1)) : ℕ) : ℝ) := by
      gcongr
    _ ≤ boundedWeightedDefectEnvelope C κ₀ N L := by
      unfold boundedWeightedDefectEnvelope
        boundedWeightedDefectResidual
        CriticalWeightedDefect.residualFactor
      norm_num only [Nat.cast_add, Nat.cast_one]
      have hsqrtThree : 1 ≤ Real.sqrt 3 := by
        nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
          Real.sqrt_nonneg 3]
      calc
        (L + 2 : ℝ) *
              (Real.sqrt (κ₀ + 1) * Real.sqrt N) *
              Real.exp (2 * Real.sqrt (L + 1)) *
              ((2 ^ (2 *
                RungeLogarithmicGrowth.cappedRadius N (L + 1)
                  (CriticalWindowParameters.logarithmicCap N) *
                2 ^ (CriticalWindowParameters.codingConstant
                  CriticalRunWindow.lowerConstant
                  CriticalRunWindow.upperConstant + 1)) : ℕ) : ℝ) =
            Real.sqrt N *
              (Real.sqrt (κ₀ + 1) *
                ((L + 2 : ℝ) *
                  Real.exp (2 * Real.sqrt (L + 1)) *
                  ((2 ^ (2 *
                    RungeLogarithmicGrowth.cappedRadius N (L + 1)
                      (CriticalWindowParameters.logarithmicCap N) *
                    2 ^ (CriticalWindowParameters.codingConstant
                      CriticalRunWindow.lowerConstant
                      CriticalRunWindow.upperConstant + 1)) :
                        ℕ) : ℝ))) := by ring
        _ ≤
            Real.sqrt N *
              (Real.sqrt (κ₀ + 1) *
                ((L + 2 : ℝ) * Real.sqrt 3 *
                  Real.exp (2 * Real.sqrt (L + 1)) *
                  ((2 ^ (2 *
                    RungeLogarithmicGrowth.cappedRadius N (L + 1)
                      (CriticalWindowParameters.logarithmicCap N) *
                    2 ^ (CriticalWindowParameters.codingConstant
                      CriticalRunWindow.lowerConstant
                      CriticalRunWindow.upperConstant + 1)) :
                        ℕ) : ℝ))) := by
          gcongr
          nlinarith [hsqrtThree]
        _ = _ := by ring

/-! ## Uniform consequences -/

theorem boundedTerminalDefectWeightMass_uniformHalfPower
    {C : ℝ} (hC : 0 ≤ C) (κ₀ : ℕ) :
    UniformHalfPowerSubpolynomialInBoundedRatioWindow C κ₀
      (fun N M L ↦
        boundedTerminalDefectWeightMass N M L (L + 1)) := by
  have hEnvelope :=
    boundedWeightedDefectEnvelope_uniformHalfPower hC κ₀
  obtain ⟨Nbound, hbound⟩ :=
    boundedTerminalDefectWeightMass_le_envelope hC κ₀
  intro k hk
  obtain ⟨Nhalf, hhalf⟩ := hEnvelope k hk
  refine ⟨max Nbound Nhalf, ?_⟩
  intro N hN M L hNM hMκ hrun
  have hb :=
    hbound N ((le_max_left _ _).trans hN) M L hNM hMκ hrun
  have hh :=
    hhalf N ((le_max_right _ _).trans hN) L hrun
  have hmassNonneg :
      0 ≤ boundedTerminalDefectWeightMass N M L (L + 1) := by
    unfold boundedTerminalDefectWeightMass
    positivity
  have hEnvelopeNonneg :
      0 ≤ boundedWeightedDefectEnvelope C κ₀ N L := by
    unfold boundedWeightedDefectEnvelope
      boundedWeightedDefectResidual
      CriticalWeightedDefect.residualFactor
    positivity
  rw [abs_of_nonneg hEnvelopeNonneg] at hh
  rw [abs_of_nonneg hmassNonneg]
  exact (pow_le_pow_left₀ hmassNonneg hb _).trans hh

/-- The weighted base-defect mass is uniformly `o(N)`. -/
theorem boundedTerminalDefectWeightMass_uniformLittleOLinear
    {C : ℝ} (hC : 0 ≤ C) (κ₀ : ℕ) :
    UniformLittleOLinearInBoundedRatioWindow C κ₀
      (fun N M L ↦
        boundedTerminalDefectWeightMass N M L (L + 1)) := by
  have hEnvelopeHalf :=
    boundedWeightedDefectEnvelope_uniformHalfPower hC κ₀
  have hEnvelopeRational :
      UniformRationalPowerSubpolynomialOn 1 2
        (CriticalRunWindow.InRunLengthWindow C)
        (boundedWeightedDefectEnvelope C κ₀) := by
    simpa [UniformHalfPowerSubpolynomialOn,
      UniformRationalPowerSubpolynomialOn] using hEnvelopeHalf
  have hEnvelopeLinear :
      UniformLittleOOn
        (CriticalRunWindow.InRunLengthWindow C)
        (boundedWeightedDefectEnvelope C κ₀)
        (fun N _ ↦ (N : ℝ)) := by
    simpa only [pow_one] using
      (UniformRationalPower.littleO_natPower_of_lt
        (p := 1) (q := 2) (r := 1) (by omega) hEnvelopeRational)
  obtain ⟨Nbound, hbound⟩ :=
    boundedTerminalDefectWeightMass_le_envelope hC κ₀
  intro ε hε
  obtain ⟨Nlinear, hlinear⟩ := hEnvelopeLinear ε hε
  refine ⟨max Nbound Nlinear, ?_⟩
  intro N hN M L hNM hMκ hrun
  have hb :=
    hbound N ((le_max_left _ _).trans hN) M L hNM hMκ hrun
  have hl :=
    hlinear N ((le_max_right _ _).trans hN) L hrun
  have hmassNonneg :
      0 ≤ boundedTerminalDefectWeightMass N M L (L + 1) := by
    unfold boundedTerminalDefectWeightMass
    positivity
  have hEnvelopeNonneg :
      0 ≤ boundedWeightedDefectEnvelope C κ₀ N L := by
    unfold boundedWeightedDefectEnvelope
      boundedWeightedDefectResidual
      CriticalWeightedDefect.residualFactor
    positivity
  rw [abs_of_nonneg hEnvelopeNonneg] at hl
  rw [abs_of_nonneg hmassNonneg]
  exact hb.trans hl

/-- The normalized weighted contribution in Lemma 17.34 is `o(1)`. -/
theorem normalized_boundedTerminalDefectWeightMass_uniformLittleOOne
    {C : ℝ} (hC : 0 ≤ C) (κ₀ : ℕ) :
    UniformLittleOOneInBoundedRatioWindow C κ₀
      (fun N M L ↦
        2 * boundedTerminalDefectWeightMass N M L (L + 1) /
          (2 : ℝ) ^ L) := by
  have hmass :=
    boundedTerminalDefectWeightMass_uniformLittleOLinear hC κ₀
  have hbalancePos :
      0 < CriticalRunWindow.balanceConstant C := by
    unfold CriticalRunWindow.balanceConstant
    positivity
  obtain ⟨Nwindow, hwindow⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  intro ε hε
  obtain ⟨Nmass, hmassBound⟩ :=
    hmass
      (ε / (2 * CriticalRunWindow.balanceConstant C))
      (by positivity)
  refine ⟨max Nwindow Nmass, ?_⟩
  intro N hN M L hNM hMκ hrun
  have hw :=
    hwindow N ((le_max_left _ _).trans hN) L hrun
  have hm :=
    hmassBound N ((le_max_right _ _).trans hN)
      M L hNM hMκ hrun
  have hmassNonneg :
      0 ≤ boundedTerminalDefectWeightMass N M L (L + 1) := by
    unfold boundedTerminalDefectWeightMass
    positivity
  have hNnonneg : (0 : ℝ) ≤ N := by positivity
  have hpowPos : (0 : ℝ) < (2 : ℝ) ^ L := by positivity
  simp only [abs_of_nonneg hmassNonneg,
    abs_of_nonneg hNnonneg] at hm
  rw [abs_of_nonneg (by positivity :
    0 ≤ 2 * boundedTerminalDefectWeightMass N M L (L + 1) /
      (2 : ℝ) ^ L)]
  calc
    2 * boundedTerminalDefectWeightMass N M L (L + 1) /
          (2 : ℝ) ^ L ≤
        2 *
          ((ε / (2 * CriticalRunWindow.balanceConstant C)) *
            (N : ℝ)) /
          (2 : ℝ) ^ L := by
      gcongr
    _ =
        (ε / CriticalRunWindow.balanceConstant C) *
          ((N : ℝ) / (2 : ℝ) ^ L) := by ring
    _ ≤
        (ε / CriticalRunWindow.balanceConstant C) *
          CriticalRunWindow.balanceConstant C :=
      mul_le_mul_of_nonneg_left hw.2.2
        (div_nonneg hε.le hbalancePos.le)
    _ = ε := by field_simp

/--
Lemma 17.34, probability-mass part: the total probability mass of terminal
bad starts is uniformly `o(1)` on every bounded-ratio critical window.
-/
theorem boundedBadStartProbabilityMass_uniformLittleOOne
    {C : ℝ} (hC : 0 ≤ C) (κ₀ : ℕ) :
    UniformLittleOOneInBoundedRatioWindow C κ₀
      (fun N M L ↦
        boundedBadStartProbabilityMass N M L
          (TerminalPrimeCutoff.terminalPrimeCutoff (L + 1))) := by
  have hdefect :=
    normalized_boundedTerminalDefectWeightMass_uniformLittleOOne hC κ₀
  have hcard :=
    normalized_boundedTerminalBadStarts_uniformLittleOOne hC κ₀
  obtain ⟨Nwindow, hwindow⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  intro ε hε
  obtain ⟨Ndefect, hdefectBound⟩ :=
    hdefect (ε / 2) (by positivity)
  obtain ⟨Ncard, hcardBound⟩ :=
    hcard (ε / 2) (by positivity)
  refine
    ⟨max 2 (max Nwindow (max Ndefect Ncard)), ?_⟩
  intro N hN M L hNM hMκ hrun
  have hNtwo : 2 ≤ N :=
    (le_max_left 2
      (max Nwindow (max Ndefect Ncard))).trans hN
  have htail :
      max Nwindow (max Ndefect Ncard) ≤ N :=
    (le_max_right 2
      (max Nwindow (max Ndefect Ncard))).trans hN
  have hw :=
    hwindow N ((le_max_left _ _).trans htail) L hrun
  have hLpos : 0 < L := hw.2.1
  have htail' :
      max Ndefect Ncard ≤ N :=
    (le_max_right Nwindow (max Ndefect Ncard)).trans htail
  have hd :=
    hdefectBound N ((le_max_left _ _).trans htail')
      M L hNM hMκ hrun
  have hc :=
    hcardBound N ((le_max_right _ _).trans htail')
      M L hNM hMκ hrun
  have hfinite :=
    boundedBadStartProbabilityMass_le_two_cutoffs
      (N := N) (M := M) (L := L)
      (B := L + 1)
      (Y := TerminalPrimeCutoff.terminalPrimeCutoff (L + 1))
      hNtwo hw.2.1 le_rfl
      (TerminalPrimeCutoff.le_terminalPrimeCutoff
        (show 2 ≤ L + 1 by omega))
  have hmassNonneg :
      0 ≤
        boundedBadStartProbabilityMass N M L
          (TerminalPrimeCutoff.terminalPrimeCutoff (L + 1)) := by
    unfold boundedBadStartProbabilityMass boundedStartProbability
    exact Finset.sum_nonneg fun x _hx ↦
      eventProbability_nonneg _ _
  have hdefectNonneg :
      0 ≤
        2 * boundedTerminalDefectWeightMass N M L (L + 1) /
          (2 : ℝ) ^ L := by
    have hweightNonneg :
        0 ≤ boundedTerminalDefectWeightMass N M L (L + 1) := by
      unfold boundedTerminalDefectWeightMass
      positivity
    exact div_nonneg
      (mul_nonneg (by norm_num) hweightNonneg) (by positivity)
  have hcardNonneg :
      0 ≤
        ((boundedTerminalBadStarts N M L
          (TerminalPrimeCutoff.terminalPrimeCutoff
            (L + 1))).card : ℝ) /
          (2 : ℝ) ^ L := by
    exact div_nonneg (by positivity) (by positivity)
  rw [abs_of_nonneg hmassNonneg]
  rw [abs_of_nonneg hdefectNonneg] at hd
  rw [abs_of_nonneg hcardNonneg] at hc
  calc
    boundedBadStartProbabilityMass N M L
          (TerminalPrimeCutoff.terminalPrimeCutoff (L + 1)) ≤
        2 * boundedTerminalDefectWeightMass N M L (L + 1) /
            (2 : ℝ) ^ L +
          ((boundedTerminalBadStarts N M L
            (TerminalPrimeCutoff.terminalPrimeCutoff
              (L + 1))).card : ℝ) /
            (2 : ℝ) ^ L :=
      hfinite
    _ ≤ ε / 2 + ε / 2 := add_le_add hd hc
    _ = ε := by ring

end

end BoundedRatioWeightedDefect
end PaperC
