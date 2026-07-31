import PaperC.Analysis.CriticalWeightedDefect
import PaperC.Asymptotics.RationalPowerLittleO
import PaperC.Asymptotics.TerminalBadStartsCritical
import PaperC.Probability.BadStartMass

/-!
# Terminal bad-start probability mass in the critical window

This file closes Lemma 13.4.  Its finite core contains no new bridge:
at `B = L+1`, `BadStartMass.startDefectIndicesAt` is definitionally the
same filtered set as `StartDefectRank.startDefectIndices`.  The latter is
bounded by the concrete interval defect set, which
`WeightedDefectMass.localCount_positiveDefectValues_eq` identifies exactly
with the local count in `CriticalWeightedDefect.dyadicDefectMass`.

Consequently the weighted terminal defect mass is dominated by the already
certified Proposition 3.2 mass.  Both terms in the finite two-cutoff
decomposition are therefore `o_C(1)` after division by `2^L`.
-/

namespace PaperC
namespace BadStartMassCritical

open scoped BigOperators

open BadStartCount
open TerminalPrimeCutoff

noncomputable section

/-- Natural-valued version of the rational weighted mass in `BadStartMass`. -/
def terminalDefectWeightMassNat
    (N L B : ℕ) : ℕ :=
  ∑ x ∈ dyadicBlock N,
    ((2 : ℕ) ^ (BadStartMass.startDefectIndicesAt B x L).card - 1)

/-- The rational mass is exactly the cast of its natural-valued version. -/
theorem terminalDefectWeightMass_eq_natCast
    (N L B : ℕ) :
    BadStartMass.terminalDefectWeightMass N L B =
      (terminalDefectWeightMassNat N L B : ℚ) := by
  unfold BadStartMass.terminalDefectWeightMass
    terminalDefectWeightMassNat
  push_cast
  rfl

/--
Finite exact bridge from the weighted start-defect mass at `B=L+1` to the
canonical dyadic defect mass of Proposition 3.2.
-/
theorem terminalDefectWeightMassNat_le_dyadicDefectMass
    {N L : ℕ}
    (hN : 2 ≤ N)
    (htwo : 2 * (L + 1) ≤ N) :
    terminalDefectWeightMassNat N L (L + 1) ≤
      CriticalWeightedDefect.dyadicDefectMass N (L + 1) := by
  classical
  let defects :=
    WeightedDefectCounting.positiveDefectValues
      (DefectCounting.smallPrimesUpTo (L + 1)) (3 * N)
  unfold terminalDefectWeightMassNat
    CriticalWeightedDefect.dyadicDefectMass
  dsimp only
  apply Finset.sum_le_sum
  intro x hx
  have hxBlock : x ∈ dyadicBlock N := by
    simpa only [dyadicBlock] using hx
  have hxLower : N ≤ x := (Finset.mem_Ico.mp hx).1
  have hxUpper : x < 2 * N := (Finset.mem_Ico.mp hx).2
  have hxPos : 0 < x := by omega
  have hxThree : x + (L + 1) ≤ 3 * N := by omega
  have hlocal :=
    WeightedDefectMass.localCount_positiveDefectValues_eq
      (H := L + 1) (U := x) (X := 3 * N) hxPos hxThree
  have hindices :
      (BadStartMass.startDefectIndicesAt (L + 1) x L).card ≤
        IntervalDefectAggregation.localCount defects (L + 1) x := by
    calc
      (BadStartMass.startDefectIndicesAt (L + 1) x L).card =
          (Affine.StartDefectRank.startDefectIndices x L).card := by
        rfl
      _ ≤
          (IntervalDefectBound.defectsInInterval (L + 1) x).card :=
        Affine.StartDefectRank.card_startDefectIndices_le
          (by omega)
      _ =
          IntervalDefectAggregation.localCount defects (L + 1) x := by
        simpa only [defects] using hlocal.symm
  exact Nat.sub_le_sub_right
    (Nat.pow_le_pow_right (by norm_num) hindices) 1

/-- Real-cast form of the finite mass bridge. -/
theorem terminalDefectWeightMass_cast_le_dyadicDefectMass
    {N L : ℕ}
    (hN : 2 ≤ N)
    (htwo : 2 * (L + 1) ≤ N) :
    ((BadStartMass.terminalDefectWeightMass N L (L + 1) : ℚ) : ℝ) ≤
      (CriticalWeightedDefect.dyadicDefectMass N (L + 1) : ℝ) := by
  rw [terminalDefectWeightMass_eq_natCast]
  norm_num
  exact_mod_cast
    terminalDefectWeightMassNat_le_dyadicDefectMass hN htwo

/-- Real-valued weighted start-defect mass at the natural base cutoff. -/
noncomputable def terminalDefectWeightMassReal
    (N L : ℕ) : ℝ :=
  ((BadStartMass.terminalDefectWeightMass N L (L + 1) : ℚ) : ℝ)

/--
The weighted mass inherited from Proposition 3.2 has the strong
`N^(1/2+o_C(1))` rate.
-/
theorem terminalDefectWeightMass_uniformHalfPower
    {C : ℝ} (hC : 0 ≤ C) :
    UniformHalfPowerSubpolynomialOn
      (CriticalRunWindow.InRunLengthWindow C)
      terminalDefectWeightMassReal := by
  have hwindowMass :=
    CriticalWeightedDefect.dyadicDefectMass_uniformHalfPower_on_window
      CriticalRunWindow.lowerConstant_pos
      CriticalRunWindow.lowerConstant_lt_upperConstant
  have hmass :
      UniformHalfPowerSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C)
        (fun N L =>
          (CriticalWeightedDefect.dyadicDefectMass N (L + 1) : ℝ)) := by
    obtain ⟨Nwindow, hwindow⟩ :=
      CriticalRunWindow.firstMomentWindow_eventually hC
    intro k hk
    obtain ⟨Nmass, hmass⟩ := hwindowMass k hk
    refine ⟨max Nwindow Nmass, ?_⟩
    intro N hN L hrun
    exact
      hmass N ((le_max_right _ _).trans hN) (L + 1)
        (hwindow N ((le_max_left _ _).trans hN) L hrun).1
  apply UniformHalfPower.mono hmass
  obtain ⟨Nwindow, hwindow⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  obtain ⟨Nadm, hadm⟩ :=
    CriticalWeightedDefect.admissible_eventually
      CriticalRunWindow.lowerConstant_pos
      CriticalRunWindow.lowerConstant_lt_upperConstant
  refine ⟨max Nwindow Nadm, ?_⟩
  intro N hN L hrun
  have hw :=
    hwindow N ((le_max_left _ _).trans hN) L hrun
  have hAdm :=
    hadm N ((le_max_right _ _).trans hN) (L + 1) hw.1
  have htwo : 2 * (L + 1) ≤ N :=
    CriticalWindowParameters.two_mul_H_le_N_of_criticalWindow
      hAdm.1 hAdm.2.2.2.1
  have hfinite :=
    terminalDefectWeightMass_cast_le_dyadicDefectMass
      hAdm.2.1 htwo
  rw [abs_of_nonneg (by
      unfold terminalDefectWeightMassReal
      rw [terminalDefectWeightMass_eq_natCast]
      positivity),
    abs_of_nonneg (by positivity)]
  exact hfinite

/-- The weighted mass is, in particular, `o_C(N)`. -/
theorem terminalDefectWeightMass_uniformLittleOLinear
    {C : ℝ} (hC : 0 ≤ C) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      terminalDefectWeightMassReal
      (fun N _ => (N : ℝ)) := by
  have hhalf :=
    terminalDefectWeightMass_uniformHalfPower hC
  have hrat :
      UniformRationalPowerSubpolynomialOn 1 2
        (CriticalRunWindow.InRunLengthWindow C)
        terminalDefectWeightMassReal := by
    simpa [UniformHalfPowerSubpolynomialOn,
      UniformRationalPowerSubpolynomialOn] using hhalf
  simpa only [pow_one] using
    (UniformRationalPower.littleO_natPower_of_lt
      (p := 1) (q := 2) (r := 1) (by omega) hrat)

/-- The normalized weighted contribution `2 M_B / 2^L`. -/
noncomputable def normalizedTerminalDefectContribution
    (N L : ℕ) : ℝ :=
  2 * terminalDefectWeightMassReal N L / (2 : ℝ) ^ L

/-- The weighted contribution in Lemma 13.4 is uniformly `o_C(1)`. -/
theorem normalizedTerminalDefectContribution_uniformLittleOOne
    {C : ℝ} (hC : 0 ≤ C) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      normalizedTerminalDefectContribution
      (fun _ _ => 1) := by
  have hmass :=
    terminalDefectWeightMass_uniformLittleOLinear hC
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
      (div_pos hε (mul_pos (by norm_num) hbalancePos))
  refine ⟨max Nwindow Nmass, ?_⟩
  intro N hN L hrun
  have hw :=
    hwindow N ((le_max_left _ _).trans hN) L hrun
  have hm :=
    hmassBound N ((le_max_right _ _).trans hN) L hrun
  have hmassNonneg : 0 ≤ terminalDefectWeightMassReal N L := by
    unfold terminalDefectWeightMassReal
    rw [terminalDefectWeightMass_eq_natCast]
    positivity
  have hNnonneg : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have hpowPos : (0 : ℝ) < (2 : ℝ) ^ L := by positivity
  simp only [normalizedTerminalDefectContribution, abs_div, abs_mul,
    abs_of_nonneg hmassNonneg, abs_of_nonneg hNnonneg,
    abs_of_pos hpowPos,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    abs_one, mul_one] at hm ⊢
  calc
    2 * terminalDefectWeightMassReal N L / (2 : ℝ) ^ L ≤
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
    _ = ε := by
      field_simp

/-- Real probability mass of terminal bad starts at the Section 13 cutoff. -/
noncomputable def terminalBadStartProbabilityMass
    (N L : ℕ) : ℝ :=
  ((BadStartMass.startProbabilityMass N L
    (terminalBadStarts N L
      (terminalPrimeCutoff (L + 1))) : ℚ) : ℝ)

/-- The exact real two-cutoff inequality used in Lemma 13.4. -/
theorem terminalBadStartProbabilityMass_le
    {N L : ℕ}
    (hN : 2 ≤ N)
    (hL : 0 < L) :
    terminalBadStartProbabilityMass N L ≤
      normalizedTerminalDefectContribution N L +
        ((terminalBadStarts N L
          (terminalPrimeCutoff (L + 1))).card : ℝ) /
            (2 : ℝ) ^ L := by
  have hBY :
      L + 1 ≤ terminalPrimeCutoff (L + 1) :=
    le_terminalPrimeCutoff (by omega)
  have hfinite :=
    BadStartMass.startProbabilityMass_terminalBadStarts_le_two_cutoffs
      (N := N) (L := L) (B := L + 1)
      (Y := terminalPrimeCutoff (L + 1))
      hN hL le_rfl hBY
  have hcast := (Rat.cast_le (K := ℝ)).2 hfinite
  push_cast at hcast
  simpa only [terminalBadStartProbabilityMass,
    normalizedTerminalDefectContribution,
    terminalDefectWeightMassReal] using hcast

/-- Addition preserves a uniform little-oh bound relative to one. -/
private theorem uniformLittleOOne_add
    {admissible : ℕ → ℕ → Prop}
    {f g : ℕ → ℕ → ℝ}
    (hf : UniformLittleOOn admissible f (fun _ _ => 1))
    (hg : UniformLittleOOn admissible g (fun _ _ => 1)) :
    UniformLittleOOn admissible
      (fun N L => f N L + g N L) (fun _ _ => 1) := by
  intro ε hε
  obtain ⟨Nf, hNf⟩ := hf (ε / 2) (by positivity)
  obtain ⟨Ng, hNg⟩ := hg (ε / 2) (by positivity)
  refine ⟨max Nf Ng, ?_⟩
  intro N hN L hNL
  have hf' := hNf N ((le_max_left _ _).trans hN) L hNL
  have hg' := hNg N ((le_max_right _ _).trans hN) L hNL
  simp only [abs_one, mul_one] at hf' hg' ⊢
  calc
    |f N L + g N L| ≤ |f N L| + |g N L| := abs_add_le _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add hf' hg'
    _ = ε := by ring

/--
Lemma 13.4: the probability mass of terminal bad starts is `o_C(1)`,
uniformly in the literal critical run-length window.
-/
theorem terminalBadStartProbabilityMass_uniformLittleOOne
    {C : ℝ} (hC : 0 ≤ C) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      terminalBadStartProbabilityMass
      (fun _ _ => 1) := by
  let countContribution : ℕ → ℕ → ℝ :=
    fun N L =>
      ((terminalBadStarts N L
        (terminalPrimeCutoff (L + 1))).card : ℝ) /
          (2 : ℝ) ^ L
  have hdefect :=
    normalizedTerminalDefectContribution_uniformLittleOOne hC
  have hcount :
      UniformLittleOOn
        (CriticalRunWindow.InRunLengthWindow C)
        countContribution (fun _ _ => 1) := by
    simpa only [countContribution] using
      TerminalBadStartsCritical.normalized_terminalBadStarts_uniformLittleOOne
        hC
  have hsum :=
    uniformLittleOOne_add hdefect hcount
  obtain ⟨Nwindow, hwindow⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  obtain ⟨Nadm, hadm⟩ :=
    CriticalWeightedDefect.admissible_eventually
      CriticalRunWindow.lowerConstant_pos
      CriticalRunWindow.lowerConstant_lt_upperConstant
  intro ε hε
  obtain ⟨Nsum, hsumBound⟩ := hsum ε hε
  refine ⟨max Nwindow (max Nsum Nadm), ?_⟩
  intro N hN L hrun
  have hw :=
    hwindow N ((le_max_left _ _).trans hN) L hrun
  have hNtail :
      max Nsum Nadm ≤ N :=
    (le_max_right Nwindow (max Nsum Nadm)).trans hN
  have hAdm :=
    hadm N ((le_max_right Nsum Nadm).trans hNtail)
      (L + 1) hw.1
  have hfinite :=
    terminalBadStartProbabilityMass_le
      (N := N) (L := L)
      hAdm.2.1
      hw.2.1
  have hs :=
    hsumBound N ((le_max_left Nsum Nadm).trans hNtail) L hrun
  have hprobNonneg :
      0 ≤ terminalBadStartProbabilityMass N L := by
    unfold terminalBadStartProbabilityMass
    apply Rat.cast_nonneg.mpr
    unfold BadStartMass.startProbabilityMass
    exact Finset.sum_nonneg fun x _ ↦
      BadStartMass.startProbability_nonneg N L x
  have hdefectNonneg :
      0 ≤ normalizedTerminalDefectContribution N L := by
    unfold normalizedTerminalDefectContribution terminalDefectWeightMassReal
    rw [terminalDefectWeightMass_eq_natCast]
    positivity
  have hcountNonneg : 0 ≤ countContribution N L := by
    dsimp only [countContribution]
    positivity
  simp only [abs_of_nonneg hprobNonneg, abs_one, mul_one] at hs ⊢
  rw [abs_of_nonneg (add_nonneg hdefectNonneg hcountNonneg)] at hs
  exact hfinite.trans hs

end

end BadStartMassCritical
end PaperC
