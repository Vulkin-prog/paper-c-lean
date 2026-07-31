import PaperC.Asymptotics.BadStartMassCritical
import PaperC.Probability.ExactLengthBadStartMass
import PaperC.Probability.InfiniteExactLengthProbabilityTransfer

set_option maxHeartbeats 1800000

/-!
# Removed exact-length starts in the critical window

This file closes the asymptotic summation in Lemma 14.7.

For fixed maximal excess `E`, put

`qₑ = L + e + 1`, `Q = L + E + 1`, and `W = Q + 1`.

The finite theorem in `ExactLengthBadStartMass` gives

`sum_{e=0}^E sum_{x in D(Q)} P(K_{x,e}=1)
  ≤ (E+1) (2 M_W(N,Q) + #D(Q)) / 2^(L+1)`.

Since `Q = (L+1)+E`, the right-hand side is

`(E+1) 2^E
  (2 M_W(N,Q)/2^Q + #D(Q)/2^Q)`.

Both normalized common-length terms have already been proved uniformly
`o(1)` in `BadStartMassCritical` and `TerminalBadStartsCritical`.  Replacing
`L` by `Q=L+E+1` only enlarges the literal run-length window by the fixed
amount `E+1`.  Hence the full removed mass is uniformly `o_{C,E}(1)`.

All shifts and little-oh quantifiers are explicit.  No asymptotic bridge is
assumed.
-/

namespace PaperC
namespace ExactLengthBadStartMassCritical

open scoped BigOperators

open BadStartCount
open MixedLengthAffine
open ExactLengthBadStartMass
open InfiniteExactLengthProbabilityTransfer
open BadStartMassCritical
open TerminalBadStartsCritical

noncomputable section

/-! ## The fixed shift from `L` to the common row count -/

/--
Adding the fixed row-count shift `E+1` enlarges the literal critical-window
constant by at most `E+1`.
-/
theorem commonExactRowCount_in_runLengthWindow
    {C : ℝ} {N L E : ℕ}
    (hrun : CriticalRunWindow.InRunLengthWindow C N L) :
    CriticalRunWindow.InRunLengthWindow
      (C + (E + 1 : ℕ)) N (commonExactRowCount L E) := by
  unfold CriticalRunWindow.InRunLengthWindow at hrun ⊢
  have hcast :
      ((commonExactRowCount L E : ℕ) : ℝ) -
          Real.log N / Real.log 2 =
        ((L : ℝ) - Real.log N / Real.log 2) + (E + 1 : ℕ) := by
    simp only [commonExactRowCount, excessRowCount]
    push_cast
    ring
  rw [hcast]
  calc
    |(L : ℝ) - Real.log N / Real.log 2 + (E + 1 : ℕ)| ≤
        |(L : ℝ) - Real.log N / Real.log 2| + |((E + 1 : ℕ) : ℝ)| :=
      abs_add _ _
    _ = |(L : ℝ) - Real.log N / Real.log 2| + (E + 1 : ℕ) := by
      congr 1
      exact abs_of_nonneg (Nat.cast_nonneg _)
    _ ≤ C + (E + 1 : ℕ) :=
      add_le_add_right hrun _

/-! ## Common-length normalizations -/

/-- The weighted-defect contribution at the common row count `Q`. -/
def commonNormalizedDefectContribution
    (E N L : ℕ) : ℝ :=
  normalizedTerminalDefectContribution N (commonExactRowCount L E)

/-- The cardinal contribution `#D(Q) / 2^Q`. -/
def commonNormalizedRemovedCountContribution
    (E N L : ℕ) : ℝ :=
  ((removedExactLengthStarts N L E).card : ℝ) /
    (2 : ℝ) ^ commonExactRowCount L E

/--
The common asymptotic envelope.  Its fixed coefficient is exactly the loss
from summing `E+1` marks and replacing `2^(L+1)` by `2^Q`.
-/
def totalRemovedExactLengthEnvelope
    (E N L : ℕ) : ℝ :=
  (E + 1 : ℝ) * (2 : ℝ) ^ E *
    (commonNormalizedDefectContribution E N L +
      commonNormalizedRemovedCountContribution E N L)

/-- Real form of the complete removed exact-length mass. -/
def totalRemovedExactLengthProbabilityMassReal
    (E N L : ℕ) : ℝ :=
  (totalRemovedExactLengthProbabilityMass N L E : ℝ)

/-! ## Finite comparison with the common-length envelope -/

/--
Exact finite reduction of the full removed mass to the two common-length
normalizations.
-/
theorem totalRemovedExactLengthProbabilityMassReal_le_envelope
    {N L E : ℕ}
    (hN : 2 ≤ N) (hL : 1 ≤ L) :
    totalRemovedExactLengthProbabilityMassReal E N L ≤
      totalRemovedExactLengthEnvelope E N L := by
  let Q := commonExactRowCount L E
  let massQ : ℝ :=
    (BadStartMass.terminalDefectWeightMass N Q (Q + 1) : ℝ)
  let countQ : ℝ :=
    ((removedExactLengthStarts N L E).card : ℝ)
  have hQ :
      Q = (L + 1) + E := by
    simp [Q, commonExactRowCount, excessRowCount]
    omega
  have hfinite :=
    totalRemovedExactLengthProbabilityMass_le
      (N := N) (L := L) (E := E) hN hL
  have hcast :
      totalRemovedExactLengthProbabilityMassReal E N L ≤
        (E + 1 : ℝ) * (2 * massQ + countQ) /
          (2 : ℝ) ^ (L + 1) := by
    have hcast' :
        ((totalRemovedExactLengthProbabilityMass N L E : ℚ) : ℝ) ≤
          (((E + 1 : ℚ) *
              (2 * BadStartMass.terminalDefectWeightMass N
                    (commonExactRowCount L E)
                    (exactLengthBaseCutoff L E) +
                (removedExactLengthStarts N L E).card) /
              (2 : ℚ) ^ (L + 1) : ℚ) : ℝ) :=
      Rat.cast_le.mpr hfinite
    push_cast at hcast'
    simpa only [totalRemovedExactLengthProbabilityMassReal, Q, massQ,
      countQ, exactLengthBaseCutoff] using hcast'
  calc
    totalRemovedExactLengthProbabilityMassReal E N L ≤
        (E + 1 : ℝ) * (2 * massQ + countQ) /
          (2 : ℝ) ^ (L + 1) :=
      hcast
    _ =
        (E + 1 : ℝ) * (2 : ℝ) ^ E *
          (commonNormalizedDefectContribution E N L +
            commonNormalizedRemovedCountContribution E N L) := by
      unfold commonNormalizedDefectContribution
        commonNormalizedRemovedCountContribution
        normalizedTerminalDefectContribution
        BadStartMassCritical.terminalDefectWeightMassReal
      have hQ' :
          commonExactRowCount L E = (L + 1) + E := by
        simpa only [Q] using hQ
      simp only [Q, massQ, countQ, exactLengthBaseCutoff]
      rw [hQ', pow_add]
      field_simp
      ring
    _ = totalRemovedExactLengthEnvelope E N L := rfl

/-! ## Uniform little-oh closure -/

/-- Pull back the weighted common-length estimate along `Q = L+E+1`. -/
theorem commonNormalizedDefectContribution_uniformLittleOOne
    {C : ℝ} (hC : 0 ≤ C) (E : ℕ) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (commonNormalizedDefectContribution E)
      (fun _ _ => 1) := by
  have hshiftNonneg :
      0 ≤ C + (E + 1 : ℕ) := by positivity
  have hcore :=
    normalizedTerminalDefectContribution_uniformLittleOOne
      hshiftNonneg
  intro ε hε
  obtain ⟨Ncore, hNcore⟩ := hcore ε hε
  refine ⟨Ncore, ?_⟩
  intro N hN L hrun
  exact
    hNcore N hN (commonExactRowCount L E)
      (commonExactRowCount_in_runLengthWindow hrun)

/-- Pull back the `#D(Q)/2^Q` estimate along `Q = L+E+1`. -/
theorem commonNormalizedRemovedCountContribution_uniformLittleOOne
    {C : ℝ} (hC : 0 ≤ C) (E : ℕ) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (commonNormalizedRemovedCountContribution E)
      (fun _ _ => 1) := by
  have hshiftNonneg :
      0 ≤ C + (E + 1 : ℕ) := by positivity
  have hcore :=
    normalized_terminalBadStarts_uniformLittleOOne hshiftNonneg
  intro ε hε
  obtain ⟨Ncore, hNcore⟩ := hcore ε hε
  refine ⟨Ncore, ?_⟩
  intro N hN L hrun
  have hbound :=
    hNcore N hN (commonExactRowCount L E)
      (commonExactRowCount_in_runLengthWindow hrun)
  simpa only [commonNormalizedRemovedCountContribution,
    removedExactLengthStarts, exactLengthBaseCutoff] using hbound

/-- Addition preserves a uniform little-oh estimate relative to one. -/
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
  intro N hN L hrun
  have hf' := hNf N ((le_max_left _ _).trans hN) L hrun
  have hg' := hNg N ((le_max_right _ _).trans hN) L hrun
  simp only [abs_one, mul_one] at hf' hg' ⊢
  calc
    |f N L + g N L| ≤ |f N L| + |g N L| := abs_add _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add hf' hg'
    _ = ε := by ring

/-- Multiplication by a fixed nonnegative constant preserves `o(1)`. -/
private theorem uniformLittleOOne_const_mul
    {admissible : ℕ → ℕ → Prop}
    {f : ℕ → ℕ → ℝ} (A : ℝ) (hA : 0 ≤ A)
    (hf : UniformLittleOOn admissible f (fun _ _ => 1)) :
    UniformLittleOOn admissible
      (fun N L => A * f N L) (fun _ _ => 1) := by
  by_cases hAzero : A = 0
  · subst A
    simpa using uniformLittleOOn_zero admissible (fun _ _ => 1)
  · have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hAzero)
    intro ε hε
    obtain ⟨Nf, hNf⟩ := hf (ε / A) (div_pos hε hApos)
    refine ⟨Nf, ?_⟩
    intro N hN L hrun
    have hbound := hNf N hN L hrun
    simp only [abs_one, mul_one] at hbound ⊢
    rw [abs_mul, abs_of_nonneg hA]
    calc
      A * |f N L| ≤ A * (ε / A) :=
        mul_le_mul_of_nonneg_left hbound hA
      _ = ε := by field_simp

/-- The common envelope is uniformly `o_{C,E}(1)`. -/
theorem totalRemovedExactLengthEnvelope_uniformLittleOOne
    {C : ℝ} (hC : 0 ≤ C) (E : ℕ) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (totalRemovedExactLengthEnvelope E)
      (fun _ _ => 1) := by
  have hsum :=
    uniformLittleOOne_add
      (commonNormalizedDefectContribution_uniformLittleOOne hC E)
      (commonNormalizedRemovedCountContribution_uniformLittleOOne hC E)
  unfold totalRemovedExactLengthEnvelope
  exact uniformLittleOOne_const_mul
    ((E + 1 : ℝ) * (2 : ℝ) ^ E) (by positivity) hsum

/--
Lemma 14.7, in the manuscript's literal uniform form:

`sum_{e=0}^E sum_{x in D(Q)} P(K_{x,e}=1) = o_{C,E}(1)`.
-/
theorem totalRemovedExactLengthProbabilityMassReal_uniformLittleOOne
    {C : ℝ} (hC : 0 ≤ C) (E : ℕ) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (totalRemovedExactLengthProbabilityMassReal E)
      (fun _ _ => 1) := by
  have hEnvelope :=
    totalRemovedExactLengthEnvelope_uniformLittleOOne hC E
  obtain ⟨Nwindow, hNwindow⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  intro ε hε
  obtain ⟨Nenv, hNenv⟩ := hEnvelope ε hε
  refine ⟨max 2 (max Nwindow Nenv), ?_⟩
  intro N hN L hrun
  have hNtwo : 2 ≤ N :=
    (le_max_left 2 (max Nwindow Nenv)).trans hN
  have hNtail : max Nwindow Nenv ≤ N :=
    (le_max_right 2 (max Nwindow Nenv)).trans hN
  have hw :=
    hNwindow N ((le_max_left _ _).trans hNtail) L hrun
  have hfinite :=
    totalRemovedExactLengthProbabilityMassReal_le_envelope
      (N := N) (L := L) (E := E) hNtwo
      (Nat.succ_le_iff.mpr hw.2.1)
  have henv :=
    hNenv N ((le_max_right _ _).trans hNtail) L hrun
  have hmassNonneg :
      0 ≤ totalRemovedExactLengthProbabilityMassReal E N L := by
    unfold totalRemovedExactLengthProbabilityMassReal
      totalRemovedExactLengthProbabilityMass
    apply Rat.cast_nonneg.mpr
    exact Finset.sum_nonneg fun e _ =>
      by
        unfold removedExactLengthProbabilityMass
          exactLengthProbabilityMass
        exact Finset.sum_nonneg fun x _ =>
          exactLengthProbability_nonneg N (excessRowCount L e) x
  have henvNonneg :
      0 ≤ totalRemovedExactLengthEnvelope E N L := by
    unfold totalRemovedExactLengthEnvelope
      commonNormalizedDefectContribution
      commonNormalizedRemovedCountContribution
      normalizedTerminalDefectContribution
      BadStartMassCritical.terminalDefectWeightMassReal
    rw [BadStartMassCritical.terminalDefectWeightMass_eq_natCast]
    positivity
  simp only [abs_of_nonneg hmassNonneg, abs_one, mul_one] at henv ⊢
  rw [abs_of_nonneg henvNonneg] at henv
  exact hfinite.trans henv

/--
Source-facing name for Lemma 14.7:

`∑_{e=0}^E ∑_{x∈D(Q)} P(K_{x,e}=1) = o_{C,E}(1)`,

uniformly for `|L-log₂ N| ≤ C`.
-/
theorem lemma_fourteen_seven_finiteCylinder
    {C : ℝ} (hC : 0 ≤ C) (E : ℕ) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun N L =>
        ((∑ e ∈ Finset.range (E + 1),
            exactLengthProbabilityMass N (excessRowCount L e)
              (removedExactLengthStarts N L E) : ℚ) : ℝ))
      (fun _ _ => 1) := by
  simpa only [totalRemovedExactLengthProbabilityMassReal,
    totalRemovedExactLengthProbabilityMass,
    removedExactLengthProbabilityMass] using
      totalRemovedExactLengthProbabilityMassReal_uniformLittleOOne hC E

/--
**Lemma 14.7 under the source infinite Rademacher law.**

The preceding cylinder estimate and the exact image-law transfer give

`∑_{e=0}^E ∑_{x∈D(Q)} P∞(K_{x,e}=1) = o_{C,E}(1)`,

uniformly for `|L-log₂ N| ≤ C`.
-/
theorem lemma_fourteen_seven
    {C : ℝ} (hC : 0 ≤ C) (E : ℕ) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun N L =>
        ∑ e ∈ Finset.range (E + 1),
          ∑ x ∈ removedExactLengthStarts N L E,
            infiniteExactLengthProbability x
              (excessRowCount L e))
      (fun _ _ => 1) := by
  have hsource :
      UniformLittleOOn
        (CriticalRunWindow.InRunLengthWindow C)
        (fun N L =>
          totalRemovedInfiniteExactLengthProbability N L E)
        (fun _ _ => 1) := by
    simpa only [totalRemovedExactLengthProbabilityMassReal,
      totalRemovedInfiniteExactLengthProbability_eq_finiteMass] using
        totalRemovedExactLengthProbabilityMassReal_uniformLittleOOne hC E
  simpa only [totalRemovedInfiniteExactLengthProbability] using hsource

end

end ExactLengthBadStartMassCritical
end PaperC
