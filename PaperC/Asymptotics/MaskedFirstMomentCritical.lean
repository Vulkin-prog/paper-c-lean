import PaperC.Asymptotics.BadStartMassCritical
import PaperC.Asymptotics.LogLogRunWindow
import PaperC.Probability.MaskedFirstMoment

/-!
# Uniform masked first moments in the critical window

This file closes Proposition 14.1 in its full manuscript window

`|L - log₂ N| ≤ C⋆ log log N`.

The finite estimate in `MaskedFirstMoment` is uniform in the deterministic
mask: its right-hand side is the full-block defect mass.  Proposition 3.2
gives that mass the uniform rate `N^(1/2+o(1))`.  The widened-window balance
factor `N / 2^L` is `N^o(1)` by `LogLogRunWindow`, so the common error
envelope is `N^(-1/2+o(1))`, and hence `o(1)`.

The earlier fixed-width specialization is retained as a separate theorem.
-/

namespace PaperC
namespace MaskedFirstMomentCritical

open MaskedFirstMoment

noncomputable section

/-- Absolute real first-moment error for a deterministic mask. -/
def maskedFirstMomentErrorReal
    (N L : ℕ) (mask : Finset ℕ) : ℝ :=
  |((maskedDyadicExpectation N L mask -
      (mask.card : ℚ) / (2 : ℚ) ^ L : ℚ) : ℝ)|

/-- The sharp common error envelope, independent of the mask. -/
noncomputable def maskedFirstMomentEnvelope
    (N L : ℕ) : ℝ :=
  BadStartMassCritical.terminalDefectWeightMassReal N L /
    (2 : ℝ) ^ L

/--
Every deterministic mask is bounded by the sharp full-block envelope.
This is the finite `O(2⁻ᴸ N^(1/2+o(1)))` part of Proposition 14.1.
-/
theorem maskedFirstMomentErrorReal_le_envelope
    {N L : ℕ} {mask : Finset ℕ}
    (hN : 2 ≤ N)
    (hL : 0 < L)
    (hmask : mask ⊆ dyadicBlock N) :
    maskedFirstMomentErrorReal N L mask ≤
      maskedFirstMomentEnvelope N L := by
  have hfinite :=
    MaskedFirstMoment.abs_maskedDyadicExpectation_sub_baseline_le
      (N := N) (L := L) (B := L + 1) (mask := mask)
      hN hL le_rfl hmask
  have hcast := (Rat.cast_le (K := ℝ)).2 hfinite
  simpa only [maskedFirstMomentErrorReal, maskedFirstMomentEnvelope,
    BadStartMassCritical.terminalDefectWeightMassReal,
    Rat.cast_abs, Rat.cast_sub, Rat.cast_div, Rat.cast_natCast,
    Rat.cast_pow, Rat.cast_ofNat] using hcast

/--
Every deterministic mask is controlled by the same normalized full-block
defect contribution.
-/
theorem maskedFirstMomentErrorReal_le
    {N L : ℕ} {mask : Finset ℕ}
    (hN : 2 ≤ N)
    (hL : 0 < L)
    (hmask : mask ⊆ dyadicBlock N) :
    maskedFirstMomentErrorReal N L mask ≤
      BadStartMassCritical.normalizedTerminalDefectContribution N L := by
  have hfinite :=
    MaskedFirstMoment.abs_maskedDyadicExpectation_sub_baseline_le
      (N := N) (L := L) (B := L + 1) (mask := mask)
      hN hL le_rfl hmask
  have hcast := (Rat.cast_le (K := ℝ)).2 hfinite
  have hmassNonneg :
      0 ≤ BadStartMassCritical.terminalDefectWeightMassReal N L := by
    unfold BadStartMassCritical.terminalDefectWeightMassReal
    rw [BadStartMassCritical.terminalDefectWeightMass_eq_natCast]
    positivity
  have hpowPos : (0 : ℝ) < (2 : ℝ) ^ L := by positivity
  have hone :
      BadStartMassCritical.terminalDefectWeightMassReal N L /
          (2 : ℝ) ^ L ≤
        BadStartMassCritical.normalizedTerminalDefectContribution N L := by
    unfold BadStartMassCritical.normalizedTerminalDefectContribution
    have hquotient :
        0 ≤
          BadStartMassCritical.terminalDefectWeightMassReal N L /
            (2 : ℝ) ^ L :=
      div_nonneg hmassNonneg hpowPos.le
    calc
      BadStartMassCritical.terminalDefectWeightMassReal N L /
            (2 : ℝ) ^ L ≤
          2 *
            (BadStartMassCritical.terminalDefectWeightMassReal N L /
              (2 : ℝ) ^ L) := by
        linarith
      _ =
          2 * BadStartMassCritical.terminalDefectWeightMassReal N L /
            (2 : ℝ) ^ L := by ring
  apply le_trans _ hone
  simpa only [maskedFirstMomentErrorReal,
    BadStartMassCritical.terminalDefectWeightMassReal,
    Rat.cast_abs, Rat.cast_sub, Rat.cast_div, Rat.cast_natCast,
    Rat.cast_pow, Rat.cast_ofNat] using hcast

/-! ## Full `C⋆ log log N` window -/

/--
The weighted defect mass retains its `N^(1/2+o(1))` rate in the full
run-length window of Proposition 14.1.
-/
theorem terminalDefectWeightMass_uniformHalfPower_loglogWindow
    {Cstar : ℝ} (hCstar : 0 ≤ Cstar) :
    UniformHalfPowerSubpolynomialOn
      (LogLogRunWindow.InRunLengthWindow Cstar)
      BadStartMassCritical.terminalDefectWeightMassReal := by
  have hwindowMass :=
    CriticalWeightedDefect.dyadicDefectMass_uniformHalfPower_on_window
      CriticalRunWindow.lowerConstant_pos
      CriticalRunWindow.lowerConstant_lt_upperConstant
  have hmass :
      UniformHalfPowerSubpolynomialOn
        (LogLogRunWindow.InRunLengthWindow Cstar)
        (fun N L =>
          (CriticalWeightedDefect.dyadicDefectMass N (L + 1) : ℝ)) := by
    obtain ⟨Nwindow, hwindow⟩ :=
      LogLogRunWindow.heightWindow_eventually hCstar
    intro k hk
    obtain ⟨Nmass, hmass⟩ := hwindowMass k hk
    refine ⟨max Nwindow Nmass, ?_⟩
    intro N hN L hrun
    exact
      hmass N ((le_max_right _ _).trans hN) (L + 1)
        (hwindow N ((le_max_left _ _).trans hN) L hrun).1
  apply UniformHalfPower.mono hmass
  obtain ⟨Nwindow, hwindow⟩ :=
    LogLogRunWindow.heightWindow_eventually hCstar
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
    BadStartMassCritical.terminalDefectWeightMass_cast_le_dyadicDefectMass
      hAdm.2.1 htwo
  rw [abs_of_nonneg (by
      unfold BadStartMassCritical.terminalDefectWeightMassReal
      rw [BadStartMassCritical.terminalDefectWeightMass_eq_natCast]
      positivity),
    abs_of_nonneg (by positivity)]
  exact hfinite

/--
The mask-independent error envelope has the full
`N^(-1/2+o_{C⋆}(1))` rate in the widened window.
-/
theorem maskedFirstMomentEnvelope_uniformNegativeHalfPower
    {Cstar : ℝ} (hCstar : 0 ≤ Cstar) :
    UniformNegativeHalfPowerSubpolynomialOn
      (LogLogRunWindow.InRunLengthWindow Cstar)
      maskedFirstMomentEnvelope := by
  have hmass :=
    terminalDefectWeightMass_uniformHalfPower_loglogWindow hCstar
  have hbalance :=
    LogLogRunWindow.balanceRatio_uniformSubpolynomial hCstar
  have hproduct :=
    UniformHalfPower.mul_subpolynomial hmass hbalance
  unfold UniformNegativeHalfPowerSubpolynomialOn
  have heq :
      (fun (N L : ℕ) =>
        (N : ℝ) * maskedFirstMomentEnvelope N L) =
      (fun (N L : ℕ) =>
        BadStartMassCritical.terminalDefectWeightMassReal N L *
          ((N : ℝ) / (2 : ℝ) ^ L)) := by
    funext N L
    unfold maskedFirstMomentEnvelope
    ring
  rw [heq]
  exact hproduct

/-- The common envelope is uniformly `o(1)` in the widened window. -/
theorem maskedFirstMomentEnvelope_uniformLittleOOne
    {Cstar : ℝ} (hCstar : 0 ≤ Cstar) :
    UniformLittleOOn
      (LogLogRunWindow.InRunLengthWindow Cstar)
      maskedFirstMomentEnvelope
      (fun _ _ => 1) :=
  UniformNegativeHalfPower.littleOOne
    (maskedFirstMomentEnvelope_uniformNegativeHalfPower hCstar)

/--
Proposition 14.1 in the exact manuscript window:

for every `ε > 0`, all sufficiently large admissible `(N,L)` and every
deterministic mask `A_N ⊆ I_N` have first-moment error at most `ε`.
-/
theorem maskedFirstMomentError_uniformLittleOOne_loglogWindow
    {Cstar : ℝ} (hCstar : 0 ≤ Cstar) :
    ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ L : ℕ,
          LogLogRunWindow.InRunLengthWindow Cstar N L →
          ∀ mask : Finset ℕ, mask ⊆ dyadicBlock N →
            maskedFirstMomentErrorReal N L mask ≤ ε := by
  have henvelope :=
    maskedFirstMomentEnvelope_uniformLittleOOne hCstar
  obtain ⟨Nwindow, hwindow⟩ :=
    LogLogRunWindow.heightWindow_eventually hCstar
  intro ε hε
  obtain ⟨Nerror, herror⟩ := henvelope ε hε
  refine ⟨max Nwindow Nerror, ?_⟩
  intro N hN L hrun mask hmask
  have hw :=
    hwindow N ((le_max_left _ _).trans hN) L hrun
  have hfinite :=
    maskedFirstMomentErrorReal_le_envelope
      (N := N) (L := L) (mask := mask)
      hw.2.2 hw.2.1 hmask
  have hsmall :=
    herror N ((le_max_right _ _).trans hN) L hrun
  have henvelopeNonneg :
      0 ≤ maskedFirstMomentEnvelope N L := by
    unfold maskedFirstMomentEnvelope
      BadStartMassCritical.terminalDefectWeightMassReal
    rw [BadStartMassCritical.terminalDefectWeightMass_eq_natCast]
    positivity
  have hsmall' :
      maskedFirstMomentEnvelope N L ≤ ε := by
    simpa only [abs_of_nonneg henvelopeNonneg, abs_one, mul_one] using hsmall
  exact hfinite.trans hsmall'

/--
Uniform masked form of the first-moment conclusion:

for every `ε > 0`, all sufficiently large critical pairs `(N,L)` and every
deterministic `mask ⊆ I_N` have first-moment error at most `ε`.
-/
theorem maskedFirstMomentError_uniformLittleOOne
    {C : ℝ} (hC : 0 ≤ C) :
    ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ L : ℕ,
          CriticalRunWindow.InRunLengthWindow C N L →
          ∀ mask : Finset ℕ, mask ⊆ dyadicBlock N →
            maskedFirstMomentErrorReal N L mask ≤ ε := by
  have hdefect :=
    BadStartMassCritical.normalizedTerminalDefectContribution_uniformLittleOOne
      hC
  obtain ⟨Nwindow, hwindow⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  obtain ⟨Nadm, hadm⟩ :=
    CriticalWeightedDefect.admissible_eventually
      CriticalRunWindow.lowerConstant_pos
      CriticalRunWindow.lowerConstant_lt_upperConstant
  intro ε hε
  obtain ⟨Ndefect, hdefectBound⟩ := hdefect ε hε
  refine ⟨max Nwindow (max Nadm Ndefect), ?_⟩
  intro N hN L hrun mask hmask
  have hw :=
    hwindow N ((le_max_left _ _).trans hN) L hrun
  have htail :
      max Nadm Ndefect ≤ N :=
    (le_max_right Nwindow (max Nadm Ndefect)).trans hN
  have hAdm :=
    hadm N ((le_max_left Nadm Ndefect).trans htail)
      (L + 1) hw.1
  have hfinite :=
    maskedFirstMomentErrorReal_le
      (N := N) (L := L) (mask := mask)
      hAdm.2.1 hw.2.1 hmask
  have hsmall :=
    hdefectBound N
      ((le_max_right Nadm Ndefect).trans htail) L hrun
  have hdefectNonneg :
      0 ≤
        BadStartMassCritical.normalizedTerminalDefectContribution N L := by
    unfold BadStartMassCritical.normalizedTerminalDefectContribution
      BadStartMassCritical.terminalDefectWeightMassReal
    rw [BadStartMassCritical.terminalDefectWeightMass_eq_natCast]
    positivity
  have hsmall' :
      BadStartMassCritical.normalizedTerminalDefectContribution N L ≤ ε := by
    simpa only [abs_of_nonneg hdefectNonneg, abs_one, mul_one] using hsmall
  exact hfinite.trans hsmall'

end

end MaskedFirstMomentCritical
end PaperC
