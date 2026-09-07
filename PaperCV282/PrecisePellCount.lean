import PaperC.Diophantine.PellDivisorEnvelope
import PaperC.Diophantine.PellRealExponent

/-!
# The precise bounded-height Pell rate of 3.13 and A.2

The conductor, ideal-divisor, unit-orbit and real-height reductions are
already proved in the core. These interfaces discharge their intermediate
Pell proposition from the source-shaped Nicolas--Robin inequality. The
constant and threshold precede all coefficients and all finite solution sets.
-/

namespace PaperC.V282.PrecisePellCount

open PellInput

noncomputable section

/-- Article 3.13, with the literal real polynomial height and uniform coefficients. -/
theorem lemma_three_thirteen
    (hNR : NicolasRobinDivisorLogBoundStatement) :
    PellSourceExactRealPolynomialBoxStatement :=
  pellSourceExactRealPolynomialBox_of_generalizedPell
    (generalizedPellPolynomialBox_of_divisorLogBound hNR)

/-- Companion A.2 is the same bounded-height statement, with no separate Pell input. -/
theorem lemma_a_two
    (hNR : NicolasRobinDivisorLogBoundStatement) :
    PellSourceExactRealPolynomialBoxStatement :=
  lemma_three_thirteen hNR

/-- An independently bounded integral radius, convenient for squareclass fibres.
The exponent may be zero; only the nonsquare branch is counted here. -/
theorem pellBox_atMost_expLogLog_eventually
    (hNR : NicolasRobinDivisorLogBoundStatement) (K : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∃ Mzero : ℕ, ∀ M ≥ Mzero,
      ∀ A C H : ℕ, ∀ e : ℤ,
      0 < A → 0 < C → Squarefree A → Squarefree C →
      ¬ IsSquare ((A : ℚ) / (C : ℚ)) → e ≠ 0 →
      A ≤ M ^ K → C ≤ M ^ K → H ≤ M ^ K → e.natAbs ≤ M ^ K →
      HasAtMostSolutionsReal (pellBox A C e H) (expLogLogBound c M) := by
  obtain ⟨c, hc, Mzero, hcount⟩ :=
    pellPolynomialBox_of_generalizedPell
      (generalizedPellPolynomialBox_of_divisorLogBound hNR) (K + 1) (by omega)
  refine ⟨c, hc, max Mzero 1, ?_⟩
  intro M hM A C H e hA hC hAsq hCsq hratio he hAM hCM hHM heM
  have hone : 1 ≤ M := (le_max_right _ _).trans hM
  have hpow : M ^ K ≤ M ^ (K + 1) := Nat.pow_le_pow_right hone (by omega)
  have h := hcount M ((le_max_left _ _).trans hM) A C e hA hC hAsq hCsq
    hratio he (hAM.trans hpow) (hCM.trans hpow) (heM.trans hpow)
  intro s hs
  apply h s
  intro p hp
  obtain ⟨heq, hz, hw⟩ := hs p hp
  exact ⟨heq, hz.trans (hHM.trans hpow), hw.trans (hHM.trans hpow)⟩

end
end PaperC.V282.PrecisePellCount
