import PaperC.Asymptotics.PositiveSigmaQuadraticCritical
import PaperC.Asymptotics.QuadraticAndInterpolationClosure
import PaperC.Asymptotics.RelationalHostsThreeHalves
import PaperC.Asymptotics.SigmaZeroQuadraticCritical

/-!
# Proposition 7.3 in the critical window

This file recombines the exceptional (`σ = 0`) and systematic (`σ > 0`)
quadratic branches, then applies the paper's finite interpolation inequality
(6.6).  Its public quantities do not depend on a proof of `2 ≤ N`; below
that harmless finite threshold they are defined to be zero.
-/

namespace PaperC
namespace PropositionSevenThreeCritical

open ResidualMasses

noncomputable section

/--
Proof-independent real form of the paper's complete small-product
quadratic residual mass `Q_res`.
-/
noncomputable def smallProductQuadraticResidualMassTotal
    (A N L : ℕ) : ℝ :=
  if hN : 2 ≤ N then
    (ResidualMasses.smallProductQuadraticResidualMass N A L hN : ℝ)
  else 0

/--
Proof-independent real form of the paper's complete small-product
linear residual mass `R_res`.
-/
noncomputable def smallProductLinearResidualMassTotal
    (A N L : ℕ) : ℝ :=
  if hN : 2 ≤ N then
    (ResidualMasses.smallProductLinearResidualMass N A L hN : ℝ)
  else 0

/--
The proof-independent quadratic total is exactly the sum of the two
proof-independent branch totals.
-/
theorem smallProductQuadraticResidualMassTotal_eq_branches
    (A N L : ℕ) :
    smallProductQuadraticResidualMassTotal A N L =
      SigmaZeroQuadraticCritical.sigmaZeroQuadraticResidualMassTotal
          A N L +
        PositiveSigmaQuadraticCritical.positiveSigmaQuadraticResidualMassTotal
          A N L := by
  by_cases hN : 2 ≤ N
  · simp only [smallProductQuadraticResidualMassTotal,
      SigmaZeroQuadraticCritical.sigmaZeroQuadraticResidualMassTotal,
      PositiveSigmaQuadraticCritical.positiveSigmaQuadraticResidualMassTotal,
      dif_pos hN]
    exact_mod_cast
      ResidualMasses.smallProductQuadraticResidualMass_eq_sigmaZero_add_positiveSigma
        (A := A) (L := L) hN
  · simp only [smallProductQuadraticResidualMassTotal,
      SigmaZeroQuadraticCritical.sigmaZeroQuadraticResidualMassTotal,
      PositiveSigmaQuadraticCritical.positiveSigmaQuadraticResidualMassTotal,
      dif_neg hN, add_zero]

/--
The complete quadratic residual mass in Proposition 7.3 satisfies
`Q_res ≤ N^(2+o_C(1))`, uniformly in the critical run-length window.
-/
theorem smallProductQuadraticResidualMass_uniformQuadratic
    {C : ℝ} (hC : 0 ≤ C) (A : ℕ) :
    UniformRationalPowerSubpolynomialOn 2 1
      (CriticalRunWindow.InRunLengthWindow C)
      (smallProductQuadraticResidualMassTotal A) := by
  have hzero :=
    SigmaZeroQuadraticCritical.sigmaZeroQuadraticResidualMass_uniformQuadratic
      hC A
  have hpositive :=
    PositiveSigmaQuadraticCritical.positiveSigmaQuadraticResidualMass_uniformQuadratic
      hC A
  have hsum :=
    UniformRationalPower.add_quadratic hzero hpositive
  have htotal :
      smallProductQuadraticResidualMassTotal A =
        fun N L =>
          SigmaZeroQuadraticCritical.sigmaZeroQuadraticResidualMassTotal
              A N L +
            PositiveSigmaQuadraticCritical.positiveSigmaQuadraticResidualMassTotal
              A N L := by
    funext N L
    exact smallProductQuadraticResidualMassTotal_eq_branches A N L
  rw [htotal]
  exact hsum

/--
Equation (6.6), expressed with proof-independent real totals.
-/
theorem smallProductLinearResidualMassTotal_le
    {A N L : ℕ} (hN : 2 ≤ N) :
    smallProductLinearResidualMassTotal A N L ≤
      Real.sqrt
          ((RelationalHosts.relationalHosts N L).card : ℝ) *
        Real.sqrt (smallProductQuadraticResidualMassTotal A N L) := by
  simpa only [smallProductLinearResidualMassTotal,
    smallProductQuadraticResidualMassTotal, dif_pos hN] using
    (ResidualMasses.smallProductLinearResidualMass_cast_le
      (A := A) hN)

/--
The complete linear residual mass in Proposition 7.3 satisfies
`R_res ≤ N^(7/4+o_C(1))`, uniformly in the critical run-length window.
-/
theorem smallProductLinearResidualMass_uniformSevenFourths
    {C : ℝ} (hC : 0 ≤ C) (A : ℕ) :
    UniformRationalPowerSubpolynomialOn 7 4
      (CriticalRunWindow.InRunLengthWindow C)
      (smallProductLinearResidualMassTotal A) := by
  let hosts : ℕ → ℕ → ℝ :=
    fun N L =>
      ((RelationalHosts.relationalHosts N L).card : ℝ)
  have hhosts :
      UniformThreeHalvesSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C) hosts := by
    simpa only [hosts] using
      RelationalHostsThreeHalves.card_relationalHosts_uniformThreeHalves_inRunLengthWindow
        hC
  have hquadratic :=
    smallProductQuadraticResidualMass_uniformQuadratic hC A
  apply
    UniformRationalPower.interpolate_threeHalves_quadratic
      hhosts hquadratic
  refine ⟨2, ?_⟩
  intro N hN L _hwindow
  have hlinearNonneg :
      0 ≤ smallProductLinearResidualMassTotal A N L := by
    simp [smallProductLinearResidualMassTotal, hN]
  have hquadraticNonneg :
      0 ≤ smallProductQuadraticResidualMassTotal A N L := by
    simp [smallProductQuadraticResidualMassTotal, hN]
  refine ⟨by positivity, hquadraticNonneg, hlinearNonneg, ?_⟩
  simpa only [hosts] using
    (smallProductLinearResidualMassTotal_le (A := A) hN)

end

end PropositionSevenThreeCritical
end PaperC
