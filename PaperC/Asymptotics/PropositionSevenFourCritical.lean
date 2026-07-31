import PaperC.Asymptotics.RationalPowerClosure
import PaperC.Asymptotics.RationalPowerLittleO
import PaperC.Asymptotics.RelationalHostsThreeHalves
import PaperC.Asymptotics.SmallHeightPositiveSigmaCritical
import PaperC.Asymptotics.SmallHeightSigmaZeroCritical
import PaperC.Combinatorics.SmallHeightLargeProductMassBound

/-!
# Proposition 7.4 in the critical window

This module recombines the two quadratic branches of the small-height,
large-residual-product population.  The exceptional branch is
`N^(3/2+o_C(1))`, while the positive-systematic branch is
`N^(5/3+o_C(1))`; their sum therefore has the latter exponent.

The finite Cauchy--Schwarz inequality against the relational-host population
then interpolates the exponents `3/2` and `5/3`, giving `19/12` for the
linear residual mass.

The public real-valued totals do not depend on a proof of `2 ≤ N`; below
that harmless finite threshold they are defined to be zero.
-/

namespace PaperC
namespace PropositionSevenFourCritical

open SmallHeightLargeProductMassBound
open SmallHeightLargeProductPairs

noncomputable section

/--
Proof-independent real form of the complete small-height, large-product
quadratic residual mass `Q_res`.
-/
noncomputable def smallHeightLargeProductQuadraticResidualMassTotal
    (A N L : ℕ) : ℝ :=
  if hN : 2 ≤ N then
    (smallHeightLargeProductQuadraticResidualMass N A L hN : ℝ)
  else 0

/--
Proof-independent real form of the complete small-height, large-product
linear residual mass `R_res`.
-/
noncomputable def smallHeightLargeProductLinearResidualMassTotal
    (A N L : ℕ) : ℝ :=
  if hN : 2 ≤ N then
    (smallHeightLargeProductLinearResidualMass N A L hN : ℝ)
  else 0

/--
The proof-independent quadratic total is exactly the sum of its exceptional
and positive-systematic branch totals.
-/
theorem smallHeightLargeProductQuadraticResidualMassTotal_eq_branches
    (A N L : ℕ) :
    smallHeightLargeProductQuadraticResidualMassTotal A N L =
      SmallHeightSigmaZeroCritical.sigmaZeroQuadraticResidualMassTotal
          A N L +
        SmallHeightPositiveSigmaCritical.positiveSigmaQuadraticResidualMassTotal
          A N L := by
  by_cases hN : 2 ≤ N
  · simp only [smallHeightLargeProductQuadraticResidualMassTotal,
      SmallHeightSigmaZeroCritical.sigmaZeroQuadraticResidualMassTotal,
      SmallHeightPositiveSigmaCritical.positiveSigmaQuadraticResidualMassTotal,
      dif_pos hN]
    exact_mod_cast
      smallHeightLargeProductQuadraticResidualMass_eq_branches
        (A := A) (L := L) hN
  · simp only [smallHeightLargeProductQuadraticResidualMassTotal,
      SmallHeightSigmaZeroCritical.sigmaZeroQuadraticResidualMassTotal,
      SmallHeightPositiveSigmaCritical.positiveSigmaQuadraticResidualMassTotal,
      dif_neg hN, add_zero]

/--
The complete quadratic residual mass of Proposition 7.4 satisfies

`Q_res ≤ N^(5/3+o_C(1))`

uniformly in the critical run-length window.
-/
theorem smallHeightLargeProductQuadraticResidualMass_uniformFiveThird
    {C : ℝ} (hC : 0 ≤ C)
    (A : ℕ) (hA : 1 ≤ A) :
    UniformFiveThirdSubpolynomialOn
      (CriticalRunWindow.InRunLengthWindow C)
      (smallHeightLargeProductQuadraticResidualMassTotal A) := by
  have hzero :=
    SmallHeightSigmaZeroCritical.sigmaZeroQuadraticResidualMass_uniformThreeHalves
      hC A
  have hpositive :=
    SmallHeightPositiveSigmaCritical.positiveSigmaQuadraticResidualMass_uniformFiveThird
      hC A hA
  have hsum :=
    UniformRationalPower.add_threeHalves_fiveThird
      hzero hpositive
  have htotal :
      smallHeightLargeProductQuadraticResidualMassTotal A =
        fun N L =>
          SmallHeightSigmaZeroCritical.sigmaZeroQuadraticResidualMassTotal
              A N L +
            SmallHeightPositiveSigmaCritical.positiveSigmaQuadraticResidualMassTotal
              A N L := by
    funext N L
    exact
      smallHeightLargeProductQuadraticResidualMassTotal_eq_branches
        A N L
  rw [htotal]
  exact hsum

/--
The finite interpolation inequality (6.6), written with the
proof-independent real totals.
-/
theorem smallHeightLargeProductLinearResidualMassTotal_le
    {A N L : ℕ} (hN : 2 ≤ N) :
    smallHeightLargeProductLinearResidualMassTotal A N L ≤
      Real.sqrt
          ((RelationalHosts.relationalHosts N L).card : ℝ) *
        Real.sqrt
          (smallHeightLargeProductQuadraticResidualMassTotal
            A N L) := by
  simpa only [smallHeightLargeProductLinearResidualMassTotal,
    smallHeightLargeProductQuadraticResidualMassTotal,
    dif_pos hN] using
    (smallHeightLargeProductLinearResidualMass_cast_le
      (A := A) hN)

/--
The complete linear residual mass of Proposition 7.4 satisfies

`R_res ≤ N^(19/12+o_C(1))`

uniformly in the critical run-length window.
-/
theorem smallHeightLargeProductLinearResidualMass_uniformNineteenTwelfths
    {C : ℝ} (hC : 0 ≤ C)
    (A : ℕ) (hA : 1 ≤ A) :
    UniformRationalPowerSubpolynomialOn 19 12
      (CriticalRunWindow.InRunLengthWindow C)
      (smallHeightLargeProductLinearResidualMassTotal A) := by
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
    smallHeightLargeProductQuadraticResidualMass_uniformFiveThird
      hC A hA
  apply
    UniformRationalPower.interpolate_threeHalves_fiveThird
      hhosts hquadratic
  refine ⟨2, ?_⟩
  intro N hN L _hwindow
  have hlinearNonneg :
      0 ≤ smallHeightLargeProductLinearResidualMassTotal
        A N L := by
    simp [smallHeightLargeProductLinearResidualMassTotal, hN]
  have hquadraticNonneg :
      0 ≤ smallHeightLargeProductQuadraticResidualMassTotal
        A N L := by
    simp [smallHeightLargeProductQuadraticResidualMassTotal, hN]
  refine ⟨by positivity, hquadraticNonneg, hlinearNonneg, ?_⟩
  simpa only [hosts] using
    (smallHeightLargeProductLinearResidualMassTotal_le
      (A := A) hN)

/--
The complete linear residual mass of Proposition 7.4 is uniformly negligible
relative to the quadratic scale:

`R_res = o_C(N²)`.
-/
theorem smallHeightLargeProductLinearResidualMass_uniformLittleOQuadratic
    {C : ℝ} (hC : 0 ≤ C)
    (A : ℕ) (hA : 1 ≤ A) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (smallHeightLargeProductLinearResidualMassTotal A)
      (fun N _ => (N : ℝ) ^ 2) :=
  UniformRationalPower.nineteenTwelfths_littleO_quadratic
    (smallHeightLargeProductLinearResidualMass_uniformNineteenTwelfths
      hC A hA)

end

end PropositionSevenFourCritical
end PaperC
