import PaperC.Asymptotics.BoundedRatioManyDefectsDegreeAssembly
import PaperC.Asymptotics.BoundedRatioManyDefectsEvertseSum

set_option maxHeartbeats 3600000

/-!
# Completion of Lemma 17.26 in the bounded-ratio window

The three mobile-degree branches are now all available:

* degree one is elementary and contributes `N^(1/2+o(1))`;
* degree two is controlled by generalized Pell, with the square-coefficient
  exception treated by signed divisors;
* degree at least three is controlled by Evertse--Silverman and the
  unconditional factorial bound for the number of prime factors.

This module specializes the abstract degree assembly to the common
Evertse--Silverman residual.  It therefore proves the fifth sector from the
two already registered Diophantine inputs and introduces no new bridge.
-/

namespace PaperC
namespace BoundedRatioManyDefectsAssembly

open BoundedRatioManyDefectsDegreeAssembly
open BoundedRatioManyDefectsEvertseSum
open PropositionSixteenOne

noncomputable section

/--
Lemma 17.26 with both its source-exact `N^(3/2+o)` rate and the quadratic
little-oh consequence, uniformly in every fixed bounded-ratio critical
window.
-/
theorem manyDefectsSector_rates
    {C : ℝ} (hC : 0 ≤ C) (κ₀ A : ℕ)
    (terminal : TerminalPredicateFamily)
    (hES :
      EvertseSilvermanInput.EvertseSilvermanAbscissaStatement)
    (hPell :
      PellInput.GeneralizedPellPolynomialBoxStatement) :
    UniformRationalPowerInBoundedRatioWindow 3 2 C κ₀
        (sectorResidualMass A terminal .manyDefects) ∧
      UniformLittleOInBoundedRatioWindow C κ₀
        (sectorResidualMass A terminal .manyDefects) := by
  let highEnvelope : ℕ → ℕ → ℝ :=
    fun N L =>
      (evertseCommonFixedFiberResidual κ₀ N L : ℝ)
  apply
    manyDefectsSector_rates_of_degreeAssembly
      hC κ₀ A terminal hPell highEnvelope
  · simpa only [highEnvelope] using
      evertseCommonFixedFiberResidual_uniformSubpolynomial
        hC κ₀
  · intro N L
    dsimp only [highEnvelope]
    positivity
  · simpa only [highEnvelope] using
      evertseCommonFixedFiberResidual_eventually_one_le κ₀
  · intro N M L base hN hMκ hL shape hshape hdegree
    dsimp only [highEnvelope]
    exact_mod_cast
      card_leftBaseShapeFiber_degree_at_least_three_le_common
        (A := A) (base := base)
        hES hN hMκ hL shape hshape hdegree
  · intro N M L base hN hMκ hL shape hshape hdegree
    dsimp only [highEnvelope]
    exact_mod_cast
      card_rightBaseShapeFiber_degree_at_least_three_le_common
        (A := A) (base := base)
        hES hN hMκ hL shape hshape hdegree

/--
Source-exact form of Lemma 17.26: the many-defects sector has residual mass
`N^(3/2+o_{C,κ₀}(1))`.
-/
theorem manyDefectsSector_uniformThreeHalves
    {C : ℝ} (hC : 0 ≤ C) (κ₀ A : ℕ)
    (terminal : TerminalPredicateFamily)
    (hES :
      EvertseSilvermanInput.EvertseSilvermanAbscissaStatement)
    (hPell :
      PellInput.GeneralizedPellPolynomialBoxStatement) :
    UniformRationalPowerInBoundedRatioWindow 3 2 C κ₀
      (sectorResidualMass A terminal .manyDefects) :=
  (manyDefectsSector_rates
    hC κ₀ A terminal hES hPell).1

/--
Lemma 17.26: the many-defects sector has residual mass `o(N²)` uniformly in
every fixed bounded-ratio critical window.
-/
theorem manyDefectsSector_uniformLittleO
    {C : ℝ} (hC : 0 ≤ C) (κ₀ A : ℕ)
    (terminal : TerminalPredicateFamily)
    (hES :
      EvertseSilvermanInput.EvertseSilvermanAbscissaStatement)
    (hPell :
      PellInput.GeneralizedPellPolynomialBoxStatement) :
    UniformLittleOInBoundedRatioWindow C κ₀
      (sectorResidualMass A terminal .manyDefects) :=
  (manyDefectsSector_rates
    hC κ₀ A terminal hES hPell).2

/--
Registered historical-interface form of Lemma 17.26.  Unlike the bridge
it replaces in canonical assemblies, this theorem constructs the estimate
from Evertse--Silverman and generalized Pell.
-/
theorem manyDefectsSectorStability
    {C : ℝ} (hC : 0 ≤ C) (κ₀ A : ℕ)
    (terminal : TerminalPredicateFamily) :
    ManyDefectsSectorStabilityStatement
      C κ₀ A terminal := by
  intro hES hPell
  exact
    manyDefectsSector_uniformLittleO
      hC κ₀ A terminal hES hPell

end

end BoundedRatioManyDefectsAssembly
end PaperC
