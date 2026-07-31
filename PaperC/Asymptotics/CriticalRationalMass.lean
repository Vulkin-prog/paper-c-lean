import PaperC.Asymptotics.CriticalRationalMassEnvelopes

/-!
# Proposition 5.4 in the critical run-length window

The finite channel decomposition bounds the systematic rational mass by the
explicit envelope from `CriticalRationalMassEnvelopes`.  Monotonicity of the
uniform rational-power predicates therefore gives the two rates stated in
Proposition 5.4.
-/

namespace PaperC
namespace CriticalRationalMass

open RationalMassFinite
open CriticalRationalMassEnvelopes

/--
The base-two systematic mass is uniformly `N^(4/3+o_C(1))`.
-/
theorem rationalMass_two_uniformFourThird
    {C : ℝ} (hC : 0 ≤ C) (A : ℕ) (hA : 1 ≤ A) :
    UniformFourThirdSubpolynomialOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun N L => ((rationalMass N A L 2 : ℕ) : ℝ)) := by
  apply UniformRationalPower.mono
    (rationalMassEnvelope_two_uniformFourThird hC)
  refine ⟨0, ?_⟩
  intro N _hN L _hrun
  have hfinite :
      rationalMass N A L 2 ≤ rationalMassEnvelope 2 N L := by
    simpa [rationalMassEnvelope] using
      rationalMass_le N A L 2 hA (by norm_num)
  have hcast :
      ((rationalMass N A L 2 : ℕ) : ℝ) ≤
        ((rationalMassEnvelope 2 N L : ℕ) : ℝ) := by
    exact_mod_cast hfinite
  simpa only [abs_of_nonneg (by positivity : (0 : ℝ) ≤
      (rationalMass N A L 2 : ℕ)),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤
      (rationalMassEnvelope 2 N L : ℕ))] using hcast

/--
The base-four systematic mass is uniformly `N^(5/3+o_C(1))`.
-/
theorem rationalMass_four_uniformFiveThird
    {C : ℝ} (hC : 0 ≤ C) (A : ℕ) (hA : 1 ≤ A) :
    UniformFiveThirdSubpolynomialOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun N L => ((rationalMass N A L 4 : ℕ) : ℝ)) := by
  apply UniformRationalPower.mono
    (rationalMassEnvelope_four_uniformFiveThird hC)
  refine ⟨0, ?_⟩
  intro N _hN L _hrun
  have hfinite :
      rationalMass N A L 4 ≤ rationalMassEnvelope 4 N L := by
    simpa [rationalMassEnvelope] using
      rationalMass_le N A L 4 hA (by norm_num)
  have hcast :
      ((rationalMass N A L 4 : ℕ) : ℝ) ≤
        ((rationalMassEnvelope 4 N L : ℕ) : ℝ) := by
    exact_mod_cast hfinite
  simpa only [abs_of_nonneg (by positivity : (0 : ℝ) ≤
      (rationalMass N A L 4 : ℕ)),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤
      (rationalMassEnvelope 4 N L : ℕ))] using hcast

end CriticalRationalMass
end PaperC
