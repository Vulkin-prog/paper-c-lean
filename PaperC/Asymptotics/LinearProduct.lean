import PaperC.Asymptotics.LinearPower
import PaperC.Asymptotics.RationalPowers

/-!
# Products of two linear-subpolynomial quantities

The product of two uniform `N^(1+o(1))` bounds is uniformly
`N^(2+o(1))`.  This module records that closure directly in the general
rational-power predicate.
-/

namespace PaperC
namespace UniformLinear

/--
The pointwise product of two uniform `N^(1+o(1))` quantities is
`N^(2+o(1))`, encoded as rational power `2/1`.
-/
theorem mul
    {admissible : ℕ → ℕ → Prop}
    {f g : ℕ → ℕ → ℝ}
    (hf : UniformLinearSubpolynomialOn admissible f)
    (hg : UniformLinearSubpolynomialOn admissible g) :
    UniformRationalPowerSubpolynomialOn 2 1 admissible
      (fun N L => f N L * g N L) := by
  intro k hk
  have htwok : 0 < 2 * k := Nat.mul_pos (by omega) hk
  obtain ⟨Nf, hNf⟩ := hf (2 * k) htwok
  obtain ⟨Ng, hNg⟩ := hg (2 * k) htwok
  refine ⟨max Nf Ng, ?_⟩
  intro N hN L hNL
  rw [abs_mul, one_mul]
  apply ExpSqrtLog.mul_pow_le_nat_of_twice
      (abs_nonneg _) (abs_nonneg _)
      (show 0 ≤ (N : ℝ) ^ (2 * k + 1) by positivity)
  · simpa only [Nat.mul_assoc] using
      hNf N ((le_max_left _ _).trans hN) L hNL
  · simpa only [Nat.mul_assoc] using
      hNg N ((le_max_right _ _).trans hN) L hNL

end UniformLinear
end PaperC
