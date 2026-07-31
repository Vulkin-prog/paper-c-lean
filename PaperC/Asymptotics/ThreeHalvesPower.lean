import PaperC.Asymptotics.Uniform
import Mathlib.Data.Real.Sqrt

/-!
# A quantified meaning of `N^(3/2+o(1))`

This module uses the same reciprocal-power convention as `HalfPower` and
`LinearPower`.  A loss of size `N^(1/(2k))` is recorded by

`|f(N,L)|^(2k) ≤ N^(3k+1)`.
-/

namespace PaperC

/--
Uniform reciprocal-power formulation of
`|f(N,L)| ≤ N^(3/2+o(1))`.
-/
def UniformThreeHalvesSubpolynomialOn
    (admissible : ℕ → ℕ → Prop)
    (f : ℕ → ℕ → ℝ) : Prop :=
  ∀ k : ℕ, 0 < k →
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L, admissible N L →
      |f N L| ^ (2 * k) ≤ (N : ℝ) ^ (3 * k + 1)

namespace UniformThreeHalves

/--
A factor `N * √N` times a uniformly subpolynomial factor is
`N^(3/2+o(1))`.
-/
theorem of_linear_sqrt_mul_subpolynomial
    {admissible : ℕ → ℕ → Prop}
    {f q : ℕ → ℕ → ℝ}
    (hq : UniformSubpolynomialOn admissible q)
    (hbound :
      ∃ N₁ : ℕ, ∀ N ≥ N₁, ∀ L, admissible N L →
        |f N L| ≤
          (N : ℝ) * Real.sqrt N * |q N L|) :
    UniformThreeHalvesSubpolynomialOn admissible f := by
  intro k hk
  have htwok : 0 < 2 * k :=
    Nat.mul_pos (by omega) hk
  obtain ⟨Nq, hNq⟩ := hq (2 * k) htwok
  obtain ⟨Nb, hNb⟩ := hbound
  refine ⟨max Nq Nb, ?_⟩
  intro N hN L hNL
  have hNqN : Nq ≤ N :=
    (le_max_left _ _).trans hN
  have hNbN : Nb ≤ N :=
    (le_max_right _ _).trans hN
  have hNnonneg : 0 ≤ (N : ℝ) :=
    Nat.cast_nonneg N
  have hsqrtpow :
      (Real.sqrt N) ^ (2 * k) = (N : ℝ) ^ k := by
    rw [pow_mul, Real.sq_sqrt hNnonneg]
  calc
    |f N L| ^ (2 * k) ≤
        ((N : ℝ) * Real.sqrt N * |q N L|) ^ (2 * k) :=
      pow_le_pow_left₀ (abs_nonneg _)
        (hNb N hNbN L hNL) _
    _ = (N : ℝ) ^ (3 * k) *
        |q N L| ^ (2 * k) := by
      rw [mul_pow, mul_pow, hsqrtpow, ← pow_add]
      congr 2
      omega
    _ ≤ (N : ℝ) ^ (3 * k) * (N : ℝ) :=
      mul_le_mul_of_nonneg_left
        (hNq N hNqN L hNL) (by positivity)
    _ = (N : ℝ) ^ (3 * k + 1) := by
      rw [pow_succ]

/--
The three-halves-power predicate is stable under eventual pointwise
domination.
-/
theorem mono
    {admissible : ℕ → ℕ → Prop}
    {f g : ℕ → ℕ → ℝ}
    (hg : UniformThreeHalvesSubpolynomialOn admissible g)
    (hfg :
      ∃ N₁ : ℕ, ∀ N ≥ N₁, ∀ L, admissible N L →
        |f N L| ≤ |g N L|) :
    UniformThreeHalvesSubpolynomialOn admissible f := by
  intro k hk
  obtain ⟨Ng, hNg⟩ := hg k hk
  obtain ⟨Nb, hNb⟩ := hfg
  refine ⟨max Ng Nb, ?_⟩
  intro N hN L hNL
  exact
    (pow_le_pow_left₀ (abs_nonneg _)
      (hNb N ((le_max_right _ _).trans hN) L hNL) _).trans
      (hNg N ((le_max_left _ _).trans hN) L hNL)

end UniformThreeHalves
end PaperC
