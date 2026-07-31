import PaperC.Asymptotics.Uniform
import Mathlib.Data.Real.Sqrt

/-!
# A quantified meaning of `N^(1/2+o(1))`

The weighted-defect estimate in Proposition 3.2 has a square-root main
factor and a subpolynomial loss.  The predicate below encodes that statement
without informal exponent notation.
-/

namespace PaperC

/--
Uniform reciprocal-power formulation of `|f(N,L)| ≤ N^(1/2+o(1))`.

For every positive `k`, the exponent loss can be made at most `1/(2k)`:
`|f|^(2*k) ≤ N^(k+1)`, uniformly in the admissible auxiliary parameter.
-/
def UniformHalfPowerSubpolynomialOn
    (admissible : ℕ → ℕ → Prop) (f : ℕ → ℕ → ℝ) : Prop :=
  ∀ k : ℕ, 0 < k →
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L, admissible N L →
      |f N L| ^ (2 * k) ≤ (N : ℝ) ^ (k + 1)

/--
Uniform meaning of `f(N,L) = N^(-1/2+o(1))`, defined by moving one factor
of `N` to the left and using the half-power predicate.
-/
def UniformNegativeHalfPowerSubpolynomialOn
    (admissible : ℕ → ℕ → Prop) (f : ℕ → ℕ → ℝ) : Prop :=
  UniformHalfPowerSubpolynomialOn admissible
    (fun N L => (N : ℝ) * f N L)

namespace UniformHalfPower

/--
A square-root factor times a uniformly subpolynomial factor is
`N^(1/2+o(1))`.
-/
theorem of_sqrt_mul_subpolynomial
    {admissible : ℕ → ℕ → Prop}
    {f q : ℕ → ℕ → ℝ}
    (hq : UniformSubpolynomialOn admissible q)
    (hbound :
      ∃ N₁ : ℕ, ∀ N ≥ N₁, ∀ L, admissible N L →
        |f N L| ≤ Real.sqrt N * |q N L|) :
    UniformHalfPowerSubpolynomialOn admissible f := by
  intro k hk
  have htwok : 0 < 2 * k := Nat.mul_pos (by omega) hk
  obtain ⟨Nq, hNq⟩ := hq (2 * k) htwok
  obtain ⟨Nb, hNb⟩ := hbound
  refine ⟨max Nq Nb, ?_⟩
  intro N hN L hNL
  have hNqN : Nq ≤ N := (le_max_left _ _).trans hN
  have hNbN : Nb ≤ N := (le_max_right _ _).trans hN
  have hNnonneg : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  calc
    |f N L| ^ (2 * k)
        ≤ (Real.sqrt N * |q N L|) ^ (2 * k) :=
      pow_le_pow_left₀ (abs_nonneg _) (hNb N hNbN L hNL) _
    _ = (N : ℝ) ^ k * |q N L| ^ (2 * k) := by
      rw [mul_pow, pow_mul, Real.sq_sqrt hNnonneg]
    _ ≤ (N : ℝ) ^ k * (N : ℝ) := by
      exact mul_le_mul_of_nonneg_left
        (hNq N hNqN L hNL) (by positivity)
    _ = (N : ℝ) ^ (k + 1) := by
      rw [pow_succ]

/--
The half-power predicate is stable under an eventual pointwise domination.
-/
theorem mono
    {admissible : ℕ → ℕ → Prop}
    {f g : ℕ → ℕ → ℝ}
    (hg : UniformHalfPowerSubpolynomialOn admissible g)
    (hfg :
      ∃ N₁ : ℕ, ∀ N ≥ N₁, ∀ L, admissible N L →
        |f N L| ≤ |g N L|) :
    UniformHalfPowerSubpolynomialOn admissible f := by
  intro k hk
  obtain ⟨Ng, hNg⟩ := hg k hk
  obtain ⟨Nb, hNb⟩ := hfg
  refine ⟨max Ng Nb, ?_⟩
  intro N hN L hNL
  exact
    (pow_le_pow_left₀ (abs_nonneg _) (hNb N ((le_max_right _ _).trans hN)
      L hNL) _).trans
      (hNg N ((le_max_left _ _).trans hN) L hNL)

/-- Multiplication by a fixed real constant preserves the half-power rate. -/
theorem const_mul
    {admissible : ℕ → ℕ → Prop}
    (B : ℝ) {f : ℕ → ℕ → ℝ}
    (hf : UniformHalfPowerSubpolynomialOn admissible f) :
    UniformHalfPowerSubpolynomialOn admissible
      (fun N L => B * f N L) := by
  intro k hk
  have htwok : 0 < 2 * k := Nat.mul_pos (by omega) hk
  obtain ⟨Nf, hNf⟩ := hf (2 * k) htwok
  obtain ⟨NB, hNB⟩ := exists_nat_gt (|B| ^ (4 * k))
  refine ⟨max Nf NB, ?_⟩
  intro N hN L hNL
  have hNfN : Nf ≤ N := (le_max_left _ _).trans hN
  have hNBN : NB ≤ N := (le_max_right _ _).trans hN
  have hBpow : |B| ^ (4 * k) ≤ (N : ℝ) :=
    hNB.le.trans (by exact_mod_cast hNBN)
  have hfpow :
      |f N L| ^ (4 * k) ≤ (N : ℝ) ^ (2 * k + 1) := by
    have hexp : 2 * (2 * k) = 4 * k := by omega
    simpa only [hexp] using hNf N hNfN L hNL
  have hsq :
      (|B * f N L| ^ (2 * k)) ^ 2 ≤
        ((N : ℝ) ^ (k + 1)) ^ 2 := by
    calc
      (|B * f N L| ^ (2 * k)) ^ 2 =
          |B| ^ (4 * k) * |f N L| ^ (4 * k) := by
        rw [abs_mul, mul_pow, mul_pow]
        have hexp : (2 * k) * 2 = 4 * k := by omega
        simp only [← pow_mul, hexp]
      _ ≤ (N : ℝ) * (N : ℝ) ^ (2 * k + 1) :=
        mul_le_mul hBpow hfpow (by positivity) (Nat.cast_nonneg N)
      _ = ((N : ℝ) ^ (k + 1)) ^ 2 := by
        calc
          (N : ℝ) * (N : ℝ) ^ (2 * k + 1) =
              (N : ℝ) ^ ((2 * k + 1) + 1) :=
            (pow_succ' (N : ℝ) (2 * k + 1)).symm
          _ = (N : ℝ) ^ ((k + 1) * 2) := by congr 1; omega
          _ = ((N : ℝ) ^ (k + 1)) ^ 2 := pow_mul _ _ _
  exact
    (sq_le_sq₀ (by positivity) (by positivity)).mp hsq

end UniformHalfPower
end PaperC
