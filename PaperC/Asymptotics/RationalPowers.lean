import PaperC.Asymptotics.Uniform

/-!
# Uniform rational-power asymptotic predicates

For natural numbers `p,q`, the predicate below gives a division-free
quantified meaning to

`|f(N,L)| ≤ N^(p/q+o(1))`.

The reciprocal-power convention is

`|f|^(qk) ≤ N^(pk+1)`

for every positive integer `k`, uniformly in every admissible auxiliary
parameter.
-/

namespace PaperC

/--
Uniform reciprocal-power formulation of
`|f(N,L)| ≤ N^(p/q+o(1))`.
-/
def UniformRationalPowerSubpolynomialOn
    (p q : ℕ)
    (admissible : ℕ → ℕ → Prop)
    (f : ℕ → ℕ → ℝ) : Prop :=
  ∀ k : ℕ, 0 < k →
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L, admissible N L →
      |f N L| ^ (q * k) ≤ (N : ℝ) ^ (p * k + 1)

/-- Uniform notation for an `N^(4/3+o(1))` upper bound. -/
abbrev UniformFourThirdSubpolynomialOn
    (admissible : ℕ → ℕ → Prop)
    (f : ℕ → ℕ → ℝ) : Prop :=
  UniformRationalPowerSubpolynomialOn 4 3 admissible f

/-- Uniform notation for an `N^(5/3+o(1))` upper bound. -/
abbrev UniformFiveThirdSubpolynomialOn
    (admissible : ℕ → ℕ → Prop)
    (f : ℕ → ℕ → ℝ) : Prop :=
  UniformRationalPowerSubpolynomialOn 5 3 admissible f

namespace UniformRationalPower

/--
Composition with a cubed pointwise estimate.

If `s = N^(o(1))` uniformly and eventually

`|f|³ ≤ N^p |s|`,

then `f = N^(p/3+o(1))` in the rational-power convention.
-/
theorem of_cube_bound
    {p : ℕ}
    {admissible : ℕ → ℕ → Prop}
    {f s : ℕ → ℕ → ℝ}
    (hs : UniformSubpolynomialOn admissible s)
    (hbound :
      ∃ N₁ : ℕ, ∀ N ≥ N₁, ∀ L, admissible N L →
        |f N L| ^ 3 ≤ (N : ℝ) ^ p * |s N L|) :
    UniformRationalPowerSubpolynomialOn p 3 admissible f := by
  intro k hk
  obtain ⟨Ns, hNs⟩ := hs k hk
  obtain ⟨Nb, hNb⟩ := hbound
  refine ⟨max Ns Nb, ?_⟩
  intro N hN L hNL
  have hNsN : Ns ≤ N :=
    (le_max_left _ _).trans hN
  have hNbN : Nb ≤ N :=
    (le_max_right _ _).trans hN
  calc
    |f N L| ^ (3 * k) =
        (|f N L| ^ 3) ^ k := by
      rw [pow_mul]
    _ ≤ ((N : ℝ) ^ p * |s N L|) ^ k :=
      pow_le_pow_left₀ (pow_nonneg (abs_nonneg _) _)
        (hNb N hNbN L hNL) k
    _ = (N : ℝ) ^ (p * k) * |s N L| ^ k := by
      rw [mul_pow, pow_mul]
    _ ≤ (N : ℝ) ^ (p * k) * (N : ℝ) :=
      mul_le_mul_of_nonneg_left
        (hNs N hNsN L hNL) (pow_nonneg (Nat.cast_nonneg _) _)
    _ = (N : ℝ) ^ (p * k + 1) := by
      rw [pow_succ]

/--
The rational-power predicate is stable under eventual pointwise
domination.
-/
theorem mono
    {p q : ℕ}
    {admissible : ℕ → ℕ → Prop}
    {f g : ℕ → ℕ → ℝ}
    (hg :
      UniformRationalPowerSubpolynomialOn
        p q admissible g)
    (hfg :
      ∃ N₁ : ℕ, ∀ N ≥ N₁, ∀ L, admissible N L →
        |f N L| ≤ |g N L|) :
    UniformRationalPowerSubpolynomialOn
      p q admissible f := by
  intro k hk
  obtain ⟨Ng, hNg⟩ := hg k hk
  obtain ⟨Nb, hNb⟩ := hfg
  refine ⟨max Ng Nb, ?_⟩
  intro N hN L hNL
  exact
    (pow_le_pow_left₀ (abs_nonneg _)
      (hNb N ((le_max_right _ _).trans hN) L hNL)
      (q * k)).trans
      (hNg N ((le_max_left _ _).trans hN) L hNL)

end UniformRationalPower
end PaperC
