import Mathlib.Data.Real.Basic

/-!
# Uniform asymptotic predicates used by Paper C

The manuscript uses `O_C`, `o_C`, and `N^{o(1)}` with several auxiliary
parameters.  Lean should not encode those phrases as comments: the admissible
parameter set and all quantifiers must be part of the proposition.
-/

namespace PaperC

/-- Uniform little-oh along an explicitly supplied family of admissible pairs.

`UniformLittleOOn admissible f g` means that the threshold is independent of
the second parameter `L` as long as `(N,L)` is admissible. -/
def UniformLittleOOn
    (admissible : ℕ → ℕ → Prop) (f g : ℕ → ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L, admissible N L →
      |f N L| ≤ ε * |g N L|

/-- Uniform big-oh along an explicitly supplied family of admissible pairs. -/
def UniformBigOOn
    (admissible : ℕ → ℕ → Prop) (f g : ℕ → ℕ → ℝ) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L, admissible N L →
      |f N L| ≤ K * |g N L|

/-- A quantity is uniformly subpolynomial in `N`.

This is one precise quantified convention for an upper bound written
`N^{o(1)}` in the manuscript.  It uses the reciprocal-power formulation:
for every positive integer `k`, eventually `|f|^k ≤ N`, uniformly over the
admissible auxiliary parameter.  Its equivalence with formulations using real
powers should be proved separately before transporting a theorem stated in a
different convention. -/
def UniformSubpolynomialOn
    (admissible : ℕ → ℕ → Prop) (f : ℕ → ℕ → ℝ) : Prop :=
  ∀ k : ℕ, 0 < k →
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L, admissible N L →
      |f N L| ^ k ≤ (N : ℝ)

/-- A rate uniform in `L` in an arbitrary critical window predicate. -/
def UniformRateOn
    (admissible : ℕ → ℕ → Prop) (error rate : ℕ → ℕ → ℝ) : Prop :=
  ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L, admissible N L →
    |error N L| ≤ rate N L

theorem uniformLittleOOn_zero
    (admissible : ℕ → ℕ → Prop) (g : ℕ → ℕ → ℝ) :
    UniformLittleOOn admissible (fun _ _ => 0) g := by
  intro ε hε
  refine ⟨0, ?_⟩
  intro N hN L hNL
  simpa using mul_nonneg hε.le (abs_nonneg (g N L))

end PaperC
