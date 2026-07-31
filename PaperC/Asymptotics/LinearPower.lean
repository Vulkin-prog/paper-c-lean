import PaperC.Asymptotics.ExpSqrtLog

/-!
# A quantified meaning of `N^(1+o(1))`

The touching-pair estimate in Lemma 3.4(ii) has one linear factor in the
number of possible starts and a subpolynomial loss.  The predicate below
records that upper bound with the same reciprocal-power convention used
elsewhere in the formalization.
-/

namespace PaperC

namespace ExpSqrtLog

/--
Eventual-bound variant of
`uniformSubpolynomialOn_two_pow_log_div_loglog`.

This is useful when the logarithmic exponent estimate itself comes from an
asymptotic theorem and therefore only holds beyond a uniform threshold.
-/
theorem uniformSubpolynomialOn_two_pow_log_div_loglog_eventually
    (admissible : ℕ → ℕ → Prop)
    (M : ℕ → ℕ → ℕ)
    (D : ℝ) (hD : 0 ≤ D)
    (hM :
      ∃ N₁ : ℕ, ∀ N ≥ N₁, ∀ L, admissible N L →
        (M N L : ℝ) ≤
          D * Real.log N / Real.log (Real.log N)) :
    UniformSubpolynomialOn admissible
      (fun N L => (((2 ^ M N L : ℕ) : ℝ))) := by
  intro k hk
  obtain ⟨Npow, hNpow⟩ :=
    two_pow_log_div_loglog_pow_le_nat_eventually D hD k hk
  obtain ⟨Nbound, hNbound⟩ := hM
  refine ⟨max Npow Nbound, ?_⟩
  intro N hN L hNL
  have hnonneg : 0 ≤ (((2 ^ M N L : ℕ) : ℝ)) := by positivity
  simpa only [abs_of_nonneg hnonneg] using
    hNpow N ((le_max_left _ _).trans hN) (M N L)
      (hNbound N ((le_max_right _ _).trans hN) L hNL)

end ExpSqrtLog

/--
Uniform reciprocal-power formulation of the upper bound
`|f(N,L)| ≤ N^(1+o(1))`.

For every positive `k`, the exponent loss can be made at most `1/k`:
`|f|^k ≤ N^(k+1)`, uniformly in the admissible auxiliary parameter.
-/
def UniformLinearSubpolynomialOn
    (admissible : ℕ → ℕ → Prop) (f : ℕ → ℕ → ℝ) : Prop :=
  ∀ k : ℕ, 0 < k →
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L, admissible N L →
      |f N L| ^ k ≤ (N : ℝ) ^ (k + 1)

namespace UniformLinear

/--
A linear factor in `N` times a uniformly subpolynomial factor is
`N^(1+o(1))`.
-/
theorem of_linear_mul_subpolynomial
    {admissible : ℕ → ℕ → Prop}
    {f q : ℕ → ℕ → ℝ}
    (hq : UniformSubpolynomialOn admissible q)
    (hbound :
      ∃ N₁ : ℕ, ∀ N ≥ N₁, ∀ L, admissible N L →
        |f N L| ≤ (N : ℝ) * |q N L|) :
    UniformLinearSubpolynomialOn admissible f := by
  intro k hk
  obtain ⟨Nq, hNq⟩ := hq k hk
  obtain ⟨Nb, hNb⟩ := hbound
  refine ⟨max Nq Nb, ?_⟩
  intro N hN L hNL
  have hNqN : Nq ≤ N := (le_max_left _ _).trans hN
  have hNbN : Nb ≤ N := (le_max_right _ _).trans hN
  calc
    |f N L| ^ k ≤ ((N : ℝ) * |q N L|) ^ k :=
      pow_le_pow_left₀ (abs_nonneg _) (hNb N hNbN L hNL) _
    _ = (N : ℝ) ^ k * |q N L| ^ k := by
      rw [mul_pow]
    _ ≤ (N : ℝ) ^ k * (N : ℝ) :=
      mul_le_mul_of_nonneg_left (hNq N hNqN L hNL) (by positivity)
    _ = (N : ℝ) ^ (k + 1) := by
      rw [pow_succ]

/-- The linear-power predicate is stable under eventual domination. -/
theorem mono
    {admissible : ℕ → ℕ → Prop}
    {f g : ℕ → ℕ → ℝ}
    (hg : UniformLinearSubpolynomialOn admissible g)
    (hfg :
      ∃ N₁ : ℕ, ∀ N ≥ N₁, ∀ L, admissible N L →
        |f N L| ≤ |g N L|) :
    UniformLinearSubpolynomialOn admissible f := by
  intro k hk
  obtain ⟨Ng, hNg⟩ := hg k hk
  obtain ⟨Nb, hNb⟩ := hfg
  refine ⟨max Ng Nb, ?_⟩
  intro N hN L hNL
  exact
    (pow_le_pow_left₀ (abs_nonneg _)
      (hNb N ((le_max_right _ _).trans hN) L hNL) _).trans
      (hNg N ((le_max_left _ _).trans hN) L hNL)

end UniformLinear
end PaperC
