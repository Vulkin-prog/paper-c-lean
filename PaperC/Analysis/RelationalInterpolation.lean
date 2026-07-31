import PaperC.Asymptotics.Uniform
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Relational interpolation

This file formalizes the Cauchy--Schwarz step of Lemma 4.3 independently of
the future affine system for two starts.  For a finite set `A` and real
weights `u`,

`∑ a ∈ A, u a ≤ √(#A) * √(∑ a ∈ A, (u a)^2)`.

The second layer allows `A` to be any subset of a parametrized finite set of
relational hosts.  The final theorem packages the same argument with uniform
eventual cardinality and quadratic-mass bounds; callers may instantiate those
two bounds with whichever quantified convention for
`N^(3/2+o(1))` and `N^(5/2-δ+o(1))` they use.
-/

namespace PaperC
namespace RelationalInterpolation

open scoped BigOperators

/--
Finite Cauchy--Schwarz inequality in the exact form used in equation (4.3).
It is valid for arbitrary real weights; nonnegativity is only needed when the
left-hand side is also required to be nonnegative.
-/
theorem sum_le_sqrt_card_mul_sqrt_sum_sq
    {α : Type*} [DecidableEq α]
    (A : Finset α) (u : α → ℝ) :
    ∑ a ∈ A, u a ≤
      Real.sqrt (A.card : ℝ) *
        Real.sqrt (∑ a ∈ A, (u a) ^ 2) := by
  simpa using
    (Real.sum_mul_le_sqrt_mul_sqrt
      A (fun _a : α => (1 : ℝ)) u)

/--
For nonnegative weights, the interpolated sum is itself nonnegative in
addition to satisfying the Cauchy--Schwarz upper bound.
-/
theorem sum_nonneg_and_le_sqrt_card_mul_sqrt_sum_sq
    {α : Type*} [DecidableEq α]
    (A : Finset α) (u : α → ℝ)
    (hu : ∀ a ∈ A, 0 ≤ u a) :
    0 ≤ ∑ a ∈ A, u a ∧
      ∑ a ∈ A, u a ≤
        Real.sqrt (A.card : ℝ) *
          Real.sqrt (∑ a ∈ A, (u a) ^ 2) := by
  exact
    ⟨Finset.sum_nonneg hu,
      sum_le_sqrt_card_mul_sqrt_sum_sq A u⟩

/--
Specialization to a subset `A` of a parametrized set of relational hosts.
An upper bound `H₂` for the total host cardinality replaces `#A`.

The function `relationalHosts` is a parameter, so this theorem does not
depend on any particular construction of the two-start system.
-/
theorem sum_le_sqrt_relationalHosts_bound_mul_sqrt_sum_sq
    {α : Type*} [DecidableEq α]
    (relationalHosts : ℕ → ℕ → Finset α)
    {N L : ℕ} {A : Finset α} {u : α → ℝ} {H₂ : ℝ}
    (hsubset : A ⊆ relationalHosts N L)
    (hcard :
      ((relationalHosts N L).card : ℝ) ≤ H₂) :
    ∑ a ∈ A, u a ≤
      Real.sqrt H₂ *
        Real.sqrt (∑ a ∈ A, (u a) ^ 2) := by
  have hcardA :
      (A.card : ℝ) ≤ H₂ := by
    have hcardNat :
        A.card ≤ (relationalHosts N L).card :=
      Finset.card_le_card hsubset
    have hcardCast :
        (A.card : ℝ) ≤
          ((relationalHosts N L).card : ℝ) := by
      exact_mod_cast hcardNat
    exact hcardCast.trans hcard
  calc
    ∑ a ∈ A, u a ≤
        Real.sqrt (A.card : ℝ) *
          Real.sqrt (∑ a ∈ A, (u a) ^ 2) :=
      sum_le_sqrt_card_mul_sqrt_sum_sq A u
    _ ≤ Real.sqrt H₂ *
        Real.sqrt (∑ a ∈ A, (u a) ^ 2) :=
      mul_le_mul_of_nonneg_right
        (Real.sqrt_le_sqrt hcardA) (Real.sqrt_nonneg _)

/--
Fully bounded finite interface: a host-cardinality bound `H₂` and a
quadratic-mass bound `Q` yield the product of their square roots.
-/
theorem sum_le_sqrt_relationalHosts_bound_mul_sqrt_sqBound
    {α : Type*} [DecidableEq α]
    (relationalHosts : ℕ → ℕ → Finset α)
    {N L : ℕ} {A : Finset α} {u : α → ℝ} {H₂ Q : ℝ}
    (hsubset : A ⊆ relationalHosts N L)
    (hcard :
      ((relationalHosts N L).card : ℝ) ≤ H₂)
    (hsq : (∑ a ∈ A, (u a) ^ 2) ≤ Q) :
    ∑ a ∈ A, u a ≤
      Real.sqrt H₂ * Real.sqrt Q := by
  calc
    ∑ a ∈ A, u a ≤
        Real.sqrt H₂ *
          Real.sqrt (∑ a ∈ A, (u a) ^ 2) :=
      sum_le_sqrt_relationalHosts_bound_mul_sqrt_sum_sq
        relationalHosts hsubset hcard
    _ ≤ Real.sqrt H₂ * Real.sqrt Q :=
      mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt hsq) (Real.sqrt_nonneg _)

/--
Power-form interpolation.  If the host count is at most `N^a` and the
quadratic mass is at most `N^b`, then Cauchy--Schwarz gives the averaged
exponent `N^((a+b)/2)`.
-/
theorem sum_le_rpow_average
    {α : Type*} [DecidableEq α]
    {N : ℕ} (hN : 1 ≤ N)
    {A : Finset α} {u : α → ℝ} {a b : ℝ}
    (hcard : (A.card : ℝ) ≤ (N : ℝ) ^ a)
    (hsq :
      (∑ x ∈ A, (u x) ^ 2) ≤ (N : ℝ) ^ b) :
    ∑ x ∈ A, u x ≤
      (N : ℝ) ^ ((a + b) / 2) := by
  have hNpos : 0 < (N : ℝ) := by
    exact_mod_cast Nat.zero_lt_of_lt hN
  have hNnonneg : 0 ≤ (N : ℝ) := hNpos.le
  calc
    ∑ x ∈ A, u x ≤
        Real.sqrt (A.card : ℝ) *
          Real.sqrt (∑ x ∈ A, (u x) ^ 2) :=
      sum_le_sqrt_card_mul_sqrt_sum_sq A u
    _ ≤ Real.sqrt ((N : ℝ) ^ a) *
          Real.sqrt ((N : ℝ) ^ b) := by
      exact mul_le_mul
        (Real.sqrt_le_sqrt hcard)
        (Real.sqrt_le_sqrt hsq)
        (Real.sqrt_nonneg _)
        (Real.sqrt_nonneg _)
    _ = (N : ℝ) ^ (a / 2) *
          (N : ℝ) ^ (b / 2) := by
      congr 1 <;>
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hNnonneg] <;>
        congr 1 <;> ring
    _ = (N : ℝ) ^ ((a + b) / 2) := by
      rw [← Real.rpow_add hNpos]
      congr 1
      ring

/--
The exponent arithmetic stated after (4.3): combining
`N^(3/2+ε)` relational hosts with quadratic mass
`N^(5/2-δ+ε)` gives linear mass `N^(2-δ/2+ε)`.
-/
theorem sum_le_two_sub_half_delta_add_error
    {α : Type*} [DecidableEq α]
    {N : ℕ} (hN : 1 ≤ N)
    {A : Finset α} {u : α → ℝ} {δ ε : ℝ}
    (hcard :
      (A.card : ℝ) ≤
        (N : ℝ) ^ ((3 : ℝ) / 2 + ε))
    (hsq :
      (∑ x ∈ A, (u x) ^ 2) ≤
        (N : ℝ) ^ ((5 : ℝ) / 2 - δ + ε)) :
    ∑ x ∈ A, u x ≤
      (N : ℝ) ^ (2 - δ / 2 + ε) := by
  convert sum_le_rpow_average hN hcard hsq using 1
  ring

/--
Relational-host specialization of the preceding exponent calculation:
membership of `A` in the host population supplies its cardinality bound.
-/
theorem sum_le_two_sub_half_delta_add_error_of_subset
    {α : Type*} [DecidableEq α]
    (relationalHosts : ℕ → ℕ → Finset α)
    {N L : ℕ} (hN : 1 ≤ N)
    {A : Finset α} {u : α → ℝ} {δ ε : ℝ}
    (hsubset : A ⊆ relationalHosts N L)
    (hhosts :
      ((relationalHosts N L).card : ℝ) ≤
        (N : ℝ) ^ ((3 : ℝ) / 2 + ε))
    (hsq :
      (∑ x ∈ A, (u x) ^ 2) ≤
        (N : ℝ) ^ ((5 : ℝ) / 2 - δ + ε)) :
    ∑ x ∈ A, u x ≤
      (N : ℝ) ^ (2 - δ / 2 + ε) := by
  apply sum_le_two_sub_half_delta_add_error hN _ hsq
  exact
    (by exact_mod_cast Finset.card_le_card hsubset : (A.card : ℝ) ≤
      ((relationalHosts N L).card : ℝ)).trans hhosts

/--
Uniform eventual interpolation interface.

If `A(N,L)` is contained in the relational-host set, the host cardinality is
eventually at most `H₂(N,L)`, and the quadratic mass is eventually at most
`Q(N,L)`, then the weighted sum is eventually bounded by
`√H₂(N,L) * √Q(N,L)`.  Nonnegative weights also give the lower bound zero.
-/
theorem eventually_sum_nonneg_and_le_sqrt_mul_sqrt
    {α : Type*} [DecidableEq α]
    (admissible : ℕ → ℕ → Prop)
    (relationalHosts A : ℕ → ℕ → Finset α)
    (u : ℕ → ℕ → α → ℝ)
    (H₂ Q : ℕ → ℕ → ℝ)
    (hsubset :
      ∀ N L, admissible N L →
        A N L ⊆ relationalHosts N L)
    (hu :
      ∀ N L, admissible N L →
        ∀ a ∈ A N L, 0 ≤ u N L a)
    (hcard :
      ∃ Ncard : ℕ, ∀ N ≥ Ncard, ∀ L,
        admissible N L →
          ((relationalHosts N L).card : ℝ) ≤ H₂ N L)
    (hsq :
      ∃ Nsq : ℕ, ∀ N ≥ Nsq, ∀ L,
        admissible N L →
          (∑ a ∈ A N L, (u N L a) ^ 2) ≤ Q N L) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L,
      admissible N L →
        0 ≤ ∑ a ∈ A N L, u N L a ∧
          ∑ a ∈ A N L, u N L a ≤
            Real.sqrt (H₂ N L) * Real.sqrt (Q N L) := by
  obtain ⟨Ncard, hcard⟩ := hcard
  obtain ⟨Nsq, hsq⟩ := hsq
  refine ⟨max Ncard Nsq, ?_⟩
  intro N hN L hNL
  constructor
  · exact Finset.sum_nonneg (hu N L hNL)
  · exact
      sum_le_sqrt_relationalHosts_bound_mul_sqrt_sqBound
        relationalHosts
        (hsubset N L hNL)
        (hcard N ((le_max_left _ _).trans hN) L hNL)
        (hsq N ((le_max_right _ _).trans hN) L hNL)

end RelationalInterpolation
end PaperC
