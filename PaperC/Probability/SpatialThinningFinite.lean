import PaperC.Probability.ArratiaGoldsteinGordonInput
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Exact finite auxiliary thinning and Laplace identities

This module isolates the finite probability calculation used in Section
14.2.  For a finite family of sites and retention probabilities `q i`, it
constructs the independent Bernoulli product PMF and computes the probability
that no active site is retained.

At the manuscript choice `q i = 1 - exp (-g i)`, the answer is exactly
`exp (-∑_{i active} g i)`.  This is the finite conditional void/Laplace
identity.  No Riemann-sum limit or vague-convergence claim is made here.
-/

namespace PaperC
namespace SpatialThinningFinite

open scoped BigOperators

open ArratiaGoldsteinGordonInput

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- One-coordinate Bernoulli weight. -/
def bernoulliWeight (q : ι → ℝ) (i : ι) (b : Bool) : ℝ :=
  if b = true then q i else 1 - q i

/-- Independent, possibly inhomogeneous, finite Bernoulli product law. -/
noncomputable def bernoulliProductPMF
    (q : ι → ℝ)
    (hq0 : ∀ i, 0 ≤ q i)
    (hq1 : ∀ i, q i ≤ 1) :
    FinitePMF (ι → Bool) where
  prob ξ := ∏ i, bernoulliWeight q i (ξ i)
  nonneg ξ := by
    apply Finset.prod_nonneg
    intro i _hi
    unfold bernoulliWeight
    split_ifs
    · exact hq0 i
    · linarith [hq1 i]
  sum_prob := by
    classical
    change
      (∑ ξ : ι → Bool,
        ∏ i, bernoulliWeight q i (ξ i)) = 1
    rw [← Fintype.prod_sum]
    apply Finset.prod_eq_one
    intro i _hi
    simp [bernoulliWeight]

/-- No active coordinate is retained by the auxiliary thinning. -/
def NoRetainedActive
    (active : ι → Bool) (ξ : ι → Bool) : Prop :=
  ∀ i, active i = true → ξ i = false

/-- Number of coordinates which are both active and retained. -/
noncomputable def thinnedCount
    (active ξ : ι → Bool) : ℕ := by
  classical
  exact
    (Finset.univ.filter fun i ↦
      active i = true ∧ ξ i = true).card

omit [DecidableEq ι] in
theorem thinnedCount_eq_zero_iff
    (active ξ : ι → Bool) :
    thinnedCount active ξ = 0 ↔
      NoRetainedActive active ξ := by
  classical
  unfold thinnedCount NoRetainedActive
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h i hiActive
    have hnot : ¬ξ i = true := by
      intro hiTrue
      exact h (Finset.mem_univ i) ⟨hiActive, hiTrue⟩
    cases hi : ξ i
    · rfl
    · exact (hnot hi).elim
  · intro h i _hi
    push Not
    intro hiActive hiTrue
    have := h i hiActive
    simp_all

omit [DecidableEq ι] in
/--
Pointwise factorization of the indicator of the void event against the
Bernoulli product weight.
-/
theorem voidIndicator_mul_product_eq
    (q : ι → ℝ) (active ξ : ι → Bool) :
    (if NoRetainedActive active ξ then
        ∏ i, bernoulliWeight q i (ξ i)
      else 0) =
      ∏ i,
        if active i = true ∧ ξ i = true then
          0
        else bernoulliWeight q i (ξ i) := by
  classical
  by_cases hvoid : NoRetainedActive active ξ
  · rw [if_pos hvoid]
    apply Finset.prod_congr rfl
    intro i _hi
    rw [if_neg]
    intro h
    have := hvoid i h.1
    simp_all
  · rw [if_neg hvoid]
    unfold NoRetainedActive at hvoid
    push Not at hvoid
    obtain ⟨i, hiActive, hiRetained⟩ := hvoid
    have hiTrue : ξ i = true := by
      cases h : ξ i
      · exact (hiRetained h).elim
      · rfl
    symm
    apply (Finset.prod_eq_zero (Finset.mem_univ i))
    rw [if_pos]
    exact ⟨hiActive, hiTrue⟩

/--
Exact conditional void probability for an arbitrary deterministic active
configuration.
-/
theorem eventProbability_noRetainedActive_eq_prod
    (q : ι → ℝ)
    (hq0 : ∀ i, 0 ≤ q i)
    (hq1 : ∀ i, q i ≤ 1)
    (active : ι → Bool) :
    eventProbability
        (bernoulliProductPMF q hq0 hq1)
        (NoRetainedActive active) =
      ∏ i, if active i = true then 1 - q i else 1 := by
  classical
  unfold eventProbability
  simp only [bernoulliProductPMF]
  simp_rw [voidIndicator_mul_product_eq q active]
  let f : ι → Bool → ℝ :=
    fun i b ↦
      if active i = true ∧ b = true then
        0
      else bernoulliWeight q i b
  calc
    (∑ x : ι → Bool,
        ∏ i,
          if active i = true ∧ x i = true then
            0
          else bernoulliWeight q i (x i)) =
        ∑ x : ι → Bool, ∏ i, f i (x i) := rfl
    _ = ∏ i, ∑ b, f i b :=
      (Fintype.prod_sum f).symm
    _ = ∏ i, if active i = true then 1 - q i else 1 := by
      apply Finset.prod_congr rfl
      intro i _hi
      by_cases hactive : active i = true
      · simp [f, hactive, bernoulliWeight]
      · have hfalse : active i = false := by
          cases h : active i
          · rfl
          · exact (hactive h).elim
        simp [f, hfalse, bernoulliWeight]

/-- Manuscript retention probability `q_i = 1 - exp(-g_i)`. -/
noncomputable def exponentialRetention
    (g : ι → ℝ) (i : ι) : ℝ :=
  1 - Real.exp (-g i)

omit [Fintype ι] [DecidableEq ι] in
theorem exponentialRetention_nonneg
    (g : ι → ℝ) (hg : ∀ i, 0 ≤ g i) (i : ι) :
    0 ≤ exponentialRetention g i := by
  unfold exponentialRetention
  exact sub_nonneg.mpr
    (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hg i)))

omit [Fintype ι] [DecidableEq ι] in
theorem exponentialRetention_le_one
    (g : ι → ℝ) (i : ι) :
    exponentialRetention g i ≤ 1 := by
  unfold exponentialRetention
  linarith [Real.exp_pos (-g i)]

/--
Finite conditional Laplace identity:

`P(no retained active site | active) = exp(-∑ active g)`.
-/
theorem eventProbability_noRetainedActive_exponential_eq
    (g : ι → ℝ) (hg : ∀ i, 0 ≤ g i)
    (active : ι → Bool) :
    eventProbability
        (bernoulliProductPMF
          (exponentialRetention g)
          (fun i ↦ exponentialRetention_nonneg g hg i)
          (fun i ↦ exponentialRetention_le_one g i))
        (NoRetainedActive active) =
      Real.exp
        (-(∑ i, if active i = true then g i else 0)) := by
  rw [eventProbability_noRetainedActive_eq_prod]
  calc
    (∏ i, if active i = true then
          1 - exponentialRetention g i else 1) =
        ∏ i, Real.exp
          (if active i = true then -g i else 0) := by
      apply Finset.prod_congr rfl
      intro i _hi
      by_cases hactive : active i = true
      · simp [hactive, exponentialRetention]
      · simp [hactive]
    _ =
        Real.exp
          (∑ i, if active i = true then -g i else 0) := by
      rw [Real.exp_sum]
    _ =
        Real.exp
          (-(∑ i, if active i = true then g i else 0)) := by
      congr 1
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _hi
      by_cases hactive : active i = true <;>
        simp [hactive]

/--
Equivalent count form of the finite Laplace identity, matching the manuscript
event `W_g = 0`.
-/
theorem eventProbability_thinnedCount_zero_exponential_eq
    (g : ι → ℝ) (hg : ∀ i, 0 ≤ g i)
    (active : ι → Bool) :
    eventProbability
        (bernoulliProductPMF
          (exponentialRetention g)
          (fun i ↦ exponentialRetention_nonneg g hg i)
          (fun i ↦ exponentialRetention_le_one g i))
        (fun ξ ↦ thinnedCount active ξ = 0) =
      Real.exp
        (-(∑ i, if active i = true then g i else 0)) := by
  have hevent :
      (fun ξ : ι → Bool ↦ thinnedCount active ξ = 0) =
        NoRetainedActive active := by
    funext ξ
    apply propext
    exact thinnedCount_eq_zero_iff active ξ
  rw [hevent]
  exact eventProbability_noRetainedActive_exponential_eq g hg active

omit [DecidableEq ι] in
/--
The weighted Poisson parameter of a thinned finite family is bounded by the
unthinned parameter.
-/
theorem sum_retention_mul_le_sum
    (q p : ι → ℝ)
    (hq1 : ∀ i, q i ≤ 1)
    (hp : ∀ i, 0 ≤ p i) :
    (∑ i, q i * p i) ≤ ∑ i, p i := by
  apply Finset.sum_le_sum
  intro i _hi
  exact mul_le_of_le_one_left (hp i) (hq1 i)

omit [DecidableEq ι] in
/--
The pair-weighted Stein--Chen summand is likewise dominated coordinatewise.
-/
theorem sum_pair_retention_mul_le_sum
    (q : ι → ℝ) (p : ι → ι → ℝ)
    (hq0 : ∀ i, 0 ≤ q i)
    (hq1 : ∀ i, q i ≤ 1)
    (hp : ∀ i j, 0 ≤ p i j) :
    (∑ i, ∑ j, q i * q j * p i j) ≤
      ∑ i, ∑ j, p i j := by
  apply Finset.sum_le_sum
  intro i _hi
  apply Finset.sum_le_sum
  intro j _hj
  have hqq0 : 0 ≤ q i * q j :=
    mul_nonneg (hq0 i) (hq0 j)
  have hqq1 : q i * q j ≤ 1 := by
    nlinarith [hq0 i, hq0 j, hq1 i, hq1 j]
  nlinarith [hp i j]

end

end SpatialThinningFinite
end PaperC
