import PaperC.Probability.IndependentThinning

/-!
# Finite expectation and count identities for Stein telescoping

These identities apply to arbitrary finite probability laws, without a
uniformity or an independence assumption. The exact graph hypothesis is
used only to factor a local indicator from its complete outside vector.
-/

namespace PaperC.V282.SteinFiniteExpectation

open ArratiaGoldsteinGordonInput IndependentThinning
open scoped BigOperators

noncomputable section

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]

theorem expectation_congr (μ : FinitePMF Ω) {f g : Ω → ℝ}
    (h : ∀ ω, f ω = g ω) : finitePMFExpectation μ f = finitePMFExpectation μ g := by
  unfold finitePMFExpectation
  exact Finset.sum_congr rfl (fun ω _ => congrArg (μ.prob ω * ·) (h ω))

theorem expectation_add (μ : FinitePMF Ω) (f g : Ω → ℝ) :
    finitePMFExpectation μ (fun ω => f ω + g ω) =
      finitePMFExpectation μ f + finitePMFExpectation μ g := by
  simp [finitePMFExpectation, mul_add, Finset.sum_add_distrib]

theorem expectation_sub (μ : FinitePMF Ω) (f g : Ω → ℝ) :
    finitePMFExpectation μ (fun ω => f ω - g ω) =
      finitePMFExpectation μ f - finitePMFExpectation μ g := by
  simp [finitePMFExpectation, mul_sub, Finset.sum_sub_distrib]

theorem expectation_mul_const (μ : FinitePMF Ω) (f : Ω → ℝ) (c : ℝ) :
    finitePMFExpectation μ (fun ω => f ω * c) = finitePMFExpectation μ f * c := by
  simp [finitePMFExpectation, ← mul_assoc, Finset.sum_mul]

theorem expectation_const_mul (μ : FinitePMF Ω) (c : ℝ) (f : Ω → ℝ) :
    finitePMFExpectation μ (fun ω => c * f ω) = c * finitePMFExpectation μ f := by
  simp_rw [mul_comm c]
  exact expectation_mul_const μ f c

theorem expectation_const (μ : FinitePMF Ω) (c : ℝ) :
    finitePMFExpectation μ (fun _ => c) = c := by
  simp [finitePMFExpectation, ← Finset.sum_mul, μ.sum_prob]

omit [Fintype ι] [DecidableEq ι] in
theorem expectation_finset_sum (μ : FinitePMF Ω) (s : Finset ι) (f : ι → Ω → ℝ) :
    finitePMFExpectation μ (fun ω => ∑ i ∈ s, f i ω) =
      ∑ i ∈ s, finitePMFExpectation μ (f i) := by
  simp only [finitePMFExpectation, Finset.mul_sum]
  exact Finset.sum_comm

theorem expectation_nonneg (μ : FinitePMF Ω) {f : Ω → ℝ} (h : ∀ ω, 0 ≤ f ω) :
    0 ≤ finitePMFExpectation μ f :=
  Finset.sum_nonneg (fun ω _ => mul_nonneg (μ.nonneg ω) (h ω))

theorem expectation_mono (μ : FinitePMF Ω) {f g : Ω → ℝ} (h : ∀ ω, f ω ≤ g ω) :
    finitePMFExpectation μ f ≤ finitePMFExpectation μ g :=
  Finset.sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left (h ω) (μ.nonneg ω))

theorem abs_expectation_le (μ : FinitePMF Ω) (f : Ω → ℝ) :
    |finitePMFExpectation μ f| ≤ finitePMFExpectation μ (fun ω => |f ω|) := by
  unfold finitePMFExpectation
  calc
    _ ≤ ∑ ω, |μ.prob ω * f ω| := Finset.abs_sum_le_sum_abs _ _
    _ = _ := by simp_rw [abs_mul, abs_of_nonneg (μ.nonneg _)]

/-- Number of active indicators in a specified finite set. -/
def countOn (X : ι → Ω → Bool) (s : Finset ι) (ω : Ω) : ℕ :=
  ∑ i ∈ s, if X i ω = true then 1 else 0

omit [Fintype Ω] [DecidableEq ι] in
theorem countOn_univ (X : ι → Ω → Bool) (ω : Ω) :
    countOn X Finset.univ ω = indicatorSum X ω := by
  classical
  simp only [countOn, indicatorSum, Finset.card_filter]

omit [Fintype Ω] [Fintype ι] [DecidableEq ι] in
theorem countOn_cast (X : ι → Ω → Bool) (s : Finset ι) (ω : Ω) :
    (countOn X s ω : ℝ) = ∑ i ∈ s, if X i ω = true then (1 : ℝ) else 0 := by
  simp [countOn]

omit [Fintype ι] [DecidableEq ι] in
theorem expectation_indicator_eq_marginal (μ : FinitePMF Ω) (X : ι → Ω → Bool) (i : ι) :
    finitePMFExpectation μ (fun ω => if X i ω = true then (1 : ℝ) else 0) = marginal μ X i := by
  classical
  unfold finitePMFExpectation marginal eventProbability
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : X i ω = true <;> simp [h]

omit [Fintype ι] [DecidableEq ι] in
theorem expectation_countOn (μ : FinitePMF Ω) (X : ι → Ω → Bool) (s : Finset ι) :
    finitePMFExpectation μ (fun ω => (countOn X s ω : ℝ)) =
      ∑ i ∈ s, marginal μ X i := by
  classical
  simp_rw [countOn_cast]
  rw [expectation_finset_sum]
  exact Finset.sum_congr rfl (fun i _ => expectation_indicator_eq_marginal μ X i)

omit [Fintype ι] [DecidableEq ι] in
theorem expectation_indicator_mul (μ : FinitePMF Ω) (X : ι → Ω → Bool) (i j : ι) :
    finitePMFExpectation μ
      (fun ω => (if X i ω = true then (1 : ℝ) else 0) *
        (if X j ω = true then (1 : ℝ) else 0)) = jointMarginal μ X i j := by
  classical
  unfold finitePMFExpectation jointMarginal eventProbability
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hi : X i ω = true <;> by_cases hj : X j ω = true <;> simp [hi, hj]

omit [Fintype ι] [DecidableEq ι] in
theorem expectation_indicator_countOn (μ : FinitePMF Ω) (X : ι → Ω → Bool)
    (i : ι) (s : Finset ι) :
    finitePMFExpectation μ (fun ω =>
      (if X i ω = true then (1 : ℝ) else 0) * (countOn X s ω : ℝ)) =
      ∑ j ∈ s, jointMarginal μ X i j := by
  simp_rw [countOn_cast, Finset.mul_sum]
  rw [expectation_finset_sum]
  exact Finset.sum_congr rfl (fun j _ => expectation_indicator_mul μ X i j)

omit [Fintype Ω] in
theorem countOn_partition (X : ι → Ω → Bool) (s : Finset ι) (ω : Ω) :
    countOn X s ω + countOn X (Finset.univ \ s) ω = indicatorSum X ω := by
  rw [← countOn_univ]
  unfold countOn
  exact Finset.sum_add_sum_compl s _

omit [Fintype Ω] [Fintype ι] in
theorem countOn_erase (X : ι → Ω → Bool) {s : Finset ι} {i : ι}
    (hi : i ∈ s) (ω : Ω) :
    countOn X s ω = (if X i ω = true then 1 else 0) + countOn X (s.erase i) ω := by
  unfold countOn
  exact (Finset.add_sum_erase _ _ hi).symm

/-- Exact independence from the outside count, with arbitrary real test function. -/
theorem expectation_indicator_outside (μ : FinitePMF Ω) (X : ι → Ω → Bool)
    (G : SimpleGraph ι) (hdep : HasExactDependencyGraph μ X G)
    (i : ι) (f : ℕ → ℝ) :
    finitePMFExpectation μ (fun ω =>
      (if X i ω = true then (1 : ℝ) else 0) *
        f (countOn X (Finset.univ \ closedNeighborhood G i) ω + 1)) =
      marginal μ X i * finitePMFExpectation μ
        (fun ω => f (countOn X (Finset.univ \ closedNeighborhood G i) ω + 1)) := by
  classical
  letI : Finite (OutsideIndex G i) := Finite.of_injective Subtype.val Subtype.coe_injective
  letI : Fintype (OutsideIndex G i) := Fintype.ofFinite _
  let v : (OutsideIndex G i → Bool) → ℝ := fun pattern =>
    f ((∑ j : OutsideIndex G i, if pattern j = true then 1 else 0) + 1)
  have hv (ω : Ω) : v (outsideVector X G i ω) =
      f (countOn X (Finset.univ \ closedNeighborhood G i) ω + 1) := by
    dsimp [v, outsideVector, countOn]
    congr 2
    exact (Finset.sum_subtype (Finset.univ \ closedNeighborhood G i)
      (fun j => by simp) (fun j => if X j ω = true then (1 : ℕ) else 0)).symm
  have hh := finitePMFExpectation_mul_of_hasExactDependencyGraph μ X G hdep i
    (fun b => if b = true then (1 : ℝ) else 0) v
  simp_rw [hv] at hh
  rw [expectation_indicator_eq_marginal] at hh
  exact hh

/-- A first-difference bound telescopes over any natural displacement. -/
theorem abs_sub_le_step_mul (f : ℕ → ℝ) {d : ℝ}
    (hd : ∀ k, |f (k + 1) - f k| ≤ d) (n k : ℕ) :
    |f (n + k) - f n| ≤ d * k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := abs_add_le (f (n + k + 1) - f (n + k)) (f (n + k) - f n)
    have heq : f (n + k + 1) - f (n + k) + (f (n + k) - f n) =
        f (n + k + 1) - f n := by ring
    rw [heq] at h
    have hh := hd (n + k)
    push_cast
    simpa only [Nat.add_succ] using (show |f (n + k + 1) - f n| ≤ d * (k + 1) by nlinarith)

end
end PaperC.V282.SteinFiniteExpectation
