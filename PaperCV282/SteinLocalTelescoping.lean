import PaperCV282.SteinFiniteExpectation

/-!
# One-vertex Stein telescoping under exact dependence

The outside count is independent of the indicator at the chosen vertex.
Neighbour marginals remain their actual probabilities, including when a
neighbour belongs to an exceptional set. No Poisson approximation theorem
or Stein solution estimate is assumed in this algebraic bound.
-/

namespace PaperC.V282.SteinLocalTelescoping

open ArratiaGoldsteinGordonInput IndependentThinning SteinFiniteExpectation
open scoped BigOperators

noncomputable section

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]

omit [Fintype Ω] in
/-- The first difference between the full count and the outside count. -/
theorem full_outside_difference_le (X : ι → Ω → Bool) (G : SimpleGraph ι)
    (i : ι) (f : ℕ → ℝ) {d : ℝ}
    (hd : ∀ k, |f (k + 1) - f k| ≤ d) (ω : Ω) :
    |f (indicatorSum X ω + 1) -
      f (countOn X (Finset.univ \ closedNeighborhood G i) ω + 1)| ≤
      d * countOn X (closedNeighborhood G i) ω := by
  have h := countOn_partition X (closedNeighborhood G i) ω
  rw [show indicatorSum X ω + 1 =
    (countOn X (Finset.univ \ closedNeighborhood G i) ω + 1) +
      countOn X (closedNeighborhood G i) ω by omega]
  exact abs_sub_le_step_mul f hd _ _

omit [Fintype Ω] in
/-- On an active site only the other neighbours contribute to the displacement. -/
theorem active_outside_difference_le (X : ι → Ω → Bool) (G : SimpleGraph ι)
    (i : ι) (f : ℕ → ℝ) {d : ℝ}
    (hd : ∀ k, |f (k + 1) - f k| ≤ d) (ω : Ω) :
    (if X i ω = true then (1 : ℝ) else 0) *
      |f (countOn X (Finset.univ \ closedNeighborhood G i) ω + 1) -
        f (indicatorSum X ω)| ≤
      d * ((if X i ω = true then (1 : ℝ) else 0) *
        countOn X ((closedNeighborhood G i).erase i) ω) := by
  by_cases hi : X i ω = true
  · simp only [hi, if_true, one_mul]
    have hp := countOn_partition X (closedNeighborhood G i) ω
    have he := countOn_erase X (self_mem_closedNeighborhood G i) ω
    simp only [hi, if_true] at he
    rw [show indicatorSum X ω =
      (countOn X (Finset.univ \ closedNeighborhood G i) ω + 1) +
        countOn X ((closedNeighborhood G i).erase i) ω by omega, abs_sub_comm]
    exact abs_sub_le_step_mul f hd _ _
  · simp [hi]

/-- Literal one-site telescoping bound, with the true marginals of all neighbours. -/
theorem local_stein_error_le (μ : FinitePMF Ω) (X : ι → Ω → Bool)
    (G : SimpleGraph ι) (hdep : HasExactDependencyGraph μ X G)
    (i : ι) (f : ℕ → ℝ) {d : ℝ}
    (hd : ∀ k, |f (k + 1) - f k| ≤ d) :
    |marginal μ X i * finitePMFExpectation μ (fun ω => f (indicatorSum X ω + 1)) -
      finitePMFExpectation μ (fun ω =>
        (if X i ω = true then (1 : ℝ) else 0) * f (indicatorSum X ω))| ≤
      d * (marginal μ X i ^ 2 +
        marginal μ X i * ∑ j ∈ (closedNeighborhood G i).erase i, marginal μ X j +
        ∑ j ∈ (closedNeighborhood G i).erase i, jointMarginal μ X i j) := by
  classical
  let p := marginal μ X i
  let U : Ω → ℕ := countOn X ((closedNeighborhood G i).erase i)
  let V : Ω → ℕ := countOn X (Finset.univ \ closedNeighborhood G i)
  let bit : Ω → ℝ := fun ω => if X i ω = true then 1 else 0
  have hp : 0 ≤ p := marginal_nonneg μ X i
  have hfactor := expectation_indicator_outside μ X G hdep i f
  have hfirst :
      |finitePMFExpectation μ (fun ω => f (indicatorSum X ω + 1) - f (V ω + 1))| ≤
        d * finitePMFExpectation μ (fun ω => (countOn X (closedNeighborhood G i) ω : ℝ)) := by
    calc
      _ ≤ finitePMFExpectation μ (fun ω => |f (indicatorSum X ω + 1) - f (V ω + 1)|) :=
        abs_expectation_le μ _
      _ ≤ finitePMFExpectation μ (fun ω => d * countOn X (closedNeighborhood G i) ω) :=
        expectation_mono μ (full_outside_difference_le X G i f hd)
      _ = _ := expectation_const_mul μ _ _
  have hsecond :
      |finitePMFExpectation μ (fun ω => bit ω * (f (V ω + 1) - f (indicatorSum X ω)))| ≤
        d * finitePMFExpectation μ (fun ω => bit ω * U ω) := by
    calc
      _ ≤ finitePMFExpectation μ (fun ω => |bit ω * (f (V ω + 1) - f (indicatorSum X ω))|) :=
        abs_expectation_le μ _
      _ = finitePMFExpectation μ (fun ω => bit ω * |f (V ω + 1) - f (indicatorSum X ω)|) := by
        apply expectation_congr
        intro ω
        rw [abs_mul, abs_of_nonneg (show 0 ≤ bit ω by dsimp [bit]; split_ifs <;> norm_num)]
      _ ≤ finitePMFExpectation μ (fun ω => d * (bit ω * U ω)) :=
        expectation_mono μ (active_outside_difference_le X G i f hd)
      _ = _ := expectation_const_mul μ _ _
  have heq :
      p * finitePMFExpectation μ (fun ω => f (indicatorSum X ω + 1)) -
        finitePMFExpectation μ (fun ω => bit ω * f (indicatorSum X ω)) =
      p * finitePMFExpectation μ (fun ω => f (indicatorSum X ω + 1) - f (V ω + 1)) +
        finitePMFExpectation μ (fun ω => bit ω * (f (V ω + 1) - f (indicatorSum X ω))) := by
    rw [expectation_sub]
    simp_rw [mul_sub]
    rw [expectation_sub]
    change _ = _ + (finitePMFExpectation μ (fun ω =>
      (if X i ω = true then (1 : ℝ) else 0) *
        f (countOn X (Finset.univ \ closedNeighborhood G i) ω + 1)) - _)
    rw [hfactor]
    dsimp only [p, V]
    ring
  change |p * _ - finitePMFExpectation μ (fun ω => bit ω * f (indicatorSum X ω))| ≤ _
  rw [heq]
  have hbound := (abs_add_le
    (p * finitePMFExpectation μ (fun ω => f (indicatorSum X ω + 1) - f (V ω + 1)))
    (finitePMFExpectation μ (fun ω => bit ω * (f (V ω + 1) - f (indicatorSum X ω)))))
  rw [abs_mul, abs_of_nonneg hp] at hbound
  have hmono := mul_le_mul_of_nonneg_left hfirst hp
  have hEclosed := expectation_countOn μ X (closedNeighborhood G i)
  have hEsum := Finset.add_sum_erase (closedNeighborhood G i) (fun j => marginal μ X j)
    (self_mem_closedNeighborhood G i)
  have hEjoint := expectation_indicator_countOn μ X i ((closedNeighborhood G i).erase i)
  change finitePMFExpectation μ (fun ω => bit ω * U ω) = _ at hEjoint
  rw [hEclosed, ← hEsum] at hmono
  rw [hEjoint] at hsecond
  dsimp only [p] at *
  nlinarith

end
end PaperC.V282.SteinLocalTelescoping
