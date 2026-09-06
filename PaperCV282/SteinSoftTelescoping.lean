import PaperCV282.SteinLocalTelescoping

/-!
# Keeping exceptional indicators in the scalar Stein equation

This is the finite telescoping calculation of companion Lemma B.2. Only
good sites have the common marginal p. Exceptional neighbours retain
their actual marginal and joint probabilities throughout the bound.
The test function and its two norm bounds are explicit parameters.
-/

namespace PaperC.V282.SteinSoftTelescoping

open ArratiaGoldsteinGordonInput IndependentThinning
open SteinFiniteExpectation SteinLocalTelescoping
open scoped BigOperators

noncomputable section

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]

/-- The good-site cost in (B.4), including actual exceptional-neighbour marginals. -/
def goodSteinCost (μ : FinitePMF Ω) (X : ι → Ω → Bool) (G : SimpleGraph ι)
    (good : Finset ι) (p : ℝ) : ℝ :=
  good.card * p ^ 2 +
    p * (∑ i ∈ good, ∑ j ∈ (closedNeighborhood G i).erase i, marginal μ X j) +
    ∑ i ∈ good, ∑ j ∈ (closedNeighborhood G i).erase i, jointMarginal μ X i j

theorem goodSteinCost_nonneg (μ : FinitePMF Ω) (X : ι → Ω → Bool)
    (G : SimpleGraph ι) (good : Finset ι) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ goodSteinCost μ X G good p := by
  unfold goodSteinCost
  apply add_nonneg
  · exact add_nonneg (by positivity) (mul_nonneg hp
      (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => marginal_nonneg μ X j))
  · exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => jointMarginal_nonneg μ X i j

omit [Fintype ι] [DecidableEq ι] in
/-- A bounded test function costs at most its bound under a probability law. -/
theorem abs_expectation_bounded (μ : FinitePMF Ω) (F : Ω → ℝ) {c : ℝ}
    (hF : ∀ ω, |F ω| ≤ c) : |finitePMFExpectation μ F| ≤ c := by
  calc
    _ ≤ finitePMFExpectation μ (fun ω => |F ω|) := abs_expectation_le μ F
    _ ≤ finitePMFExpectation μ (fun _ => c) := expectation_mono μ hF
    _ = c := expectation_const μ c

omit [DecidableEq ι] in
/-- Exceptional indicators are paid through their actual first moment. -/
theorem exceptional_error_le (μ : FinitePMF Ω) (X : ι → Ω → Bool)
    (bad : Finset ι) (f : ℕ → ℝ) {e c : ℝ} (he : 0 ≤ e)
    (hf : ∀ k, |f k| ≤ c) :
    |e * finitePMFExpectation μ (fun ω => f (indicatorSum X ω + 1)) -
      finitePMFExpectation μ (fun ω => (countOn X bad ω : ℝ) * f (indicatorSum X ω))| ≤
      c * (e + ∑ i ∈ bad, marginal μ X i) := by
  have hfirst := abs_expectation_bounded μ (fun ω => f (indicatorSum X ω + 1))
    (fun ω => hf _)
  have hsecond :
      |finitePMFExpectation μ (fun ω => (countOn X bad ω : ℝ) * f (indicatorSum X ω))| ≤
        c * finitePMFExpectation μ (fun ω => (countOn X bad ω : ℝ)) := by
    calc
      _ ≤ finitePMFExpectation μ (fun ω => |(countOn X bad ω : ℝ) * f (indicatorSum X ω)|) :=
        abs_expectation_le μ _
      _ ≤ finitePMFExpectation μ (fun ω => c * countOn X bad ω) := by
        apply expectation_mono
        intro ω
        rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
        simpa only [mul_comm c] using mul_le_mul_of_nonneg_left (hf _) (Nat.cast_nonneg (countOn X bad ω))
      _ = _ := expectation_const_mul μ _ _
  rw [expectation_countOn] at hsecond
  have h := abs_add_le (e * finitePMFExpectation μ (fun ω => f (indicatorSum X ω + 1)))
    (-(finitePMFExpectation μ (fun ω => (countOn X bad ω : ℝ) * f (indicatorSum X ω))))
  rw [← sub_eq_add_neg, abs_neg, abs_mul, abs_of_nonneg he] at h
  nlinarith [mul_le_mul_of_nonneg_left hfirst he]

/-- Sum of the local Stein terms over a prescribed good population. -/
theorem good_error_le (μ : FinitePMF Ω) (X : ι → Ω → Bool)
    (G : SimpleGraph ι) (hdep : HasExactDependencyGraph μ X G)
    (good : Finset ι) {p : ℝ} (hgood : ∀ i ∈ good, marginal μ X i = p)
    (f : ℕ → ℝ) {d : ℝ} (hd : ∀ k, |f (k + 1) - f k| ≤ d) :
    |(good.card : ℝ) * p * finitePMFExpectation μ (fun ω => f (indicatorSum X ω + 1)) -
      finitePMFExpectation μ (fun ω => (countOn X good ω : ℝ) * f (indicatorSum X ω))| ≤
      d * goodSteinCost μ X G good p := by
  classical
  have hsum := Finset.sum_le_sum (s := good) (fun i hi => local_stein_error_le μ X G hdep i f hd)
  have hreplace :
      (∑ i ∈ good, |marginal μ X i * finitePMFExpectation μ (fun ω => f (indicatorSum X ω + 1)) -
        finitePMFExpectation μ (fun ω => (if X i ω = true then (1 : ℝ) else 0) * f (indicatorSum X ω))|) =
      ∑ i ∈ good, |p * finitePMFExpectation μ (fun ω => f (indicatorSum X ω + 1)) -
        finitePMFExpectation μ (fun ω => (if X i ω = true then (1 : ℝ) else 0) * f (indicatorSum X ω))| := by
    exact Finset.sum_congr rfl (fun i hi => by rw [hgood i hi])
  rw [hreplace] at hsum
  have hright :
      (∑ i ∈ good, d * (marginal μ X i ^ 2 +
        marginal μ X i * ∑ j ∈ (closedNeighborhood G i).erase i, marginal μ X j +
        ∑ j ∈ (closedNeighborhood G i).erase i, jointMarginal μ X i j)) =
        d * goodSteinCost μ X G good p := by
    calc
      _ = ∑ i ∈ good, d * (p ^ 2 +
          p * ∑ j ∈ (closedNeighborhood G i).erase i, marginal μ X j +
          ∑ j ∈ (closedNeighborhood G i).erase i, jointMarginal μ X i j) :=
        Finset.sum_congr rfl (fun i hi => by rw [hgood i hi])
      _ = _ := by simp [goodSteinCost, ← Finset.mul_sum, Finset.sum_add_distrib]
  rw [hright] at hsum
  have htriangle := Finset.abs_sum_le_sum_abs
    (fun i => p * finitePMFExpectation μ (fun ω => f (indicatorSum X ω + 1)) -
      finitePMFExpectation μ (fun ω => (if X i ω = true then (1 : ℝ) else 0) * f (indicatorSum X ω))) good
  have hid :
      (∑ i ∈ good, (p * finitePMFExpectation μ (fun ω => f (indicatorSum X ω + 1)) -
        finitePMFExpectation μ (fun ω => (if X i ω = true then (1 : ℝ) else 0) * f (indicatorSum X ω)))) =
      (good.card : ℝ) * p * finitePMFExpectation μ (fun ω => f (indicatorSum X ω + 1)) -
        finitePMFExpectation μ (fun ω => (countOn X good ω : ℝ) * f (indicatorSum X ω)) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    rw [← expectation_finset_sum]
    have heq : (fun ω => ∑ i ∈ good, (if X i ω = true then (1 : ℝ) else 0) * f (indicatorSum X ω)) =
        (fun ω => (countOn X good ω : ℝ) * f (indicatorSum X ω)) := by
      funext ω
      rw [countOn_cast, Finset.sum_mul]
    rw [heq]
    ring
  rw [hid] at htriangle
  exact htriangle.trans hsum

/-- The exact finite soft-exception calculation, before choosing Stein norm factors. -/
theorem soft_stein_error_le (μ : FinitePMF Ω) (X : ι → Ω → Bool)
    (G : SimpleGraph ι) (hdep : HasExactDependencyGraph μ X G)
    (good : Finset ι) {p : ℝ} (hp : 0 ≤ p)
    (hgood : ∀ i ∈ good, marginal μ X i = p)
    (f : ℕ → ℝ) {c d : ℝ} (hf : ∀ k, |f k| ≤ c)
    (hd : ∀ k, |f (k + 1) - f k| ≤ d) :
    |(Fintype.card ι : ℝ) * p * finitePMFExpectation μ (fun ω => f (indicatorSum X ω + 1)) -
      finitePMFExpectation μ (fun ω => (indicatorSum X ω : ℝ) * f (indicatorSum X ω))| ≤
      d * goodSteinCost μ X G good p +
        c * ((Finset.univ \ good).card * p + ∑ i ∈ Finset.univ \ good, marginal μ X i) := by
  classical
  let bad := Finset.univ \ good
  have hg := good_error_le μ X G hdep good hgood f hd
  have hb := exceptional_error_le μ X bad f (e := (bad.card : ℝ) * p) (by positivity) hf
  have hcounts : (good.card : ℝ) + bad.card = Fintype.card ι := by
    exact_mod_cast (show good.card + bad.card = Fintype.card ι by
      simpa [bad, add_comm] using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ good))
  have hE : finitePMFExpectation μ (fun ω => (indicatorSum X ω : ℝ) * f (indicatorSum X ω)) =
      finitePMFExpectation μ (fun ω => (countOn X good ω : ℝ) * f (indicatorSum X ω)) +
      finitePMFExpectation μ (fun ω => (countOn X bad ω : ℝ) * f (indicatorSum X ω)) := by
    rw [← expectation_add]
    apply expectation_congr
    intro ω
    have h := countOn_partition X good ω
    have hc : (indicatorSum X ω : ℝ) = countOn X good ω + countOn X bad ω := by exact_mod_cast h.symm
    rw [hc]
    ring
  have hid :
      (Fintype.card ι : ℝ) * p * finitePMFExpectation μ (fun ω => f (indicatorSum X ω + 1)) -
        finitePMFExpectation μ (fun ω => (indicatorSum X ω : ℝ) * f (indicatorSum X ω)) =
      ((good.card : ℝ) * p * finitePMFExpectation μ (fun ω => f (indicatorSum X ω + 1)) -
        finitePMFExpectation μ (fun ω => (countOn X good ω : ℝ) * f (indicatorSum X ω))) +
      ((bad.card : ℝ) * p * finitePMFExpectation μ (fun ω => f (indicatorSum X ω + 1)) -
        finitePMFExpectation μ (fun ω => (countOn X bad ω : ℝ) * f (indicatorSum X ω))) := by
    rw [hE, ← hcounts]
    ring
  rw [hid]
  exact (abs_add_le _ _).trans (add_le_add hg hb)

end
end PaperC.V282.SteinSoftTelescoping
