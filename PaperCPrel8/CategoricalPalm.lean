import PaperCPrel8.PalmStein

/-! # Directed categorical Palm ledger

A directed change set suffices. Distinct marks at one site are treated together;
no independence outside the change set and no reciprocal marginal are assumed.
-/
namespace PaperC.Prel8.CategoricalPalm
open PaperC.Prel8.PalmStein PaperC.V282.DirectionalSteinInput
open PaperC.V282.SteinFiniteExpectation PaperC.IndependentThinning
open PaperC.V282.FiniteFieldTotalVariation PaperC.V282.FiniteFieldPoissonCoupling
open scoped BigOperators NNReal
noncomputable section
variable {κ Ω S : Type*} [Fintype κ] [DecidableEq κ] [Fintype Ω]
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

omit [Fintype κ] [DecidableEq κ] in
/-- Every coordinate's mean follows from the exact Palm identity, even at rate zero. -/
theorem mean_of_palm (μ : FinitePMF Ω) (W : Ω → κ → ℕ)
    (Wa : κ → Ω → κ → ℕ) (t : κ → ℝ≥0) (hpalm : HasPalmLaw μ W Wa t) (i : κ) :
    finitePMFExpectation μ (fun ω => (W ω i : ℝ)) = t i := by
  simpa only [expectation_const, mul_one] using (hpalm i (fun _ => 1)).symm

omit [Fintype κ] in
/-- Planting one category deletes every category at its site after removing that point. -/
theorem removed_same_site (site : κ → S) (z : κ → ℕ) (i k : κ)
    (hplant : z i = 1)
    (hexcl : ∀ k, site k = site i → k ≠ i → z k = 0)
    (hk : site k = site i) : removePoint z i k = 0 := by
  by_cases h : k = i
  · subst k; simp [removePoint, hplant]
  · simp [removePoint, h, hexcl k hk h]

/-- Finite directed ledger: same-site products plus directed off-site product and joint masses. -/
theorem palm_cost_le (μ : FinitePMF Ω) (W : Ω → κ → ℕ)
    (Wa : κ → Ω → κ → ℕ) (t : κ → ℝ≥0) (site : κ → S) (D : κ → κ → Prop)
    (hpalm : HasPalmLaw μ W Wa t)
    (hplant : ∀ i ω, Wa i ω i = 1)
    (hexcl : ∀ i ω k, site k = site i → k ≠ i → Wa i ω k = 0)
    (hout : ∀ i k, site k ≠ site i → ¬D i k → ∀ ω, Wa i ω k = W ω k) :
    palmCost μ W Wa t ≤
      ∑ i, ∑ k, if site k = site i then (t i : ℝ) * t k else
        if D i k then (t i : ℝ) * t k +
          finitePMFExpectation μ (fun ω => (W ω i : ℝ) * W ω k) else 0 := by
  unfold palmCost latticeDistance
  apply Finset.sum_le_sum
  intro i _
  rw [expectation_finset_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  by_cases hs : site k = site i
  · simp only [hs, ite_true]
    have hz : ∀ ω, removePoint (Wa i ω) i k = 0 :=
      fun ω => removed_same_site site _ i k (hplant i ω) (hexcl i ω) hs
    simp_rw [hz, Nat.cast_zero, sub_zero, Nat.abs_cast]
    rw [mean_of_palm μ W Wa t hpalm]
  · simp only [hs, ite_false]
    have hki : k ≠ i := fun h => hs (congrArg site h)
    have hr : ∀ ω, removePoint (Wa i ω) i k = Wa i ω k := by
      intro ω; simp [removePoint, hki]
    simp_rw [hr]
    by_cases hd : D i k
    · simp only [hd, ite_true]
      calc
        _ ≤ (t i : ℝ) * finitePMFExpectation μ
            (fun ω => (W ω k : ℝ) + Wa i ω k) := by
          apply mul_le_mul_of_nonneg_left _ (t i).coe_nonneg
          apply expectation_mono
          intro ω
          exact abs_sub_le_iff.mpr ⟨by linarith [Nat.cast_nonneg (Wa i ω k) (α := ℝ)],
            by linarith [Nat.cast_nonneg (W ω k) (α := ℝ)]⟩
        _ = _ := by
          rw [expectation_add, mul_add, mean_of_palm μ W Wa t hpalm,
            hpalm i (fun z => (z k : ℝ))]
    · simp [hd, hout i k hs hd, expectation_const]

/-- The categorical comparison uses the same dimension-free analytic input as F.2. -/
theorem categorical_stein_bound (μ : FinitePMF Ω) (W : Ω → κ → ℕ)
    (Wa : κ → Ω → κ → ℕ) (t : κ → ℝ≥0) (site : κ → S) (D : κ → κ → Prop)
    (hpalm : HasPalmLaw μ W Wa t)
    (hplant : ∀ i ω, Wa i ω i = 1)
    (hexcl : ∀ i ω k, site k = site i → k ≠ i → Wa i ω k = 0)
    (hout : ∀ i k, site k ≠ site i → ¬D i k → ∀ ω, Wa i ω k = W ω k)
    (hsolution : DirectionalSolutionBounds t) :
    massTotalVariation (finiteFieldLaw μ W) (poissonFieldMass t) ≤
      ∑ i, ∑ k, if site k = site i then (t i : ℝ) * t k else
        if D i k then (t i : ℝ) * t k +
          finitePMFExpectation μ (fun ω => (W ω i : ℝ) * W ω k) else 0 :=
  (palm_stein_bound μ W Wa t hpalm (by simp [hplant]) hsolution).trans
    (palm_cost_le μ W Wa t site D hpalm hplant hexcl hout)

end
end PaperC.Prel8.CategoricalPalm
