import PaperCV282.DirectionalGradientGrowth

/-!
# Finite Palm coupling comparison (3PREL8, companion F.2)

The conditional-law identity is an assumption about the supplied coupling,
not a Poisson approximation assumption. The only analytic input used here is
the previously recorded Stein solution bound; no dependency graph is required.
-/
namespace PaperC.Prel8.PalmStein

open PaperC.V282 PaperC.V282.DirectionalSteinInput
open PaperC.V282.DirectionalGradientGrowth PaperC.V282.SteinFiniteExpectation
open PaperC.V282.FiniteFieldTotalVariation PaperC.V282.FiniteFieldPoissonCoupling
open PaperC.ArratiaGoldsteinGordonInput PaperC.IndependentThinning
open scoped BigOperators NNReal

noncomputable section
variable {κ Ω : Type*} [Fintype κ] [DecidableEq κ] [Fintype Ω]

/-- The actual lattice L1 distance, with both endpoints nonnegative. -/
def latticeDistance (v w : κ → ℕ) : ℝ := ∑ i, |(v i : ℝ) - w i|

/-- Unit-step control telescopes between arbitrary configurations, not just ordered ones. -/
theorem difference_le_latticeDistance (f : (κ → ℕ) → ℝ)
    (hs : ∀ z i, |f (addPoint z i) - f z| ≤ 1) (v w : κ → ℕ) :
    |f v - f w| ≤ latticeDistance v w := by
  let m : κ → ℕ := fun i => min (v i) (w i)
  have hv : m + (v - m) = v := by ext i; dsimp [m]; omega
  have hw : m + (w - m) = w := by ext i; dsimp [m]; omega
  have h1 := vector_difference_le f (fun _ => 1) hs m (v-m)
  have h2 := vector_difference_le f (fun _ => 1) hs m (w-m)
  rw [hv] at h1
  rw [hw] at h2
  have hsum : (∑ i, ((v-m) i : ℝ)*1) + (∑ i, ((w-m) i : ℝ)*1) =
      latticeDistance v w := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.sub_apply, mul_one]
    dsimp [m]
    rw [Nat.cast_sub (min_le_left _ _), Nat.cast_sub (min_le_right _ _)]
    push_cast
    by_cases h : v i ≤ w i
    · rw [min_eq_left (show (v i : ℝ) ≤ w i by exact_mod_cast h), abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast h))]
      ring
    · have h' := le_of_not_ge h
      rw [min_eq_right (show (w i : ℝ) ≤ v i by exact_mod_cast h'), abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast h'))]
      ring
  calc
    |f v - f w| ≤ |f v - f m| + |f w - f m| := by
      simpa only [abs_sub_comm (f m) (f w)] using abs_sub_le (f v) (f m) (f w)
    _ ≤ _ := add_le_add h1 h2
    _ = _ := hsum

/-- The constant Hessian bound gives the dimension-free gradient estimate in F.2. -/
theorem gradient_lipschitz (g : (κ → ℕ) → ℝ)
    (hsecond : ∀ z i j, |secondDifference g i j z| ≤ 1) (i : κ) (v w : κ → ℕ) :
    |firstDifference g i v - firstDifference g i w| ≤ latticeDistance v w := by
  apply difference_le_latticeDistance
  intro z j
  rw [firstDifference_addPoint]
  exact hsecond z i j

/-- Weighted conditional-law equality for a finite supplied Palm coupling. -/
def HasPalmLaw (μ : FinitePMF Ω) (W : Ω → κ → ℕ)
    (Wa : κ → Ω → κ → ℕ) (t : κ → ℝ≥0) : Prop :=
  ∀ i (f : (κ → ℕ) → ℝ),
    (t i : ℝ) * finitePMFExpectation μ (fun ω => f (Wa i ω)) =
      finitePMFExpectation μ (fun ω => (W ω i : ℝ) * f (W ω))

/-- Expected number of coordinate changes after deleting the planted point. -/
def palmCost (μ : FinitePMF Ω) (W : Ω → κ → ℕ)
    (Wa : κ → Ω → κ → ℕ) (t : κ → ℝ≥0) : ℝ :=
  ∑ i, (t i : ℝ) * finitePMFExpectation μ
    (fun ω => latticeDistance (W ω) (removePoint (Wa i ω) i))

/-- Generator identity derived from the coupling's exact conditional laws. -/
theorem generator_identity (μ : FinitePMF Ω) (W : Ω → κ → ℕ)
    (Wa : κ → Ω → κ → ℕ) (t : κ → ℝ≥0)
    (hpalm : HasPalmLaw μ W Wa t) (hplant : ∀ i ω, 0 < Wa i ω i)
    (g : (κ → ℕ) → ℝ) :
    finitePMFExpectation μ (fun ω => steinGenerator t g (W ω)) =
      ∑ i, (t i : ℝ) * finitePMFExpectation μ
        (fun ω => firstDifference g i (W ω) - firstDifference g i (removePoint (Wa i ω) i)) := by
  unfold steinGenerator
  rw [expectation_finset_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [expectation_add, expectation_const_mul, ← hpalm i (fun z => g (removePoint z i) - g z)]
  have hremove (ω : Ω) : addPoint (removePoint (Wa i ω) i) i = Wa i ω := by
    ext j
    by_cases h : j=i
    · subst j
      simpa [addPoint, removePoint] using Nat.sub_add_cancel (hplant i ω)
    · simp [addPoint, removePoint, h]
  have heq : finitePMFExpectation μ (fun ω => g (removePoint (Wa i ω) i) - g (Wa i ω)) =
      -finitePMFExpectation μ (fun ω => firstDifference g i (removePoint (Wa i ω) i)) := by
    have hh (ω : Ω) : g (removePoint (Wa i ω) i) - g (Wa i ω) =
        -firstDifference g i (removePoint (Wa i ω) i) := by
      unfold firstDifference
      rw [hremove]
      ring
    simp_rw [hh]
    simp [finitePMFExpectation, Finset.sum_neg_distrib]
  rw [heq, expectation_sub]
  ring

/-- F.2 for finite couplings, given the existing analytic solution bounds. -/
theorem palm_stein_bound (μ : FinitePMF Ω) (W : Ω → κ → ℕ)
    (Wa : κ → Ω → κ → ℕ) (t : κ → ℝ≥0)
    (hpalm : HasPalmLaw μ W Wa t) (hplant : ∀ i ω, 0 < Wa i ω i)
    (hsolution : DirectionalSolutionBounds t) :
    massTotalVariation (finiteFieldLaw μ W) (poissonFieldMass t) ≤ palmCost μ W Wa t := by
  classical
  apply massTotalVariation_le_of_test_sets (hasSum_finiteFieldLaw μ W)
    (hasSum_poissonFieldMass t) (finiteFieldLaw_nonneg μ W) (poissonFieldMass_nonneg t)
  intro A
  obtain ⟨g, heq, hsecond, _⟩ := hsolution A
  rw [restricted_finiteFieldLaw_eq_eventProbability]
  change |eventProbability μ (fun ω => W ω ∈ A) - poissonTestMass t A| ≤ _
  have htest : finitePMFExpectation μ (fun ω => steinGenerator t g (W ω)) =
      eventProbability μ (fun ω => W ω ∈ A) - poissonTestMass t A := by
    simp_rw [heq]
    rw [expectation_sub, expectation_const]
    congr 1
    simp [finitePMFExpectation, eventProbability, mul_ite]
  rw [← htest, generator_identity μ W Wa t hpalm hplant]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [abs_mul, abs_of_nonneg (t i).coe_nonneg]
  apply mul_le_mul_of_nonneg_left _ (t i).coe_nonneg
  apply (abs_expectation_le μ _).trans
  exact expectation_mono μ (fun ω => gradient_lipschitz g hsecond i _ _)

/-- The existing literature input supplies the analytic bounds in dimension at least two. -/
theorem palm_stein_of_directional_input {ι : Type} [Fintype ι] [DecidableEq ι]
    (hStein : DirectionalSteinFactorsStatement)
    (hcard : 2 ≤ Fintype.card ι) (μ : FinitePMF Ω) (W : Ω → ι → ℕ)
    (Wa : ι → Ω → ι → ℕ) (t : ι → ℝ≥0) (ht : ∀ i, 0 < t i)
    (hpalm : HasPalmLaw μ W Wa t) (hplant : ∀ i ω, 0 < Wa i ω i) :
    massTotalVariation (finiteFieldLaw μ W) (poissonFieldMass t) ≤ palmCost μ W Wa t := by
  exact palm_stein_bound μ W Wa t hpalm hplant (hStein ι hcard t ht)

end
end PaperC.Prel8.PalmStein
