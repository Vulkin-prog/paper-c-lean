import PaperCV282.PoissonFieldMeasure

/-!
# Explicit multivariate Poisson Stein solution input

Primary source: A. D. Barbour, Stein's Method and Poisson Process
Convergence, J. Appl. Probab. 25(A) (1988), printed page 179,
Lemmas 2 and 3, https://doi.org/10.2307/3214155 . The same solution
has the constant entrywise bound and the weighted quadratic-form bound.
Lemma 3 states integer directions; homogeneity and continuity extend
the weighted estimate to real directions.

The unweighted Euclidean quadratic bound printed in Roellin,
arXiv:0706.0879v3, equation (3.1), is not used: it is false.
Barbour's unweighted quadratic alternative is the square of the
l1 norm, not the sum of squares. The constant entrywise bound below
is Barbour's Lemma 2 and includes equal coordinate indices.

Writing t_i = lambda * mu_i gives the weighted coefficient below exactly.
No dependency-graph estimate, Poisson filling identity, arithmetic result,
or final weighted entrywise comparison is assumed here. The dimension assumption
is the one stated in that source; signed geometric categories have at least
two coordinates even at zero excess cutoff. No new Lean axiom is introduced.
-/
namespace PaperC.V282.DirectionalSteinInput

open FiniteFieldPoissonCoupling
open scoped BigOperators NNReal

noncomputable section

local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

/-- Add or remove a single point in the indicated category. -/
def addPoint {κ : Type*} [DecidableEq κ] (z : κ → ℕ) (i : κ) : κ → ℕ := z + Pi.single i 1

def removePoint {κ : Type*} [DecidableEq κ] (z : κ → ℕ) (i : κ) : κ → ℕ := z - Pi.single i 1

def firstDifference {κ : Type*} [DecidableEq κ] (g : (κ → ℕ) → ℝ) (i : κ) (z : κ → ℕ) : ℝ :=
  g (addPoint z i) - g z

def secondDifference {κ : Type*} [DecidableEq κ] (g : (κ → ℕ) → ℝ) (i j : κ) (z : κ → ℕ) : ℝ :=
  g (addPoint (addPoint z i) j) - g (addPoint z i) - g (addPoint z j) + g z

def steinGenerator {κ : Type*} [Fintype κ] [DecidableEq κ]
    (t : κ → ℝ≥0) (g : (κ → ℕ) → ℝ) (z : κ → ℕ) : ℝ :=
  ∑ i, ((t i : ℝ) * firstDifference g i z + (z i : ℝ) * (g (removePoint z i) - g z))

def poissonTestMass {κ : Type*} [Fintype κ] (t : κ → ℝ≥0) (A : Set (κ → ℕ)) : ℝ :=
  ∑' z, if z ∈ A then poissonFieldMass t z else 0

def directionalCoefficient {κ : Type*} [Fintype κ] (t : κ → ℝ≥0) : ℝ :=
  (1 + 2 * max 0 (Real.log (2 * ∑ i, (t i : ℝ)))) / 2

def hessianQuadratic {κ : Type*} [Fintype κ] [DecidableEq κ]
    (g : (κ → ℕ) → ℝ) (z : κ → ℕ) (alpha : κ → ℝ) : ℝ :=
  ∑ i, ∑ j, alpha i * alpha j * secondDifference g i j z

/-- One genuine solution with Barbour's constant entrywise and weighted quadratic estimates. -/
def DirectionalSolutionBounds {κ : Type*} [Fintype κ] [DecidableEq κ]
    (t : κ → ℝ≥0) : Prop :=
  ∀ A : Set (κ → ℕ), ∃ g : (κ → ℕ) → ℝ,
    (∀ z, steinGenerator t g z = (if z ∈ A then 1 else 0) - poissonTestMass t A) ∧
    (∀ z i j, |secondDifference g i j z| ≤ 1) ∧
    (∀ z alpha, |hessianQuadratic g z alpha| ≤
      directionalCoefficient t * ∑ i, (alpha i)^2 / (t i : ℝ))

/-- Only the analytic solution theorem is supplied externally. -/
def DirectionalSteinFactorsStatement : Prop :=
  ∀ (κ : Type) [Fintype κ] [DecidableEq κ], 2 ≤ Fintype.card κ →
    ∀ t : κ → ℝ≥0, (∀ i, 0 < t i) → DirectionalSolutionBounds t

theorem addPoint_comm {κ : Type*} [DecidableEq κ] (z : κ → ℕ) (i j : κ) :
    addPoint (addPoint z i) j = addPoint (addPoint z j) i := by
  unfold addPoint
  ac_rfl

theorem secondDifference_symm {κ : Type*} [DecidableEq κ]
    (g : (κ → ℕ) → ℝ) (i j : κ) (z : κ → ℕ) :
    secondDifference g i j z = secondDifference g j i z := by
  unfold secondDifference
  rw [addPoint_comm]
  ring

theorem firstDifference_addPoint {κ : Type*} [DecidableEq κ]
    (g : (κ → ℕ) → ℝ) (i j : κ) (z : κ → ℕ) :
    firstDifference g i (addPoint z j) - firstDifference g i z = secondDifference g i j z := by
  unfold firstDifference secondDifference
  rw [addPoint_comm]
  ring

theorem directionalCoefficient_nonneg {κ : Type*} [Fintype κ] (t : κ → ℝ≥0) :
    0 ≤ directionalCoefficient t := by unfold directionalCoefficient; positivity

end
end PaperC.V282.DirectionalSteinInput
