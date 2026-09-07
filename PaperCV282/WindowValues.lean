import PaperCV282.PrescribedValues
import PaperC.LinearAlgebra.PrivatePivots

/-!
# The pointwise and conditioned claims of Corollary 2.6

The window is indexed exactly as in Paper C v2.8.2: `x - 1 + j`, `j < B`.
Every nondefective value supplies a prime with odd valuation above the
window diameter. The cylinder bound ensures that prime is actually present
in the finite probability space. The asymptotic sum of defect weights is
not part of the endpoints proved here.
-/

namespace PaperC.V282.WindowValues

open Affine DefectivePredicate ConditionalStartProbability
open PrescribedValues

noncomputable section

/-- The `B` consecutive arguments of the article's word occurrence. -/
def vertex (x B : ℕ) (i : Fin B) : ℕ := x - 1 + i.val

/-- Occurrences whose odd large-prime kernel above `H` is trivial. -/
def defectIndices (H x B : ℕ) : Finset (Fin B) := by
  classical
  exact Finset.univ.filter fun i => HDefective H (vertex x B i)

/-- Nondefectiveness gives an actual prime coordinate private in the window. -/
theorem private_prime_of_not_defective
    {M H x B : ℕ} (hx : 2 ≤ x) (hBM : x - 1 + B ≤ M + 1)
    (hBH : B ≤ H) (i : Fin B) (hi : ¬HDefective H (vertex x B i)) :
    ∃ p : PrimeUpTo M, H < p.val.val ∧
      parityVec (vertex x B i) p.val.val = 1 ∧
        ∀ j : Fin B, j ≠ i → parityVec (vertex x B j) p.val.val = 0 := by
  classical
  simp only [HDefective] at hi
  push Not at hi
  obtain ⟨p, hp, hHp, hparity⟩ := hi
  have hfactor : (vertex x B i).factorization p ≠ 0 := by
    intro hz
    exact hparity (by simp [parityVec_apply, hz])
  have hpdvd : p ∣ vertex x B i := by
    by_contra hndvd
    exact hfactor (Nat.factorization_eq_zero_of_not_dvd hndvd)
  have hpos : 0 < vertex x B i := by unfold vertex; omega
  have hpM : p ≤ M := by
    have hpv := Nat.le_of_dvd hpos hpdvd
    have hiB := i.isLt
    unfold vertex at hpv
    omega
  refine ⟨⟨⟨p, Nat.lt_succ_of_le hpM⟩, hp⟩, hHp, ?_, ?_⟩
  · exact (show ∀ a : F₂, a ≠ 0 → a = 1 by decide) _ hparity
  · intro j hji
    have hne : vertex x B i ≠ vertex x B j := by
      intro heq
      apply hji
      apply Fin.ext
      unfold vertex at heq
      omega
    have hdist : Nat.dist (vertex x B i) (vertex x B j) < H := by
      unfold vertex
      rw [Nat.dist_add_add_left]
      have hiB := i.isLt
      have hjB := j.isLt
      simp only [Nat.dist]
      omega
    have hnot := PrivatePivots.not_dvd_of_dvd_and_dist_lt hpdvd hne hHp hdist
    rw [parityVec_apply, Nat.factorization_eq_zero_of_not_dvd hnot]
    rfl

/-- Equation (2.6), with `m_B(x)` the actual set of defective vertices. -/
theorem corollary_two_six_pointwise
    {M x B : ℕ} (hx : 2 ≤ x) (hBM : x - 1 + B ≤ M + 1)
    (b : Fin B → F₂) :
    |uniformSolutionProbability (valueSystem M (vertex x B)) b -
        1 / (2 : ℚ) ^ B| ≤
      ((2 : ℚ) ^ (defectIndices B x B).card - 1) / (2 : ℚ) ^ B := by
  classical
  have h := value_probability_error_le_of_private_primes
    M (vertex x B) b (defectIndices B x B) ?_
  · simpa using h
  · intro i hi
    have hn : ¬HDefective B (vertex x B i) := by
      simpa [defectIndices] using hi
    obtain ⟨p, _, hp, hother⟩ :=
      private_prime_of_not_defective hx hBM (le_refl B) i hn
    exact ⟨p, hp, hother⟩

/-- Extending a large-prime basis assignment gives the same full basis vector. -/
theorem extendLarge_prime_basis (M Y : ℕ) (p : PrimeUpTo M)
    (hp : Y < p.val.val) :
    extendLarge M Y (Pi.single (⟨p, hp⟩ : LargePrimeCoordinate M Y) 1) =
      Pi.single p 1 := by
  classical
  funext q
  by_cases hqp : q = p
  · subst q
    simp [extendLarge, hp]
  · by_cases hq : Y < q.val.val
    · simp [extendLarge, Pi.single_apply, hq, hqp]
      intro heq
      exact hqp (congrArg Subtype.val heq)
    · simp [extendLarge, hq, hqp]

/-- The conditional clause of Corollary 2.6, for every fixed small-prime assignment. -/
theorem corollary_two_six_conditioned
    {M Y x B : ℕ} (hx : 2 ≤ x) (hBM : x - 1 + B ≤ M + 1)
    (hBY : B ≤ Y) (hgood : ∀ i : Fin B, ¬HDefective Y (vertex x B i))
    (b : Fin B → F₂) (σ : SmallSample M Y) :
    uniformSolutionProbability (largeValueSystem M Y (vertex x B))
      (conditionedValueRhs M Y (vertex x B) b σ) = 1 / (2 : ℚ) ^ B := by
  classical
  have h := conditioned_value_probability_eq_baseline M Y (vertex x B) b σ ?_
  · simpa using h
  · intro i
    obtain ⟨p, hpY, hdiag, hoff⟩ :=
      private_prime_of_not_defective hx hBM hBY i (hgood i)
    refine ⟨Pi.single (⟨p, hpY⟩ : LargePrimeCoordinate M Y) 1, ?_⟩
    change valueSystem M (vertex x B)
      (extendLarge M Y (Pi.single (⟨p, hpY⟩ : LargePrimeCoordinate M Y) 1)) = _
    rw [extendLarge_prime_basis]
    exact valueSystem_prime_basis M (vertex x B) i p hdiag hoff

end
end PaperC.V282.WindowValues
