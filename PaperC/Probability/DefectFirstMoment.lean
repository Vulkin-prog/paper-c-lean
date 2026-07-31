import PaperC.Affine.Normalization
import PaperC.Analysis.WeightedDefectMass
import PaperC.Arithmetic.DefectivePredicate
import PaperC.Probability.FiniteExpectation
import PaperC.Probability.StartProbability
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# From local defects to the first moment

This module isolates the finite probabilistic bridge used in Corollary 3.3.
The arithmetic estimate of Proposition 3.2 controls a sum of weights
`2 ^ m x - 1`.  The affine Fourier identity shows that the deviation of a
one-start probability from `2⁻ᴸ` is at most the same weight, multiplied by
`2⁻ᴸ`, as soon as the relation defect `ρ(x)` is bounded by `m x`.

All statements here are exact finite inequalities over `ℚ`; no asymptotic
notation is hidden in the interface.
-/

namespace PaperC
namespace DefectFirstMoment

open scoped BigOperators
open Affine

noncomputable section

/--
Exact one-start probability in the `η 2^ρ / 2^L` normalization of Lemma 2.1.
-/
theorem startProbability_eq_eta_mul_two_pow_rho_div
    (N L x : ℕ) (hL : 0 < L) :
    startProbability N L x =
      ((relationEta
          (startSystem (dyadicCutoff N L) x L) (startRhs L) : ℚ) *
        (2 : ℚ) ^
          relationRho (startSystem (dyadicCutoff N L) x L)) /
        (2 : ℚ) ^ L := by
  classical
  rw [startProbability_eq_uniformSolutionProbability N L x hL]
  unfold uniformSolutionProbability
  rw [Fintype.card_subtype]
  let A := startSystem (dyadicCutoff N L) x L
  let b := startRhs L
  have hnormalized :=
    affineFiber_normalized_card_identity A b
  have hnormalizedQ :
      (2 : ℚ) ^ L *
          (Fintype.card (Solution A b) : ℚ) =
        (Fintype.card (DyadicSample N L) : ℚ) *
          ((relationEta A b : ℚ) *
            (2 : ℚ) ^ relationRho A) := by
    have hnormalizedQ' :
        (2 : ℚ) ^ Fintype.card (Fin L) *
            (((Finset.univ.filter fun ω : DyadicSample N L =>
                A ω = b).card : ℕ) : ℚ) =
          (Fintype.card (DyadicSample N L) : ℚ) *
            ((relationEta A b : ℚ) *
              (2 : ℚ) ^ relationRho A) := by
      exact_mod_cast hnormalized
    have hsolutionCard :
        Fintype.card (Solution A b) =
          (Finset.univ.filter fun ω : DyadicSample N L =>
            A ω = b).card := by
      rw [Fintype.card_subtype]
      apply congrArg Finset.card
      ext ω
      simp [solutionSet]
    rw [hsolutionCard]
    simpa using hnormalizedQ'
  have hcard :
      (Fintype.card (DyadicSample N L) : ℚ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero :
      Fintype.card (DyadicSample N L) ≠ 0)
  have hpow : (2 : ℚ) ^ L ≠ 0 := pow_ne_zero _ (by norm_num)
  dsimp only [A, b] at hnormalizedQ ⊢
  apply (div_eq_div_iff hcard hpow).2
  simpa [solutionSet, mul_assoc, mul_left_comm, mul_comm] using hnormalizedQ

/--
Finite pointwise form of the estimate in Corollary 3.3.

The sole structural input is the explicit inequality `ρ(x) ≤ m`; a later
arithmetic/tree lemma can instantiate `m` with the number of
`(L+1)`-defective vertices in the non-root start window.
-/
theorem abs_startProbability_sub_baseline_le
    (N L x m : ℕ) (hL : 0 < L)
    (hrho :
      relationRho (startSystem (dyadicCutoff N L) x L) ≤ m) :
    |startProbability N L x - (1 : ℚ) / (2 : ℚ) ^ L| ≤
      (((2 : ℕ) ^ m - 1 : ℕ) : ℚ) / (2 : ℚ) ^ L := by
  rw [startProbability_eq_eta_mul_two_pow_rho_div N L x hL]
  let A := startSystem (dyadicCutoff N L) x L
  let b := startRhs L
  have habsZ := abs_eta_mul_two_pow_rho_sub_one_le A b
  have habsQ :
      |(relationEta A b : ℚ) * (2 : ℚ) ^ relationRho A - 1| ≤
        (2 : ℚ) ^ relationRho A - 1 := by
    exact_mod_cast habsZ
  have hpowMono :
      (2 : ℚ) ^ relationRho A ≤ (2 : ℚ) ^ m := by
    exact pow_le_pow_right₀ (by norm_num) hrho
  have hdenom : 0 < (2 : ℚ) ^ L := pow_pos (by norm_num) L
  have hnat :
      ((((2 : ℕ) ^ m - 1 : ℕ) : ℚ)) = (2 : ℚ) ^ m - 1 := by
    rw [Nat.cast_sub]
    · norm_num
    · exact one_le_pow₀ (by omega)
  dsimp only [A, b] at habsQ hpowMono ⊢
  rw [← sub_div, abs_div, abs_of_pos hdenom, hnat]
  exact div_le_div_of_nonneg_right
    (habsQ.trans (by linarith)) hdenom.le

/--
Summed finite first-moment bridge for an arbitrary local defect majorant
`m`.  This is the exact deterministic/probabilistic implication used after
the weighted estimate (3.4).
-/
theorem abs_dyadicExpectation_sub_baseline_le
    (N L : ℕ) (m : ℕ → ℕ) (hL : 0 < L)
    (hrho : ∀ x ∈ dyadicBlock N,
      relationRho (startSystem (dyadicCutoff N L) x L) ≤ m x) :
    |dyadicExpectation N L - (N : ℚ) / (2 : ℚ) ^ L| ≤
      (∑ x ∈ dyadicBlock N,
        ((((2 : ℕ) ^ m x - 1 : ℕ) : ℚ) / (2 : ℚ) ^ L)) := by
  have hbaseline :
      (N : ℚ) / (2 : ℚ) ^ L =
        ∑ _x ∈ dyadicBlock N, (1 : ℚ) / (2 : ℚ) ^ L := by
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : (dyadicBlock N).card = N := by
      simp [dyadicBlock]
      omega
    rw [hcard]
    simp only [div_eq_mul_inv, one_mul]
  rw [dyadicExpectation, hbaseline, ← Finset.sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun x hx =>
      abs_startProbability_sub_baseline_le N L x (m x) hL
        (hrho x hx))

/--
The preceding bound with the common factor `2⁻ᴸ` pulled out.  This is the
shape directly combined with equation (3.4).
-/
theorem abs_dyadicExpectation_sub_baseline_le_weight
    (N L : ℕ) (m : ℕ → ℕ) (hL : 0 < L)
    (hrho : ∀ x ∈ dyadicBlock N,
      relationRho (startSystem (dyadicCutoff N L) x L) ≤ m x) :
    |dyadicExpectation N L - (N : ℚ) / (2 : ℚ) ^ L| ≤
      (↑(∑ x ∈ dyadicBlock N, ((2 : ℕ) ^ m x - 1 : ℕ)) : ℚ) /
        (2 : ℚ) ^ L := by
  calc
    |dyadicExpectation N L - (N : ℚ) / (2 : ℚ) ^ L| ≤
        ∑ x ∈ dyadicBlock N,
          ((((2 : ℕ) ^ m x - 1 : ℕ) : ℚ) / (2 : ℚ) ^ L) :=
      abs_dyadicExpectation_sub_baseline_le N L m hL hrho
    _ = (↑(∑ x ∈ dyadicBlock N,
          ((2 : ℕ) ^ m x - 1 : ℕ)) : ℚ) / (2 : ℚ) ^ L := by
      rw [Nat.cast_sum]
      simp_rw [div_eq_mul_inv]
      rw [← Finset.sum_mul]

/--
Concrete bridge to the global defect set used in Proposition 3.2.

The hypothesis `hrho` is deliberately stated with the exact local set
`IntervalDefectBound.defectsInInterval`.  It is the remaining start-tree
statement

`ρ(x) ≤ #{(L+1)-defects in the non-root window}`,

with the harmless enlargement from `[x,x+L-1]` to `[x,x+L+1]`.  Once that
structural inequality is supplied, the conclusion involves exactly the
weighted local counts assembled in `WeightedDefectMass`.
-/
theorem abs_dyadicExpectation_sub_baseline_le_globalDefectWeight
    {N L X : ℕ}
    (hN : 0 < N) (hL : 0 < L)
    (hupper : ∀ x ∈ dyadicBlock N, x + (L + 1) ≤ X)
    (hrho : ∀ x ∈ dyadicBlock N,
      relationRho (startSystem (dyadicCutoff N L) x L) ≤
        (IntervalDefectBound.defectsInInterval (L + 1) x).card) :
    let defects :=
      WeightedDefectCounting.positiveDefectValues
        (DefectCounting.smallPrimesUpTo (L + 1)) X
    |dyadicExpectation N L - (N : ℚ) / (2 : ℚ) ^ L| ≤
      (((∑ x ∈ dyadicBlock N,
        ((2 : ℕ) ^
          IntervalDefectAggregation.localCount defects (L + 1) x - 1)) :
          ℕ) : ℚ) /
        (2 : ℚ) ^ L := by
  dsimp only
  apply abs_dyadicExpectation_sub_baseline_le_weight
    N L (fun x =>
      IntervalDefectAggregation.localCount
        (WeightedDefectCounting.positiveDefectValues
          (DefectCounting.smallPrimesUpTo (L + 1)) X)
        (L + 1) x) hL
  intro x hx
  rw [WeightedDefectMass.localCount_positiveDefectValues_eq
    (H := L + 1) (X := X)
    (by
      have hxN :
          N ≤ x :=
        (Finset.mem_Ico.mp (by simpa [dyadicBlock] using hx)).1
      omega)
    (hupper x hx)]
  exact hrho x hx

end

end DefectFirstMoment
end PaperC
