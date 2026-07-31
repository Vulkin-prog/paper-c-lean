import PaperC.Affine.TouchingSystem
import PaperC.Probability.DefectFirstMoment

/-!
# Exact probability of two touching starts

Two starts of length `L`, based at `x` and `x + L`, use the common finite
cylinder with cutoff `dyadicCutoff N (2 * L)`.  Their conjunction is the
solution event of `Affine.touchingSystem`, whose row type is
`Sum (Fin L) (Fin L)` and therefore has cardinality `2L`.

This file proves the exact affine normalization

`P = η * 2^ρ / 2^(2L)`

and its immediate absolute defect bound.
-/

namespace PaperC

open Affine

noncomputable section

/--
Finite-cylinder probability that starts of length `L` occur simultaneously
at `x` and `x + L`.
-/
noncomputable def touchingProbability (N L x : ℕ) : ℚ := by
  classical
  exact
    uniformEventProbability (M := dyadicCutoff N (2 * L))
      (fun ω => startAt ω x L ∧ startAt ω (x + L) L)

/--
For positive length, the joint event is exactly the solution fiber of the
touching affine system.
-/
theorem touchingProbability_eq_uniformSolutionProbability
    (N L x : ℕ) (hL : 0 < L) :
    touchingProbability N L x =
      uniformSolutionProbability
        (touchingSystem (dyadicCutoff N (2 * L)) x L)
        (touchingRhs L) := by
  classical
  unfold touchingProbability uniformEventProbability
    uniformSolutionProbability
  congr 1
  rw [Fintype.card_subtype]
  apply congrArg (fun n : ℕ => (n : ℚ))
  apply congrArg Finset.card
  ext ω
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  simpa only [startAt, mem_solutionSet_iff] using
    (touchingSystem_eq_touchingRhs_iff ω hL).symm

/--
Exact normalization of the probability of two touching starts:
`P = η 2^ρ / 2^(2L)`.
-/
theorem touchingProbability_eq_eta_mul_two_pow_rho_div
    (N L x : ℕ) (hL : 0 < L) :
    touchingProbability N L x =
      ((relationEta
          (touchingSystem (dyadicCutoff N (2 * L)) x L)
          (touchingRhs L) : ℚ) *
        (2 : ℚ) ^
          relationRho
            (touchingSystem (dyadicCutoff N (2 * L)) x L)) /
        (2 : ℚ) ^ (2 * L) := by
  classical
  rw [touchingProbability_eq_uniformSolutionProbability N L x hL]
  unfold uniformSolutionProbability
  rw [Fintype.card_subtype]
  let A :=
    touchingSystem (dyadicCutoff N (2 * L)) x L
  let b := touchingRhs L
  have hnormalized :=
    affineFiber_normalized_card_identity A b
  have hnormalizedQ :
      (2 : ℚ) ^ (2 * L) *
          (Fintype.card (Solution A b) : ℚ) =
        (Fintype.card
            (SampleSpace (dyadicCutoff N (2 * L))) : ℚ) *
          ((relationEta A b : ℚ) *
            (2 : ℚ) ^ relationRho A) := by
    have hnormalizedQ' :
        (2 : ℚ) ^
              Fintype.card (Sum (Fin L) (Fin L)) *
            (((Finset.univ.filter fun ω :
                SampleSpace (dyadicCutoff N (2 * L)) =>
                  A ω = b).card : ℕ) : ℚ) =
          (Fintype.card
              (SampleSpace (dyadicCutoff N (2 * L))) : ℚ) *
            ((relationEta A b : ℚ) *
              (2 : ℚ) ^ relationRho A) := by
      exact_mod_cast hnormalized
    have hsolutionCard :
        Fintype.card (Solution A b) =
          (Finset.univ.filter fun ω :
            SampleSpace (dyadicCutoff N (2 * L)) =>
              A ω = b).card := by
      rw [Fintype.card_subtype]
      apply congrArg Finset.card
      ext ω
      simp [solutionSet]
    rw [hsolutionCard]
    simpa only [Fintype.card_sum, Fintype.card_fin, two_mul] using
      hnormalizedQ'
  have hcard :
      (Fintype.card
        (SampleSpace (dyadicCutoff N (2 * L))) : ℚ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero :
      Fintype.card
        (SampleSpace (dyadicCutoff N (2 * L))) ≠ 0)
  have hpow :
      (2 : ℚ) ^ (2 * L) ≠ 0 :=
    pow_ne_zero _ (by norm_num)
  dsimp only [A, b] at hnormalizedQ ⊢
  apply (div_eq_div_iff hcard hpow).2
  simpa [solutionSet, mul_assoc, mul_left_comm, mul_comm] using
    hnormalizedQ

/--
Pointwise absolute deviation from the independent baseline `2^(-2L)`.
The only structural input is an upper bound for the relation defect `ρ`.
-/
theorem abs_touchingProbability_sub_baseline_le
    (N L x m : ℕ) (hL : 0 < L)
    (hrho :
      relationRho
        (touchingSystem (dyadicCutoff N (2 * L)) x L) ≤ m) :
    |touchingProbability N L x -
        (1 : ℚ) / (2 : ℚ) ^ (2 * L)| ≤
      (((2 : ℕ) ^ m - 1 : ℕ) : ℚ) /
        (2 : ℚ) ^ (2 * L) := by
  rw [touchingProbability_eq_eta_mul_two_pow_rho_div N L x hL]
  let A :=
    touchingSystem (dyadicCutoff N (2 * L)) x L
  let b := touchingRhs L
  have habsZ :=
    abs_eta_mul_two_pow_rho_sub_one_le A b
  have habsQ :
      |(relationEta A b : ℚ) *
          (2 : ℚ) ^ relationRho A - 1| ≤
        (2 : ℚ) ^ relationRho A - 1 := by
    exact_mod_cast habsZ
  have hpowMono :
      (2 : ℚ) ^ relationRho A ≤ (2 : ℚ) ^ m := by
    exact pow_le_pow_right₀ (by norm_num) hrho
  have hdenom :
      0 < (2 : ℚ) ^ (2 * L) :=
    pow_pos (by norm_num) (2 * L)
  have hnat :
      ((((2 : ℕ) ^ m - 1 : ℕ) : ℚ)) =
        (2 : ℚ) ^ m - 1 := by
    rw [Nat.cast_sub]
    · norm_num
    · exact one_le_pow₀ (by omega)
  dsimp only [A, b] at habsQ hpowMono ⊢
  rw [← sub_div, abs_div, abs_of_pos hdenom, hnat]
  exact div_le_div_of_nonneg_right
    (habsQ.trans (by linarith)) hdenom.le

end

end PaperC
