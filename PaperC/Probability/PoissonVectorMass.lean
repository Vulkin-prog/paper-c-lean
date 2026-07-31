import PaperC.Probability.PoissonLaplaceFunctional
import Mathlib.Data.Fin.Tuple.Basic

set_option maxHeartbeats 800000

/-!
# Finite products of Poisson mass functions

This file supplies the literal probability mass and transform identities for
a finite vector of independent Poisson variables.
-/

open scoped BigOperators NNReal
open ProbabilityTheory

namespace PaperC
namespace PoissonVectorMass

noncomputable section

theorem hasSum_pi_prod_general
    (d : ℕ) (f : Fin d → ℕ → ℝ) (a : Fin d → ℝ)
    (hf0 : ∀ e k, 0 ≤ f e k)
    (hf : ∀ e, HasSum (f e) (a e)) :
    HasSum
      (fun k : Fin d → ℕ ↦ ∏ e : Fin d, f e (k e))
      (∏ e : Fin d, a e) := by
  induction d with
  | zero =>
      let z : Fin 0 → ℕ := fun i ↦ Fin.elim0 i
      have hfun :
          (fun k : Fin 0 → ℕ ↦ ∏ e : Fin 0, f e (k e)) =
            fun k ↦ if k = z then 1 else 0 := by
        funext k
        have hk : k = z := by
          funext i
          exact Fin.elim0 i
        simp [hk]
      rw [hfun]
      exact hasSum_ite_eq z 1
  | succ d ih =>
      let head : ℕ → ℝ := f 0
      let tail : Fin d → ℕ → ℝ := fun e ↦ f e.succ
      have hhead0 : ∀ k, 0 ≤ head k := fun k ↦ hf0 0 k
      have htail0 : ∀ e k, 0 ≤ tail e k :=
        fun e k ↦ hf0 e.succ k
      let tailSum : Fin d → ℝ := fun e ↦ a e.succ
      have hhead : HasSum head (a 0) := hf 0
      let tailMass : (Fin d → ℕ) → ℝ :=
        fun k ↦ ∏ e : Fin d, tail e (k e)
      have htailMass0 : ∀ k, 0 ≤ tailMass k :=
        fun k ↦ Finset.prod_nonneg fun e _ ↦ htail0 e (k e)
      have htail :
          HasSum tailMass (∏ e : Fin d, tailSum e) := by
        simpa only [tailMass] using
          ih tail tailSum htail0 (fun e ↦ hf e.succ)
      have hprodSummable :
          Summable
            (fun x : ℕ × (Fin d → ℕ) ↦
              head x.1 * tailMass x.2) :=
        hhead.summable.mul_of_nonneg
          htail.summable hhead0 htailMass0
      have hpair :
          HasSum
            (fun x : ℕ × (Fin d → ℕ) ↦
              head x.1 * tailMass x.2)
            (a 0 * ∏ e : Fin d, tailSum e) := by
        simpa using hhead.mul htail hprodSummable
      rw [← (Fin.consEquiv (fun _ : Fin (d + 1) ↦ ℕ)).hasSum_iff]
      convert hpair using 1
      · funext x
        simp only [Function.comp_apply, Fin.prod_univ_succ,
          Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ,
          head, tail, tailMass]
      · simp only [Fin.prod_univ_succ, tailSum]

theorem hasSum_pi_prod
    (d : ℕ) (f : Fin d → ℕ → ℝ)
    (hf0 : ∀ e k, 0 ≤ f e k)
    (hf : ∀ e, HasSum (f e) 1) :
    HasSum
      (fun k : Fin d → ℕ ↦ ∏ e : Fin d, f e (k e))
      1 := by
  simpa using
    hasSum_pi_prod_general d f (fun _ ↦ 1) hf0 hf

theorem independentPoissonVectorMass_nonneg
    {d : ℕ} (rate : Fin d → ℝ≥0)
    (k : Fin d → ℕ) :
    0 ≤ ∏ e : Fin d, poissonPMFReal (rate e) (k e) :=
  Finset.prod_nonneg fun _ _ ↦ poissonPMFReal_nonneg

theorem hasSum_independentPoissonVectorMass
    {d : ℕ} (rate : Fin d → ℝ≥0) :
    HasSum
      (fun k : Fin d → ℕ ↦
        ∏ e : Fin d, poissonPMFReal (rate e) (k e))
      1 :=
  hasSum_pi_prod d
    (fun e k ↦ poissonPMFReal (rate e) k)
    (fun _ _ ↦ poissonPMFReal_nonneg)
    (fun e ↦ poissonPMFRealSum (rate e))

theorem summable_independentPoissonVectorMass
    {d : ℕ} (rate : Fin d → ℝ≥0) :
    Summable
      (fun k : Fin d → ℕ ↦
        ∏ e : Fin d, poissonPMFReal (rate e) (k e)) :=
  (hasSum_independentPoissonVectorMass rate).summable

/--
The mass of an independent finite Poisson vector, multiplied by a
coordinatewise nonnegative Laplace weight, sums to the product of the
scalar Poisson Laplace transforms.
-/
theorem hasSum_independentPoissonVectorLaplace
    {d : ℕ} (rate : Fin d → ℝ≥0)
    (test : Fin d → ℝ) (htest : ∀ e, 0 ≤ test e) :
    HasSum
      (fun k : Fin d → ℕ ↦
        ∏ e : Fin d,
          poissonPMFReal (rate e) (k e) *
            (Real.exp (-test e)) ^ (k e))
      (∏ e : Fin d,
        PoissonLaplaceFunctional.poissonLaplaceTransform
          (rate e) (test e)) := by
  apply hasSum_pi_prod_general d
    (fun e k ↦
      poissonPMFReal (rate e) k *
        (Real.exp (-test e)) ^ k)
    (fun e ↦
      PoissonLaplaceFunctional.poissonLaplaceTransform
        (rate e) (test e))
  · intro e k
    exact mul_nonneg poissonPMFReal_nonneg (by positivity)
  · intro e
    have hbase : Real.exp (-test e) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      linarith [htest e]
    have hs :
        Summable
          (fun k : ℕ ↦
            poissonPMFReal (rate e) k *
              (Real.exp (-test e)) ^ k) := by
      apply Summable.of_nonneg_of_le
      · intro k
        exact mul_nonneg poissonPMFReal_nonneg (by positivity)
      · intro k
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left
            (pow_le_one₀ (by positivity) hbase)
            poissonPMFReal_nonneg
      · exact (poissonPMFRealSum (rate e)).summable
    simpa only [PoissonLaplaceFunctional.poissonLaplaceTransform] using
      hs.hasSum

end

end PoissonVectorMass
end PaperC
