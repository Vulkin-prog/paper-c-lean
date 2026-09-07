import PaperCV282.AffineCrossoverCylinder
import PaperCV282.AffineBorderPrimeClock

/-! # Neutrality of complete future prime-coordinate consequences

The hypothesis is the actual intersection of the affine-plus-border row
space and the first K future-coordinate row space. Neutrality at a longer
prefix implies neutrality at every shorter prefix.
-/
namespace PaperC.V282.AffineCrossoverFuture

open Affine InfiniteRademacher AffineBorderLinear AffineBorderCylinders AffineBorderPrimeClock

noncomputable section

local instance instPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

variable {Y L J K : ℕ} {W : Type*} [AddCommGroup W] [Module F₂ W]

def FutureNeutral (G : SampleSpace Y →ₗ[F₂] W) (hLY : L ≤ Y)
    (hcut : Nat.nth Nat.Prime (Nat.primeCounting L+K) ≤ Y) : Prop :=
  (rowSpace G ⊔ rowSpace (borderProjection hLY)) ⊓
    rowSpace (futurePrimeProjection hcut) = ⊥

theorem futureNeutral_iff_overlap_zero (G : SampleSpace Y →ₗ[F₂] W) (hLY : L ≤ Y)
    (hcut : Nat.nth Nat.Prime (Nat.primeCounting L+K) ≤ Y) :
    FutureNeutral G hLY hcut ↔
      rowOverlap (G.prod (borderProjection hLY)) (futurePrimeProjection hcut) = 0 := by
  rw [FutureNeutral, rowOverlap, rowSpace_prod]
  exact Submodule.finrank_eq_zero.symm

theorem future_cutoff_mono
    (hcut : Nat.nth Nat.Prime (Nat.primeCounting L+K) ≤ Y) (hJK : J ≤ K) :
    Nat.nth Nat.Prime (Nat.primeCounting L+J) ≤ Y :=
  (Nat.nth_monotone Nat.infinite_setOf_prime (Nat.add_le_add_left hJK _)).trans hcut

theorem future_rowSpace_mono
    (hcut : Nat.nth Nat.Prime (Nat.primeCounting L+K) ≤ Y) (hJK : J ≤ K) :
    rowSpace (futurePrimeProjection (future_cutoff_mono hcut hJK)) ≤
      rowSpace (futurePrimeProjection hcut) := by
  have hk : LinearMap.ker (futurePrimeProjection hcut) ≤
      LinearMap.ker (futurePrimeProjection (future_cutoff_mono hcut hJK)) := by
    intro sigma hsigma
    change futurePrimeProjection hcut sigma = 0 at hsigma
    change futurePrimeProjection (future_cutoff_mono hcut hJK) sigma = 0
    ext i
    exact congrFun hsigma ⟨i.val, lt_of_lt_of_le i.isLt hJK⟩
  simpa only [rowSpace, LinearMap.range_dualMap_eq_dualAnnihilator_ker] using
    Submodule.dualAnnihilator_anti hk

theorem futureNeutral_mono (G : SampleSpace Y →ₗ[F₂] W) (hLY : L ≤ Y)
    (hcut : Nat.nth Nat.Prime (Nat.primeCounting L+K) ≤ Y) (hJK : J ≤ K)
    (hneutral : FutureNeutral G hLY hcut) :
    FutureNeutral G hLY (future_cutoff_mono hcut hJK) := by
  apply le_antisymm _ bot_le
  exact (inf_le_inf_left _ (future_rowSpace_mono hcut hJK)).trans (le_of_eq hneutral)

end
end PaperC.V282.AffineCrossoverFuture
