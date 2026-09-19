import PaperCPrel8.TwoRankPair
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic.Simproc.Factors

set_option maxHeartbeats 2000000

/-! # The two raw windows 91..95 and 113..117 at Y=11

Coordinates are the four active small primes 2,3,5,7 and seven large primes
13,19,23,29,31,47,113. The small prime 11 has zero column.
-/
namespace PaperC.Prel8.PairRankExample
open Finset _root_.PaperC.Affine TwoRankPair
noncomputable section
abbrev SmallBits := Fin 4 → F₂
abbrev Large := Fin 7 → F₂
abbrev Rows := Fin 10 → F₂

def sp (i : Fin 4) : SmallBits →ₗ[F₂] F₂ := LinearMap.proj i

def small : SmallBits →ₗ[F₂] Rows := LinearMap.pi
  ![sp 3,0,sp 1,sp 0,sp 2,0,
    sp 0+sp 1,sp 2,0,0]
def rough : Large →ₗ[F₂] Rows := LinearMap.pi
  ![LinearMap.proj 0,LinearMap.proj 2,LinearMap.proj 4,LinearMap.proj 5,LinearMap.proj 1,
    LinearMap.proj 6,LinearMap.proj 1,LinearMap.proj 2,LinearMap.proj 3,LinearMap.proj 0]
def full : SmallBits×Large →ₗ[F₂] Rows := combined small rough

theorem rough_injective : Function.Injective rough := by
  intro x y h
  funext i
  fin_cases i
  all_goals first
    | exact congrFun h 0
    | exact congrFun h 4
    | exact congrFun h 1
    | exact congrFun h 8
    | exact congrFun h 2
    | exact congrFun h 3
    | exact congrFun h 5

theorem rough_rank : Module.finrank F₂ (LinearMap.range rough)=7 := by
  rw [LinearMap.finrank_range_of_inj rough_injective]
  simp

theorem full_surjective : Function.Surjective full := by
  intro b
  have htwo : (2:F₂)=0 := by decide
  refine ⟨(![b 6+b 4+b 7+b 1,0,b 7+b 1,b 0+b 9],
    ![b 9,b 4+b 7+b 1,b 1,b 8,b 2,b 3+b 6+b 4+b 7+b 1,b 5]),?_⟩
  funext i
  fin_cases i <;> simp [full,combined,small,sp,rough] <;> ring_nf <;> simp [htwo]

theorem full_rank : Module.finrank F₂ (LinearMap.range full)=10 := by
  rw [LinearMap.range_eq_top.mpr full_surjective]
  simp

def first : Large →ₗ[F₂] (Fin 5 → F₂) := LinearMap.pi
  ![LinearMap.proj 0,LinearMap.proj 2,LinearMap.proj 4,LinearMap.proj 5,LinearMap.proj 1]
def second : Large →ₗ[F₂] (Fin 5 → F₂) := LinearMap.pi
  ![LinearMap.proj 6,LinearMap.proj 1,LinearMap.proj 2,LinearMap.proj 3,LinearMap.proj 0]

theorem individual_ranks : Module.finrank F₂ (LinearMap.range first)=5 ∧
    Module.finrank F₂ (LinearMap.range second)=5 := by
  have h1 : Function.Surjective first := by
    intro b
    exact ⟨![b 0,b 4,b 1,0,b 2,b 3,0],by ext i; fin_cases i <;> rfl⟩
  have h2 : Function.Surjective second := by
    intro b
    exact ⟨![b 4,b 1,b 2,b 3,0,0,b 0],by ext i; fin_cases i <;> rfl⟩
  rw [LinearMap.range_eq_top.mpr h1,LinearMap.range_eq_top.mpr h2]
  simp

/-- All prime factors, including their multiplicities: no omitted prime column. -/
theorem factorization_certificate :
    (91:ℕ).primeFactorsList=[7,13] ∧ (92:ℕ).primeFactorsList=[2,2,23] ∧
    (93:ℕ).primeFactorsList=[3,31] ∧ (94:ℕ).primeFactorsList=[2,47] ∧
    (95:ℕ).primeFactorsList=[5,19] ∧ (113:ℕ).primeFactorsList=[113] ∧
    (114:ℕ).primeFactorsList=[2,3,19] ∧ (115:ℕ).primeFactorsList=[5,23] ∧
    (116:ℕ).primeFactorsList=[2,2,29] ∧ (117:ℕ).primeFactorsList=[3,3,13] := by simp

def vertices : Fin 10 → ℕ := ![91,92,93,94,95,113,114,115,116,117]
def primes : Fin 11 → ℕ := ![2,3,5,7,13,19,23,29,31,47,113]

/-- The displayed linear map is exactly the odd valuation matrix on every active prime. -/
theorem valuation_matrix : ∀ i : Fin 10, ∀ k : Fin 11,
    full ((fun j : Fin 4 ↦ if j.val=k.val then 1 else 0),
      (fun j : Fin 7 ↦ if j.val+4=k.val then 1 else 0)) i =
    ((vertices i).factorization (primes k):F₂) := by
  have htwo : (2:F₂)=0 := by decide
  intro i k
  fin_cases i <;> fin_cases k <;> norm_num [full,combined,small,rough,vertices,primes,sp,Nat.factorization] <;> simp [htwo]
end
end PaperC.Prel8.PairRankExample
