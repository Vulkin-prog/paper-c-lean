import PaperCV282.TransitionPrimeRows
import PaperCV282.MicroscopicValuationMatrix

/-! # A literal transition identity minor and its start-probability bound

All rows belong to the window a,...,a+B-1. The result is finite, before
any prime-counting asymptotic is used.
-/
namespace PaperC.V282.TransitionPrimeMinor

open Matrix Affine PrescribedValues WindowValues MicroscopicValuationMatrix
open TransitionPrimeRows MatrixAffineRank PointwiseStartBounds
open scoped BigOperators Classical

noncomputable section

local instance instPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

def transitionPrimes (a B Y : ℕ) : Finset ℕ :=
  (Nat.primesLE (a+B-1)).filter (fun p => Y<p)

theorem mem_transitionPrimes {a B Y p : ℕ} :
    p∈transitionPrimes a B Y ↔ p.Prime ∧ Y<p ∧ p≤a+B-1 := by
  simp only [transitionPrimes,Finset.mem_filter,Nat.mem_primesLE]
  tauto

/-- The minor uses exactly the primes in the displayed open-closed interval. -/
theorem transitionPrimes_eq_sdiff (a B Y : ℕ) :
    transitionPrimes a B Y = Nat.primesLE (a+B-1) \ Nat.primesLE Y := by
  ext p
  simp only [mem_transitionPrimes,Finset.mem_sdiff,Nat.mem_primesLE]
  constructor
  · rintro ⟨hp,hY,hT⟩
    exact ⟨⟨hT,hp⟩,fun h => by omega⟩
  · rintro ⟨⟨hT,hp⟩,h⟩
    refine ⟨hp,?_,hT⟩
    by_contra he
    exact h ⟨by omega,hp⟩

/-- Exact prime-counting size of the selected minor. -/
theorem card_transitionPrimes {a B Y : ℕ} (hY : Y≤a+B-1) :
    (transitionPrimes a B Y).card=Nat.primeCounting (a+B-1)-Nat.primeCounting Y := by
  rw [transitionPrimes_eq_sdiff,Finset.card_sdiff_of_subset (Nat.primesLE_mono hY),
    Nat.primesLE_card_eq_primeCounting,Nat.primesLE_card_eq_primeCounting]

def transitionRowIndex {a B Y : ℕ} (ha : 0<a) (haB : a≤B)
    (p : transitionPrimes a B Y) : Fin B :=
  ⟨transitionRow a p.val-a,by
    have hp := mem_transitionPrimes.mp p.property
    have hr := transitionRow_mem_interval ha haB hp.1.pos hp.2.2
    omega⟩

def transitionColumnIndex {M a B Y : ℕ} (hM : a+B≤M+1)
    (p : transitionPrimes a B Y) : PrimeUpTo M :=
  ⟨⟨p.val,by have hp := mem_transitionPrimes.mp p.property;omega⟩,
    (mem_transitionPrimes.mp p.property).1⟩

/-- The selected row is exactly the chosen multiple, including the left endpoint. -/
theorem transitionRowIndex_vertex {a B Y : ℕ} (ha : 0<a) (haB : a≤B)
    (p : transitionPrimes a B Y) :
    vertex (a+1) B (transitionRowIndex ha haB p) = transitionRow a p.val := by
  have hp := mem_transitionPrimes.mp p.property
  have hl := transitionRow_lower (a := a) hp.1.pos
  simp only [vertex,transitionRowIndex,Nat.add_sub_cancel]
  omega

/-- This is a genuine square identity submatrix of the full valuation matrix. -/
theorem transition_identity_minor {M a B Y : ℕ} (ha : 0<a) (haB : a≤B)
    (hBY : B≤Y^2) (hM : a+B≤M+1) :
    (valuationMatrix M (a+1) B).submatrix
      (transitionRowIndex ha haB (Y := Y)) (transitionColumnIndex (Y := Y) hM) = 1 := by
  ext p q
  have hp := mem_transitionPrimes.mp p.property
  have hq := mem_transitionPrimes.mp q.property
  change parityVec (vertex (a+1) B (transitionRowIndex ha haB p)) q.val = (1 : Matrix _ _ F₂) p q
  rw [transitionRowIndex_vertex]
  rw [transitionRow_parity ha haB hBY hp.1 hq.1 hp.2.1 hq.2.1]
  by_cases hpq : p=q
  · subst q; simp
  · have hv : q.val≠p.val := by intro h;exact hpq (Subtype.ext h.symm)
    simp [hpq,hv]

/-- No rank is postulated: the finite identity minor supplies its full dimension. -/
theorem transition_value_rank_lower {M a B Y : ℕ} (ha : 0<a) (haB : a≤B)
    (hBY : B≤Y^2) (hM : a+B≤M+1) :
    (transitionPrimes a B Y).card ≤ (valuationMatrix M (a+1) B).rank := by
  have h := Matrix.rank_submatrix_le (valuationMatrix M (a+1) B)
    (transitionRowIndex ha haB (Y := Y)) (transitionColumnIndex (Y := Y) hM)
  rw [transition_identity_minor ha haB hBY hM,Matrix.rank_one,Fintype.card_coe] at h
  exact h

/-- The actual start matrix loses at most its one constant-value direction. -/
theorem transition_start_rank_lower {M a L Y : ℕ} (ha : 0<a) (haL : a≤L+1)
    (hLY : L+1≤Y^2) (hM : a+(L+1)≤M+1) :
    (transitionPrimes a (L+1) Y).card-1 ≤ (startMatrix M (a+1) L).rank := by
  have hv := transition_value_rank_lower ha haL hLY hM
  have hs := valuation_rank_le_start_rank_add_one (M := M) (L := L) (by omega : 1≤a+1)
  omega

/-- Every affine right-hand side obeys the exact finite-minor probability bound. -/
theorem transition_finite_probability_le {M a L Y : ℕ} (ha : 0<a) (haL : a≤L+1)
    (hLY : L+1≤Y^2) (hM : a+(L+1)≤M+1) (b : Fin L → F₂) :
    uniformSolutionProbability (startSystem M (a+1) L) b ≤
      1/(2 : ℚ)^((transitionPrimes a (L+1) Y).card-1) := by
  have hp := probability_le_inverse_rank (startMatrix M (a+1) L) b
  rw [startMatrix_mulVecLin] at hp
  exact hp.trans (one_div_le_one_div_of_le (by positivity)
    (pow_le_pow_right₀ (by norm_num) (transition_start_rank_lower ha haL hLY hM)))

/-- The same bound holds for the true infinite-model affine event. -/
theorem transition_infinite_probability_le {M a L Y : ℕ} (ha : 0<a) (haL : a≤L+1)
    (hLY : L+1≤Y^2) (hM : a+1+L≤M) (b : Fin L → F₂) :
    infiniteAffineStartProbability (a+1) L b ≤
      1/(2 : ℝ)^((transitionPrimes a (L+1) Y).card-1) := by
  rw [infiniteAffineStartProbability_eq_uniformSolutionProbability hM b]
  have h := transition_finite_probability_le (M := M) ha haL hLY (by omega : a+(L+1)≤M+1) b
  have hc := (Rat.cast_le (K := ℝ)).mpr h
  simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_ofNat] using hc

/-- The ordinary start event has the same exact finite prime-counting bound. -/
theorem transition_start_probability_le_count {a L Y : ℕ} (ha : 0<a) (hL : 0<L)
    (haL : a≤L+1) (hLY : L+1≤Y^2) (hY : Y≤a+L) :
    InfiniteStartProbabilityTransfer.infiniteStartProbability (a+1) L ≤
      1/(2 : ℝ)^(Nat.primeCounting (a+L)-Nat.primeCounting Y-1) := by
  have hh := transition_infinite_probability_le (M := a+1+L) ha haL hLY (le_refl _) (startRhs L)
  rw [infiniteAffineStartProbability_startRhs_eq hL,
    card_transitionPrimes (by omega : Y≤a+(L+1)-1)] at hh
  simpa only [show a+(L+1)-1=a+L by omega] using hh

end
end PaperC.V282.TransitionPrimeMinor
