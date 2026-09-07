import PaperCV282.ExactMarkedModel
import PaperCV282.WordOverlapProbability

/-!
# Exact marks as prescribed absolute words

The two boundary values are 1+s and every interior value is s.
The prime cylinder C remains free; every displayed vertex is covered explicitly.
-/
namespace PaperC.V282.SignedExactMarks

open ExactMarkedModel MixedLengthAffine ExactLengthDecomposition MarkedLocalGeometry
open Affine ConditionalStartProbability ArratiaGoldsteinGordonInput ConditionalAGGInstantiation
open WindowValues InfiniteWordTransfer WordOverlap WordOverlapProbability
open DefectivePredicate

noncomputable section

/-- A characteristic-two identity used at each boundary. -/
theorem eq_one_add_iff_add_eq_one (a b : F₂) : a = 1+b ↔ a+b = 1 := by
  revert a b
  decide

/-- The complete signed exact word, including its two changes. -/
def signedExactWord (L e : ℕ) (s : F₂) : Fin (L+e+2) → F₂ :=
  fun i => if i.val = 0 ∨ i.val+1 = L+e+2 then 1+s else s

/-- The prescribed word is exactly the signed source event, with no discarded equation. -/
theorem signedExactMark_iff_occurs {g : ℕ → F₂} {x L e : ℕ}
    (hx : 1 ≤ x) (hL : 1 ≤ L) (s : F₂) :
    SignedExactMark g x L e s ↔ Occurs g x (signedExactWord L e s) := by
  constructor
  · rintro ⟨he,hs⟩ i
    by_cases hi0 : i.val = 0
    · have hb : g (x-1) = 1+s := by
        apply (eq_one_add_iff_add_eq_one _ _).mpr
        rw [← hs]
        exact he.1
      simpa [vertex,signedExactWord,hi0] using hb
    · by_cases hilast : i.val+1 = L+e+2
      · have hi : i.val = L+e+1 := by omega
        have hb : g (x+(L+e)) = 1+s := by
          apply (eq_one_add_iff_add_eq_one _ _).mpr
          have hr := he.2.2
          simpa only [excessRowCount,Nat.add_sub_cancel,hs,add_comm] using hr
        have hv : vertex x (L+e+2) i = x+(L+e) := by unfold vertex; omega
        simpa [hv,signedExactWord,hilast] using hb
      · have hj : (i.val-1)+1 < excessRowCount L e := by
          have hi := i.isLt
          unfold excessRowCount
          omega
        have hh := exactLengthEvent_eq_start_of_before_right he hj
        have hv : vertex x (L+e+2) i = x+(i.val-1) := by unfold vertex; omega
        simpa only [hv,hs,signedExactWord,hi0,hilast,false_or,if_false] using hh.symm
  · intro hw
    have hzero := hw ⟨0,by omega⟩
    have hone := hw ⟨1,by omega⟩
    have hlast := hw ⟨L+e+1,by omega⟩
    have hvone : vertex x (L+e+2) ⟨1,by omega⟩ = x := by change x-1+1=x; omega
    have hvlast : vertex x (L+e+2) ⟨L+e+1,by omega⟩ = x+(L+e) := by change x-1+(L+e+1)=x+(L+e); omega
    have hs : g x = s := by
      rw [hvone] at hone
      simpa [signedExactWord,show L ≠ 0 by omega] using hone
    have hz : g (x-1) = 1+s := by simpa [vertex,signedExactWord] using hzero
    have hl : g (x+(L+e)) = 1+s := by simpa [hvlast,signedExactWord] using hlast
    refine ⟨⟨?_,?_,?_⟩,hs⟩
    · rw [hs]
      exact (eq_one_add_iff_add_eq_one _ _).mp hz
    · intro j hj hjq
      have hjlt : j+1 < L+e+2 := by unfold excessRowCount at hjq; omega
      have hv : vertex x (L+e+2) ⟨j+1,hjlt⟩ = x+j := by change x-1+(j+1)=x+j; omega
      have hmid := hw ⟨j+1,hjlt⟩
      have hnj : j ≠ L+e := by unfold excessRowCount at hjq; omega
      have hg : g (x+j) = s := by simpa [signedExactWord,hv,hnj] using hmid
      exact hs.trans hg.symm
    · have hh := (eq_one_add_iff_add_eq_one _ _).mp hl
      simpa only [excessRowCount,Nat.add_sub_cancel,hs,add_comm] using hh

/-- Event identity directly in a freely chosen finite prime cylinder. -/
theorem signedExactMark_iff_finiteWordEvent {C x L e : ℕ}
    (hx : 1 ≤ x) (hL : 1 ≤ L) (s : F₂) (omega : SampleSpace C) :
    SignedExactMark (valueBit omega) x L e s ↔
      omega ∈ finiteWordEvent C x (L+e+2) (signedExactWord L e s) :=
  signedExactMark_iff_occurs hx hL s

/-- Nondefectiveness of the maximal support covers every actual marked support. -/
theorem marked_vertices_good_of_max {Y x L E e : ℕ} (he : e ≤ E)
    (hgood : ∀ i : Fin (L+E+2), ¬HDefective Y (vertex x (L+E+2) i)) :
    ∀ i : Fin (L+e+2), ¬HDefective Y (vertex x (L+e+2) i) := by
  intro i
  exact hgood ⟨i.val,by have hi := i.isLt; omega⟩

/-- The actual signed marginal is exactly 2^(-L-e-2), uniformly in fixed small primes. -/
theorem conditioned_signedMark_probability {C Y x L E e : ℕ}
    (hx : 2 ≤ x) (hL : 1 ≤ L) (he : e ≤ E)
    (hcut : x-1+(L+E+2) ≤ C+1) (hY : L+E+2 ≤ Y)
    (hgood : ∀ i : Fin (L+E+2), ¬HDefective Y (vertex x (L+E+2) i))
    (s : F₂) (sigma : SmallSample C Y) :
    eventProbability (largeUniformPMF C Y) (fun eta =>
      SignedExactMark (valueBit (assemble C Y sigma eta)) x L e s) = (signedMarkRate L e : ℝ) := by
  simp_rw [signedExactMark_iff_finiteWordEvent (by omega : 1 ≤ x) hL s]
  exact conditionedWord_probability_eq_baseline hx (by omega) (by omega)
    (marked_vertices_good_of_max he hgood) _ sigma

end
end PaperC.V282.SignedExactMarks
