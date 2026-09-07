import PaperCV282.PreciseSingletonTriples
import PaperC.Affine.RationalChannelCode

/-! # Printed integer offsets in Lemma 3.17

Offsets range over {-1,...,L-1}. The membership formula is precisely the
integer equation (x+i)(y+j)=dz² on all triples, without separation.
-/
namespace PaperC.V282.PreciseSingletonTriplesOffsets

open Affine RationalChannelCode PreciseSingletonTriples PreciseSingletonHosts MacroscopicGeometry
open BalasubramanianShoreyInput

noncomputable section

/-- Reindex the actual triple set by integer offsets in the complete window. -/
def offsetTriples (M L : ℕ) (i j : ℤ) (hi : i ∈ offsetInterval L) (hj : j ∈ offsetInterval L)
    (s : Finset ℕ) : Finset ((ℕ × ℕ) × ℕ) :=
  triples M L (offsetVertexOfMem i hi) (offsetVertexOfMem j hj) s

theorem shifted_product_eq_iff {L x y d z : ℕ} (i j : ℤ)
    (hi : i ∈ offsetInterval L) (hj : j ∈ offsetInterval L) (hx : 1 ≤ x) (hy : 1 ≤ y) :
    startCompleteVertexLabel x L (offsetVertexOfMem i hi) *
      startCompleteVertexLabel y L (offsetVertexOfMem j hj) = d*z^2 ↔
    ((x : ℤ)+i)*((y : ℤ)+j) = (d : ℤ)*(z : ℤ)^2 := by
  have hxcast : (startCompleteVertexLabel x L (offsetVertexOfMem i hi) : ℤ) = (x : ℤ)+i := by
    rw [startCompleteVertexLabel_cast hx, channelVertexOffset_offsetVertexOfMem]
  have hycast : (startCompleteVertexLabel y L (offsetVertexOfMem j hj) : ℤ) = (y : ℤ)+j := by
    rw [startCompleteVertexLabel_cast hy, channelVertexOffset_offsetVertexOfMem]
  rw [← hxcast, ← hycast]
  exact_mod_cast (Iff.rfl : startCompleteVertexLabel x L (offsetVertexOfMem i hi) *
    startCompleteVertexLabel y L (offsetVertexOfMem j hj) = d*z^2 ↔
    startCompleteVertexLabel x L (offsetVertexOfMem i hi) *
    startCompleteVertexLabel y L (offsetVertexOfMem j hj) = d*z^2)

/-- This is the exact unrestricted predicate of the printed triples. -/
theorem mem_offsetTriples {M L : ℕ} (i j : ℤ)
    (hi : i ∈ offsetInterval L) (hj : j ∈ offsetInterval L) (s : Finset ℕ)
    (hs : s ⊆ Finset.Icc 2 M) (x y d : ℕ) :
    ((x,y),d) ∈ offsetTriples M L i j hi hj s ↔
      x ∈ s ∧ y ∈ s ∧ 0 < d ∧ Squarefree d ∧ IsSmoothAt (L+1) d ∧
        ∃ z : ℕ, ((x : ℤ)+i)*((y : ℤ)+j) = (d : ℤ)*(z : ℤ)^2 := by
  rw [offsetTriples, mem_triples _ _ s hs]
  by_cases hx : x ∈ s
  · by_cases hy : y ∈ s
    · have hxpos : 1 ≤ x := by have := (Finset.mem_Icc.mp (hs hx)).1; omega
      have hypos : 1 ≤ y := by have := (Finset.mem_Icc.mp (hs hy)).1; omega
      simp only [shifted_product_eq_iff i j hi hj hxpos hypos]
    · simp [hy]
  · simp [hx]

/-- Lemma 3.17 with its literal integer offsets and its sharp exponential rate. -/
theorem lemma_three_seventeen_integer_offsets (betaMin betaMax : ℝ)
    (hmin : 0 < betaMin) (hmax : 0 ≤ betaMax) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L+1 : ℝ) → (L+1 : ℝ) ≤ betaMax * Real.log M →
      ∀ (i j : ℤ) (hi : i ∈ offsetInterval L) (hj : j ∈ offsetInterval L)
        (delta : ℝ), 0 < delta →
      ((offsetTriples M L i j hi hj (macroscopicStarts M delta)).card : ℝ) ≤
        (M : ℝ) * Real.exp (singletonConstant betaMin *
          (Real.sqrt (L+1 : ℝ) / Real.log (L+1 : ℝ))) := by
  obtain ⟨Mzero,hbound⟩ := lemma_three_seventeen betaMin betaMax hmin hmax
  refine ⟨Mzero, ?_⟩
  intro M hM L hlo hhi i j hi hj delta hdelta
  exact hbound M hM L hlo hhi (offsetVertexOfMem i hi) (offsetVertexOfMem j hj) delta hdelta

end
end PaperC.V282.PreciseSingletonTriplesOffsets
