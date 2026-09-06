import PaperCV282.PrescribedValues
import Mathlib.LinearAlgebra.Matrix.Rank

/-! # Matrix rank and the exact affine fibre bound

The rank used for incidence minors is linked to the retained relation-space
normalization. All matrices and right-hand sides here are literal finite
binary systems; no rank or compatibility assumption is hidden in the bound.
-/

namespace PaperC.V282.MatrixAffineRank

open Matrix Affine PrescribedValues
open scoped BigOperators

noncomputable section

local instance instPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

variable {R V : Type*} [Fintype R] [Fintype V]

/-- Relations of a matrix are exactly the kernel of its transpose. -/
theorem relationSpace_eq_transpose_kernel (A : Matrix R V F₂) :
    RelationSpace A.mulVecLin = LinearMap.ker A.transpose.mulVecLin := by
  classical
  ext u
  simp only [RelationSpace, LinearMap.mem_ker, LinearMap.ext_iff,
    relationMap_apply, relationFunctional_apply, LinearMap.zero_apply]
  constructor
  · intro h
    funext v
    have hv := h (Pi.single v 1)
    change dotProduct u (A.mulVec (Pi.single v 1)) = 0 at hv
    rw [Matrix.mulVec_single_one] at hv
    change (∑ i, u i * A i v) = 0 at hv
    simpa only [Matrix.mulVecLin_apply, Matrix.mulVec_transpose, Matrix.vecMul,
      dotProduct, Pi.zero_apply] using hv
  · intro h z
    change dotProduct u (A.mulVec z) = 0
    rw [Matrix.dotProduct_mulVec]
    have ht : Matrix.vecMul u A = 0 := by
      simpa only [Matrix.mulVecLin_apply, Matrix.mulVec_transpose] using h
    rw [ht, zero_dotProduct]

/-- Exact rank/nullity identity in row coordinates. -/
theorem rank_add_relationRho (A : Matrix R V F₂) :
    A.rank + relationRho A.mulVecLin = Fintype.card R := by
  rw [relationRho, relationSpace_eq_transpose_kernel, ← Matrix.rank_transpose A,
    Matrix.rank]
  simpa only [Module.finrank_pi] using
    LinearMap.finrank_range_add_finrank_ker (K := F₂) A.transpose.mulVecLin

/-- The probability of any affine fibre is at most two to minus matrix rank. -/
theorem probability_le_inverse_rank [DecidableEq V] (A : Matrix R V F₂) (b : R → F₂) :
    uniformSolutionProbability A.mulVecLin b ≤ 1 / (2 : ℚ) ^ A.rank := by
  classical
  rw [probability_eq_eta_weight, ← rank_add_relationRho A, pow_add]
  have heta : (relationEta A.mulVecLin b : ℚ) ≤ 1 := by
    rcases relationEta_eq_zero_or_one A.mulVecLin b with h | h <;> simp [h]
  have hp : (0 : ℚ) < 2 ^ relationRho A.mulVecLin := by positivity
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  nlinarith [mul_le_mul_of_nonneg_right heta
    (show 0 ≤ (2 : ℚ) ^ relationRho A.mulVecLin * 2 ^ A.rank by positivity)]

end
end PaperC.V282.MatrixAffineRank
