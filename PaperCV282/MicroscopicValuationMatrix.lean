import PaperCV282.MatrixAffineRank
import PaperCV282.PointwiseStartBounds

/-! # Literal valuation matrices for microscopic starts

The complete window has one more value row than the start system. Its
relation embedding proves the loss of at most one in rank, including empty
and singular systems. Matrix minors therefore control the actual infinite
Rademacher start probability.
-/

namespace PaperC.V282.MicroscopicValuationMatrix

open Matrix Affine PrescribedValues WindowValues PointwiseStartBounds
open MatrixAffineRank StartDefectRank
open scoped BigOperators Classical

noncomputable section

local instance instPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

/-- Parity valuations of every integer in the complete window. -/
def valuationMatrix (M x B : ℕ) : Matrix (Fin B) (PrimeUpTo M) F₂ :=
  fun i p => parityVec (vertex x B i) p.val.val

/-- This matrix is the existing absolute-value system, with no change of model. -/
theorem valuationMatrix_mulVecLin (M x B : ℕ) :
    (valuationMatrix M x B).mulVecLin = valueSystem M (vertex x B) := by
  ext ω i
  simp [valuationMatrix, Matrix.mulVec, dotProduct,
    valueSystem_apply, valueBit, mul_comm]

/-- Its matrix rank is exactly the dimension of the value-system image. -/
theorem valuationMatrix_rank (M x B : ℕ) :
    (valuationMatrix M x B).rank =
      Module.finrank F₂ (LinearMap.range (valueSystem M (vertex x B))) := by
  rw [Matrix.rank, valuationMatrix_mulVecLin]

/-- The actual root edge and the remaining star edges. -/
def startMatrix (M x L : ℕ) : Matrix (Fin L) (PrimeUpTo M) F₂ :=
  fun i p => if i.val = 0 then parityVec (x - 1) p.val.val + parityVec x p.val.val
    else parityVec x p.val.val + parityVec (x + i.val) p.val.val

theorem startMatrix_mulVecLin (M x L : ℕ) :
    (startMatrix M x L).mulVecLin = startSystem M x L := by
  ext ω i
  by_cases hi : i.val = 0 <;>
    simp [startMatrix, Matrix.mulVec, dotProduct,
      startSystem_apply, valueBit, hi, add_mul, Finset.sum_add_distrib,
      mul_comm]

/-- The tree boundary embeds edge relations in complete-value relations. -/
def relationBoundary {M x L : ℕ} (hx : 1 ≤ x) :
    RelationSpace (startSystem M x L) →ₗ[F₂]
      RelationSpace (valueSystem M (vertex x (L + 1))) where
  toFun u := ⟨startCompleteBoundary L u, boundary_mem_value_relation hx u⟩
  map_add' u v := Subtype.ext (map_add (startCompleteBoundary L) u.val v.val)
  map_smul' c u := Subtype.ext (map_smul (startCompleteBoundary L) c u.val)

theorem relationBoundary_injective {M x L : ℕ} (hx : 1 ≤ x) :
    Function.Injective (relationBoundary (M := M) (L := L) hx) := by
  intro u v h
  apply Subtype.ext
  exact startCompleteBoundary_injective L (congrArg Subtype.val h)

/-- The boundary embedding bounds the actual relation dimensions. -/
theorem start_relationRho_le_values {M x L : ℕ} (hx : 1 ≤ x) :
    relationRho (startSystem M x L) ≤
      relationRho (valueSystem M (vertex x (L + 1))) :=
  LinearMap.finrank_le_finrank_of_injective (relationBoundary_injective hx)

/-- The start equations lose at most one rank from the complete values. -/
theorem valuation_rank_le_start_rank_add_one {M x L : ℕ} (hx : 1 ≤ x) :
    (valuationMatrix M x (L + 1)).rank ≤ (startMatrix M x L).rank + 1 := by
  have hv := rank_add_relationRho (valuationMatrix M x (L + 1))
  have hs := rank_add_relationRho (startMatrix M x L)
  rw [valuationMatrix_mulVecLin, Fintype.card_fin] at hv
  rw [startMatrix_mulVecLin, Fintype.card_fin] at hs
  have hr := start_relationRho_le_values (M := M) (L := L) hx
  omega

/-- Any lower bound on the complete-value rank bounds every affine fibre. -/
theorem finite_probability_le_rank {M x L r : ℕ} (hx : 1 ≤ x)
    (hr : r + 1 ≤ (valuationMatrix M x (L + 1)).rank) (b : Fin L → F₂) :
    uniformSolutionProbability (startSystem M x L) b ≤ 1 / (2 : ℚ) ^ r := by
  have hdim := valuation_rank_le_start_rank_add_one (M := M) (L := L) hx
  have hb := probability_le_inverse_rank (startMatrix M x L) b
  rw [startMatrix_mulVecLin] at hb
  apply hb.trans
  exact one_div_le_one_div_of_le (by positivity)
    (pow_le_pow_right₀ (by norm_num) (by omega : r ≤ (startMatrix M x L).rank))

/-- The same bound holds in the infinite model whenever the cylinder is adequate. -/
theorem infinite_probability_le_rank {M x L r : ℕ} (hx : 1 ≤ x)
    (hcut : x + L ≤ M) (hr : r + 1 ≤ (valuationMatrix M x (L + 1)).rank)
    (b : Fin L → F₂) :
    infiniteAffineStartProbability x L b ≤ 1 / (2 : ℝ) ^ r := by
  rw [infiniteAffineStartProbability_eq_uniformSolutionProbability hcut b]
  have hq := finite_probability_le_rank hx hr b
  have hc := (Rat.cast_le (K := ℝ)).mpr hq
  simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat] using hc

/-- Rank bound in real-exponent form, suitable for uniform asymptotic estimates. -/
theorem infinite_probability_le_real_start_rank {M x L : ℕ} (hcut : x + L ≤ M)
    (b : Fin L → F₂) :
    infiniteAffineStartProbability x L b ≤ (2 : ℝ) ^ (-(startMatrix M x L).rank : ℝ) := by
  rw [infiniteAffineStartProbability_eq_uniformSolutionProbability hcut b]
  have hq := probability_le_inverse_rank (startMatrix M x L) b
  rw [startMatrix_mulVecLin] at hq
  have hc := (Rat.cast_le (K := ℝ)).mpr hq
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),Real.rpow_natCast]
  simpa using hc

/-- A real lower bound on complete-value rank loses precisely the constant direction. -/
theorem infinite_probability_le_real_value_rank {M x L : ℕ} {r : ℝ}
    (hx : 1 ≤ x) (hcut : x + L ≤ M)
    (hr : r + 1 ≤ ((valuationMatrix M x (L + 1)).rank : ℝ)) (b : Fin L → F₂) :
    infiniteAffineStartProbability x L b ≤ (2 : ℝ) ^ (-r) := by
  have hd := valuation_rank_le_start_rank_add_one (M := M) (L := L) hx
  have hdr : ((valuationMatrix M x (L + 1)).rank : ℝ) ≤ (startMatrix M x L).rank + 1 := by
    exact_mod_cast hd
  exact (infinite_probability_le_real_start_rank hcut b).trans
    (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith))

end
end PaperC.V282.MicroscopicValuationMatrix
