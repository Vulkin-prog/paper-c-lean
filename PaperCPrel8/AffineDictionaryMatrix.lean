import PaperCPrel8.AffineDictionaryMoments
import Mathlib.LinearAlgebra.Matrix.Rank

/-! # Literal full-row-rank matrices, equivalent to the uniform surjection sample -/
namespace PaperC.Prel8.AffineDictionaryMatrix
open PaperC PaperC.SectionThirteenFiniteBound
open PaperC.Prel8.AffineDictionarySample PaperC.Prel8.AffineDictionaryInclusion
noncomputable section
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- Full row rank is exactly surjectivity of the associated coordinate map. -/
theorem rank_eq_iff_surjective {B r : ℕ} (A : Matrix (Fin r) (Fin B) F₂) :
    A.rank=r ↔ Function.Surjective (Matrix.toLin' A) := by
  change Module.finrank F₂ (LinearMap.range A.mulVecLin)=r ↔ _
  rw [Matrix.toLin'_apply',← LinearMap.range_eq_top]
  constructor
  · intro h
    apply Submodule.eq_top_of_finrank_eq
    simpa using h
  · intro h
    have hh := congrArg (fun S : Submodule F₂ (Word r) => Module.finrank F₂ S) h
    simpa only [finrank_top,Module.finrank_pi,Fintype.card_fin] using hh

abbrev FullRank (B r : ℕ) := {A : Matrix (Fin r) (Fin B) F₂ // A.rank=r}
abbrev MatrixSample (B r : ℕ) := FullRank B r × Word r

/-- No matrix or offset is discarded or counted twice by the linear-map encoding. -/
def matrixEquiv (B r : ℕ) : FullRank B r ≃ Surjection B r where
  toFun A := ⟨Matrix.toLin' A.val,(rank_eq_iff_surjective A.val).mp A.property⟩
  invFun A := ⟨LinearMap.toMatrix' A.val,by
    rw [rank_eq_iff_surjective,Matrix.toLin'_toMatrix']; exact A.property⟩
  left_inv A := by apply Subtype.ext; simp
  right_inv A := by apply Subtype.ext; simp

def sampleEquiv (B r : ℕ) : MatrixSample B r ≃ Sample B r :=
  Equiv.prodCongr (matrixEquiv B r) (Equiv.refl _)

def matrixDictionary {B r : ℕ} (s : MatrixSample B r) : Finset (Word B) :=
  Finset.univ.filter (fun u => s.1.val.mulVec u=s.2)

theorem matrixDictionary_eq {B r : ℕ} (s : MatrixSample B r) :
    matrixDictionary s=dictionary (sampleEquiv B r s) := by
  ext u
  simp [matrixDictionary,mem_dictionary,sampleEquiv,matrixEquiv,Matrix.toLin'_apply]

/-- Uniform full-rank matrices with independent offsets give exactly our affine average. -/
theorem matrix_average_eq (B r : ℕ) (f : Finset (Word B) → ℝ) :
    finiteUniformAverage (fun s : MatrixSample B r => f (matrixDictionary s))=affineAverage B r f := by
  have hs := (sampleEquiv B r).sum_comp (fun s => f (dictionary s))
  simp only [← matrixDictionary_eq] at hs
  unfold affineAverage finiteUniformAverage
  rw [hs,Fintype.card_congr (sampleEquiv B r)]

/-- The description consists of r*B matrix entries and r offset entries. -/
theorem description_bits (B r : ℕ) : r*B+r=r*(B+1) := by ring

theorem description_bits_le {B r : ℕ} (hr : r ≤ B) : r*(B+1) ≤ B*(B+1) :=
  Nat.mul_le_mul_right (B+1) hr

end
end PaperC.Prel8.AffineDictionaryMatrix
