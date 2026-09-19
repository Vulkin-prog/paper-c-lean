import PaperCPrel8.CenteredAffineBlocks
import PaperCPrel8.PalmVoidPolynomial

/-! # The exact signed centered Palm coefficient, including its environment -/
namespace PaperC.Prel8.CenteredPalmFourier
open Finset IndependentThinning ArratiaGoldsteinGordonInput V282.SteinFiniteExpectation
open _root_.PaperC.Affine AffinePalmCharacters AffinePalmEnvironment CenteredAffineBlocks FiniteConditioning
noncomputable section
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P
variable {U V α β ι : Type*}
  [AddCommGroup U] [Module F₂ U] [Fintype U] [DecidableEq U]
  [AddCommGroup V] [Module F₂ V] [Fintype V] [DecidableEq V]
  [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype ι] [DecidableEq ι]

/-- Exact G.6 coefficient: nonzero block frequencies, a matching planted row
multiplier, its sign and the actual environment Fourier transform. -/
def coefficient (mu : FinitePMF U) (Az : U →ₗ[F₂] (β → F₂)) (Bz : V →ₗ[F₂] (β → F₂))
    (bz : β → F₂) (A : ι → U →ₗ[F₂] (α → F₂)) (B : ι → V →ₗ[F₂] (α → F₂))
    (b : ι → α → F₂) : ℝ :=
  ∑ u : ι → α → F₂, if ∀ j, u j≠0 then
    (∏ j, (binarySign (dotProduct (u j) (b j)):ℝ))*
      ∑ v : β → F₂, if relationMap Bz v=∑ j, relationMap (B j) (u j) then
        (binarySign (dotProduct v bz):ℝ)*
          environmentFourier mu ((∑ j, relationMap (A j) (u j))-relationMap Az v) else 0 else 0

/-- The full centered moment identity, with no separation or independence of the queried blocks. -/
theorem centered_moment (mu : FinitePMF U) (Az : U →ₗ[F₂] (β → F₂))
    (Bz : V →ₗ[F₂] (β → F₂)) (hBz : Function.Surjective Bz) (bz : β → F₂)
    (A : ι → U →ₗ[F₂] (α → F₂)) (B : ι → V →ₗ[F₂] (α → F₂)) (b : ι → α → F₂)
    (hp : 0<eventProbability (productPMF mu (FinitePMF.uniform V)) (plant Az Bz bz)) :
    finitePMFExpectation (conditional (productPMF mu (FinitePMF.uniform V)) (plant Az Bz bz) hp)
      (fun z ↦ ∏ j, (block (A j) (B j) (b j) z-referenceRate α))=
      (referenceRate α)^Fintype.card ι*coefficient mu Az Bz bz A B b := by
  simp_rw [centered_product]
  rw [expectation_const_mul,expectation_finset_sum]
  congr 1
  apply sum_congr rfl
  intro u hu
  simp_rw [block_product]
  by_cases hn : ∀ j, u j≠0
  · simp_rw [if_pos hn]
    have he (z : U×V) :
        (∏ j, (binarySign (dotProduct (u j) (b j)):ℝ))*
          sign (∑ j, relationMap (A j) (u j)) z.1*sign (∑ j, relationMap (B j) (u j)) z.2=
        (∏ j, (binarySign (dotProduct (u j) (b j)):ℝ))*
          (sign (∑ j, relationMap (A j) (u j)) z.1*sign (∑ j, relationMap (B j) (u j)) z.2) := by ring
    simp_rw [he]
    rw [expectation_const_mul,conditional_fourier mu Az Bz hBz bz _ _ hp]
  · simp_rw [if_neg hn]
    exact expectation_const _ 0

/-- The binary reference rate in the paper is exactly 2^(-L). -/
theorem referenceRate_fin (L : ℕ) : referenceRate (Fin L)=1/(2:ℝ)^L := by
  simp [referenceRate,one_div]

/-- The displayed product of phases is the phase of their sum. -/
theorem phase_product (a : ι → F₂) :
    (∏ j, (binarySign (a j):ℝ))=(binarySign (∑ j, a j):ℝ) := by
  have h (S : Finset ι) : (∏ j∈S, (binarySign (a j):ℝ))=(binarySign (∑ j∈S, a j):ℝ) := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert j S hj ih => rw [prod_insert hj,sum_insert hj,ih,binarySign_add,Int.cast_mul]
  exact h univ

end
end PaperC.Prel8.CenteredPalmFourier
