import PaperCPrel8.DictionaryAverage
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # The actual uniform surjection and offset ensemble of affine dictionaries -/
namespace PaperC.Prel8.AffineDictionarySample
open PaperC
open scoped BigOperators
noncomputable section
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

abbrev Word (B : ℕ) := Fin B → F₂
abbrev Surjection (B r : ℕ) := {A : Word B →ₗ[F₂] Word r // Function.Surjective A}
abbrev Sample (B r : ℕ) := Surjection B r × Word r

instance (B r : ℕ) : Finite (Word B →ₗ[F₂] Word r) :=
  Finite.of_injective (fun A : Word B →ₗ[F₂] Word r => (A : Word B → Word r)) DFunLike.coe_injective
instance (B r : ℕ) : Fintype (Surjection B r) := Fintype.ofFinite _

/-- Every full-row-rank map and every offset occur once in this finite sample. -/
def dictionary {B r : ℕ} (s : Sample B r) : Finset (Word B) :=
  Finset.univ.filter (fun u => s.1.val u=s.2)

theorem mem_dictionary {B r : ℕ} (s : Sample B r) (u : Word B) :
    u ∈ dictionary s ↔ s.1.val u=s.2 := by simp [dictionary]

/-- Coordinate projection constructs a full-row-rank map whenever r<=B. -/
theorem surjection_nonempty {B r : ℕ} (hr : r ≤ B) : Nonempty (Surjection B r) := by
  let A : Word B →ₗ[F₂] Word r := LinearMap.funLeft F₂ F₂ (Fin.castLE hr)
  refine ⟨⟨A,?_⟩⟩
  intro v
  refine ⟨fun j => if h : j.val < r then v ⟨j.val,h⟩ else 0,?_⟩
  ext j
  simp [A,LinearMap.funLeft,Fin.castLE,j.isLt]

/-- The fibre size is the literal 2^(B-r), including both endpoint ranks. -/
theorem card_dictionary {B r : ℕ} (s : Sample B r) : (dictionary s).card=2^(B-r) := by
  have hdim := s.1.val.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr s.1.property] at hdim
  simp only [finrank_top,Module.finrank_pi,Fintype.card_fin] at hdim
  have hk : Module.finrank F₂ (LinearMap.ker s.1.val)=B-r := by omega
  obtain ⟨x,hx⟩ := s.1.property s.2
  letI : Fintype (LinearMap.ker s.1.val) := Fintype.ofFinite _
  let e : {u // u ∈ dictionary s} ≃ LinearMap.ker s.1.val := {
    toFun := fun u => ⟨u.val-x,by simp [LinearMap.mem_ker,map_sub,(mem_dictionary s u.val).mp u.property,hx]⟩
    invFun := fun z => ⟨z.val+x,by rw [mem_dictionary,map_add]; simpa [hx] using z.property⟩
    left_inv := fun u => by apply Subtype.ext; simp
    right_inv := fun z => by apply Subtype.ext; simp }
  calc
    _ = Fintype.card {u // u ∈ dictionary s} := (Fintype.card_coe _).symm
    _ = Fintype.card (LinearMap.ker s.1.val) := Fintype.card_congr e
    _ = 2^Module.finrank F₂ (LinearMap.ker s.1.val) := PaperC.Affine.card_eq_two_pow_finrank
    _ = _ := by rw [hk]

/-- Precomposition by an invertible coordinate map permutes all surjections. -/
def precompose {B r : ℕ} (e : Word B ≃ₗ[F₂] Word B) : Surjection B r ≃ Surjection B r where
  toFun A := ⟨A.val.comp e.toLinearMap,A.property.comp e.surjective⟩
  invFun A := ⟨A.val.comp e.symm.toLinearMap,A.property.comp e.symm.surjective⟩
  left_inv A := by apply Subtype.ext; ext x; simp
  right_inv A := by apply Subtype.ext; ext x; simp

/-- The general linear group sends any nonzero word to any other nonzero word. -/
theorem exists_equiv_nonzero {B : ℕ} (u v : Word B) (hu : u ≠ 0) (hv : v ≠ 0) :
    ∃ e : Word B ≃ₗ[F₂] Word B, e u=v := by
  let eu := LinearEquiv.toSpanNonzeroSingleton F₂ (Word B) u hu
  let ev := LinearEquiv.toSpanNonzeroSingleton F₂ (Word B) v hv
  obtain ⟨e,he⟩ := Submodule.exists_linearEquiv_restrict_eq (eu.symm.trans ev)
  refine ⟨e,?_⟩
  have h := he (eu 1)
  change ↑(ev (eu.symm (eu 1)))=e ↑(eu 1) at h
  rw [eu.symm_apply_apply] at h
  simpa [eu,ev] using h.symm

end
end PaperC.Prel8.AffineDictionarySample
