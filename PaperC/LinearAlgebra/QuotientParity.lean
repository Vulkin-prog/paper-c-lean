import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# A quotient-dimension loss from a surviving parity functional

This file isolates the finite-dimensional linear-algebra step used in
Lemma 6.4 of the manuscript.  If `S ≤ R ≤ W`, the systematic code `S`
has dimension `m - 1`, and a nonzero functional on `W` vanishes on `R`,
then the residual quotient `R / S` has dimension at most
`dim W - m`.

The hypotheses about disjoint exact units enter only through the already
proved identity `dim S = m - 1`; the argument below is independent of the
particular construction of that code.
-/

namespace PaperC
namespace QuotientParity

noncomputable section

variable {K V : Type*}
variable [Field K] [AddCommGroup V] [Module K V]

/--
The functional induced on `V ⧸ S` by a functional which vanishes on `S`.
-/
def quotientFunctional
    (S : Submodule K V)
    (lambda : V →ₗ[K] K)
    (hSker : S ≤ LinearMap.ker lambda) :
    (V ⧸ S) →ₗ[K] K :=
  S.liftQ lambda hSker

@[simp]
theorem quotientFunctional_mkQ
    (S : Submodule K V)
    (lambda : V →ₗ[K] K)
    (hSker : S ≤ LinearMap.ker lambda)
    (v : V) :
    quotientFunctional S lambda hSker (S.mkQ v) = lambda v := by
  rfl

/--
Factoring through a quotient does not destroy a genuinely nonzero
functional.  Thus, once `lambda` vanishes on `S`, saying that it survives
on `V / S` is equivalent to saying that it is nonzero on `V`.
-/
theorem quotientFunctional_ne_zero_iff
    (S : Submodule K V)
    (lambda : V →ₗ[K] K)
    (hSker : S ≤ LinearMap.ker lambda) :
    quotientFunctional S lambda hSker ≠ 0 ↔ lambda ≠ 0 := by
  constructor
  · intro hquot hlambda
    apply hquot
    subst lambda
    apply LinearMap.ext
    intro q
    obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective S q
    rfl
  · intro hlambda hquot
    apply hlambda
    ext v
    have hv :=
      LinearMap.congr_fun hquot (S.mkQ v)
    change lambda v = 0 at hv
    exact hv

/--
Regard a smaller ambient submodule `S ≤ W` as a submodule of the type `W`.
Its dimension is unchanged.
-/
theorem finrank_comap_subtype_of_le
    [FiniteDimensional K V]
    {S W : Submodule K V}
    (hSW : S ≤ W) :
    Module.finrank K (S.comap W.subtype) =
      Module.finrank K S := by
  rw [← Submodule.finrank_map_subtype_eq W (S.comap W.subtype)]
  rw [Submodule.map_comap_subtype, inf_eq_right.mpr hSW]

/--
A nonzero functional annihilating `R` cuts at least one dimension from the
ambient space.
-/
theorem finrank_le_finrank_sub_one_of_le_ker
    [FiniteDimensional K V]
    {R : Submodule K V}
    (lambda : V →ₗ[K] K)
    (hlambda : lambda ≠ 0)
    (hRker : R ≤ LinearMap.ker lambda) :
    Module.finrank K R ≤ Module.finrank K V - 1 := by
  have hmono :
      Module.finrank K R ≤
        Module.finrank K (LinearMap.ker lambda) :=
    Submodule.finrank_mono hRker
  have hcodim :
      Module.finrank K (LinearMap.ker lambda) + 1 =
        Module.finrank K V :=
    Module.Dual.finrank_ker_add_one_of_ne_zero hlambda
  omega

/--
Ambient-space form of the quotient estimate.  Here `V` plays the role of
`W`; the quotient is represented literally as a quotient of the subtype
`R` by the copy of `S` inside it.
-/
theorem finrank_quotient_le_finrank_sub
    [FiniteDimensional K V]
    {S R : Submodule K V}
    {m : ℕ}
    (hm : 0 < m)
    (hSR : S ≤ R)
    (hSdim : Module.finrank K S = m - 1)
    (lambda : V →ₗ[K] K)
    (hlambda : lambda ≠ 0)
    (hRker : R ≤ LinearMap.ker lambda) :
    Module.finrank K (R ⧸ S.comap R.subtype) ≤
      Module.finrank K V - m := by
  rw [Submodule.finrank_quotient]
  rw [finrank_comap_subtype_of_le hSR, hSdim]
  have hRdim :=
    finrank_le_finrank_sub_one_of_le_ker
      lambda hlambda hRker
  omega

/--
Version whose nonvanishing hypothesis is stated literally on the quotient
`V / S`.
-/
theorem finrank_quotient_le_finrank_sub_of_induced_ne_zero
    [FiniteDimensional K V]
    {S R : Submodule K V}
    {m : ℕ}
    (hm : 0 < m)
    (hSR : S ≤ R)
    (hSdim : Module.finrank K S = m - 1)
    (lambda : V →ₗ[K] K)
    (hRker : R ≤ LinearMap.ker lambda)
    (hlambdaQuot :
      quotientFunctional S lambda (hSR.trans hRker) ≠ 0) :
    Module.finrank K (R ⧸ S.comap R.subtype) ≤
      Module.finrank K V - m := by
  apply finrank_quotient_le_finrank_sub
    hm hSR hSdim lambda
  · exact
      (quotientFunctional_ne_zero_iff
        S lambda (hSR.trans hRker)).mp hlambdaQuot
  · exact hRker

/--
Nested-submodule form used by Lemma 6.4.  The functional is given on the
original ambient space, but it only has to survive after restriction to
`W`; it annihilates all of `R`.
-/
theorem finrank_nested_quotient_le_finrank_sub
    [FiniteDimensional K V]
    {S R W : Submodule K V}
    {m : ℕ}
    (hm : 0 < m)
    (hSR : S ≤ R)
    (hRW : R ≤ W)
    (hSdim : Module.finrank K S = m - 1)
    (lambda : V →ₗ[K] K)
    (hlambdaW : lambda.domRestrict W ≠ 0)
    (hRker : R ≤ LinearMap.ker lambda) :
    Module.finrank K (R ⧸ S.comap R.subtype) ≤
      Module.finrank K W - m := by
  let RwithinW : Submodule K W := R.comap W.subtype
  let SwithinW : Submodule K W := S.comap W.subtype
  have hSRwithin : SwithinW ≤ RwithinW := by
    intro s hs
    exact hSR hs
  have hRwithinKer :
      RwithinW ≤ LinearMap.ker (lambda.domRestrict W) := by
    intro r hr
    exact hRker hr
  have hSwithinDim :
      Module.finrank K SwithinW = m - 1 := by
    rw [finrank_comap_subtype_of_le (hSR.trans hRW)]
    exact hSdim
  have hbound :
      Module.finrank K
          (RwithinW ⧸ SwithinW.comap RwithinW.subtype) ≤
        Module.finrank K W - m :=
    finrank_quotient_le_finrank_sub
      hm hSRwithin hSwithinDim
      (lambda.domRestrict W) hlambdaW hRwithinKer
  rw [Submodule.finrank_quotient] at hbound ⊢
  rw [finrank_comap_subtype_of_le hSR]
  rw [finrank_comap_subtype_of_le hSRwithin] at hbound
  rw [finrank_comap_subtype_of_le (hSR.trans hRW)] at hbound
  rw [finrank_comap_subtype_of_le hRW] at hbound
  exact hbound

/--
The same nested estimate when the surviving functional is defined directly
on `W`.  This is often the most convenient interface after passing to the
large-prime solution space.
-/
theorem finrank_nested_quotient_le_of_functional_on_W
    [FiniteDimensional K V]
    {S R W : Submodule K V}
    {m : ℕ}
    (hm : 0 < m)
    (hSR : S ≤ R)
    (hRW : R ≤ W)
    (hSdim : Module.finrank K S = m - 1)
    (lambda : W →ₗ[K] K)
    (hlambda : lambda ≠ 0)
    (hRker :
      R.comap W.subtype ≤ LinearMap.ker lambda) :
    Module.finrank K (R ⧸ S.comap R.subtype) ≤
      Module.finrank K W - m := by
  let RwithinW : Submodule K W := R.comap W.subtype
  let SwithinW : Submodule K W := S.comap W.subtype
  have hSRwithin : SwithinW ≤ RwithinW := by
    intro s hs
    exact hSR hs
  have hSwithinDim :
      Module.finrank K SwithinW = m - 1 := by
    rw [finrank_comap_subtype_of_le (hSR.trans hRW)]
    exact hSdim
  have hbound :
      Module.finrank K
          (RwithinW ⧸ SwithinW.comap RwithinW.subtype) ≤
        Module.finrank K W - m :=
    finrank_quotient_le_finrank_sub
      hm hSRwithin hSwithinDim lambda hlambda hRker
  rw [Submodule.finrank_quotient] at hbound ⊢
  rw [finrank_comap_subtype_of_le hSR]
  rw [finrank_comap_subtype_of_le hSRwithin] at hbound
  rw [finrank_comap_subtype_of_le (hSR.trans hRW)] at hbound
  rw [finrank_comap_subtype_of_le hRW] at hbound
  exact hbound

end

end QuotientParity
end PaperC
