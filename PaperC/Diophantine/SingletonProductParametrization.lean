import PaperC.Diophantine.ComponentNormalization
import Mathlib.Data.Nat.Sqrt

/-!
# Parametrization of a product of two singleton components

This file isolates the exact arithmetic core of Lemma 9.5.  For positive
integers satisfying

`X * Y = d * z²`

with `d` squarefree, the squarefree kernels of `X` and `Y` have a unique
decomposition

`X = e c u²`, `Y = (d / e) c v²`,

where `e ∣ d`, `c` is squarefree, and `c` is coprime to `d`.

The parameters are canonical:

* `e = gcd (squarefreeKernel X) d`;
* `c = squarefreeKernel X / e`;
* `u` and `v` are the canonical square parts of `X` and `Y`.

No counting theorem or external Diophantine input is used here.
-/

namespace PaperC
namespace SingletonProductParametrization

open DefectivePredicate
open LargeOddKernel
open ComponentNormalization

/-- The part of `d` assigned to the first singleton. -/
noncomputable def canonicalDPart (X d : ℕ) : ℕ :=
  Nat.gcd (squarefreeKernel X) d

/--
The squarefree factor common to the two singleton square classes and
coprime to `d`.
-/
noncomputable def canonicalCommonPart (X d : ℕ) : ℕ :=
  squarefreeKernel X / canonicalDPart X d

/-- The canonical square root attached to `X`. -/
noncomputable def canonicalFirstRoot (X : ℕ) : ℕ :=
  canonicalSquarePart X

/-- The canonical square root attached to `Y`. -/
noncomputable def canonicalSecondRoot (Y : ℕ) : ℕ :=
  canonicalSquarePart Y

/-! ## Elementary properties of the canonical parameters -/

/-- The canonical `d`-part divides `d`. -/
theorem canonicalDPart_dvd_right (X d : ℕ) :
    canonicalDPart X d ∣ d :=
  Nat.gcd_dvd_right _ _

/-- The canonical `d`-part also divides the squarefree kernel of `X`. -/
theorem canonicalDPart_dvd_kernel (X d : ℕ) :
    canonicalDPart X d ∣ squarefreeKernel X :=
  Nat.gcd_dvd_left _ _

/-- Positivity of the canonical `d`-part when `d` is positive. -/
theorem canonicalDPart_pos
    {X d : ℕ} (hd : 0 < d) :
    0 < canonicalDPart X d :=
  Nat.gcd_pos_of_pos_right _ hd

/-- The canonical common part is positive. -/
theorem canonicalCommonPart_pos
    {X d : ℕ} (hd : 0 < d) :
    0 < canonicalCommonPart X d := by
  rw [canonicalCommonPart, Nat.div_pos_iff]
  refine ⟨canonicalDPart_pos hd, ?_⟩
  exact Nat.le_of_dvd (squarefreeKernel_pos X)
    (canonicalDPart_dvd_kernel X d)

/-- Recombining the two canonical factors recovers the kernel of `X`. -/
theorem canonical_parts_mul
    (X d : ℕ) :
    canonicalDPart X d * canonicalCommonPart X d =
      squarefreeKernel X := by
  rw [canonicalCommonPart]
  exact Nat.mul_div_cancel'
    (canonicalDPart_dvd_kernel X d)

/-- The canonical `d`-part is squarefree when `d` is. -/
theorem canonicalDPart_squarefree
    {X d : ℕ} (hdSquarefree : Squarefree d) :
    Squarefree (canonicalDPart X d) :=
  hdSquarefree.squarefree_of_dvd
    (canonicalDPart_dvd_right X d)

/-- The canonical common part is squarefree. -/
theorem canonicalCommonPart_squarefree
    (X d : ℕ) :
    Squarefree (canonicalCommonPart X d) := by
  apply (squarefreeKernel_squarefree X).squarefree_of_dvd
  rw [canonicalCommonPart]
  exact Nat.div_dvd_of_dvd (canonicalDPart_dvd_kernel X d)

/--
The defining gcd removes every prime shared with `d`, so the remaining
common part is coprime to `d`.
-/
theorem canonicalCommonPart_coprime
    {X d : ℕ} (hd : 0 < d) :
    (canonicalCommonPart X d).Coprime d := by
  simpa [canonicalCommonPart, canonicalDPart] using
    Nat.coprime_div_gcd_of_squarefree
      (squarefreeKernel_squarefree X) hd.ne'

/-- The complementary divisor `d/e` is positive. -/
theorem complementaryDPart_pos
    {X d : ℕ} (hd : 0 < d) :
    0 < d / canonicalDPart X d := by
  rw [Nat.div_pos_iff]
  exact ⟨canonicalDPart_pos hd,
    Nat.le_of_dvd hd (canonicalDPart_dvd_right X d)⟩

/-- The complementary divisor `d/e` is squarefree. -/
theorem complementaryDPart_squarefree
    {X d : ℕ} (hdSquarefree : Squarefree d) :
    Squarefree (d / canonicalDPart X d) :=
  hdSquarefree.squarefree_of_dvd
    (Nat.div_dvd_of_dvd (canonicalDPart_dvd_right X d))

/--
The squarefree kernel of `X` is the product of the canonical `d`-part and
the canonical common part.
-/
theorem first_kernel_eq
    (X d : ℕ) :
    squarefreeKernel X =
      canonicalDPart X d * canonicalCommonPart X d :=
  (canonical_parts_mul X d).symm

/--
The product `(d/e)c` is squarefree.  This is the prospective squarefree
kernel of `Y`.
-/
theorem complementary_mul_common_squarefree
    {X d : ℕ}
    (hd : 0 < d)
    (hdSquarefree : Squarefree d) :
    Squarefree
      ((d / canonicalDPart X d) *
        canonicalCommonPart X d) := by
  have hcommonD :
      (canonicalCommonPart X d).Coprime d :=
    canonicalCommonPart_coprime hd
  have hquotDvd :
      d / canonicalDPart X d ∣ d :=
    Nat.div_dvd_of_dvd (canonicalDPart_dvd_right X d)
  have hcoprime :
      (d / canonicalDPart X d).Coprime
        (canonicalCommonPart X d) :=
    (hcommonD.of_dvd_right hquotDvd).symm
  exact (Nat.squarefree_mul hcoprime).mpr
    ⟨complementaryDPart_squarefree hdSquarefree,
      canonicalCommonPart_squarefree X d⟩

/-! ## The canonical parametrization -/

/--
Parity identity underlying the second factor:

`squarefreeKernel Y = (d/e)c`.
-/
theorem second_kernel_eq
    {X Y d z : ℕ}
    (hX : 0 < X)
    (hY : 0 < Y)
    (hd : 0 < d)
    (hz : 0 < z)
    (hdSquarefree : Squarefree d)
    (hequation : X * Y = d * z ^ 2) :
    squarefreeKernel Y =
      (d / canonicalDPart X d) *
        canonicalCommonPart X d := by
  let e := canonicalDPart X d
  let c := canonicalCommonPart X d
  let d' := d / e
  have he : 0 < e := canonicalDPart_pos hd
  have hc : 0 < c := canonicalCommonPart_pos hd
  have hd' : 0 < d' := complementaryDPart_pos hd
  have hed : e ∣ d := canonicalDPart_dvd_right X d
  have hek : e * c = squarefreeKernel X :=
    canonical_parts_mul X d
  have hdFactor : e * d' = d := by
    simpa only [d', e, mul_comm] using
      Nat.div_mul_cancel hed
  have hparityX :
      parityVec X = parityVec (e * c) := by
    have hcanonical :=
      (canonical_squarefree_decomposition hX).2.2.2
    calc
      parityVec X =
          parityVec
            (squarefreeKernel X *
              canonicalSquarePart X ^ 2) :=
        congrArg parityVec hcanonical
      _ = parityVec (squarefreeKernel X) := by
        rw [parityVec_mul
          (squarefreeKernel_pos X).ne'
          (pow_ne_zero 2
            (canonicalSquarePart_ne_zero hX.ne')),
          parityVec_pow_two, add_zero]
      _ = parityVec (e * c) := by
        rw [hek]
  have hparityY :
      parityVec Y = parityVec (d' * c) := by
    have htransfer :
        parityVec Y = parityVec (d * X) :=
      parityVec_right_factor hX hY hd hz hequation
    have hdouble :
        parityVec e + parityVec e = 0 := by
      rw [← parityVec_mul he.ne' he.ne',
        parityVec_mul_self]
    calc
      parityVec Y =
          parityVec d + parityVec X := by
        rw [htransfer,
          parityVec_mul hd.ne' hX.ne']
      _ =
          parityVec (e * d') +
            parityVec (e * c) := by
        rw [hdFactor, hparityX]
      _ =
          (parityVec e + parityVec d') +
            (parityVec e + parityVec c) := by
        rw [parityVec_mul he.ne' hd'.ne',
          parityVec_mul he.ne' hc.ne']
      _ =
          (parityVec e + parityVec e) +
            (parityVec d' + parityVec c) := by
        abel
      _ = parityVec d' + parityVec c := by
        rw [hdouble, zero_add]
      _ = parityVec (d' * c) :=
        (parityVec_mul hd'.ne' hc.ne').symm
  have hkernel :
      squarefreeKernel Y = squarefreeKernel (d' * c) :=
    squarefreeKernel_eq_of_parityVec_eq hparityY
  have htargetSquarefree :
      Squarefree (d' * c) := by
    simpa only [d', c] using
      complementary_mul_common_squarefree hd hdSquarefree
  have htargetCanonical :
      d' * c = squarefreeKernel (d' * c) := by
    exact squarefree_factor_unique
      (n := d' * c) (e := d' * c) (v := 1)
      (Nat.mul_pos hd' hc) (by simp)
      htargetSquarefree (by simp)
  exact hkernel.trans htargetCanonical.symm

/--
The two exact factorization identities with the canonical parameters.
-/
theorem canonical_factorizations
    {X Y d z : ℕ}
    (hX : 0 < X)
    (hY : 0 < Y)
    (hd : 0 < d)
    (hz : 0 < z)
    (hdSquarefree : Squarefree d)
    (hequation : X * Y = d * z ^ 2) :
    X =
        canonicalDPart X d *
          canonicalCommonPart X d *
          canonicalFirstRoot X ^ 2 ∧
      Y =
        (d / canonicalDPart X d) *
          canonicalCommonPart X d *
          canonicalSecondRoot Y ^ 2 := by
  constructor
  · have hcanonical :=
      (canonical_squarefree_decomposition hX).2.2.2
    rw [first_kernel_eq X d] at hcanonical
    simpa [canonicalFirstRoot, mul_assoc] using hcanonical
  · have hcanonical :=
      (canonical_squarefree_decomposition hY).2.2.2
    rw [second_kernel_eq hX hY hd hz hdSquarefree hequation]
      at hcanonical
    simpa [canonicalSecondRoot, mul_assoc] using hcanonical

/--
Existential formulation matching Lemma 9.5, with positivity,
squarefreeness, coprimality and both exact identities.
-/
theorem exists_singleton_product_parametrization
    {X Y d z : ℕ}
    (hX : 0 < X)
    (hY : 0 < Y)
    (hd : 0 < d)
    (hz : 0 < z)
    (hdSquarefree : Squarefree d)
    (hequation : X * Y = d * z ^ 2) :
    ∃ e c u v : ℕ,
      0 < e ∧
      e ∣ d ∧
      Squarefree e ∧
      0 < c ∧
      Squarefree c ∧
      c.Coprime d ∧
      0 < u ∧
      0 < v ∧
      X = e * c * u ^ 2 ∧
      Y = (d / e) * c * v ^ 2 := by
  refine
    ⟨canonicalDPart X d,
      canonicalCommonPart X d,
      canonicalFirstRoot X,
      canonicalSecondRoot Y,
      canonicalDPart_pos hd,
      canonicalDPart_dvd_right X d,
      canonicalDPart_squarefree hdSquarefree,
      canonicalCommonPart_pos hd,
      canonicalCommonPart_squarefree X d,
      canonicalCommonPart_coprime hd,
      ?_, ?_, ?_⟩
  · exact Nat.pos_of_ne_zero
      (canonicalSquarePart_ne_zero hX.ne')
  · exact Nat.pos_of_ne_zero
      (canonicalSquarePart_ne_zero hY.ne')
  · exact canonical_factorizations
      hX hY hd hz hdSquarefree hequation

/-! ## Bounds used by the counting argument -/

/-- The parameter `e` lies among the divisors of `d`. -/
theorem canonicalDPart_le
    {X d : ℕ} (hd : 0 < d) :
    canonicalDPart X d ≤ d :=
  Nat.le_of_dvd hd (canonicalDPart_dvd_right X d)

/-- The common squarefree factor divides `X`. -/
theorem canonicalCommonPart_dvd_first
    {X d : ℕ} (hX : 0 < X) :
    canonicalCommonPart X d ∣ X := by
  exact (Nat.div_dvd_of_dvd
    (canonicalDPart_dvd_kernel X d)).trans
      (squarefreeKernel_dvd hX)

/-- Hence the common factor is bounded by `X`. -/
theorem canonicalCommonPart_le_first
    {X d : ℕ} (hX : 0 < X) :
    canonicalCommonPart X d ≤ X :=
  Nat.le_of_dvd hX
    (canonicalCommonPart_dvd_first hX)

/-- The full nonsquare coefficient `ec` divides `X`. -/
theorem first_coefficient_dvd
    {X d : ℕ} (hX : 0 < X) :
    canonicalDPart X d *
        canonicalCommonPart X d ∣ X := by
  rw [canonical_parts_mul]
  exact squarefreeKernel_dvd hX

/-- The full nonsquare coefficient `ec` is bounded by `X`. -/
theorem first_coefficient_le
    {X d : ℕ} (hX : 0 < X) :
    canonicalDPart X d *
        canonicalCommonPart X d ≤ X :=
  Nat.le_of_dvd hX (first_coefficient_dvd hX)

/-- The complementary divisor `d/e` is bounded by `d`. -/
theorem complementaryDPart_le
    {X d : ℕ} (hd : 0 < d) :
    d / canonicalDPart X d ≤ d := by
  exact Nat.le_of_dvd hd
    (Nat.div_dvd_of_dvd
      (canonicalDPart_dvd_right X d))

/-- Under the product equation, the second nonsquare coefficient divides `Y`. -/
theorem second_coefficient_dvd
    {X Y d z : ℕ}
    (hX : 0 < X)
    (hY : 0 < Y)
    (hd : 0 < d)
    (hz : 0 < z)
    (hdSquarefree : Squarefree d)
    (hequation : X * Y = d * z ^ 2) :
    (d / canonicalDPart X d) *
        canonicalCommonPart X d ∣ Y := by
  rw [← second_kernel_eq
    hX hY hd hz hdSquarefree hequation]
  exact squarefreeKernel_dvd hY

/-- Under the product equation, the second nonsquare coefficient is at most `Y`. -/
theorem second_coefficient_le
    {X Y d z : ℕ}
    (hX : 0 < X)
    (hY : 0 < Y)
    (hd : 0 < d)
    (hz : 0 < z)
    (hdSquarefree : Squarefree d)
    (hequation : X * Y = d * z ^ 2) :
    (d / canonicalDPart X d) *
        canonicalCommonPart X d ≤ Y :=
  Nat.le_of_dvd hY
    (second_coefficient_dvd
      hX hY hd hz hdSquarefree hequation)

/-- The common factor divides the second singleton as well. -/
theorem canonicalCommonPart_dvd_second
    {X Y d z : ℕ}
    (hX : 0 < X)
    (hY : 0 < Y)
    (hd : 0 < d)
    (hz : 0 < z)
    (hdSquarefree : Squarefree d)
    (hequation : X * Y = d * z ^ 2) :
    canonicalCommonPart X d ∣ Y := by
  exact (dvd_mul_left
    (canonicalCommonPart X d)
    (d / canonicalDPart X d)).trans
      (second_coefficient_dvd
        hX hY hd hz hdSquarefree hequation)

/-- The canonical square `u²` divides `X`. -/
theorem first_square_dvd
    {X : ℕ} (hX : 0 < X) :
    canonicalFirstRoot X ^ 2 ∣ X := by
  refine ⟨squarefreeKernel X, ?_⟩
  simpa [canonicalFirstRoot, mul_comm] using
    (canonical_squarefree_decomposition hX).2.2.2

/-- The canonical square `v²` divides `Y`. -/
theorem second_square_dvd
    {Y : ℕ} (hY : 0 < Y) :
    canonicalSecondRoot Y ^ 2 ∣ Y := by
  refine ⟨squarefreeKernel Y, ?_⟩
  simpa [canonicalSecondRoot, mul_comm] using
    (canonical_squarefree_decomposition hY).2.2.2

/-- The first canonical root is bounded by `√X`. -/
theorem canonicalFirstRoot_le_sqrt
    {X : ℕ} (hX : 0 < X) :
    canonicalFirstRoot X ≤ Nat.sqrt X := by
  rw [Nat.le_sqrt']
  exact Nat.le_of_dvd hX (first_square_dvd hX)

/-- The second canonical root is bounded by `√Y`. -/
theorem canonicalSecondRoot_le_sqrt
    {Y : ℕ} (hY : 0 < Y) :
    canonicalSecondRoot Y ≤ Nat.sqrt Y := by
  rw [Nat.le_sqrt']
  exact Nat.le_of_dvd hY (second_square_dvd hY)

/-- Polynomial bounds on `X` transfer directly to `c`. -/
theorem canonicalCommonPart_polynomial_bound
    {N K X d : ℕ}
    (hX : 0 < X)
    (hXBound : X ≤ N ^ K) :
    canonicalCommonPart X d ≤ N ^ K :=
  (canonicalCommonPart_le_first hX).trans hXBound

/-!
The parametrization also has an elementary converse: the two displayed
factors always multiply to `d` times a square.  This identity is useful when
replacing the original equation by sums over `(e,c,u,v)`.
-/
theorem product_identity_of_parameters
    {d e c u v : ℕ}
    (heDvd : e ∣ d) :
    (e * c * u ^ 2) *
        ((d / e) * c * v ^ 2) =
      d * (c * u * v) ^ 2 := by
  have heComplement : e * (d / e) = d := by
    simpa [mul_comm] using Nat.div_mul_cancel heDvd
  calc
    (e * c * u ^ 2) *
          ((d / e) * c * v ^ 2) =
        (e * (d / e)) *
          (c * u * v) ^ 2 := by
      ring
    _ = d * (c * u * v) ^ 2 := by
      rw [heComplement]

/-!
In particular, every admissible tuple yields a solution of the original
square-class equation.
-/
theorem parameters_give_square_product
    {X Y d e c u v : ℕ}
    (heDvd : e ∣ d)
    (hX : X = e * c * u ^ 2)
    (hY : Y = (d / e) * c * v ^ 2) :
    X * Y = d * (c * u * v) ^ 2 := by
  rw [hX, hY]
  exact product_identity_of_parameters heDvd

/-! ## Uniqueness -/

/--
Any positive parameters satisfying the structural conditions and the first
factorization have the canonical values of `e`, `c`, and `u`.
-/
theorem first_parameters_unique
    {X d e c u : ℕ}
    (hX : 0 < X)
    (_hd : 0 < d)
    (hdSquarefree : Squarefree d)
    (he : 0 < e)
    (hc : 0 < c)
    (hu : 0 < u)
    (heDvd : e ∣ d)
    (hcSquarefree : Squarefree c)
    (hcD : c.Coprime d)
    (hfactor : X = e * c * u ^ 2) :
    e = canonicalDPart X d ∧
      c = canonicalCommonPart X d ∧
      u = canonicalFirstRoot X := by
  have heSquarefree : Squarefree e :=
    hdSquarefree.squarefree_of_dvd heDvd
  have hecCoprime : e.Coprime c :=
    (hcD.of_dvd_right heDvd).symm
  have hecSquarefree : Squarefree (e * c) :=
    (Nat.squarefree_mul hecCoprime).mpr
      ⟨heSquarefree, hcSquarefree⟩
  have hecKernel :
      e * c = squarefreeKernel X :=
    squarefree_factor_unique
      (Nat.mul_pos he hc) hu hecSquarefree hfactor
  have heCanonical : e = canonicalDPart X d := by
    symm
    calc
      canonicalDPart X d =
          Nat.gcd (squarefreeKernel X) d := rfl
      _ = Nat.gcd (c * e) d := by
        rw [← hecKernel, mul_comm]
      _ = e :=
        Nat.gcd_mul_of_coprime_of_dvd hcD heDvd
  have hcCanonical :
      c = canonicalCommonPart X d := by
    rw [canonicalCommonPart, ← heCanonical,
      ← hecKernel]
    simpa [mul_comm] using
      (Nat.mul_div_left c he).symm
  have huCanonical :
      u = canonicalFirstRoot X := by
    have hcanonical :=
      (canonical_squarefree_decomposition hX).2.2.2
    have hsquares :
        u ^ 2 = canonicalSquarePart X ^ 2 := by
      apply mul_left_cancel₀ (Nat.mul_pos he hc).ne'
      rw [← hfactor, hecKernel]
      exact hcanonical
    simpa [canonicalFirstRoot] using
      Nat.pow_left_injective
        (by decide : 2 ≠ 0) hsquares
  exact ⟨heCanonical, hcCanonical, huCanonical⟩

/--
Joint uniqueness of all four positive parameters.
-/
theorem singleton_product_parametrization_unique
    {X Y d e c u v : ℕ}
    (hX : 0 < X)
    (hY : 0 < Y)
    (hd : 0 < d)
    (hdSquarefree : Squarefree d)
    (he : 0 < e)
    (hc : 0 < c)
    (hu : 0 < u)
    (hv : 0 < v)
    (heDvd : e ∣ d)
    (hcSquarefree : Squarefree c)
    (hcD : c.Coprime d)
    (hfirst : X = e * c * u ^ 2)
    (hsecond : Y = (d / e) * c * v ^ 2) :
    e = canonicalDPart X d ∧
      c = canonicalCommonPart X d ∧
      u = canonicalFirstRoot X ∧
      v = canonicalSecondRoot Y := by
  obtain ⟨heCanonical, hcCanonical, huCanonical⟩ :=
    first_parameters_unique hX hd hdSquarefree
      he hc hu heDvd hcSquarefree hcD hfirst
  have hquotPos : 0 < d / e := by
    rw [Nat.div_pos_iff]
    exact ⟨he, Nat.le_of_dvd hd heDvd⟩
  have hquotSquarefree :
      Squarefree (d / e) :=
    hdSquarefree.squarefree_of_dvd
      (Nat.div_dvd_of_dvd heDvd)
  have hquotCoprime :
      (d / e).Coprime c :=
    (hcD.of_dvd_right
      (Nat.div_dvd_of_dvd heDvd)).symm
  have hcoefficientSquarefree :
      Squarefree ((d / e) * c) :=
    (Nat.squarefree_mul hquotCoprime).mpr
      ⟨hquotSquarefree, hcSquarefree⟩
  have hsecondKernel :
      (d / e) * c = squarefreeKernel Y :=
    squarefree_factor_unique
      (Nat.mul_pos hquotPos hc) hv
      hcoefficientSquarefree hsecond
  have hvCanonical :
      v = canonicalSecondRoot Y := by
    have hcanonical :=
      (canonical_squarefree_decomposition hY).2.2.2
    have hsquares :
        v ^ 2 = canonicalSquarePart Y ^ 2 := by
      apply mul_left_cancel₀
        (Nat.mul_pos hquotPos hc).ne'
      rw [← hsecond, hsecondKernel]
      exact hcanonical
    simpa [canonicalSecondRoot] using
      Nat.pow_left_injective
        (by decide : 2 ≠ 0) hsquares
  exact
    ⟨heCanonical, hcCanonical, huCanonical,
      hvCanonical⟩

end SingletonProductParametrization
end PaperC
