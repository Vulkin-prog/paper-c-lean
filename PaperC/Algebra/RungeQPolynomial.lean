import PaperC.Algebra.IntegerPolynomialRootBound
import PaperC.Algebra.PolynomialHeightOperations
import PaperC.Algebra.RungeSplitProduct
import PaperC.Algebra.RungeTruncation
import PaperC.Algebra.RungeTruncationBounds
import PaperC.Analysis.RungePowerSeries
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Data.Int.AbsoluteValue
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.RingTheory.PowerSeries.Trunc

/-!
# The integral auxiliary polynomial in Runge's equality case

For `d = 2k` and integral shifts `γ`, put

`G(T) = ∏ ν, (T + γ ν)`

and let `P̄ = 2^d P` be the integral truncation constructed in
`RungeTruncation`.  The equality case in Paper C, Lemma 3.1, introduces

`Q(T) = 2^(2d) G(T) - P̄(T)^2`.

This file constructs `G` and `Q` directly in `ℤ[T]`.  It proves that `G`
has the advertised rational split form, that distinct shifts make `G`
non-square, and consequently that `Q` is nonzero.  We also record the
degree bounds available before using the high-coefficient cancellation,
and coefficient/height estimates that reduce the eventual height bound
to estimates for `G` and `P̄`.
-/

namespace PaperC
namespace RungeQPolynomial

open Finset Polynomial
open scoped BigOperators

-- The coefficient-ring argument of `PowerSeries.coeff` became implicit in
-- Lean 4.32.  This local compatibility syntax keeps the public statements
-- below textually unchanged.
local macro:max "PowerSeries.coeff" R:term:arg n:term:arg : term =>
  `(@PowerSeries.coeff $R _ $n)

/-- The integral polynomial `G(T) = ∏ ν, (T + γ ν)`. -/
noncomputable def integerSplitProduct
    {d : ℕ} (γ : Fin d → ℤ) : ℤ[X] :=
  ∏ ν, (X + C (γ ν))

/-- Mapping `G` to `ℚ[T]` gives the split product with roots `-γ ν`. -/
theorem map_integerSplitProduct
    {d : ℕ} (γ : Fin d → ℤ) :
    (integerSplitProduct γ).map (Int.castRingHom ℚ) =
      RungeSplitProduct.splitProduct
        (fun ν ↦ -(γ ν : ℚ)) := by
  classical
  rw [integerSplitProduct, Polynomial.map_prod]
  simp [RungeSplitProduct.splitProduct, sub_eq_add_neg]

/-- `G` is monic. -/
theorem monic_integerSplitProduct
    {d : ℕ} (γ : Fin d → ℤ) :
    (integerSplitProduct γ).Monic := by
  classical
  exact
    monic_prod_of_monic Finset.univ
      (fun ν ↦ X + C (γ ν))
      (fun ν _ ↦
        (monic_X_add_C (γ ν) :
          (X + C (γ ν) : ℤ[X]).Monic))

/-- The degree of `G` is the number of shifts. -/
@[simp]
theorem natDegree_integerSplitProduct
    {d : ℕ} (γ : Fin d → ℤ) :
    (integerSplitProduct γ).natDegree = d := by
  classical
  rw [integerSplitProduct,
    natDegree_prod_of_monic Finset.univ
      (fun ν ↦ X + C (γ ν))
      (fun ν _ ↦
        (monic_X_add_C (γ ν) :
          (X + C (γ ν) : ℤ[X]).Monic))]
  calc
    ∑ ν : Fin d, (X + C (γ ν) : ℤ[X]).natDegree =
        ∑ _ν : Fin d, 1 := by
      apply Finset.sum_congr rfl
      intro ν _
      exact natDegree_X_add_C (γ ν)
    _ = d := by simp

/-- In particular, `G` is never the zero polynomial. -/
theorem integerSplitProduct_ne_zero
    {d : ℕ} (γ : Fin d → ℤ) :
    integerSplitProduct γ ≠ 0 :=
  (monic_integerSplitProduct γ).ne_zero

private theorem int_natAbs_finset_prod
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℤ) :
    (∏ i ∈ s, f i).natAbs = ∏ i ∈ s, (f i).natAbs := by
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert i s hi ih =>
      simp [Finset.prod_insert, hi, Int.natAbs_mul, ih]

set_option linter.unusedVariables false in
/--
Vieta's formula gives a uniform coefficient bound for `G`.  The factor
`2^d` counts subsets, while `R^d` bounds every elementary product.
-/
theorem coeff_integerSplitProduct_natAbs_le
    {d R n : ℕ} (hd : 0 < d) (hR : 1 ≤ R)
    (γ : Fin d → ℤ) (hγ : ∀ i, |γ i| ≤ (R : ℤ)) :
    ((integerSplitProduct γ).coeff n).natAbs ≤
      2 ^ d * R ^ d := by
  classical
  by_cases hn : n ≤ d
  · have hnCard :
        n ≤ (Finset.univ : Finset (Fin d)).card := by
      simpa using hn
    have hVieta :
        (integerSplitProduct γ).coeff n =
          ∑ t ∈
              (Finset.univ : Finset (Fin d)).powersetCard (d - n),
            ∏ i ∈ t, γ i := by
      simpa [integerSplitProduct] using
        (Finset.prod_X_add_C_coeff
          (R := ℤ) (Finset.univ : Finset (Fin d)) γ hnCard)
    rw [hVieta]
    calc
      (∑ t ∈
            (Finset.univ : Finset (Fin d)).powersetCard (d - n),
          ∏ i ∈ t, γ i).natAbs
          ≤
        ∑ t ∈
            (Finset.univ : Finset (Fin d)).powersetCard (d - n),
          (∏ i ∈ t, γ i).natAbs :=
        Int.natAbs_sum_le _ _
      _ ≤
        ∑ _t ∈
            (Finset.univ : Finset (Fin d)).powersetCard (d - n),
          R ^ d := by
        apply Finset.sum_le_sum
        intro t ht
        have htCard : t.card = d - n :=
          (Finset.mem_powersetCard.mp ht).2
        calc
          (∏ i ∈ t, γ i).natAbs =
              ∏ i ∈ t, (γ i).natAbs := by
            exact int_natAbs_finset_prod t γ
          _ ≤ ∏ _i ∈ t, R := by
            apply Finset.prod_le_prod
            · intro i _
              exact Nat.zero_le _
            · intro i _
              have hiInt := hγ i
              rw [Int.abs_eq_natAbs] at hiInt
              exact_mod_cast hiInt
          _ = R ^ t.card := by simp
          _ = R ^ (d - n) := by rw [htCard]
          _ ≤ R ^ d :=
            Nat.pow_le_pow_right hR (Nat.sub_le d n)
      _ =
          Nat.choose d (d - n) * R ^ d := by
        simp
      _ ≤ 2 ^ d * R ^ d := by
        gcongr
        exact Nat.choose_le_two_pow d (d - n)
  · have hdegree : d < n := lt_of_not_ge hn
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
    · simp
    · simpa [natDegree_integerSplitProduct] using hdegree

/-- Height form of the uniform Vieta bound. -/
theorem integerPolynomialHeight_integerSplitProduct_le
    {d R : ℕ} (hd : 0 < d) (hR : 1 ≤ R)
    (γ : Fin d → ℤ) (hγ : ∀ i, |γ i| ≤ (R : ℤ)) :
    integerPolynomialHeight (integerSplitProduct γ) ≤
      2 ^ d * R ^ d := by
  unfold integerPolynomialHeight
  exact Finset.sup_le fun n _ ↦
    coeff_integerSplitProduct_natAbs_le hd hR γ hγ

private theorem reflect_monomial_of_le
    {R : Type*} [Semiring R] {N m : ℕ} (hm : m ≤ N) (a : R) :
    Polynomial.reflect N (monomial m a) =
      monomial (N - m) a := by
  rw [← C_mul_X_pow_eq_monomial,
    reflect_C_mul_X_pow, revAt_le hm,
    C_mul_X_pow_eq_monomial]

private theorem reflect_sum_monomial_of_le
    {R : Type*} [Semiring R] (N : ℕ) (s : Finset ℕ)
    (a : ℕ → R) (hs : ∀ m ∈ s, m ≤ N) :
    Polynomial.reflect N (∑ m ∈ s, monomial m (a m)) =
      ∑ m ∈ s, monomial (N - m) (a m) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert m s hm ih =>
      rw [Finset.sum_insert hm, Finset.sum_insert hm,
        Polynomial.reflect_add,
        reflect_monomial_of_le (hs m (by simp))]
      exact congrArg
        (fun p : R[X] ↦ monomial (N - m) (a m) + p)
        (ih fun n hn ↦ hs n (by simp [hn]))

/--
The ordinary (non-reversed) polynomial made from the first `k+1`
coefficients of the Runge product series.
-/
noncomputable def forwardRungeTruncation
    {k : ℕ} (γ : Fin (2 * k) → ℤ) : ℚ[X] :=
  ∑ m ∈ Finset.range (k + 1),
    monomial m (RungeCoefficients.rungeCoefficient γ m)

/-- The forward polynomial is exactly the formal-power-series truncation. -/
theorem forwardRungeTruncation_eq_trunc
    {k : ℕ} (γ : Fin (2 * k) → ℤ) :
    forwardRungeTruncation γ =
      PowerSeries.trunc (k + 1)
        (RungePowerSeries.rungeProductSeries γ) := by
  classical
  rw [forwardRungeTruncation, PowerSeries.trunc_apply,
    Nat.Ico_zero_eq_range]
  apply Finset.sum_congr rfl
  intro m _
  rw [RungePowerSeries.coeff_rungeProductSeries]

/-- The forward truncation has degree at most `k`. -/
theorem natDegree_forwardRungeTruncation_le
    {k : ℕ} (γ : Fin (2 * k) → ℤ) :
    (forwardRungeTruncation γ).natDegree ≤ k := by
  rw [forwardRungeTruncation_eq_trunc]
  exact Nat.lt_succ_iff.mp
    (PowerSeries.natDegree_trunc_lt
      (RungePowerSeries.rungeProductSeries γ) k)

/--
Reflecting the ordinary truncation in degree `k` gives the paper's
polynomial `P(T) = ∑_{m≤k} c_m T^(k-m)`.
-/
theorem reflect_forwardRungeTruncation
    {k : ℕ} (γ : Fin (2 * k) → ℤ) :
    Polynomial.reflect k (forwardRungeTruncation γ) =
      RungeTruncation.rungeTruncation γ := by
  classical
  rw [forwardRungeTruncation, RungeTruncation.rungeTruncation]
  apply reflect_sum_monomial_of_le
  intro m hm
  simpa only [Finset.mem_range, Nat.lt_succ_iff] using hm

/--
The polynomial in the reciprocal variable,
`H(X) = ∏ ν, (1 + γν X)`.
-/
noncomputable def reciprocalSplitProduct
    {d : ℕ} (γ : Fin d → ℤ) : ℚ[X] :=
  ∏ ν, (1 + C (γ ν : ℚ) * X)

private theorem natDegree_one_add_C_mul_X_le
    (a : ℚ) :
    (1 + C a * X : ℚ[X]).natDegree ≤ 1 := by
  rw [← C_1, natDegree_C_add]
  simpa using natDegree_C_mul_le a (X : ℚ[X])

private theorem natDegree_reciprocalProductOn_le
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι → ℚ) :
    (∏ i ∈ s, (1 + C (a i) * X : ℚ[X])).natDegree ≤ s.card := by
  calc
    (∏ i ∈ s, (1 + C (a i) * X : ℚ[X])).natDegree
        ≤ ∑ i ∈ s, (1 + C (a i) * X : ℚ[X]).natDegree :=
      natDegree_prod_le s _
    _ ≤ ∑ _i ∈ s, 1 := by
      exact Finset.sum_le_sum fun i _ ↦
        natDegree_one_add_C_mul_X_le (a i)
    _ = s.card := by simp

private theorem reflect_one_add_C_mul_X
    (a : ℚ) :
    Polynomial.reflect 1 (1 + C a * X : ℚ[X]) =
      X + C a := by
  calc
    Polynomial.reflect 1 (1 + C a * X : ℚ[X]) =
        Polynomial.reflect 1 (1 : ℚ[X]) +
          Polynomial.reflect 1 (C a * X) := by
      rw [Polynomial.reflect_add]
    _ = X + C a := by
      rw [Polynomial.reflect_one,
        show C a * X = C a * X ^ 1 by simp,
        reflect_C_mul_X_pow, revAt_le (by omega : 1 ≤ 1)]
      simp

private theorem reflect_reciprocalProductOn
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι → ℚ) :
    Polynomial.reflect s.card
        (∏ i ∈ s, (1 + C (a i) * X : ℚ[X])) =
      ∏ i ∈ s, (X + C (a i) : ℚ[X]) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert i s hi ih =>
      rw [Finset.card_insert_of_notMem hi,
        Finset.prod_insert hi, Finset.prod_insert hi]
      rw [show s.card + 1 = 1 + s.card by omega]
      rw [Polynomial.reflect_mul
        (1 + C (a i) * X : ℚ[X])
        (∏ j ∈ s, (1 + C (a j) * X : ℚ[X]))
        (natDegree_one_add_C_mul_X_le (a i))
        (natDegree_reciprocalProductOn_le s a)]
      rw [reflect_one_add_C_mul_X, ih]

private theorem coe_finset_prod
    {R ι : Type*} [CommSemiring R] [DecidableEq ι]
    (s : Finset ι) (f : ι → R[X]) :
    ((∏ i ∈ s, f i : R[X]) : PowerSeries R) =
      ∏ i ∈ s, (f i : PowerSeries R) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert i s hi ih =>
      simp [Finset.prod_insert, hi, ih]

/--
Reflecting `H` in degree `d` gives the rational image of
`G(T) = ∏ (T + γν)`.
-/
theorem reflect_reciprocalSplitProduct
    {d : ℕ} (γ : Fin d → ℤ) :
    Polynomial.reflect d (reciprocalSplitProduct γ) =
      (integerSplitProduct γ).map (Int.castRingHom ℚ) := by
  classical
  rw [reciprocalSplitProduct, integerSplitProduct,
    Polynomial.map_prod]
  simpa using
    (reflect_reciprocalProductOn
      (Finset.univ : Finset (Fin d))
      (fun ν ↦ (γ ν : ℚ)))

/--
As a formal power series, `H` is the square of the Runge product
series.
-/
theorem coe_reciprocalSplitProduct_eq_rungeProductSeries_sq
    {d : ℕ} (γ : Fin d → ℤ) :
    (reciprocalSplitProduct γ : PowerSeries ℚ) =
      (RungePowerSeries.rungeProductSeries γ) ^ 2 := by
  rw [RungePowerSeries.rungeProductSeries_sq]
  rw [reciprocalSplitProduct,
    coe_finset_prod (Finset.univ : Finset (Fin d))]
  apply Finset.prod_congr rfl
  intro i _
  simp only [Polynomial.coe_add, Polynomial.coe_one,
    Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_X]

/--
For `n ≤ k`, the coefficient of `T^(2k-n)` in `P(T)^2` is the
coefficient of `X^n` in the square of the full Runge product series.
This is the precise finite truncation statement behind the cancellation
of the high coefficients of `Q`.
-/
theorem coeff_rungeTruncation_sq_high
    {k n : ℕ} (γ : Fin (2 * k) → ℤ) (hn : n ≤ k) :
    ((RungeTruncation.rungeTruncation γ) ^ 2).coeff (2 * k - n) =
      PowerSeries.coeff ℚ n
        ((RungePowerSeries.rungeProductSeries γ) ^ 2) := by
  let A : ℚ[X] := forwardRungeTruncation γ
  have hAdegree : A.natDegree ≤ k := by
    exact natDegree_forwardRungeTruncation_le γ
  have hreflectProduct :
      Polynomial.reflect (k + k) (A * A) =
        Polynomial.reflect k A * Polynomial.reflect k A :=
    Polynomial.reflect_mul A A hAdegree hAdegree
  have hreflectA :
      Polynomial.reflect k A =
        RungeTruncation.rungeTruncation γ := by
    dsimp [A]
    exact reflect_forwardRungeTruncation γ
  have hreverse :
      (RungeTruncation.rungeTruncation γ) ^ 2 =
        Polynomial.reflect (2 * k) (A ^ 2) := by
    calc
      (RungeTruncation.rungeTruncation γ) ^ 2 =
          Polynomial.reflect k A * Polynomial.reflect k A := by
        rw [pow_two, hreflectA]
      _ = Polynomial.reflect (k + k) (A * A) :=
        hreflectProduct.symm
      _ = Polynomial.reflect (2 * k) (A ^ 2) := by
        rw [two_mul, pow_two]
  have hnTwo : n ≤ 2 * k := by omega
  have htrunc :=
    PowerSeries.coeff_mul_eq_coeff_trunc_mul_trunc
      (R := ℚ)
      (RungePowerSeries.rungeProductSeries γ)
      (RungePowerSeries.rungeProductSeries γ)
      (by omega : n < k + 1)
  have hforwardCoefficient :
      (A ^ 2).coeff n =
        PowerSeries.coeff ℚ n
          ((RungePowerSeries.rungeProductSeries γ) ^ 2) := by
    calc
      (A ^ 2).coeff n =
          PowerSeries.coeff ℚ n ((A ^ 2 : ℚ[X]) : PowerSeries ℚ) := by
        rw [Polynomial.coeff_coe]
      _ =
          PowerSeries.coeff ℚ n
            ((A : PowerSeries ℚ) ^ 2) := by
        simp only [pow_two, Polynomial.coe_mul]
      _ =
          PowerSeries.coeff ℚ n
            ((RungePowerSeries.rungeProductSeries γ) ^ 2) := by
        simpa [A, forwardRungeTruncation_eq_trunc, pow_two] using
          htrunc.symm
  rw [hreverse, Polynomial.coeff_reflect,
    revAt_le (Nat.sub_le (2 * k) n),
    Nat.sub_sub_self hnTwo]
  exact hforwardCoefficient

/--
For `n ≤ 2k`, the coefficient of `T^(2k-n)` in `G(T)` is the
coefficient of `X^n` in the square of the Runge product series.
-/
theorem coeff_map_integerSplitProduct_high
    {k n : ℕ} (γ : Fin (2 * k) → ℤ) (hn : n ≤ 2 * k) :
    ((integerSplitProduct γ).map (Int.castRingHom ℚ)).coeff
        (2 * k - n) =
      PowerSeries.coeff ℚ n
        ((RungePowerSeries.rungeProductSeries γ) ^ 2) := by
  calc
    ((integerSplitProduct γ).map (Int.castRingHom ℚ)).coeff
          (2 * k - n) =
        (Polynomial.reflect (2 * k)
          (reciprocalSplitProduct γ)).coeff (2 * k - n) := by
      rw [reflect_reciprocalSplitProduct]
    _ = (reciprocalSplitProduct γ).coeff n := by
      rw [Polynomial.coeff_reflect,
        revAt_le (Nat.sub_le (2 * k) n),
        Nat.sub_sub_self hn]
    _ =
        PowerSeries.coeff ℚ n
          (reciprocalSplitProduct γ : PowerSeries ℚ) := by
      rw [Polynomial.coeff_coe]
    _ =
        PowerSeries.coeff ℚ n
          ((RungePowerSeries.rungeProductSeries γ) ^ 2) := by
      rw [coe_reciprocalSplitProduct_eq_rungeProductSeries_sq]

/-- The top `k+1` coefficients of rational `G` and `P^2` agree. -/
theorem coeff_map_integerSplitProduct_eq_rungeTruncation_sq
    {k n : ℕ} (γ : Fin (2 * k) → ℤ) (hn : n ≤ k) :
    ((integerSplitProduct γ).map (Int.castRingHom ℚ)).coeff
        (2 * k - n) =
      ((RungeTruncation.rungeTruncation γ) ^ 2).coeff
        (2 * k - n) := by
  rw [coeff_map_integerSplitProduct_high γ (by omega),
    coeff_rungeTruncation_sq_high γ hn]

/--
Distinct integral shifts give distinct rational roots `-γ ν`, so `G` is
not a square over `ℚ`.
-/
theorem map_integerSplitProduct_not_isSquare
    {d : ℕ} (hd : 0 < d) (γ : Fin d → ℤ)
    (hγ : Function.Injective γ) :
    ¬ ∃ p : ℚ[X],
      (integerSplitProduct γ).map (Int.castRingHom ℚ) = p ^ 2 := by
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  have hroot :
      Function.Injective (fun ν : Fin d ↦ -(γ ν : ℚ)) := by
    intro i j hij
    apply hγ
    have hcast : (γ i : ℚ) = (γ j : ℚ) := neg_injective hij
    exact_mod_cast hcast
  rw [map_integerSplitProduct]
  exact RungeSplitProduct.splitProduct_not_isSquare _ hroot

/-- The dyadic scale `2^d`, with `d = 2k`. -/
def rungeScale (k : ℕ) : ℤ :=
  (2 : ℤ) ^ (2 * k)

/--
The integral auxiliary polynomial
`Q = 2^(2d) G - (2^d P)^2`, where `d = 2k`.
-/
noncomputable def rungeQ
    {k : ℕ} (γ : Fin (2 * k) → ℤ) : ℤ[X] :=
  C (rungeScale k ^ 2) * integerSplitProduct γ -
    (RungeTruncation.integralRungeTruncation γ) ^ 2

/-- The definition is exactly the paper's `2^(2d)` normalization. -/
theorem rungeScale_sq
    (k : ℕ) :
    rungeScale k ^ 2 = (2 : ℤ) ^ (2 * (2 * k)) := by
  rw [rungeScale, ← pow_mul]
  congr 1
  omega

/-- The integral truncation has degree at most `k`. -/
theorem natDegree_integralRungeTruncation_le
    {k : ℕ} (γ : Fin (2 * k) → ℤ) :
    (RungeTruncation.integralRungeTruncation γ).natDegree ≤ k := by
  classical
  rw [RungeTruncation.integralRungeTruncation]
  apply natDegree_sum_le_of_forall_le
  intro m hm
  exact (natDegree_monomial_le _).trans (Nat.sub_le k m)

/--
Before exploiting cancellation of the top `k+1` coefficients, the formal
degree rules give `deg Q ≤ 2k`.
-/
theorem natDegree_rungeQ_le_two_mul
    {k : ℕ} (γ : Fin (2 * k) → ℤ) :
    (rungeQ γ).natDegree ≤ 2 * k := by
  unfold rungeQ
  apply (natDegree_sub_le _ _).trans
  apply max_le
  · calc
      (C (rungeScale k ^ 2) * integerSplitProduct γ).natDegree
          ≤ (integerSplitProduct γ).natDegree :=
        natDegree_C_mul_le _ _
      _ = 2 * k := natDegree_integerSplitProduct γ
  · calc
      ((RungeTruncation.integralRungeTruncation γ) ^ 2).natDegree
          ≤ 2 *
              (RungeTruncation.integralRungeTruncation γ).natDegree :=
        natDegree_pow_le
      _ ≤ 2 * k :=
        Nat.mul_le_mul_left 2 (natDegree_integralRungeTruncation_le γ)

/--
Mapping the integral truncation to `ℚ[T]` is multiplication by the
rational image of `rungeScale`.
-/
theorem map_integralRungeTruncation_eq_scale_mul
    {k : ℕ} (γ : Fin (2 * k) → ℤ) :
    (RungeTruncation.integralRungeTruncation γ).map
        (Int.castRingHom ℚ) =
      C (rungeScale k : ℚ) *
        RungeTruncation.rungeTruncation γ := by
  simpa [rungeScale] using
    RungeTruncation.map_integralRungeTruncation γ

/--
The rational image of `Q`, in a form that displays the common square
factor `2^(2d)`.
-/
theorem map_rungeQ
    {k : ℕ} (γ : Fin (2 * k) → ℤ) :
    (rungeQ γ).map (Int.castRingHom ℚ) =
      C ((rungeScale k : ℚ) ^ 2) *
          (integerSplitProduct γ).map (Int.castRingHom ℚ) -
        (C (rungeScale k : ℚ) *
          RungeTruncation.rungeTruncation γ) ^ 2 := by
  simp only [rungeQ, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.map_pow,
    map_integralRungeTruncation_eq_scale_mul]
  norm_cast

/--
The coefficients of `Q` in degrees `2k, 2k-1, ..., k` vanish.
This is the exact high-coefficient cancellation asserted in the equality
case of Lemma 3.1.
-/
theorem coeff_rungeQ_high_eq_zero
    {k n : ℕ} (γ : Fin (2 * k) → ℤ) (hn : n ≤ k) :
    (rungeQ γ).coeff (2 * k - n) = 0 := by
  have hcoefficient :=
    coeff_map_integerSplitProduct_eq_rungeTruncation_sq γ hn
  have hsquare :
      (C (rungeScale k : ℚ) *
          RungeTruncation.rungeTruncation γ) ^ 2 =
        C ((rungeScale k : ℚ) ^ 2) *
          (RungeTruncation.rungeTruncation γ) ^ 2 := by
    rw [Polynomial.C_pow]
    ring
  have hcast :
      (((rungeQ γ).coeff (2 * k - n) : ℤ) : ℚ) = 0 := by
    calc
      (((rungeQ γ).coeff (2 * k - n) : ℤ) : ℚ) =
          ((rungeQ γ).map (Int.castRingHom ℚ)).coeff
            (2 * k - n) := by
        simp
      _ =
          (C ((rungeScale k : ℚ) ^ 2) *
              (integerSplitProduct γ).map (Int.castRingHom ℚ) -
            (C (rungeScale k : ℚ) *
              RungeTruncation.rungeTruncation γ) ^ 2).coeff
              (2 * k - n) := by
        rw [map_rungeQ]
      _ =
          (rungeScale k : ℚ) ^ 2 *
              ((integerSplitProduct γ).map
                (Int.castRingHom ℚ)).coeff (2 * k - n) -
            (rungeScale k : ℚ) ^ 2 *
              ((RungeTruncation.rungeTruncation γ) ^ 2).coeff
                (2 * k - n) := by
        rw [hsquare, coeff_sub, coeff_C_mul, coeff_C_mul]
      _ = 0 := by
        rw [hcoefficient]
        ring
  exact_mod_cast hcast

/--
For `k > 0`, cancellation of the top `k+1` coefficients improves the
coarse degree bound `2k` to the paper's `deg Q ≤ k-1`.
-/
theorem natDegree_rungeQ_le_pred
    {k : ℕ} (hk : 0 < k) (γ : Fin (2 * k) → ℤ) :
    (rungeQ γ).natDegree ≤ k - 1 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  by_cases hNtop : N ≤ 2 * k
  · let n := 2 * k - N
    have hn : n ≤ k := by
      dsimp [n]
      omega
    have hindex : 2 * k - n = N := by
      dsimp [n]
      exact Nat.sub_sub_self hNtop
    rw [← hindex]
    exact coeff_rungeQ_high_eq_zero γ hn
  · exact coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt
        (natDegree_rungeQ_le_two_mul γ)
        (lt_of_not_ge hNtop))

/--
The equality polynomial `Q` is nonzero when the shifts are distinct and
`k > 0`.  If it vanished, cancellation of the nonzero scalar `2^(2d)`
would make `G` the square of the rational Runge truncation.
-/
theorem rungeQ_ne_zero
    {k : ℕ} (hk : 0 < k) (γ : Fin (2 * k) → ℤ)
    (hγ : Function.Injective γ) :
    rungeQ γ ≠ 0 := by
  intro hQ
  have hmapQ :
      (rungeQ γ).map (Int.castRingHom ℚ) = 0 := by
    simp [hQ]
  rw [map_rungeQ] at hmapQ
  have hscale : (rungeScale k : ℚ) ≠ 0 := by
    simp [rungeScale]
  have hscaleC : C (rungeScale k : ℚ) ^ 2 ≠ (0 : ℚ[X]) := by
    exact pow_ne_zero 2 (C_ne_zero.mpr hscale)
  have hfactor :
      C (rungeScale k : ℚ) ^ 2 *
          (integerSplitProduct γ).map (Int.castRingHom ℚ) =
        C (rungeScale k : ℚ) ^ 2 *
          (RungeTruncation.rungeTruncation γ) ^ 2 := by
    calc
      C (rungeScale k : ℚ) ^ 2 *
            (integerSplitProduct γ).map (Int.castRingHom ℚ) =
          C ((rungeScale k : ℚ) ^ 2) *
            (integerSplitProduct γ).map (Int.castRingHom ℚ) := by
              rw [C_pow]
      _ =
          (C (rungeScale k : ℚ) *
            RungeTruncation.rungeTruncation γ) ^ 2 :=
        sub_eq_zero.mp hmapQ
      _ =
          C (rungeScale k : ℚ) ^ 2 *
            (RungeTruncation.rungeTruncation γ) ^ 2 := by
        ring
  have hsquare :
      (integerSplitProduct γ).map (Int.castRingHom ℚ) =
        (RungeTruncation.rungeTruncation γ) ^ 2 :=
    mul_left_cancel₀ hscaleC hfactor
  exact
    (map_integerSplitProduct_not_isSquare (by omega) γ hγ)
      ⟨RungeTruncation.rungeTruncation γ, hsquare⟩

/-- Coefficient formula for the integral auxiliary polynomial. -/
theorem coeff_rungeQ
    {k n : ℕ} (γ : Fin (2 * k) → ℤ) :
    (rungeQ γ).coeff n =
      rungeScale k ^ 2 * (integerSplitProduct γ).coeff n -
        ((RungeTruncation.integralRungeTruncation γ) ^ 2).coeff n := by
  simp only [rungeQ, coeff_sub, coeff_C_mul]

/--
Every coefficient of `Q` is bounded by the sum of the corresponding
height bounds for its two defining terms.
-/
theorem coeff_rungeQ_natAbs_le
    {k n : ℕ} (γ : Fin (2 * k) → ℤ) :
    ((rungeQ γ).coeff n).natAbs ≤
      (rungeScale k ^ 2).natAbs *
          integerPolynomialHeight (integerSplitProduct γ) +
        integerPolynomialHeight
          ((RungeTruncation.integralRungeTruncation γ) ^ 2) := by
  rw [coeff_rungeQ]
  calc
    (rungeScale k ^ 2 * (integerSplitProduct γ).coeff n -
          ((RungeTruncation.integralRungeTruncation γ) ^ 2).coeff n).natAbs
        ≤
      (rungeScale k ^ 2 * (integerSplitProduct γ).coeff n).natAbs +
        (((RungeTruncation.integralRungeTruncation γ) ^ 2).coeff n).natAbs :=
      Int.natAbs_sub_le _ _
    _ =
      (rungeScale k ^ 2).natAbs *
          ((integerSplitProduct γ).coeff n).natAbs +
        (((RungeTruncation.integralRungeTruncation γ) ^ 2).coeff n).natAbs := by
      rw [Int.natAbs_mul]
    _ ≤
      (rungeScale k ^ 2).natAbs *
          integerPolynomialHeight (integerSplitProduct γ) +
        integerPolynomialHeight
          ((RungeTruncation.integralRungeTruncation γ) ^ 2) := by
      gcongr
      · exact coeff_natAbs_le_integerPolynomialHeight _ _
      · exact coeff_natAbs_le_integerPolynomialHeight _ _

/--
Height reduction for `Q`: it remains to bound the heights of the split
product and of the square of the integral truncation.
-/
theorem integerPolynomialHeight_rungeQ_le
    {k : ℕ} (γ : Fin (2 * k) → ℤ) :
    integerPolynomialHeight (rungeQ γ) ≤
      (rungeScale k ^ 2).natAbs *
          integerPolynomialHeight (integerSplitProduct γ) +
        integerPolynomialHeight
          ((RungeTruncation.integralRungeTruncation γ) ^ 2) := by
  unfold integerPolynomialHeight
  exact Finset.sup_le fun n _ ↦ coeff_rungeQ_natAbs_le γ

/--
Using the convolution estimate for a polynomial square, the second term
in the height reduction is controlled solely by the height of the
integral Runge truncation.
-/
theorem integerPolynomialHeight_rungeQ_le_of_truncationHeight
    {k : ℕ} (γ : Fin (2 * k) → ℤ) :
    integerPolynomialHeight (rungeQ γ) ≤
      (rungeScale k ^ 2).natAbs *
          integerPolynomialHeight (integerSplitProduct γ) +
        (2 * k + 1) *
          integerPolynomialHeight
            (RungeTruncation.integralRungeTruncation γ) ^ 2 := by
  calc
    integerPolynomialHeight (rungeQ γ) ≤
        (rungeScale k ^ 2).natAbs *
            integerPolynomialHeight (integerSplitProduct γ) +
          integerPolynomialHeight
            ((RungeTruncation.integralRungeTruncation γ) ^ 2) :=
      integerPolynomialHeight_rungeQ_le γ
    _ ≤
        (rungeScale k ^ 2).natAbs *
            integerPolynomialHeight (integerSplitProduct γ) +
          (2 *
              (RungeTruncation.integralRungeTruncation γ).natDegree +
              1) *
            integerPolynomialHeight
              (RungeTruncation.integralRungeTruncation γ) ^ 2 := by
      gcongr
      exact integerPolynomialHeight_sq_le
        (RungeTruncation.integralRungeTruncation γ)
    _ ≤
        (rungeScale k ^ 2).natAbs *
            integerPolynomialHeight (integerSplitProduct γ) +
          (2 * k + 1) *
            integerPolynomialHeight
              (RungeTruncation.integralRungeTruncation γ) ^ 2 := by
      gcongr
      exact natDegree_integralRungeTruncation_le γ

/--
Fully explicit height bound obtained from Vieta for `G` and the
coefficient estimate (3.2) for the integral truncation.  Its deliberately
coarse constants are of the `(C k R)^(O(k))` form needed by the final
integer-root argument.
-/
theorem integerPolynomialHeight_rungeQ_explicit
    {k R : ℕ} (hk : 1 ≤ k) (hR : 1 ≤ R)
    (γ : Fin (2 * k) → ℤ)
    (hγ : ∀ i, |γ i| ≤ (R : ℤ)) :
    integerPolynomialHeight (rungeQ γ) ≤
      (rungeScale k ^ 2).natAbs *
          (2 ^ (2 * k) * R ^ (2 * k)) +
        (2 * k + 1) *
          ((k + 1) * (16 * R) ^ (2 * k)) ^ 2 := by
  calc
    integerPolynomialHeight (rungeQ γ) ≤
        (rungeScale k ^ 2).natAbs *
            integerPolynomialHeight (integerSplitProduct γ) +
          (2 * k + 1) *
            integerPolynomialHeight
              (RungeTruncation.integralRungeTruncation γ) ^ 2 :=
      integerPolynomialHeight_rungeQ_le_of_truncationHeight γ
    _ ≤
        (rungeScale k ^ 2).natAbs *
            (2 ^ (2 * k) * R ^ (2 * k)) +
          (2 * k + 1) *
            ((k + 1) * (16 * R) ^ (2 * k)) ^ 2 := by
      gcongr
      · exact integerPolynomialHeight_integerSplitProduct_le
          (by omega) hR γ hγ
      · exact
          _root_.PaperC.RungeTruncationBounds.integerPolynomialHeight_integralRungeTruncation_le
            hk hR γ hγ

/--
Once a value `u` is known to annihilate `Q`, nonvanishing immediately
feeds the integral Cauchy bound from `IntegerPolynomialRootBound`.
-/
theorem rungeEquality_root_natAbs_le_height
    {k : ℕ} (hk : 0 < k) (γ : Fin (2 * k) → ℤ)
    (hγ : Function.Injective γ) {u : ℤ}
    (hu : (rungeQ γ).IsRoot u) :
    u.natAbs ≤ integerPolynomialHeight (rungeQ γ) :=
  integerRoot_natAbs_le_height (rungeQ_ne_zero hk γ hγ) hu

/--
If `G(u) = a^2` and the integral truncation takes the compatible value
`2^d a`, then `u` is an integral root of `Q`.
-/
theorem rungeQ_isRoot_of_square_and_truncation
    {k : ℕ} (γ : Fin (2 * k) → ℤ) (u a : ℤ)
    (hG : (integerSplitProduct γ).eval u = a ^ 2)
    (hP :
      (RungeTruncation.integralRungeTruncation γ).eval u =
        rungeScale k * a) :
    (rungeQ γ).IsRoot u := by
  change (rungeQ γ).eval u = 0
  rw [rungeQ, eval_sub, eval_mul, eval_C, eval_pow, hG, hP]
  ring

/--
Complete explicit root bound for the equality branch.  This combines
nonvanishing, Vieta, the truncation coefficient estimate, and the
integral Cauchy bound without any unproved algebraic step.
-/
theorem rungeEquality_root_natAbs_le_explicit
    {k R : ℕ} (hk : 1 ≤ k) (hR : 1 ≤ R)
    (γ : Fin (2 * k) → ℤ)
    (hγBound : ∀ i, |γ i| ≤ (R : ℤ))
    (hγInjective : Function.Injective γ)
    (u a : ℤ)
    (hG : (integerSplitProduct γ).eval u = a ^ 2)
    (hP :
      (RungeTruncation.integralRungeTruncation γ).eval u =
        rungeScale k * a) :
    u.natAbs ≤
      (rungeScale k ^ 2).natAbs *
          (2 ^ (2 * k) * R ^ (2 * k)) +
        (2 * k + 1) *
          ((k + 1) * (16 * R) ^ (2 * k)) ^ 2 := by
  exact
    (rungeEquality_root_natAbs_le_height
      (by omega) γ hγInjective
      (rungeQ_isRoot_of_square_and_truncation γ u a hG hP)).trans
      (integerPolynomialHeight_rungeQ_explicit
        hk hR γ hγBound)

end RungeQPolynomial
end PaperC
