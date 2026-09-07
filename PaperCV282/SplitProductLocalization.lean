import PaperC.Diophantine.ComponentNormalization
import PaperC.Affine.RelationalPrimeAssignment
import PaperCV282.DivisorSubpolynomial

/-!
# Squareclass localization for split products

Every odd valuation of one factor either belongs to the right-hand
coefficient or occurs in a second factor. A product of nonzero shift
differences therefore contains all the possible squareclasses. The
ordered difference product is used only as a convenient positive
integer of bounded polynomial height.
-/

namespace PaperC.V282.SplitProductLocalization

open Affine ComponentNormalization LargeOddKernel DefectivePredicate
open scoped BigOperators

noncomputable section

/-- Ordered differences, with diagonal factors replaced by one. -/
def shiftDifferenceProduct {d : ℕ} (h : Fin d → ℤ) : ℕ :=
  ∏ i : Fin d, ∏ j : Fin d, if i = j then 1 else (h i - h j).natAbs

/-- Distinct shifts make the difference product positive. -/
theorem shiftDifferenceProduct_pos {d : ℕ} {h : Fin d → ℤ}
    (hh : Function.Injective h) : 0 < shiftDifferenceProduct h := by
  unfold shiftDifferenceProduct
  apply Finset.prod_pos
  intro i hi
  apply Finset.prod_pos
  intro j hj
  split_ifs with hij
  · norm_num
  · exact Int.natAbs_pos.mpr (sub_ne_zero.mpr (fun hEq => hij (hh hEq)))

/-- Every off-diagonal difference divides the common difference product. -/
theorem difference_dvd_shiftDifferenceProduct {d : ℕ} (h : Fin d → ℤ)
    {i j : Fin d} (hij : i ≠ j) : (h i - h j).natAbs ∣ shiftDifferenceProduct h := by
  classical
  unfold shiftDifferenceProduct
  apply dvd_trans _ (Finset.dvd_prod_of_mem (fun i : Fin d =>
    ∏ j : Fin d, if i = j then 1 else (h i - h j).natAbs) (Finset.mem_univ i))
  simpa only [if_neg hij] using Finset.dvd_prod_of_mem
    (fun j : Fin d => if i = j then 1 else (h i - h j).natAbs) (Finset.mem_univ j)

/-- Generic squareclass localization, phrased through a common divisor bound for pairs of factors. -/
theorem squarefreeKernel_factor_dvd_of_product_square
    {ι : Type*} [Fintype ι] (f : ι → ℕ) {e r D : ℕ}
    (hf : ∀ i, 0 < f i) (he : 0 < e) (hr : 0 < r) (hD : 0 < D)
    (heq : ∏ i, f i = e * r ^ 2)
    (hcommon : ∀ p : ℕ, p.Prime → ∀ i j : ι, i ≠ j → p ∣ f i → p ∣ f j → p ∣ D)
    (i : ι) : squarefreeKernel (f i) ∣ e * D := by
  classical
  have htarget : e * D ≠ 0 := (Nat.mul_pos he hD).ne'
  rw [← Nat.prod_primeFactors_of_squarefree (squarefreeKernel_squarefree (f i))]
  apply (Nat.prod_primeFactors_dvd_iff htarget).mpr
  intro p hp
  have hsupport : (squarefreeKernel (f i)).primeFactors = oddPrimeSupport (f i) := by
    exact Nat.primeFactors_prod (fun p hp => prime_of_mem_oddPrimeSupport' hp)
  have hodd : p ∈ oddPrimeSupport (f i) := hsupport ▸ hp
  have hpPrime := prime_of_mem_oddPrimeSupport' hodd
  apply Nat.mem_primeFactors.mpr
  refine ⟨hpPrime, ?_, htarget⟩
  by_contra hnot
  have hpe : ¬ p ∣ e := fun h => hnot (dvd_mul_of_dvd_left h D)
  have hpD : ¬ p ∣ D := fun h => hnot (dvd_mul_of_dvd_right h e)
  have hpi : parityVec (f i) p ≠ 0 := mem_oddPrimeSupport_iff_parityVec_ne_zero.mp hodd
  have hpfi : p ∣ f i := by
    by_contra hnot
    apply hpi
    rw [parityVec_apply, Nat.factorization_eq_zero_of_not_dvd hnot]
    rfl
  have hother : ∀ j : ι, j ≠ i → parityVec (f j) p = 0 := by
    intro j hji
    have hpfj : ¬ p ∣ f j := fun h => hpD (hcommon p hpPrime i j hji.symm hpfi h)
    rw [parityVec_apply, Nat.factorization_eq_zero_of_not_dvd hpfj]
    rfl
  have hsum : parityVec (∏ j, f j) p = parityVec (f i) p := by
    rw [parityVec_prod _ f (fun j _ => (hf j).ne')]
    simp only [Finsupp.finsetSum_apply]
    exact Finset.sum_eq_single i (fun j _ hji => hother j hji) (by simp)
  have hzero : parityVec (∏ j, f j) p = 0 := by
    rw [heq, parityVec_mul he.ne' (pow_ne_zero 2 hr.ne'), parityVec_pow_two, add_zero,
      parityVec_apply, Nat.factorization_eq_zero_of_not_dvd hpe]
    rfl
  exact hpi (hsum.symm.trans hzero)

/-- Polynomial height of the common difference product, uniformly over every shift tuple. -/
theorem shiftDifferenceProduct_le_polynomial
    {M K d : ℕ} (hM : 2 ≤ M) (h : Fin d → ℤ)
    (hh : ∀ i, (h i).natAbs ≤ M ^ K) :
    shiftDifferenceProduct h ≤ M ^ ((K + 1) * (d * d)) := by
  classical
  have hbase : 1 ≤ M ^ (K + 1) := Nat.one_le_pow _ _ (by omega)
  have hfactor : ∀ i j : Fin d,
      (if i = j then 1 else (h i - h j).natAbs) ≤ M ^ (K + 1) := by
    intro i j
    split_ifs
    · exact hbase
    · calc
        _ ≤ (h i).natAbs + (h j).natAbs := Int.natAbs_sub_le _ _
        _ ≤ M ^ K + M ^ K := Nat.add_le_add (hh i) (hh j)
        _ ≤ M * M ^ K := by simpa only [two_mul] using Nat.mul_le_mul_right (M ^ K) hM
        _ = M ^ (K + 1) := (pow_succ' _ _).symm
  calc
    shiftDifferenceProduct h ≤ ∏ i : Fin d, ∏ j : Fin d, M ^ (K + 1) := by
      exact Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun i _ =>
        Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun j _ => hfactor i j))
    _ = M ^ ((K + 1) * (d * d)) := by simp [← pow_mul, Nat.mul_assoc]

/-- Every shift factor has its canonical squareclass in one fixed divisor set. -/
theorem squarefreeKernel_shift_dvd
    {d : ℕ} {h : Fin d → ℤ} {X Y : ℤ} {e : ℕ}
    (hh : Function.Injective h) (he : 0 < e)
    (hpositive : ∀ i, 0 < X + h i)
    (heq : ∏ i, (X + h i) = (e : ℤ) * Y ^ 2) (i : Fin d) :
    squarefreeKernel (X + h i).toNat ∣ e * shiftDifferenceProduct h := by
  have hf : ∀ j : Fin d, 0 < (X + h j).toNat := by intro j; have := hpositive j; omega
  have hcast : ∀ j : Fin d, ((X + h j).toNat : ℤ) = X + h j :=
    fun j => Int.toNat_of_nonneg (hpositive j).le
  have hprod : ∏ j, (X + h j).toNat = e * Y.natAbs ^ 2 := by
    apply Int.natCast_inj.mp
    push_cast
    simp only [hcast, sq_abs]
    exact heq
  have hY : 0 < Y.natAbs := by
    have hprodpos : 0 < ∏ j, (X + h j).toNat := Finset.prod_pos (fun j _ => hf j)
    rw [hprod] at hprodpos
    by_contra hn
    have hz : Y.natAbs = 0 := by omega
    rw [hz] at hprodpos
    norm_num at hprodpos
  apply squarefreeKernel_factor_dvd_of_product_square _ hf he hY
    (shiftDifferenceProduct_pos hh) hprod _ i
  intro p hp j k hjk hpj hpk
  have hpj' : (p : ℤ) ∣ X + h j := by exact_mod_cast (hcast j ▸ (Int.natCast_dvd_natCast.mpr hpj))
  have hpk' : (p : ℤ) ∣ X + h k := by exact_mod_cast (hcast k ▸ (Int.natCast_dvd_natCast.mpr hpk))
  have hdiff : (p : ℤ) ∣ h j - h k := by
    have hid : X + h j - (X + h k) = h j - h k := by ring
    rw [← hid]
    exact dvd_sub hpj' hpk'
  exact (Int.natCast_dvd.mp hdiff).trans (difference_dvd_shiftDifferenceProduct h hjk)

/-- The entire common divisor set is subpolynomial, uniformly in the shift tuple and coefficient. -/
theorem card_squareclass_divisors_le_rpow_eventually
    (K d : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ e : ℕ, ∀ h : Fin d → ℤ,
      e ≤ M ^ K → (∀ i, (h i).natAbs ≤ M ^ K) →
      ((e * shiftDifferenceProduct h).divisors.card : ℝ) ≤ (M : ℝ) ^ epsilon := by
  obtain ⟨Mdiv, hdiv⟩ := DivisorSubpolynomial.card_divisors_le_rpow_eventually
    (K + (K + 1) * (d * d)) epsilon hepsilon
  refine ⟨max Mdiv 2, ?_⟩
  intro M hM e h he hh
  apply hdiv M ((le_max_left _ _).trans hM)
  calc
    e * shiftDifferenceProduct h ≤ M ^ K * M ^ ((K + 1) * (d * d)) :=
      Nat.mul_le_mul he (shiftDifferenceProduct_le_polynomial ((le_max_right _ _).trans hM) h hh)
    _ = _ := (pow_add _ _ _).symm

end
end PaperC.V282.SplitProductLocalization
