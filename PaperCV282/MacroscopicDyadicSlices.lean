import PaperCV282.MacroscopicLogarithms
import PaperCV282.ShiftedKernelDyadicCover

/-!
# Uniform dyadic transport for the macroscopic interval

The scale is determined by the actual larger start. A fixed macroscopic
lower endpoint makes every nonempty slice large enough, and transports
the logarithmic band. Exact fibrewise summation counts every original
ordered pair once, without comparing its two coordinates.
-/

namespace PaperC.V282.MacroscopicDyadicSlices

open MacroscopicGeometry MacroscopicLogarithms LogarithmicWordPowers
open scoped BigOperators

noncomputable section

/-- Exact logarithmic fibres of an arbitrary integer-valued scale map. -/
def dyadicSlice {alpha : Type*} [DecidableEq alpha]
    (s : Finset alpha) (f : alpha → ℕ) (j : ℕ) : Finset alpha :=
  s.filter fun p => Nat.log 2 (f p) = j

/-- A positive value belongs to the half-open interval of its logarithmic fibre. -/
theorem bounds_of_mem_dyadicSlice {alpha : Type*} [DecidableEq alpha]
    {s : Finset alpha} {f : alpha → ℕ} {j : ℕ} {p : alpha}
    (hp : p ∈ dyadicSlice s f j) (hpos : 0 < f p) :
    2 ^ j ≤ f p ∧ f p < 2 * 2 ^ j := by
  have hj := (Finset.mem_filter.mp hp).2
  constructor
  · simpa only [hj] using Nat.pow_log_le_self 2 (by omega : f p ≠ 0)
  · simpa only [hj, pow_succ, Nat.mul_comm] using Nat.lt_pow_succ_log_self (by omega : 1 < 2) (f p)

/-- The original weighted mass is exactly the sum over logarithmic fibres. -/
theorem sum_eq_sum_dyadicSlices {alpha : Type*} [DecidableEq alpha]
    (s : Finset alpha) (f : alpha → ℕ) (w : alpha → ℝ) (M : ℕ)
    (hbound : ∀ p ∈ s, f p ≤ M) :
    (∑ p ∈ s, w p) =
      ∑ j ∈ Finset.range (Nat.log 2 M + 1), ∑ p ∈ dyadicSlice s f j, w p := by
  symm
  apply Finset.sum_fiberwise_of_maps_to
  intro p hp
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.log_mono_right (hbound p hp)))

/-- A common nonnegative bound on nonempty fibres bounds their complete sum. -/
theorem sum_le_number_of_slices_mul {alpha : Type*} [DecidableEq alpha]
    (s : Finset alpha) (f : alpha → ℕ) (w : alpha → ℝ) (M : ℕ) {E : ℝ}
    (hE : 0 ≤ E) (hbound : ∀ p ∈ s, f p ≤ M)
    (hslice : ∀ j ∈ Finset.range (Nat.log 2 M + 1),
      (dyadicSlice s f j).Nonempty → (∑ p ∈ dyadicSlice s f j, w p) ≤ E) :
    (∑ p ∈ s, w p) ≤ (Nat.log 2 M + 1 : ℝ) * E := by
  rw [sum_eq_sum_dyadicSlices s f w M hbound]
  calc
    _ ≤ ∑ _j ∈ Finset.range (Nat.log 2 M + 1), E := by
      apply Finset.sum_le_sum
      intro j hj
      by_cases hempty : dyadicSlice s f j = ∅
      · simpa only [hempty, Finset.sum_empty] using hE
      · exact hslice j hj (Finset.nonempty_iff_ne_empty.mpr hempty)
    _ = _ := by simp

/-- Every nonempty macroscopic slice eventually exceeds an arbitrary fixed threshold. -/
theorem dyadic_transport_eventually (delta : ℝ) (hdelta : 0 < delta) (K : ℕ) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ x ∈ macroscopicStarts M delta, ∀ X : ℕ,
      X ≤ x → x < 2 * X →
      K ≤ X ∧ 2 ≤ X ∧ X ≤ M ∧
        delta * Real.log M ≤ 2 * Real.log X ∧ Real.log X ≤ Real.log M := by
  obtain ⟨Mroot, hroot⟩ := root_ge_eventually delta hdelta (2 * max K 2)
  refine ⟨max Mroot 2, ?_⟩
  intro M hM x hx X hXx hxX
  have hr := hroot M (by omega) x hx
  have hxdata := (mem_macroscopicStarts_iff_real M delta x).mp hx
  have hXtwo : 2 ≤ X := by omega
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hxSquare : x ≤ X ^ 2 := by nlinarith
  have hpower : (M : ℝ) ^ delta ≤ (X : ℝ) ^ 2 :=
    hxdata.1.trans (by exact_mod_cast hxSquare)
  refine ⟨by omega, hXtwo, by omega, ?_, ?_⟩
  · calc
      delta * Real.log M = Real.log ((M : ℝ) ^ delta) := (Real.log_rpow hMpos delta).symm
      _ ≤ Real.log ((X : ℝ) ^ 2) := Real.log_le_log (Real.rpow_pos_of_pos hMpos _) hpower
      _ = _ := by rw [Real.log_pow]; norm_num
  · exact Real.log_le_log hXpos (by exact_mod_cast (show X ≤ M by omega))

/-- An ambient band yields one fixed band on every nonempty larger-start slice. -/
theorem logarithmic_band_on_slice
    {M X L : ℕ} {betaMin betaMax delta : ℝ}
    (hbetaMin : 0 < betaMin) (hbetaMax : 0 < betaMax) (hdelta : 0 < delta)
    (hlowerLog : delta * Real.log M ≤ 2 * Real.log X)
    (hupperLog : Real.log X ≤ Real.log M)
    (hlower : betaMin * Real.log M ≤ (L + 1 : ℝ))
    (hupper : (L + 1 : ℝ) ≤ betaMax * Real.log M) :
    betaMin * Real.log X ≤ (L + 1 : ℝ) ∧
      (L + 1 : ℝ) ≤ (2 * betaMax / delta) * Real.log X := by
  refine ⟨(mul_le_mul_of_nonneg_left hupperLog hbetaMin.le).trans hlower, ?_⟩
  have hscaled : (L + 1 : ℝ) * delta ≤ 2 * betaMax * Real.log X := by nlinarith
  have hdiv := (le_div_iff₀ hdelta).mpr hscaled
  exact hdiv.trans_eq (by ring)

/-- The complete number of logarithmic slices is subpolynomial in the ambient scale. -/
theorem number_of_dyadicSlices_le_rpow_eventually (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero,
      (Nat.log 2 M + 1 : ℝ) ≤ (M : ℝ) ^ epsilon := by
  let C : ℝ := 1 / Real.log 2 + 1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  obtain ⟨Mpoly, hpoly⟩ := polynomial_factor_le_rpow_eventually C hC 1 1 epsilon hepsilon
  refine ⟨max Mpoly (max (⌈Real.exp 1⌉₊ + 1) 2), ?_⟩
  intro M hM
  have hexp : Real.exp 1 ≤ (M : ℝ) := (Nat.le_ceil _).trans
    (by exact_mod_cast (show ⌈Real.exp 1⌉₊ ≤ M by omega))
  have hlogOne : 1 ≤ Real.log M := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hexp
  have hlog := DivisorSubpolynomial.binary_log_le_polynomial_log
    (by omega : 0 < M) (show M ≤ M ^ 1 by simp)
  have hceiling : ((Nat.log 2 M + 1 : ℕ) : ℝ) ≤ C * Real.log M := by
    dsimp [C]
    push_cast
    norm_num at hlog
    rw [one_div]
    nlinarith
  simpa only [pow_one, one_mul, Nat.cast_add, Nat.cast_one,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ Nat.log 2 M + 1)]
    using hpoly M (by omega) (Nat.log 2 M) hceiling

end
end PaperC.V282.MacroscopicDyadicSlices
