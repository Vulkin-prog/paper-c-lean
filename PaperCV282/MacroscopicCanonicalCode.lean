import PaperCV282.MacroscopicGeometry
import PaperC.Affine.CanonicalRationalCode
import PaperC.Asymptotics.ExpSqrtLog

/-!
# Canonical rational channels in a macroscopic logarithmic band

For fixed positive `δ`, every fixed power of a logarithmic window length
is eventually smaller than `M^δ`. This supplies the determinant threshold
for channel height `(L+1)^3`, uniformly before choosing the length or either
start. The finite uniqueness and canonical-code theorems then apply without
a dyadic geometry or a critical run-length balance condition.
-/

namespace PaperC.V282.MacroscopicCanonicalCode

open Affine Affine.RationalChannelCode Affine.CanonicalRationalCode
open MacroscopicGeometry

noncomputable section

/-- Fixed powers of logarithmic heights are uniformly smaller than any positive real power. -/
theorem logarithmic_power_lt_rpow_eventually
    (C delta : ℝ) (hC : 0 ≤ C) (hdelta : 0 < delta)
    (e : ℕ) (he : 0 < e) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ B : ℕ,
      (B : ℝ) ≤ C * Real.log M →
      (B + 1 : ℝ) ^ e < (M : ℝ) ^ delta := by
  obtain ⟨k, hkBound⟩ := exists_nat_gt (1 / delta)
  have hkReal : (0 : ℝ) < k := (one_div_pos.mpr hdelta).trans hkBound
  have hk : 0 < k := by exact_mod_cast hkReal
  have hdeltaK : (1 : ℝ) < delta * (k : ℝ) := by
    have h := (div_lt_iff₀ hdelta).mp hkBound
    nlinarith
  obtain ⟨Mpower, hpower⟩ :=
    ExpSqrtLog.linear_log_add_one_pow_le_nat_eventually C hC (e * k) (Nat.mul_pos he hk)
  refine ⟨max 2 Mpower, ?_⟩
  intro M hM B hB
  have hMtwo : 2 ≤ M := (le_max_left _ _).trans hM
  have hMpower : Mpower ≤ M := (le_max_right _ _).trans hM
  have hMone : (1 : ℝ) < M := by exact_mod_cast (show 1 < M by omega)
  have hstrict : (M : ℝ) < ((M : ℝ) ^ delta) ^ k := by
    calc
      (M : ℝ) = (M : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ < (M : ℝ) ^ (delta * (k : ℝ)) :=
        Real.rpow_lt_rpow_of_exponent_lt hMone hdeltaK
      _ = ((M : ℝ) ^ delta) ^ k := Real.rpow_mul_natCast (by positivity) delta k
  have hpowers : ((B + 1 : ℝ) ^ e) ^ k < ((M : ℝ) ^ delta) ^ k := by
    rw [← pow_mul]
    exact (hpower M hMpower B hB).trans_lt hstrict
  exact lt_of_pow_lt_pow_left₀ k (Real.rpow_nonneg (by positivity) delta) hpowers

/-- The height-`(L+1)^3` determinant threshold holds below every macroscopic start. -/
theorem determinant_threshold_macroscopic_eventually
    (C delta : ℝ) (hC : 0 ≤ C) (hdelta : 0 < delta) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      ((L + 1 : ℕ) : ℝ) ≤ C * Real.log M →
      ((4 * ((L + 1) ^ 3) ^ 2 * (L + 1) : ℕ) : ℝ) < (M : ℝ) ^ delta ∧
        ∀ x ∈ macroscopicStarts M delta,
          4 * ((L + 1) ^ 3) ^ 2 * (L + 1) < x := by
  obtain ⟨Mzero, hpower⟩ :=
    logarithmic_power_lt_rpow_eventually C delta hC hdelta 9 (by omega)
  refine ⟨Mzero, ?_⟩
  intro M hM L hL
  have hfinite :
      4 * ((L + 1) ^ 3) ^ 2 * (L + 1) < ((L + 1) + 1) ^ 9 := by
    have hpow : (L + 1) ^ 7 < ((L + 1) + 1) ^ 7 :=
      Nat.pow_lt_pow_left (Nat.lt_succ_self _) (by omega)
    have hfour : 4 ≤ ((L + 1) + 1) ^ 2 := by
      exact Nat.pow_le_pow_left (by omega : 2 ≤ (L + 1) + 1) 2
    calc
      4 * ((L + 1) ^ 3) ^ 2 * (L + 1) = 4 * (L + 1) ^ 7 := by ring
      _ < 4 * ((L + 1) + 1) ^ 7 := (Nat.mul_lt_mul_left (by omega : 0 < 4)).2 hpow
      _ ≤ ((L + 1) + 1) ^ 2 * ((L + 1) + 1) ^ 7 :=
        Nat.mul_le_mul_right _ hfour
      _ = ((L + 1) + 1) ^ 9 := by ring
  have hfiniteReal :
      ((4 * ((L + 1) ^ 3) ^ 2 * (L + 1) : ℕ) : ℝ) <
        ((L + 1 : ℕ) + 1 : ℝ) ^ 9 := by exact_mod_cast hfinite
  have hthreshold := hfiniteReal.trans (hpower M hM (L + 1) hL)
  refine ⟨hthreshold, ?_⟩
  intro x hx
  have hxLower := ((mem_macroscopicStarts_iff_real M delta x).mp hx).1
  exact_mod_cast hthreshold.trans_le hxLower

/-- Above a common macroscopic threshold there is at most one reduced candidate. -/
theorem card_reduced_candidates_le_one_eventually
    (C delta : ℝ) (hC : 0 ≤ C) (hdelta : 0 < delta) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      ((L + 1 : ℕ) : ℝ) ≤ C * Real.log M →
      ∀ x ∈ macroscopicStarts M delta, ∀ y : ℕ,
        (reducedChannelCandidates x y (L + 1) ((L + 1) ^ 3)).card ≤ 1 := by
  obtain ⟨Mzero, hthreshold⟩ := determinant_threshold_macroscopic_eventually C delta hC hdelta
  refine ⟨Mzero, ?_⟩
  intro M hM L hL x hx y
  exact card_reducedChannelCandidates_le_one ((hthreshold M hM L hL).2 x hx)

/-- Every candidate witness equals the bundled canonical choice, uniformly in both starts. -/
theorem canonical_candidate_eq_some_eventually
    (C delta : ℝ) (hC : 0 ≤ C) (hdelta : 0 < delta) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      ((L + 1 : ℕ) : ℝ) ≤ C * Real.log M →
      ∀ x ∈ macroscopicStarts M delta, ∀ y : ℕ, ∀ c : ℕ × ℕ,
      ∀ hc : c ∈ reducedChannelCandidates x y (L + 1) ((L + 1) ^ 3),
        canonicalReducedCandidate? x y (L + 1) ((L + 1) ^ 3) =
          some (⟨c, hc⟩ : ReducedCandidate x y (L + 1) ((L + 1) ^ 3)) := by
  obtain ⟨Mzero, hthreshold⟩ := determinant_threshold_macroscopic_eventually C delta hC hdelta
  refine ⟨Mzero, ?_⟩
  intro M hM L hL x hx y c hc
  exact canonicalReducedCandidate?_eq_some_of_mem ((hthreshold M hM L hL).2 x hx) hc

/-- Every nonzero primitive rational-channel code is the canonical code in the macroscopic band.
The prime cutoff is arbitrary; no asymptotic bound for relation weights is asserted. -/
theorem canonical_rational_code_eq_of_nonzero_eventually
    (C delta : ℝ) (hC : 0 ≤ C) (hdelta : 0 < delta) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      ((L + 1 : ℕ) : ℝ) ≤ C * Real.log M →
      ∀ x ∈ macroscopicStarts M delta, ∀ y ∈ macroscopicStarts M delta,
        ∃ hxTwo : 2 ≤ x, ∃ hyTwo : 2 ≤ y,
          ∀ K a b : ℕ, ∀ (ha : 0 < a) (hb : 0 < b), a.Coprime b →
            rationalCode K x y L a b (pairChannelError x y a b)
              ha hb hxTwo hyTwo (by rfl) ≠ ⊥ →
            canonicalRationalCode K 3 x y L hxTwo hyTwo =
              rationalCode K x y L a b (pairChannelError x y a b)
                ha hb hxTwo hyTwo (by rfl) := by
  obtain ⟨Mthreshold, hthreshold⟩ :=
    determinant_threshold_macroscopic_eventually C delta hC hdelta
  refine ⟨max 2 Mthreshold, ?_⟩
  intro M hM L hL x hx y hy
  have hMtwo : 2 ≤ M := (le_max_left _ _).trans hM
  have hMthreshold : Mthreshold ≤ M := (le_max_right _ _).trans hM
  have hxTwo : 2 ≤ x := (Finset.mem_Icc.mp (macroscopicStarts_subset_Icc hMtwo hdelta hx)).1
  have hyTwo : 2 ≤ y := (Finset.mem_Icc.mp (macroscopicStarts_subset_Icc hMtwo hdelta hy)).1
  refine ⟨hxTwo, hyTwo, ?_⟩
  intro K a b ha hb hab hcode
  exact canonicalRationalCode_eq_of_rationalCode_ne_bot hxTwo hyTwo ha hb hab
    (by omega : 1 ≤ 3) ((hthreshold M hMthreshold L hL).2 x hx) hcode

end
end PaperC.V282.MacroscopicCanonicalCode
