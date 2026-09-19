import PaperCPrel8.PrimeWitnessRetention

/-! # Uniform explicit errors in the certified-prime-site count -/
namespace PaperC.Prel8.PrimeWitnessCountBounds
open Finset PrimeWitnessRetention
noncomputable section

theorem cast_sub_lower (a b : ℕ) : (a:ℝ)-b ≤ ((a-b:ℕ):ℝ) := by
  by_cases h : b≤a
  · rw [Nat.cast_sub h]
  · have hh : (a:ℝ)≤b := by exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge h))
    have hn : (0:ℝ)≤((a-b:ℕ):ℝ) := by positivity
    linarith

theorem cast_div_lower (a : ℕ) {q : ℕ} (hq : 0<q) :
    (a:ℝ)/q-1 ≤ ((a/q:ℕ):ℝ) := by
  have h := Nat.lt_mul_div_succ a hq
  have hr : (a:ℝ)<q*((a/q:ℕ)+1) := by exact_mod_cast h
  have hqr : (0:ℝ)<q := by exact_mod_cast hq
  have hh : (a:ℝ)/q<((a/q:ℕ):ℝ)+1 := (div_lt_iff₀ hqr).mpr (by nlinarith)
  linarith

/-- A uniform O(1) error, also valid when the window is shorter than the prime. -/
theorem certified_count_lower {q M : ℕ} (hq : 2≤q) :
    (M:ℝ)/q-3-2*M/(q:ℝ)^2 ≤ ((certifiedSites q M).card:ℝ) := by
  rw [certified_sites_count hq]
  let T := M/q-1
  have hqr : (0:ℝ)<q := by exact_mod_cast (show 0<q by omega)
  have hq1 : (1:ℝ)≤q := by exact_mod_cast (show 1≤q by omega)
  have ht : (M:ℝ)/q-2 ≤ (T:ℝ) := by
    have h1 := cast_div_lower M (show 0<q by omega)
    have h2 := cast_sub_lower (M/q) 1
    dsimp [T]
    norm_num at h2
    linarith
  have htu : (T:ℝ)≤(M:ℝ)/q :=
    (show (T:ℝ)≤((M/q:ℕ):ℝ) by exact_mod_cast Nat.sub_le (M/q) 1).trans Nat.cast_div_le
  have h1 : ((T/q:ℕ):ℝ)≤(M:ℝ)/q/q :=
    (Nat.cast_div_le).trans (div_le_div_of_nonneg_right htu hqr.le)
  have h2 : (((T+1)/q:ℕ):ℝ)≤((M:ℝ)/q+1)/q := by
    apply (Nat.cast_div_le).trans
    apply div_le_div_of_nonneg_right _ hqr.le
    push_cast
    linarith
  have h3 := cast_sub_lower T (T/q)
  have h4 := cast_sub_lower (T-T/q) ((T+1)/q)
  have hi : 1/(q:ℝ)≤1 := (div_le_one hqr).mpr hq1
  have he : ((M:ℝ)/q+1)/q=(M:ℝ)/q/q+1/q := by ring
  have he2 : (M:ℝ)/q/q=M/(q:ℝ)^2 := by ring
  rw [he,he2] at h2
  rw [he2] at h1
  change (M:ℝ)/q-3-2*M/(q:ℝ)^2 ≤ (((T-T/q)-(T+1)/q:ℕ):ℝ)
  have he3 : 2*(M:ℝ)/(q:ℝ)^2=2*((M:ℝ)/(q:ℝ)^2) := by ring
  rw [he3]
  linarith

/-- Any deletion budget can be subtracted before taking a limit. -/
theorem retained_count_lower {q M : ℕ} (hq : 2≤q) (G : Finset ℕ) :
    (M:ℝ)/q-3-2*M/(q:ℝ)^2-(((Icc 1 M)\G).card:ℝ) ≤
      (((certifiedSites q M).card-((Icc 1 M)\G).card:ℕ):ℝ) := by
  have h1 := certified_count_lower (M:=M) hq
  have h2 := cast_sub_lower (certifiedSites q M).card ((Icc 1 M)\G).card
  linarith

end
end PaperC.Prel8.PrimeWitnessCountBounds
