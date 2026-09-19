import PaperCPrel8.AffineDictionaryMatrix
import PaperCPrel8.AffineDictionaryConsequences

/-! # The concrete inclusion formulas and logarithmic description example -/
namespace PaperC.Prel8.AffineDictionaryDescription
open PaperC.Prel8.AffineDictionarySample PaperC.Prel8.AffineDictionaryInclusion
open PaperC.Prel8.AffineDictionaryMatrix
noncomputable section
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- The one-word inclusion probability is 2^(-r), also at rank zero and full rank. -/
theorem single_probability {B r : ℕ} (hr : r ≤ B) (u : Word B) :
    affineAverage B r (fun W => if u ∈ W then 1 else 0)=1/(2:ℝ)^r := by
  have h := pair_probability_kernel B r u u
  simpa only [and_self,sub_self,kernelFrequency_zero hr] using h

/-- The literal distinct-word formula in the affine corollary. -/
theorem distinct_pair_probability {B r : ℕ} (hB : 1 ≤ B) (hr : r ≤ B)
    (u v : Word B) (huv : u ≠ v) :
    affineAverage B r (fun W => if u ∈ W ∧ v ∈ W then 1 else 0)=
      (1/(2:ℝ)^r)*(((2:ℝ)^(B-r)-1)/((2:ℝ)^B-1)) := by
  rw [pair_probability_kernel,kernelFrequency_eq hB hr (u-v) (sub_ne_zero.mpr huv)]
  ring

/-- An explicit log-squared bound on the literal matrix/offset bit count. -/
theorem bits_le_log_squared {B r : ℕ} {N beta : ℝ} (hr : r ≤ B)
    (hlog : 1 ≤ Real.log N) (hbeta : 0 ≤ beta) (hB : (B:ℝ) ≤ beta*Real.log N) :
    (r*(B+1):ℝ) ≤ beta*(beta+1)*(Real.log N)^2 := by
  have hrR : (r:ℝ) ≤ B := by exact_mod_cast hr
  have hb1 : (B:ℝ)+1 ≤ (beta+1)*Real.log N := by nlinarith
  calc
    _ ≤ (B:ℝ)*(B+1) := mul_le_mul_of_nonneg_right hrR (by positivity)
    _ ≤ (beta*Real.log N)*((beta+1)*Real.log N) := by gcongr
    _ = _ := by ring

/-- B=2*log_2(N)+O(1), r=log_2(N)+O(1) gives a bounded log(m/N). -/
theorem log_size_ratio_bound {B r : ℕ} {N CB Cr : ℝ} (hr : r ≤ B) (hN : 0 < N)
    (hB : |(B:ℝ)-2*Real.log N/Real.log 2| ≤ CB)
    (hrate : |(r:ℝ)-Real.log N/Real.log 2| ≤ Cr) :
    |Real.log (((2^(B-r):ℕ):ℝ)/N)| ≤ (CB+Cr)*Real.log 2 := by
  have htwo : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have he : Real.log (((2^(B-r):ℕ):ℝ)/N)=
      (((B:ℝ)-2*Real.log N/Real.log 2)-((r:ℝ)-Real.log N/Real.log 2))*Real.log 2 := by
    rw [Nat.cast_pow,Nat.cast_ofNat,Real.log_div (by positivity) hN.ne',Real.log_pow,Nat.cast_sub hr]
    field_simp
    ring
  rw [he,abs_mul,abs_of_pos htwo]
  exact mul_le_mul_of_nonneg_right ((abs_sub _ _).trans (add_le_add hB hrate)) htwo.le

/-- Finite positive constants exhibit dictionaries of order N in that example. -/
theorem size_ratio_bounds {B r : ℕ} {N CB Cr : ℝ} (hr : r ≤ B) (hN : 0 < N)
    (hB : |(B:ℝ)-2*Real.log N/Real.log 2| ≤ CB)
    (hrate : |(r:ℝ)-Real.log N/Real.log 2| ≤ Cr) :
    Real.exp (-((CB+Cr)*Real.log 2))*N ≤ ((2^(B-r):ℕ):ℝ) ∧
      ((2^(B-r):ℕ):ℝ) ≤ Real.exp ((CB+Cr)*Real.log 2)*N := by
  have h := abs_le.mp (log_size_ratio_bound hr hN hB hrate)
  have hlo := Real.exp_le_exp.mpr h.1
  have hhi := Real.exp_le_exp.mpr h.2
  rw [Real.exp_log (by positivity)] at hlo hhi
  exact ⟨(le_div_iff₀ hN).mp hlo,(div_le_iff₀ hN).mp hhi⟩

end
end PaperC.Prel8.AffineDictionaryDescription
