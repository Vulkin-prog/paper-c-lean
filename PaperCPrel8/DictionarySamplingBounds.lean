import PaperCPrel8.DictionarySelection

/-! # One- and two-point sampling bounds for typical dictionaries

These bounds average the selected dictionary after fixing the source law.
They apply without any uniformity assumption on an arithmetic word.
-/
namespace PaperC.Prel8.DictionarySamplingBounds
open PaperC.Prel8.DictionarySelection
open PaperC.V282.RandomDictionary PaperC.V282.RandomDictionaryOverlap
open PaperC.ArratiaGoldsteinGordonInput PaperC.Affine
open scoped BigOperators
noncomputable section
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- Exact distinct-word inclusion probability, including m=1. -/
theorem twoInclusion_eq {B m : ℕ} (hB : 1 ≤ B) (hm : 1 ≤ m) (hmb : m ≤ 2^B) :
    twoInclusion B m = (m:ℝ)*((m:ℝ)-1)/((2:ℝ)^B*((2:ℝ)^B-1)) := by
  have hn : 2 ≤ 2^B := by simpa using Nat.pow_le_pow_right (by decide : 1 ≤ 2) hB
  have hc : (0:ℝ)<((2^B).choose m:ℕ) := by exact_mod_cast Nat.choose_pos hmb
  have hq : (1:ℝ)<(2:ℝ)^B := one_lt_pow₀ (by norm_num) (by omega)
  have hOne := one_inclusion_count_identity (by omega : 1 ≤ 2^B) hm
  have hTwo := congrArg (fun n : ℕ => (n:ℝ)) (pair_inclusion_count_identity hn hm)
  push_cast [Nat.cast_sub (by omega : 1 ≤ 2^B),Nat.cast_sub hm] at hTwo
  have hOne' : (2:ℝ)^B*((2^B-1).choose (m-1):ℝ) = ((2^B).choose m:ℝ)*m := by exact_mod_cast hOne
  have hTwo' : ((if 2 ≤ m then (2^B-2).choose (m-2) else 0 : ℕ):ℝ)*((2:ℝ)^B-1) =
      ((m:ℝ)-1)*((2^B-1).choose (m-1):ℝ) := by simpa only [Nat.cast_ite,Nat.cast_zero] using hTwo
  unfold twoInclusion
  apply (div_eq_div_iff hc.ne' (mul_pos (by positivity) (by linarith)).ne').mpr
  calc
    _ = (2:ℝ)^B*((m:ℝ)-1)*((2^B-1).choose (m-1):ℝ) := by nlinarith [congrArg (fun t : ℝ => (2:ℝ)^B*t) hTwo']
    _ = _ := by nlinarith [congrArg (fun t : ℝ => ((m:ℝ)-1)*t) hOne']

/-- Sampling without replacement has b<=a^2<=a. -/
theorem inclusion_bounds {B m : ℕ} (hB : 1 ≤ B) (hm : 1 ≤ m) (hmb : m ≤ 2^B) :
    0 ≤ twoInclusion B m ∧ twoInclusion B m ≤ (oneInclusion B m)^2 ∧
      (oneInclusion B m)^2 ≤ oneInclusion B m := by
  have hq : (1:ℝ)<(2:ℝ)^B := one_lt_pow₀ (by norm_num) (by omega)
  have hmR : (1:ℝ)≤m := by exact_mod_cast hm
  have hmQ : (m:ℝ)≤(2:ℝ)^B := by exact_mod_cast hmb
  rw [oneInclusion_eq hm hmb,twoInclusion_eq hB hm hmb]
  have ha : 0 ≤ (m:ℝ)/(2:ℝ)^B := by positivity
  have ha1 : (m:ℝ)/(2:ℝ)^B ≤ 1 := (div_le_one (by positivity)).mpr hmQ
  refine ⟨by positivity,?_,by nlinarith⟩
  apply (div_le_iff₀ (mul_pos (by positivity) (by linarith))).mpr
  field_simp
  nlinarith

/-- The averaged joint probability is bounded by a^2 plus a times collision probability. -/
theorem averaged_pair_le {B m : ℕ} (hB : 1 ≤ B) (hm : 1 ≤ m) (hmb : m ≤ 2^B)
    {Ω : Type*} [Fintype Ω] (μ : FinitePMF Ω) (u v : Ω → Fin B → F₂) :
    dictionaryAverage B m (fun W => eventProbability μ (fun ω => u ω ∈ W ∧ v ω ∈ W)) ≤
      ((m:ℝ)/(2:ℝ)^B)^2+((m:ℝ)/(2:ℝ)^B)*eventProbability μ (fun ω => u ω=v ω) := by
  rw [averaged_pair_probability hm hmb]
  have hb := inclusion_bounds hB hm hmb
  have hp : 0 ≤ eventProbability μ (fun ω => u ω=v ω) := by
    unfold eventProbability; exact Finset.sum_nonneg (fun x _ => by split_ifs; exact μ.nonneg x; exact le_rfl)
  rw [← oneInclusion_eq hm hmb]
  nlinarith [mul_nonneg hb.1 hp]

/-- Exact average deletion cost for any source word law, including bad windows. -/
theorem averaged_word_probability {B m : ℕ} (hm : 1 ≤ m) (hmb : m ≤ 2^B)
    {Ω : Type*} [Fintype Ω] (μ : FinitePMF Ω) (u : Ω → Fin B → F₂) :
    dictionaryAverage B m (fun W => eventProbability μ (fun ω => u ω ∈ W)) =
      (m:ℝ)/(2:ℝ)^B := by
  have h := averaged_pair_probability hm hmb μ u u
  have hp : eventProbability μ (fun ω => u ω=u ω)=1 := by simp [eventProbability,μ.sum_prob]
  rw [hp] at h
  simp only [and_self,mul_one,add_sub_cancel] at h
  exact h.trans (oneInclusion_eq hm hmb)

/-- Averaging a whole deleted set costs exactly a times its cardinality. -/
theorem averaged_deletion_sum {B m : ℕ} (hm : 1 ≤ m) (hmb : m ≤ 2^B)
    {Ω ι : Type*} [Fintype Ω] (μ : FinitePMF Ω) (S : Finset ι) (u : ι → Ω → Fin B → F₂) :
    dictionaryAverage B m (fun W => ∑ i ∈ S, eventProbability μ (fun ω => u i ω ∈ W)) =
      ((m:ℝ)/(2:ℝ)^B)*S.card := by
  rw [dictionaryAverage_finset_sum]
  simp_rw [averaged_word_probability hm hmb μ]
  simp [mul_comm]

end
end PaperC.Prel8.DictionarySamplingBounds
