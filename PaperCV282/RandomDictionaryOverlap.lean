import PaperCV282.RandomDictionary

/-!
# Exact mean overlap and exceptional fractions for uniform dictionaries

The expectation is under the uniform law on m-element subsets. The distinct
pair count is used with its without-replacement inclusion probability. The
result strengthens (5.8) from denominator 2^B-1 to denominator 2^B.
-/
namespace PaperC.V282.RandomDictionaryOverlap

open RandomDictionary RandomDictionaryWordCount WordOverlap WordOverlapSum
open scoped BigOperators

noncomputable section

@[reducible]
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

/-- Finite linearity for the literal subset average. -/
theorem dictionaryAverage_finset_sum {B m : ℕ} {T : Type*} (s : Finset T)
    (f : T → Finset (Fin B → F₂) → ℝ) :
    dictionaryAverage B m (fun W => ∑ t ∈ s, f t W) =
      ∑ t ∈ s, dictionaryAverage B m (f t) := by
  unfold dictionaryAverage
  rw [Finset.sum_comm,Finset.sum_div]

/-- The inner word sums are exactly the unmasked ambient sums with membership indicators. -/
theorem pair_sum_eq_indicators {B : ℕ} (W : Finset (Fin B → F₂))
    (f : (Fin B → F₂) → (Fin B → F₂) → ℝ) :
    (∑ w ∈ W, ∑ v ∈ W, f w v) =
      ∑ w : Fin B → F₂, ∑ v : Fin B → F₂, if w ∈ W ∧ v ∈ W then f w v else 0 := by
  simp_rw [ite_and,Finset.sum_ite_irrel,Finset.sum_const_zero,← Finset.sum_filter]
  simp

/-- Fixed-pair inclusion counts distinguish the diagonal from distinct words. -/
theorem sum_pair_indicator {B m : ℕ} (hm : 1 ≤ m)
    (w v : Fin B → F₂) (c : ℝ) :
    (∑ W ∈ dictionaries B m, if w ∈ W ∧ v ∈ W then c else 0) =
      if w = v then ((2^B-1).choose (m-1) : ℝ) * c
      else ((if 2 ≤ m then (2^B-2).choose (m-2) else 0 : ℕ) : ℝ) * c := by
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const,nsmul_eq_mul]
  by_cases h : w = v
  · subst v
    simp [card_dictionaries_containing hm]
  · rw [if_neg h]
    by_cases hm2 : 2 ≤ m
    · rw [if_pos hm2,card_dictionaries_containing_pair hm2 w v h]
    · rw [if_neg hm2,card_dictionaries_containing_pair_of_lt (by omega) w v h]

/-- The double subset sum retains the exact dependent inclusion counts. -/
theorem sum_sampled_pairs {B m : ℕ} (hm : 1 ≤ m)
    (f : (Fin B → F₂) → (Fin B → F₂) → ℝ) :
    (∑ W ∈ dictionaries B m, ∑ w ∈ W, ∑ v ∈ W, f w v) =
      ((2^B-1).choose (m-1) : ℝ) * (∑ w : Fin B → F₂, f w w) +
      ((if 2 ≤ m then (2^B-2).choose (m-2) else 0 : ℕ) : ℝ) *
        (∑ w : Fin B → F₂, ∑ v : Fin B → F₂, if w ≠ v then f w v else 0) := by
  have hexpand : (∑ W ∈ dictionaries B m, ∑ w ∈ W, ∑ v ∈ W, f w v) =
      ∑ W ∈ dictionaries B m, ∑ w : Fin B → F₂, ∑ v : Fin B → F₂,
        if w ∈ W ∧ v ∈ W then f w v else 0 :=
    Finset.sum_congr rfl (fun W _ => pair_sum_eq_indicators W f)
  rw [hexpand]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := dictionaries B m)]
  simp_rw [sum_pair_indicator hm]
  have ht (w v : Fin B → F₂) :
      (if w = v then ((2^B-1).choose (m-1) : ℝ) * f w v else
        ((if 2 ≤ m then (2^B-2).choose (m-2) else 0 : ℕ) : ℝ) * f w v) =
      ((2^B-1).choose (m-1) : ℝ) * (if w = v then f w w else 0) +
        ((if 2 ≤ m then (2^B-2).choose (m-2) else 0 : ℕ) : ℝ) *
          (if w ≠ v then f w v else 0) := by
    by_cases h : w = v <;> simp [h]
  simp_rw [ht,Finset.sum_add_distrib,← Finset.mul_sum]
  simp

/-- At each positive shift the exact expected normalized weight is m/2^B. -/
theorem average_shift_weight {B m d : ℕ} (hm : 1 ≤ m) (hmB : m ≤ 2^B)
    (hd : 0 < d) (hdB : d ≤ B) :
    dictionaryAverage B m (fun W =>
      (∑ w ∈ W, ∑ v ∈ W, directedOverlapWeight d w v) / (m : ℝ)) = (m : ℝ) / (2 : ℝ)^B := by
  unfold dictionaryAverage
  rw [← Finset.sum_div,sum_sampled_pairs hm,
    sum_self_directedOverlapWeight hd hdB,sum_distinct_directedOverlapWeight hd hdB,card_dictionaries]
  have hn : 2 ≤ 2^B := by
    have hb : 1 ≤ B := by omega
    simpa using Nat.pow_le_pow_right (by decide : 1 ≤ 2) hb
  have hnp : (0 : ℝ) < (2 : ℝ)^B := by positivity
  have hmp : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hcp : (0 : ℝ) < ((2^B).choose m : ℕ) := by exact_mod_cast Nat.choose_pos hmB
  have hOne : (2 : ℝ)^B * ((2^B-1).choose (m-1) : ℝ) =
      ((2^B).choose m : ℝ) * (m : ℝ) := by
    exact_mod_cast one_inclusion_count_identity (by omega : 1 ≤ 2^B) hm
  have hTwo : ((if 2 ≤ m then (2^B-2).choose (m-2) else 0 : ℕ) : ℝ) * ((2 : ℝ)^B - 1) =
      ((m : ℝ)-1) * ((2^B-1).choose (m-1) : ℝ) := by
    have h := congrArg (fun n : ℕ => (n : ℝ)) (pair_inclusion_count_identity hn hm)
    push_cast [Nat.cast_sub (by omega : 1 ≤ 2^B),Nat.cast_sub hm] at h
    by_cases hm2 : 2 ≤ m <;> simpa [hm2] using h
  rw [hTwo]
  field_simp
  nlinarith

/-- The defining triple sum may be grouped by displacement without changing Omega. -/
theorem overlapWeight_eq_shift_sum {B m : ℕ} (W : Finset (Fin B → F₂)) (hW : W.card = m) :
    overlapWeight W = ∑ d ∈ Finset.Icc 1 (B-1),
      (∑ w ∈ W, ∑ v ∈ W, directedOverlapWeight d w v) / (m : ℝ) := by
  unfold overlapWeight
  rw [hW,← Finset.sum_div]
  congr 1
  simp_rw [Finset.sum_comm (s := W) (t := Finset.Icc 1 (B-1))]

/-- Exact mean overlap under the actual uniform without-replacement dictionary law. -/
theorem average_overlapWeight_eq {B m : ℕ} (hm : 1 ≤ m) (hmB : m ≤ 2^B) :
    dictionaryAverage B m overlapWeight = (m : ℝ) * (B-1 : ℕ) / (2 : ℝ)^B := by
  calc
    _ = dictionaryAverage B m (fun W => ∑ d ∈ Finset.Icc 1 (B-1),
        (∑ w ∈ W, ∑ v ∈ W, directedOverlapWeight d w v) / (m : ℝ)) := by
      unfold dictionaryAverage
      congr 1
      apply Finset.sum_congr rfl
      intro W hW
      exact overlapWeight_eq_shift_sum W (mem_dictionaries W |>.mp hW)
    _ = ∑ d ∈ Finset.Icc 1 (B-1), dictionaryAverage B m (fun W =>
        (∑ w ∈ W, ∑ v ∈ W, directedOverlapWeight d w v) / (m : ℝ)) :=
      dictionaryAverage_finset_sum _ _
    _ = ∑ d ∈ Finset.Icc 1 (B-1), (m : ℝ) / (2 : ℝ)^B := by
      apply Finset.sum_congr rfl
      intro d hd
      obtain ⟨hlo,hhi⟩ := Finset.mem_Icc.mp hd
      exact average_shift_weight hm hmB (by omega) (by omega)
    _ = _ := by simp; ring

/-- The printed estimate (5.8) follows from the exact, slightly stronger mean. -/
theorem equation_five_eight {B m : ℕ} (hm : 1 ≤ m) (hmB : m ≤ 2^B) :
    dictionaryAverage B m overlapWeight ≤ (m : ℝ) * (B-1 : ℕ) / ((2 : ℝ)^B-1) := by
  rw [average_overlapWeight_eq hm hmB]
  by_cases hB : B = 0
  · simp [hB]
  · have hp : (1 : ℝ) < (2 : ℝ)^B := one_lt_pow₀ (by norm_num) hB
    exact div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)

/-- Markov's inequality for the exact fraction of actual sampled dictionaries. -/
theorem dictionaryFraction_overlapWeight_gt_le {B m : ℕ} (hm : 1 ≤ m) (hmB : m ≤ 2^B)
    {t : ℝ} (ht : 0 < t) :
    dictionaryFraction B m (fun W => t < overlapWeight W) ≤
      ((m : ℝ) * (B-1 : ℕ) / (2 : ℝ)^B) / t := by
  let bad := (dictionaries B m).filter (fun W => t < overlapWeight W)
  have hsum : t * (bad.card : ℝ) ≤ ∑ W ∈ dictionaries B m, overlapWeight W := by
    calc
      _ = ∑ W ∈ bad, t := by simp [mul_comm]
      _ ≤ ∑ W ∈ bad, overlapWeight W := Finset.sum_le_sum fun W hW =>
        (Finset.mem_filter.mp hW).2.le
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun W _ _ => overlapWeight_nonneg W)
  have hc : (0 : ℝ) < (dictionaries B m).card := by
    exact_mod_cast Finset.card_pos.mpr (dictionaries_nonempty hmB)
  have hmean := average_overlapWeight_eq hm hmB
  unfold dictionaryAverage at hmean
  change (bad.card : ℝ) / (dictionaries B m).card ≤ _
  rw [← hmean]
  apply (le_div_iff₀ ht).mpr
  rw [div_mul_eq_mul_div]
  apply (div_le_div_iff_of_pos_right hc).mpr
  nlinarith

end
end PaperC.V282.RandomDictionaryOverlap
