import PaperCV282.RandomDictionaryWordCount
import PaperC.Probability.FinitePMF
import Mathlib.Data.Nat.Choose.Basic

/-!
# Uniform dictionaries of a fixed size, without replacement

The sample points are the actual m-element subsets of all 2^B words.
Their probabilities are equal and normalized. Cardinality identities below
record the dependence between two distinct labels in this sampling scheme.
-/
namespace PaperC.V282.RandomDictionary

open WordOverlap WordOverlapSum RandomDictionaryWordCount
open scoped BigOperators

noncomputable section

@[reducible]
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

def dictionaries (B m : ℕ) : Finset (Finset (Fin B → F₂)) :=
  (Finset.univ : Finset (Fin B → F₂)).powersetCard m

@[reducible]
def DictionarySample (B m : ℕ) := {W : Finset (Fin B → F₂) // W ∈ dictionaries B m}

theorem mem_dictionaries {B m : ℕ} (W : Finset (Fin B → F₂)) :
    W ∈ dictionaries B m ↔ W.card = m := by
  simp [dictionaries]

theorem card_dictionaries (B m : ℕ) : (dictionaries B m).card = (2^B).choose m := by
  simp [dictionaries,F₂]

theorem dictionaries_nonempty {B m : ℕ} (hm : m ≤ 2^B) : (dictionaries B m).Nonempty := by
  rw [← Finset.card_pos,card_dictionaries]
  exact Nat.choose_pos hm

/-- Equal mass on each actual subset, with a proved nonempty sample space. -/
def uniformDictionaryPMF (B m : ℕ) (hm : m ≤ 2^B) : FinitePMF (DictionarySample B m) := by
  letI : Nonempty (DictionarySample B m) := by
    obtain ⟨W,hW⟩ := dictionaries_nonempty hm
    exact ⟨⟨W,hW⟩⟩
  exact FinitePMF.uniform (DictionarySample B m)

def dictionaryAverage (B m : ℕ) (f : Finset (Fin B → F₂) → ℝ) : ℝ :=
  (∑ W ∈ dictionaries B m, f W) / (dictionaries B m).card

def dictionaryFraction (B m : ℕ) (P : Finset (Fin B → F₂) → Prop) : ℝ :=
  ((dictionaries B m).filter P).card / ((dictionaries B m).card : ℝ)

theorem uniformDictionaryPMF_prob (B m : ℕ) (hm : m ≤ 2^B) (W : DictionarySample B m) :
    (uniformDictionaryPMF B m hm).prob W = 1 / ((2^B).choose m : ℝ) := by
  simp [uniformDictionaryPMF,FinitePMF.uniform,DictionarySample,card_dictionaries,one_div]

/-- The displayed arithmetic average is exactly expectation under the uniform subset law. -/
theorem dictionaryAverage_eq_expectation (B m : ℕ) (hm : m ≤ 2^B)
    (f : Finset (Fin B → F₂) → ℝ) :
    dictionaryAverage B m f =
      ∑ W : DictionarySample B m, (uniformDictionaryPMF B m hm).prob W * f W.val := by
  simp_rw [uniformDictionaryPMF_prob]
  rw [← Finset.mul_sum]
  rw [← Finset.sum_subtype (dictionaries B m) (fun _ => Iff.rfl)]
  simp [dictionaryAverage,card_dictionaries,div_eq_mul_inv,mul_comm]

/-- The exceptional fraction is the exact event probability under the same law. -/
theorem dictionaryFraction_eq_probability (B m : ℕ) (hm : m ≤ 2^B)
    (P : Finset (Fin B → F₂) → Prop) :
    dictionaryFraction B m P =
      ∑ W : DictionarySample B m, if P W.val then (uniformDictionaryPMF B m hm).prob W else 0 := by
  simp_rw [uniformDictionaryPMF_prob]
  have hs := Finset.sum_subtype (p := fun W => W ∈ dictionaries B m)
    (F := inferInstance) (dictionaries B m) (fun _ => Iff.rfl)
    (fun W => if P W then 1 / ((2^B).choose m : ℝ) else 0)
  rw [← hs,← Finset.sum_filter]
  simp [dictionaryFraction,card_dictionaries,div_eq_mul_inv]

/-- Exact count of sampled dictionaries containing a prescribed word. -/
theorem card_dictionaries_containing {B m : ℕ} (hm : 1 ≤ m) (w : Fin B → F₂) :
    ((dictionaries B m).filter (fun W => w ∈ W)).card = (2^B-1).choose (m-1) := by
  have h := Finset.card_filter_powersetCard_subset {w} (Finset.univ : Finset (Fin B → F₂)) m
    (Finset.subset_univ _) (by simpa using hm)
  simpa [dictionaries,F₂] using h

/-- Exact count of sampled dictionaries containing a prescribed distinct pair. -/
theorem card_dictionaries_containing_pair {B m : ℕ} (hm : 2 ≤ m)
    (w v : Fin B → F₂) (hne : w ≠ v) :
    ((dictionaries B m).filter (fun W => w ∈ W ∧ v ∈ W)).card = (2^B-2).choose (m-2) := by
  have h := Finset.card_filter_powersetCard_subset {w,v} (Finset.univ : Finset (Fin B → F₂)) m
    (Finset.subset_univ _) (by simpa [hne] using hm)
  simpa [dictionaries,F₂,hne,Finset.insert_subset_iff,Finset.singleton_subset_iff] using h

/-- A dictionary of size below two contains no pair of distinct words. -/
theorem card_dictionaries_containing_pair_of_lt {B m : ℕ} (hm : m < 2)
    (w v : Fin B → F₂) (hne : w ≠ v) :
    ((dictionaries B m).filter (fun W => w ∈ W ∧ v ∈ W)).card = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro W hW
  obtain ⟨hsize,hw,hv⟩ := Finset.mem_filter.mp hW
  have hs : ({w,v} : Finset (Fin B → F₂)) ⊆ W :=
    Finset.insert_subset_iff.mpr ⟨hw,Finset.singleton_subset_iff.mpr hv⟩
  have hc := Finset.card_le_card hs
  rw [mem_dictionaries] at hsize
  simp only [Finset.card_pair hne,hsize] at hc
  omega

/-- The first binomial inclusion identity, before division by the sample-space size. -/
theorem one_inclusion_count_identity {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) :
    n * (n-1).choose (m-1) = n.choose m * m := by
  have h := Nat.add_one_mul_choose_eq (n-1) (m-1)
  simpa [Nat.sub_add_cancel hn,Nat.sub_add_cancel hm] using h

/-- The second identity is also valid at m=1, where distinct-pair counts vanish. -/
theorem pair_inclusion_count_identity {n m : ℕ} (hn : 2 ≤ n) (hm : 1 ≤ m) :
    (if 2 ≤ m then (n-2).choose (m-2) else 0) * (n-1) =
      (m-1) * (n-1).choose (m-1) := by
  by_cases hm2 : 2 ≤ m
  · rw [if_pos hm2]
    have h := Nat.add_one_mul_choose_eq (n-2) (m-2)
    have hn' : n-2+1=n-1 := by omega
    have hm' : m-2+1=m-1 := by omega
    rw [hn',hm'] at h
    nlinarith
  · have heq : m=1 := by omega
    simp [heq]

end
end PaperC.V282.RandomDictionary
