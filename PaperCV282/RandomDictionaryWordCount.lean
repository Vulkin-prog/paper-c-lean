import PaperCV282.WordOverlapSum
import Mathlib.Data.Finset.Powerset

/-!
# Exact word counts behind uniform dictionaries

A self-overlap at displacement d is a d-periodic word determined by its
first d letters. For a fixed first word, exactly d letters of a compatible
second word remain free. Both statements concern actual binary words.
-/
namespace PaperC.V282.RandomDictionaryWordCount

open WordOverlap WordOverlapSum
open scoped BigOperators

noncomputable section

@[reducible]
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

def selfOverlapWords (B d : ℕ) : Finset (Fin B → F₂) :=
  Finset.univ.filter (fun w => Compatible d w w)

def compatibleSecondWords {B : ℕ} (d : ℕ) (w : Fin B → F₂) : Finset (Fin B → F₂) :=
  Finset.univ.filter (Compatible d w)

/-- Repeat the first d letters, with the actual residue of every index. -/
def periodicWord (B d : ℕ) (hd : 0 < d) (u : Fin d → F₂) : Fin B → F₂ :=
  fun i => u ⟨i.val % d,Nat.mod_lt _ hd⟩

theorem periodicWord_compatible (B d : ℕ) (hd : 0 < d) (u : Fin d → F₂) :
    Compatible d (periodicWord B d hd u) (periodicWord B d hd u) := by
  intro j hj
  simp [periodicWord]

theorem compatible_self_eq_mod {B d : ℕ} (hd : 0 < d) (hdB : d ≤ B)
    (w : Fin B → F₂) (hw : Compatible d w w) (i : Fin B) :
    w i = w ⟨i.val % d,(Nat.mod_lt _ hd).trans_le hdB⟩ := by
  have hrec : ∀ n : ℕ, ∀ hn : n < B,
      w ⟨n,hn⟩ = w ⟨n % d,(Nat.mod_lt _ hd).trans_le hdB⟩ := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      by_cases hnd : n < d
      · simp [Nat.mod_eq_of_lt hnd]
      · have hdn : d ≤ n := by omega
        have hlt : n-d < n := by omega
        have hstep := hw ⟨n-d,by omega⟩ (by simp only; omega)
        have heq : d+(n-d)=n := by omega
        simp only [heq] at hstep
        rw [hstep,ih (n-d) hlt (by omega)]
        congr 1
        apply Fin.ext
        exact (Nat.mod_eq_sub_mod hdn).symm
  exact hrec i.val i.isLt

theorem periodicWord_injective {B d : ℕ} (hd : 0 < d) (hdB : d ≤ B) :
    Function.Injective (periodicWord B d hd) := by
  intro u v h
  funext i
  have heq := congrFun h ⟨i.val,i.isLt.trans_le hdB⟩
  simpa [periodicWord,Nat.mod_eq_of_lt i.isLt] using heq

/-- Exactly 2^d words have a self-overlap at the given proper positive shift. -/
theorem card_selfOverlapWords {B d : ℕ} (hd : 0 < d) (hdB : d ≤ B) :
    (selfOverlapWords B d).card = 2^d := by
  have heq : selfOverlapWords B d = Finset.univ.image (periodicWord B d hd) := by
    ext w
    simp only [selfOverlapWords,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_image]
    constructor
    · intro hw
      let u : Fin d → F₂ := fun i => w ⟨i.val,i.isLt.trans_le hdB⟩
      refine ⟨u,?_⟩
      funext i
      exact (compatible_self_eq_mod hd hdB w hw i).symm
    · rintro ⟨u,rfl⟩
      exact periodicWord_compatible B d hd u
  rw [heq,Finset.card_image_of_injective _ (periodicWord_injective hd hdB)]
  simp [F₂]

/-- Complete the forced prefix of the second word with its freely chosen d-letter tail. -/
def completedSecondWord {B : ℕ} (d : ℕ) (hd : d ≤ B) (w : Fin B → F₂)
    (u : Fin d → F₂) : Fin B → F₂ :=
  fun i => if hi : i.val < B-d then w ⟨d+i.val,by omega⟩
    else u ⟨i.val-(B-d),by have hb := i.isLt; omega⟩

theorem completedSecondWord_compatible {B d : ℕ} (hd : d ≤ B)
    (w : Fin B → F₂) (u : Fin d → F₂) :
    Compatible d w (completedSecondWord d hd w u) := by
  intro j hj
  simp [completedSecondWord,show j.val < B-d by omega]

theorem completedSecondWord_injective {B d : ℕ} (hd : d ≤ B)
    (w : Fin B → F₂) : Function.Injective (completedSecondWord d hd w) := by
  intro u v huv
  funext i
  have heq := congrFun huv ⟨B-d+i.val,by omega⟩
  simpa [completedSecondWord,show ¬B-d+i.val<B-d by omega] using heq

/-- The complete compatible-prefix fibre contains exactly 2^d second words. -/
theorem card_compatibleSecondWords {B d : ℕ} (hd : d ≤ B) (w : Fin B → F₂) :
    (compatibleSecondWords d w).card = 2^d := by
  have heq : compatibleSecondWords d w = Finset.univ.image (completedSecondWord d hd w) := by
    ext v
    simp only [compatibleSecondWords,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_image]
    constructor
    · intro hv
      let u : Fin d → F₂ := fun i => v ⟨B-d+i.val,by omega⟩
      refine ⟨u,?_⟩
      funext i
      by_cases hi : i.val < B-d
      · exact (by simpa [completedSecondWord,hi] using hv i (by omega))
      · simp [completedSecondWord,hi,u,show B-d+(i.val-(B-d))=i.val by omega]
    · rintro ⟨u,rfl⟩
      exact completedSecondWord_compatible hd w u
  rw [heq,Finset.card_image_of_injective _ (completedSecondWord_injective hd w)]
  simp [F₂]

/-- Requiring the second word to be different cannot enlarge its true prefix fibre. -/
theorem card_distinct_compatibleSecondWords_le {B d : ℕ} (hd : d ≤ B) (w : Fin B → F₂) :
    ((compatibleSecondWords d w).erase w).card ≤ 2^d := by
  exact (Finset.card_le_card (Finset.erase_subset _ _)).trans_eq (card_compatibleSecondWords hd w)

/-- At each shift, the total diagonal compatibility weight is exactly one. -/
theorem sum_self_directedOverlapWeight {B d : ℕ} (hd : 0 < d) (hdB : d ≤ B) :
    (∑ w : Fin B → F₂, directedOverlapWeight d w w) = 1 := by
  unfold directedOverlapWeight
  rw [← Finset.sum_filter]
  change (∑ w ∈ selfOverlapWords B d, 1 / (2 : ℝ)^d) = 1
  simp only [Finset.sum_const,nsmul_eq_mul,card_selfOverlapWords hd hdB]
  push_cast
  field_simp

/-- For each first word, the total compatibility weight over second words is exactly one. -/
theorem sum_directedOverlapWeight_second {B d : ℕ} (hd : d ≤ B) (w : Fin B → F₂) :
    (∑ v : Fin B → F₂, directedOverlapWeight d w v) = 1 := by
  unfold directedOverlapWeight
  rw [← Finset.sum_filter]
  change (∑ v ∈ compatibleSecondWords d w, 1 / (2 : ℝ)^d) = 1
  simp only [Finset.sum_const,nsmul_eq_mul,card_compatibleSecondWords hd w]
  push_cast
  field_simp

/-- All ordered compatibility weights total 2^B. -/
theorem sum_pair_directedOverlapWeight {B d : ℕ} (hd : d ≤ B) :
    (∑ w : Fin B → F₂, ∑ v : Fin B → F₂, directedOverlapWeight d w v) = (2 : ℝ)^B := by
  simp_rw [sum_directedOverlapWeight_second hd]
  simp [F₂]

/-- Removing the diagonal gives the exact distinct-pair weight 2^B-1. -/
theorem sum_distinct_directedOverlapWeight {B d : ℕ} (hd : 0 < d) (hdB : d ≤ B) :
    (∑ w : Fin B → F₂, ∑ v : Fin B → F₂, if w ≠ v then directedOverlapWeight d w v else 0) =
      (2 : ℝ)^B - 1 := by
  have hsplit : (∑ w : Fin B → F₂, ∑ v : Fin B → F₂, directedOverlapWeight d w v) =
      (∑ w : Fin B → F₂, directedOverlapWeight d w w) +
      (∑ w : Fin B → F₂, ∑ v : Fin B → F₂, if w ≠ v then directedOverlapWeight d w v else 0) := by
    calc
      _ = ∑ w : Fin B → F₂, (directedOverlapWeight d w w +
          ∑ v : Fin B → F₂, if w ≠ v then directedOverlapWeight d w v else 0) := by
        apply Finset.sum_congr rfl
        intro w hw
        have he (v : Fin B → F₂) : directedOverlapWeight d w v =
            (if w = v then directedOverlapWeight d w w else 0) +
              (if w ≠ v then directedOverlapWeight d w v else 0) := by
          by_cases h : w = v <;> simp [h]
        calc
          _ = ∑ v : Fin B → F₂, ((if w = v then directedOverlapWeight d w w else 0) +
              (if w ≠ v then directedOverlapWeight d w v else 0)) :=
            Finset.sum_congr rfl (fun v _ => he v)
          _ = _ := by rw [Finset.sum_add_distrib]; simp
      _ = _ := Finset.sum_add_distrib
  rw [sum_pair_directedOverlapWeight hdB,sum_self_directedOverlapWeight hd hdB] at hsplit
  linarith

end
end PaperC.V282.RandomDictionaryWordCount
