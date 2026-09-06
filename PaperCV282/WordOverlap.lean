import PaperCV282.InfiniteWordTransfer

/-!
# Directed word overlaps and their actual union

All letters are prescribed. The occurrence starting at x uses x-1+j.
Compatibility is directed and includes self-overlaps when the words agree.
-/

namespace PaperC.V282.WordOverlap

open WindowValues

/-- The suffix of the first word agrees with the prefix of the second. -/
def Compatible {B : ℕ} (d : ℕ) (w v : Fin B → F₂) : Prop :=
  ∀ j : Fin B, ∀ h : d + j.val < B, w ⟨d + j.val, h⟩ = v j

/-- A word occurrence in any deterministic sequence, with the article's left border. -/
def Occurs {B : ℕ} (f : ℕ → F₂) (x : ℕ) (w : Fin B → F₂) : Prop :=
  ∀ i : Fin B, f (vertex x B i) = w i

/-- The union word uses the first word, then the uncovered tail of the second. -/
def mergedWord {B : ℕ} (d : ℕ) (hd : d ≤ B) (w v : Fin B → F₂) :
    Fin (B + d) → F₂ :=
  fun i => if h : i.val < B then w ⟨i.val, h⟩ else
    v ⟨i.val - d, by have hi := i.isLt; omega⟩

theorem mergedWord_prefix {B d : ℕ} (hd : d ≤ B) (w v : Fin B → F₂)
    (i : Fin B) : mergedWord d hd w v ⟨i.val, by omega⟩ = w i := by
  simp [mergedWord, i.isLt]

theorem mergedWord_suffix {B d : ℕ} (hd : d ≤ B) (w v : Fin B → F₂)
    (hcompat : Compatible d w v) (j : Fin B) :
    mergedWord d hd w v ⟨d + j.val, by omega⟩ = v j := by
  by_cases h : d + j.val < B
  · simpa [mergedWord, h] using hcompat j h
  · simp [mergedWord, h]

/-- Simultaneous occurrences force the directed compatibility constraint. -/
theorem compatible_of_occurs {B d x : ℕ} (hx : 1 ≤ x)
    (f : ℕ → F₂) (w v : Fin B → F₂)
    (hw : Occurs f x w) (hv : Occurs f (x + d) v) : Compatible d w v := by
  intro j hj
  have hleft := hw ⟨d + j.val, hj⟩
  have hright := hv j
  have heq : vertex x B ⟨d + j.val, hj⟩ = vertex (x + d) B j := by
    simp only [vertex]
    omega
  rw [heq] at hleft
  exact hleft.symm.trans hright

/-- Two compatible overlapping occurrences are exactly one occurrence on their union. -/
theorem occurs_pair_iff {B d x : ℕ} (hx : 1 ≤ x) (hd : d ≤ B)
    (f : ℕ → F₂) (w v : Fin B → F₂) :
    Occurs f x w ∧ Occurs f (x + d) v ↔
      Compatible d w v ∧ Occurs f x (mergedWord d hd w v) := by
  constructor
  · rintro ⟨hw,hv⟩
    refine ⟨compatible_of_occurs hx f w v hw hv, ?_⟩
    intro i
    by_cases hi : i.val < B
    · simpa [mergedWord, hi, vertex] using hw ⟨i.val,hi⟩
    · have hsub : i.val - d < B := by have hb := i.isLt; omega
      have hcoord : vertex x (B + d) i = vertex (x + d) B ⟨i.val-d,hsub⟩ := by
        simp only [vertex]
        have hb := i.isLt
        omega
      simpa [mergedWord, hi, hcoord] using hv ⟨i.val-d,hsub⟩
  · rintro ⟨hcompat,hunion⟩
    constructor
    · intro i
      have h := hunion ⟨i.val,by omega⟩
      rw [mergedWord_prefix] at h
      exact h
    · intro j
      have h := hunion ⟨d+j.val,by omega⟩
      rw [mergedWord_suffix hd w v hcompat] at h
      have hcoord : vertex x (B+d) ⟨d+j.val,by omega⟩ = vertex (x+d) B j := by
        simp only [vertex]
        omega
      rwa [hcoord] at h

/-- Distinct prescribed words cannot occur at the same site. -/
theorem not_occurs_pair_same_site {B x : ℕ} (f : ℕ → F₂)
    (w v : Fin B → F₂) (hne : w ≠ v) : ¬(Occurs f x w ∧ Occurs f x v) := by
  rintro ⟨hw,hv⟩
  apply hne
  funext i
  exact (hw i).symm.trans (hv i)

/-- A property valid on each support is valid on the overlapping union. -/
theorem union_vertex_property {B d x : ℕ} (hx : 1 ≤ x) (hd : d ≤ B)
    (P : ℕ → Prop) (hw : ∀ i : Fin B, P (vertex x B i))
    (hv : ∀ j : Fin B, P (vertex (x+d) B j)) :
    ∀ i : Fin (B+d), P (vertex x (B+d) i) := by
  intro i
  by_cases hi : i.val < B
  · exact hw ⟨i.val,hi⟩
  · have hsub : i.val-d < B := by have hb := i.isLt; omega
    have hcoord : vertex x (B+d) i = vertex (x+d) B ⟨i.val-d,hsub⟩ := by
      simp only [vertex]
      have hb := i.isLt
      omega
    rw [hcoord]
    exact hv ⟨i.val-d,hsub⟩

end PaperC.V282.WordOverlap
