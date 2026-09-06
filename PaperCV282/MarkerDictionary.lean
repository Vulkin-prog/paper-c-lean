import PaperCV282.WordOverlapSum

/-!
# Explicit binary marker words

The family consists of 0^k 1 u 1, with u containing no block of k zeros.
Its no-overlap property includes a word paired with itself.
-/

namespace PaperC.V282.MarkerDictionary

open WordOverlap WordOverlapSum

noncomputable section

/-- The middle word contains no complete run of k zeros. -/
def AvoidsZeroBlock {n : ℕ} (k : ℕ) (u : Fin n → F₂) : Prop :=
  ∀ j : ℕ, ∀ hj : j+k ≤ n, ¬ ∀ i : Fin k, u ⟨j+i.val, by omega⟩ = 0

/-- Assemble the prescribed marker, separator, middle and final one. -/
def wordOfMiddle (B k : ℕ) (hB : k+2 ≤ B) (u : Fin (B-k-2) → F₂) :
    Fin B → F₂ :=
  fun i => if hi : i.val < k then 0 else if heq : i.val = k then 1 else
    if hlast : i.val+1 = B then 1 else u ⟨i.val-k-1, by have hb := i.isLt; omega⟩

/-- A finite effective filter of all middle words. -/
def admissibleMiddles (n k : ℕ) : Finset (Fin n → F₂) := by
  classical
  exact Finset.univ.filter (AvoidsZeroBlock k)

/-- The explicit family of marker words of total length B. -/
def markerDictionary (B k : ℕ) (hB : k+2 ≤ B) : Finset (Fin B → F₂) := by
  classical
  exact (admissibleMiddles (B-k-2) k).image (wordOfMiddle B k hB)

theorem wordOfMiddle_prefix (B k : ℕ) (hB : k+2 ≤ B)
    (u : Fin (B-k-2) → F₂) (i : Fin B) (hi : i.val < k) :
    wordOfMiddle B k hB u i = 0 := by simp [wordOfMiddle, hi]

theorem wordOfMiddle_separator (B k : ℕ) (hB : k+2 ≤ B)
    (u : Fin (B-k-2) → F₂) :
    wordOfMiddle B k hB u ⟨k,by omega⟩ = 1 := by simp [wordOfMiddle]

theorem wordOfMiddle_last (B k : ℕ) (hB : k+2 ≤ B)
    (u : Fin (B-k-2) → F₂) :
    wordOfMiddle B k hB u ⟨B-1,by omega⟩ = 1 := by
  simp [wordOfMiddle, show ¬B-1<k by omega, show B-1≠k by omega,
    show B-1+1=B by omega]

theorem wordOfMiddle_middle (B k : ℕ) (hB : k+2 ≤ B)
    (u : Fin (B-k-2) → F₂) (i : Fin (B-k-2)) :
    wordOfMiddle B k hB u ⟨k+1+i.val,by omega⟩ = u i := by
  have hi := i.isLt
  simp [wordOfMiddle, show ¬k+1+i.val<k by omega,
    show k+1+i.val≠k by omega, show k+1+i.val+1≠B by omega]
  congr 1
  apply Fin.ext
  change k+1+i.val-k-1 = i.val
  omega

theorem wordOfMiddle_injective (B k : ℕ) (hB : k+2 ≤ B) :
    Function.Injective (wordOfMiddle B k hB) := by
  intro u v huv
  funext i
  have h := congrFun huv ⟨k+1+i.val,by omega⟩
  simpa only [wordOfMiddle_middle] using h

/-- The only possible complete marker block begins at the first letter. -/
theorem wordOfMiddle_no_later_zeroBlock (B k : ℕ) (hB : k+2 ≤ B) (hk : 1 ≤ k)
    (u : Fin (B-k-2) → F₂) (hu : AvoidsZeroBlock k u)
    (j : ℕ) (hjpos : 0 < j) (hj : j+k ≤ B) :
    ¬ ∀ i : Fin k, wordOfMiddle B k hB u ⟨j+i.val,by omega⟩ = 0 := by
  intro hzero
  by_cases hjk : j ≤ k
  · have hi : k-j < k := by omega
    have h := hzero ⟨k-j,hi⟩
    have heq : j+(k-j)=k := by omega
    simp only [heq, wordOfMiddle_separator] at h
    exact one_ne_zero h
  · by_cases hjend : j+k = B
    · have h := hzero ⟨k-1,by omega⟩
      have heq : j+(k-1)=B-1 := by omega
      simp only [heq, wordOfMiddle_last] at h
      exact one_ne_zero h
    · apply hu (j-k-1) (by omega)
      intro i
      have hi := i.isLt
      have h := hzero i
      have hmiddle := wordOfMiddle_middle B k hB u
        ⟨j-k-1+i.val,by omega⟩
      have heq : k+1+(j-k-1+i.val)=j+i.val := by omega
      simp only [heq] at hmiddle
      exact hmiddle.symm.trans h

/-- Two marker words have no directed proper overlap, even if equal. -/
theorem wordOfMiddle_not_compatible (B k : ℕ) (hB : k+2 ≤ B) (hk : 1 ≤ k)
    (u v : Fin (B-k-2) → F₂) (hu : AvoidsZeroBlock k u)
    (d : ℕ) (hdpos : 1 ≤ d) (hd : d < B) :
    ¬ Compatible d (wordOfMiddle B k hB u) (wordOfMiddle B k hB v) := by
  intro hc
  by_cases hshort : B-d ≤ k
  · have hi : B-1-d < B := by omega
    have h := hc ⟨B-1-d,hi⟩ (by simp only; omega)
    have heq : d+(B-1-d)=B-1 := by omega
    simp only [heq, wordOfMiddle_last] at h
    have hz := wordOfMiddle_prefix B k hB v ⟨B-1-d,hi⟩ (by simp only; omega)
    exact one_ne_zero (h.trans hz)
  · apply wordOfMiddle_no_later_zeroBlock B k hB hk u hu d (by omega) (by omega)
    intro i
    have hi := i.isLt
    exact (hc ⟨i.val,by omega⟩ (by simp only; omega)).trans
      (wordOfMiddle_prefix B k hB v ⟨i.val,by omega⟩ hi)

theorem markerDictionary_not_compatible (B k : ℕ) (hB : k+2 ≤ B) (hk : 1 ≤ k)
    (w v : Fin B → F₂) (hw : w ∈ markerDictionary B k hB)
    (hv : v ∈ markerDictionary B k hB) (d : ℕ) (hdpos : 1 ≤ d) (hd : d < B) :
    ¬ Compatible d w v := by
  classical
  obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hw
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hv
  exact wordOfMiddle_not_compatible B k hB hk u v
    (Finset.mem_filter.mp hu).2 d hdpos hd

/-- Every subdictionary has exactly zero directed overlap weight. -/
theorem overlapWeight_eq_zero_of_subset (B k : ℕ) (hB : k+2 ≤ B) (hk : 1 ≤ k)
    (W : Finset (Fin B → F₂)) (hW : W ⊆ markerDictionary B k hB) :
    overlapWeight W = 0 := by
  classical
  unfold overlapWeight
  have hsum : (∑ w ∈ W, ∑ v ∈ W, ∑ d ∈ Finset.Icc 1 (B-1),
      directedOverlapWeight d w v) = 0 := by
    apply Finset.sum_eq_zero
    intro w hw
    apply Finset.sum_eq_zero
    intro v hv
    apply Finset.sum_eq_zero
    intro d hd
    obtain ⟨hdpos,hdtop⟩ := Finset.mem_Icc.mp hd
    simp [directedOverlapWeight,
      markerDictionary_not_compatible B k hB hk w v (hW hw) (hW hv) d hdpos (by omega)]
  rw [hsum, zero_div]

theorem card_markerDictionary (B k : ℕ) (hB : k+2 ≤ B) :
    (markerDictionary B k hB).card = (admissibleMiddles (B-k-2) k).card := by
  classical
  exact Finset.card_image_of_injective _ (wordOfMiddle_injective B k hB)

end
end PaperC.V282.MarkerDictionary
