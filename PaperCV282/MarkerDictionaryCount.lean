import PaperCV282.MarkerDictionary

/-! # Counting the actual marker filter by a union bound -/

namespace PaperC.V282.MarkerDictionaryCount

open MarkerDictionary
open scoped BigOperators

noncomputable section

/-- Middle words with a specified complete zero block. -/
def zeroBlockWords (n k j : ℕ) : Finset (Fin n → F₂) := by
  classical
  exact Finset.univ.filter fun u => j+k ≤ n ∧
    ∀ i : Fin n, j ≤ i.val → i.val < j+k → u i = 0

/-- Delete the coordinates occupied by a specified zero block. -/
def eraseBlock (n k j : ℕ) (hj : j+k ≤ n) (u : Fin n → F₂) : Fin (n-k) → F₂ :=
  fun i => if hi : i.val < j then u ⟨i.val,by omega⟩ else u ⟨i.val+k,by omega⟩

theorem eraseBlock_injective_on_zeroBlockWords (n k j : ℕ) (hj : j+k ≤ n) :
    Set.InjOn (eraseBlock n k j hj) (zeroBlockWords n k j : Set (Fin n → F₂)) := by
  classical
  intro u hu v hv heq
  have huzu := (Finset.mem_filter.mp hu).2.2
  have hvzu := (Finset.mem_filter.mp hv).2.2
  funext i
  have hi := i.isLt
  by_cases hij : i.val < j
  · have h := congrFun heq ⟨i.val,by omega⟩
    simpa [eraseBlock, hij] using h
  · by_cases hik : i.val < j+k
    · rw [huzu i (by omega) hik, hvzu i (by omega) hik]
    · have h := congrFun heq ⟨i.val-k,by omega⟩
      have hsub : ¬i.val-k<j := by omega
      have hadd : i.val-k+k=i.val := by omega
      simpa [eraseBlock, hsub, hadd] using h

/-- At most 2^(n-k) choices survive a fixed complete zero block. -/
theorem card_zeroBlockWords_le (n k j : ℕ) :
    (zeroBlockWords n k j).card ≤ 2^(n-k) := by
  classical
  by_cases hj : j+k ≤ n
  · have h := Finset.card_le_card_of_injOn (eraseBlock n k j hj)
      (s := zeroBlockWords n k j) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _) (eraseBlock_injective_on_zeroBlockWords n k j hj)
    simpa [Fintype.card_fun, F₂] using h
  · simp [zeroBlockWords, hj]

/-- Every excluded middle word is accounted for at an actual block position. -/
theorem excludedMiddles_subset_union (n k : ℕ) :
    Finset.univ \ admissibleMiddles n k ⊆
      (Finset.range (n+1)).biUnion (zeroBlockWords n k) := by
  classical
  intro u hu
  have hnot : ¬ AvoidsZeroBlock k u := by
    simpa [admissibleMiddles] using (Finset.mem_sdiff.mp hu).2
  unfold AvoidsZeroBlock at hnot
  push Not at hnot
  obtain ⟨j,hj,hzero⟩ := hnot
  apply Finset.mem_biUnion.mpr
  refine ⟨j, Finset.mem_range.mpr (by omega), ?_⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, hj, ?_⟩
  intro i hij hik
  have h := hzero ⟨i.val-j,by omega⟩
  have heq : j+(i.val-j)=i.val := by omega
  simpa only [heq] using h

theorem card_excludedMiddles_le (n k : ℕ) :
    (Finset.univ \ admissibleMiddles n k).card ≤ (n+1)*2^(n-k) := by
  apply (Finset.card_le_card (excludedMiddles_subset_union n k)).trans
  apply (Finset.card_biUnion_le).trans
  calc
    _ ≤ ∑ j ∈ Finset.range (n+1), 2^(n-k) := by
      exact Finset.sum_le_sum fun j _ => card_zeroBlockWords_le n k j
    _ = _ := by simp

/-- If the marker exceeds the middle length, every middle word is admissible. -/
theorem admissibleMiddles_eq_univ_of_lt {n k : ℕ} (hkn : n < k) :
    admissibleMiddles n k = Finset.univ := by
  classical
  ext u
  simp only [admissibleMiddles, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
  intro j hj
  omega

/-- The union bound retains at least one half of all middle words. -/
theorem two_pow_le_two_mul_card_admissibleMiddles (n k : ℕ)
    (hsmall : 2*(n+1) ≤ 2^k) :
    2^n ≤ 2*(admissibleMiddles n k).card := by
  classical
  by_cases hkn : k ≤ n
  · have hcount := card_excludedMiddles_le n k
    have hsplit := Finset.card_sdiff_add_card_eq_card
      (Finset.subset_univ (admissibleMiddles n k))
    have htotal : (Finset.univ : Finset (Fin n → F₂)).card = 2^n := by
      simp [F₂]
    rw [htotal] at hsplit
    have hpow : 2^k * 2^(n-k) = 2^n := by rw [← pow_add, Nat.add_sub_of_le hkn]
    have htwobad : 2 * (Finset.univ \ admissibleMiddles n k).card ≤ 2^n := by
      calc
        _ ≤ 2 * ((n+1)*2^(n-k)) := Nat.mul_le_mul_left 2 hcount
        _ = (2*(n+1))*2^(n-k) := by ring
        _ ≤ 2^k * 2^(n-k) := Nat.mul_le_mul_right _ hsmall
        _ = 2^n := hpow
    omega
  · rw [admissibleMiddles_eq_univ_of_lt (by omega)]
    simp [F₂]

/-- A finite lower bound for the real, explicitly filtered marker family. -/
theorem markerDictionary_card_lower_bound (B k : ℕ) (hB : k+2 ≤ B)
    (hlow : 2*B ≤ 2^k) (hhigh : 2^k ≤ 4*B) :
    (2 : ℝ)^B / (32*(B : ℝ)) ≤ (markerDictionary B k hB).card := by
  have hhalf := two_pow_le_two_mul_card_admissibleMiddles (B-k-2) k (by omega)
  rw [← card_markerDictionary B k hB] at hhalf
  have hexp : 2^B = 4*2^k*2^(B-k-2) := by
    have heq : B = k+2+(B-k-2) := by omega
    conv_lhs => rw [heq]
    rw [pow_add, pow_add]
    ring
  have hnat : 2^B ≤ 32*B*(markerDictionary B k hB).card := by
    rw [hexp]
    nlinarith [Nat.mul_le_mul hhigh hhalf]
  have hreal : (2 : ℝ)^B ≤ (32*(B : ℝ))*(markerDictionary B k hB).card := by
    exact_mod_cast hnat
  have hBpos : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  exact (div_le_iff₀ (by positivity : (0 : ℝ) < 32*(B : ℝ))).mpr (by nlinarith [hreal])

end
end PaperC.V282.MarkerDictionaryCount
