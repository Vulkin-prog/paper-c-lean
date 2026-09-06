import PaperCV282.MarkerDictionaryCount
import Mathlib.Data.Nat.Log

/-!
# An explicit family for every B at least eight

The integer marker length is floor(log_2(2B))+1. This choice may exceed
the ceiling by one at a power of two; its 2B < 2^k <= 4B bounds preserve
the advertised constant 32. No coding-theory theorem is assumed.
-/

namespace PaperC.V282.MarkerDictionaryAsymptotics

open WordOverlap WordOverlapSum MarkerDictionary MarkerDictionaryCount

noncomputable section

/-- An explicit integer marker length with the required power-of-two bounds. -/
def markerLength (B : ℕ) : ℕ := Nat.log 2 (2*B) + 1

theorem markerLength_pos (B : ℕ) : 1 ≤ markerLength B := by
  unfold markerLength
  omega

theorem markerLength_power_bounds {B : ℕ} (hB : 1 ≤ B) :
    2*B < 2^(markerLength B) ∧ 2^(markerLength B) ≤ 4*B := by
  constructor
  · exact Nat.lt_pow_succ_log_self (by decide : 1 < 2) (2*B)
  · have h := Nat.pow_log_le_self 2 (by omega : 2*B ≠ 0)
    unfold markerLength
    rw [pow_succ]
    omega

/-- From length eight, the fixed prefix, separator and final bit fit. -/
theorem twice_length_lt_power {B : ℕ} (hB : 8 ≤ B) : 2*B < 2^(B-2) := by
  induction B, hB using Nat.le_induction with
  | base => norm_num
  | succ B hB ih =>
    have hexp : B+1-2 = (B-2)+1 := by omega
    rw [hexp, pow_succ]
    omega

theorem markerLength_room {B : ℕ} (hB : 8 ≤ B) : markerLength B + 2 ≤ B := by
  have hlog := Nat.log_lt_of_lt_pow (by omega : 2*B ≠ 0) (twice_length_lt_power hB)
  unfold markerLength
  omega

/-- The effective family is empty below eight and explicit at every larger length. -/
def explicitDictionary (B : ℕ) : Finset (Fin B → F₂) :=
  if hB : 8 ≤ B then markerDictionary B (markerLength B) (markerLength_room hB) else ∅

theorem explicitDictionary_no_overlap {B : ℕ} (hB : 8 ≤ B)
    (w v : Fin B → F₂) (hw : w ∈ explicitDictionary B) (hv : v ∈ explicitDictionary B)
    (d : ℕ) (hdpos : 1 ≤ d) (hd : d < B) : ¬ Compatible d w v := by
  simp only [explicitDictionary, dif_pos hB] at hw hv
  exact markerDictionary_not_compatible B (markerLength B) (markerLength_room hB)
    (markerLength_pos B) w v hw hv d hdpos hd

theorem explicitDictionary_card_lower_bound {B : ℕ} (hB : 8 ≤ B) :
    (2 : ℝ)^B / (32*(B : ℝ)) ≤ (explicitDictionary B).card := by
  rw [explicitDictionary, dif_pos hB]
  obtain ⟨hlo,hhi⟩ := markerLength_power_bounds (by omega : 1 ≤ B)
  exact markerDictionary_card_lower_bound B (markerLength B) (markerLength_room hB) hlo.le hhi

theorem subdictionary_overlapWeight_eq_zero {B : ℕ} (hB : 8 ≤ B)
    (W : Finset (Fin B → F₂)) (hW : W ⊆ explicitDictionary B) : overlapWeight W = 0 := by
  simp only [explicitDictionary, dif_pos hB] at hW
  exact overlapWeight_eq_zero_of_subset B (markerLength B) (markerLength_room hB)
    (markerLength_pos B) W hW

/-- The two substantive claims of Corollary 5.4, with an explicit length threshold. -/
theorem corollary_five_four {B : ℕ} (hB : 8 ≤ B) :
    (2 : ℝ)^B / (32*(B : ℝ)) ≤ (explicitDictionary B).card ∧
    (∀ w ∈ explicitDictionary B, ∀ v ∈ explicitDictionary B,
      ∀ d : ℕ, 1 ≤ d → d < B → ¬ Compatible d w v) ∧
    (∀ W : Finset (Fin B → F₂), W ⊆ explicitDictionary B → overlapWeight W = 0) := by
  exact ⟨explicitDictionary_card_lower_bound hB,
    fun w hw v hv d hdpos hd => explicitDictionary_no_overlap hB w v hw hv d hdpos hd,
    fun W hW => subdictionary_overlapWeight_eq_zero hB W hW⟩

/-- Any requested integer cardinality below the displayed bound can be selected. -/
theorem exists_subdictionary_of_card_bound {B m : ℕ} (hB : 8 ≤ B)
    (hm : (m : ℝ) ≤ (2 : ℝ)^B / (32*(B : ℝ))) :
    ∃ W : Finset (Fin B → F₂), W ⊆ explicitDictionary B ∧ W.card = m ∧
      overlapWeight W = 0 := by
  have hcard : m ≤ (explicitDictionary B).card := by
    exact_mod_cast hm.trans (explicitDictionary_card_lower_bound hB)
  obtain ⟨W,hW,hsize⟩ := Finset.exists_subset_card_eq hcard
  exact ⟨W,hW,hsize,subdictionary_overlapWeight_eq_zero hB W hW⟩

end
end PaperC.V282.MarkerDictionaryAsymptotics
