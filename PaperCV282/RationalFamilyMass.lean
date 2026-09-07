import PaperCV282.RationalLowerBounds

/-!
# Summing both orientations of the rational lower-bound families

Each positive parameter supplies two distinct ordered pairs. Their exact
cardinality and the embedded rational codes yield lower bounds on every
pair mask containing the family.
-/

namespace PaperC.V282.RationalFamilyMass

open Affine HostRankMass RationalLowerBounds
open scoped BigOperators

noncomputable section

/-- Both orientations of a rational family, parameterized by an explicit finite set. -/
def orientedPairs (a b : ℕ) (T : Finset ℕ) : Finset (ℕ × ℕ) :=
  T.image (fun t => (a * t, b * t)) ∪ T.image (fun t => (b * t, a * t))

/-- Literal membership in either orientation. -/
theorem mem_orientedPairs (a b : ℕ) (T : Finset ℕ) (xy : ℕ × ℕ) :
    xy ∈ orientedPairs a b T ↔
      (∃ t ∈ T, (a * t, b * t) = xy) ∨ (∃ t ∈ T, (b * t, a * t) = xy) := by
  simp [orientedPairs]

/-- Distinct positive slopes and positive parameters yield exactly two pairs per parameter. -/
theorem card_orientedPairs {a b : ℕ} (T : Finset ℕ)
    (ha : 0 < a) (hab : a < b) (hT : ∀ t ∈ T, 0 < t) :
    (orientedPairs a b T).card = 2 * T.card := by
  have hb : 0 < b := ha.trans hab
  have hi : Function.Injective (fun t : ℕ => (a * t, b * t)) := by
    intro t u heq
    have hh := congrArg Prod.fst heq
    exact Nat.eq_of_mul_eq_mul_left ha hh
  have hj : Function.Injective (fun t : ℕ => (b * t, a * t)) := by
    intro t u heq
    have hh := congrArg Prod.fst heq
    exact Nat.eq_of_mul_eq_mul_left hb hh
  have hdisjoint : Disjoint
      (T.image (fun t => (a * t, b * t))) (T.image (fun t => (b * t, a * t))) := by
    apply Finset.disjoint_left.mpr
    intro xy hleft hright
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hleft
    obtain ⟨u, hu, heq⟩ := Finset.mem_image.mp hright
    have htu := congrArg Prod.fst heq
    have hut := congrArg Prod.snd heq
    have htpos := hT t ht
    have hupos := hT u hu
    have htlt : a * t < b * t := Nat.mul_lt_mul_of_pos_right hab htpos
    have hult : a * u < b * u := Nat.mul_lt_mul_of_pos_right hab hupos
    change b * u = a * t at htu
    change a * u = b * t at hut
    omega
  simp only [orientedPairs, Finset.card_union_of_disjoint hdisjoint,
    Finset.card_image_of_injective T hi, Finset.card_image_of_injective T hj]
  omega

/-- A finite lower bound from a dimension bound on both orientations. -/
theorem cardinal_mul_codeWeight_le_relationWeightMass
    {K L a b e : ℕ} (T : Finset ℕ) (s : Finset (ℕ × ℕ))
    (ha : 0 < a) (hab : a < b) (hT : ∀ t ∈ T, 0 < t)
    (hsubset : orientedPairs a b T ⊆ s)
    (hforward : ∀ t ∈ T, e ≤ relationRho (twoStartSystem K (a * t) (b * t) L))
    (hreverse : ∀ t ∈ T, e ≤ relationRho (twoStartSystem K (b * t) (a * t) L)) :
    2 * T.card * (2 ^ e - 1) ≤ relationWeightMass K L s := by
  have hdim : ∀ xy ∈ orientedPairs a b T,
      e ≤ relationRho (twoStartSystem K xy.1 xy.2 L) := by
    intro xy hxy
    rcases (mem_orientedPairs a b T xy).mp hxy with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
    · exact hforward t ht
    · exact hreverse t ht
  have hfinite : (orientedPairs a b T).card * (2 ^ e - 1) ≤
      relationWeightMass K L (orientedPairs a b T) := by
    calc
      _ = ∑ _xy ∈ orientedPairs a b T, (2 ^ e - 1) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun xy hxy =>
        Nat.sub_le_sub_right (Nat.pow_le_pow_right (by omega) (hdim xy hxy)) 1)
  rw [card_orientedPairs T ha hab hT] at hfinite
  exact hfinite.trans (relationWeightMass_mono K L hsubset)

/-- Equation (3.23)'s code factor summed over both orientations of any admissible parameter set. -/
theorem half_family_lower_bound (K L : ℕ) (T : Finset ℕ) (s : Finset (ℕ × ℕ))
    (hT : ∀ t ∈ T, 2 ≤ t) (hsubset : orientedPairs 1 2 T ⊆ s) :
    2 * T.card * (2 ^ ((L + 1) / 2 - 1) - 1) ≤ relationWeightMass K L s := by
  apply cardinal_mul_codeWeight_le_relationWeightMass T s (by omega) (by omega)
    (fun t ht => by have := hT t ht; omega) hsubset
  · intro t ht
    simpa only [one_mul] using half_length_sub_one_le_relationRho K L t (hT t ht)
  · intro t ht
    simpa only [one_mul] using half_length_sub_one_le_relationRho_reverse K L t (hT t ht)

/-- Equation (3.22)'s code factor summed over both orientations of any admissible parameter set. -/
theorem third_family_lower_bound (K L : ℕ) (T : Finset ℕ) (s : Finset (ℕ × ℕ))
    (hT : ∀ t ∈ T, 1 ≤ t) (hsubset : orientedPairs 2 3 T ⊆ s) :
    2 * T.card * (2 ^ ((L + 2) / 3 - 1) - 1) ≤ relationWeightMass K L s := by
  apply cardinal_mul_codeWeight_le_relationWeightMass T s (by omega) (by omega)
    (fun t ht => by have := hT t ht; omega) hsubset
  · intro t ht
    exact third_length_sub_one_le_relationRho K L t (hT t ht)
  · intro t ht
    exact third_length_sub_one_le_relationRho_reverse K L t (hT t ht)

end
end PaperC.V282.RationalFamilyMass
