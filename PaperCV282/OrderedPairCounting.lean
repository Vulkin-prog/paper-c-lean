import PaperCV282.KernelWindowEnergy

/-!
# Counting ordered pairs through their larger endpoint

The normalization keeps the larger and smaller coordinates. Its fibres
have at most two members, so both original orientations are counted
without any assumption that a canonical predicate is symmetric.
-/

namespace PaperC.V282.OrderedPairCounting

open scoped BigOperators

noncomputable section

/-- The larger and smaller coordinates, retaining equal-coordinate pairs harmlessly. -/
def normalizedPair (p : ℕ × ℕ) : ℕ × ℕ := (max p.1 p.2, min p.1 p.2)

/-- The actual larger starts in an arbitrary finite ordered-pair mask. -/
def largerStarts (s : Finset (ℕ × ℕ)) : Finset ℕ := s.image (fun p => max p.1 p.2)

/-- Distinct smaller partners of a fixed larger start, forgetting only orientation. -/
def smallerPartners (s : Finset (ℕ × ℕ)) (x : ℕ) : Finset ℕ :=
  (s.filter fun p => max p.1 p.2 = x).image (fun p => min p.1 p.2)

/-- Normalization loses at most the original orientation. -/
theorem normalizedPair_eq_iff (p q : ℕ × ℕ) :
    normalizedPair p = normalizedPair q ↔ p = q ∨ p = q.swap := by
  rcases p with ⟨a,b⟩
  rcases q with ⟨c,d⟩
  simp only [normalizedPair, Prod.mk.injEq, Prod.swap_prod_mk]
  omega

/-- Every normalized fibre is contained in the two possible orientations. -/
theorem card_normalized_fiber_le_two (s : Finset (ℕ × ℕ)) (q : ℕ × ℕ) :
    ((s.filter fun p => normalizedPair p = q).card : ℝ) ≤ 2 := by
  have hsub : (s.filter fun p => normalizedPair p = q) ⊆ {q, q.swap} := by
    intro p hp
    have heq := (Finset.mem_filter.mp hp).2
    have hcoords : (p.1 = q.1 ∧ p.2 = q.2) ∨ (p.1 = q.2 ∧ p.2 = q.1) := by
      have hc := congrArg Prod.fst heq
      have hd := congrArg Prod.snd heq
      simp only [normalizedPair] at hc hd
      omega
    rcases hcoords with h | h
    · exact Finset.mem_insert.mpr (Or.inl (Prod.ext h.1 h.2))
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (Prod.ext h.1 h.2)))
  have hp : ({q, q.swap} : Finset (ℕ × ℕ)).card ≤ 2 := by
    exact (Finset.card_insert_le _ _).trans (by simp)
  have hc := (Finset.card_le_card hsub).trans hp
  exact_mod_cast hc

/-- A common bound on all smaller-partner populations bounds every oriented fibre. -/
theorem card_larger_fiber_le_two_partners (s : Finset (ℕ × ℕ)) (x : ℕ) :
    ((s.filter fun p => max p.1 p.2 = x).card : ℝ) ≤
      2 * ((smallerPartners s x).card : ℝ) := by
  let t := s.filter fun p => max p.1 p.2 = x
  have hcolors : ∀ p ∈ t, min p.1 p.2 ∈ smallerPartners s x := by
    intro p hp
    exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
  have hfib : ∀ y ∈ smallerPartners s x,
      ((t.filter fun p => min p.1 p.2 = y).card : ℝ) ≤ 2 := by
    intro y hy
    have hsub : (t.filter fun p => min p.1 p.2 = y) ⊆
        s.filter fun p => normalizedPair p = (x,y) := by
      intro p hp
      obtain ⟨hpt, hpy⟩ := Finset.mem_filter.mp hp
      obtain ⟨hps,hpx⟩ := Finset.mem_filter.mp hpt
      exact Finset.mem_filter.mpr ⟨hps, Prod.ext hpx hpy⟩
    have hc : ((t.filter fun p => min p.1 p.2 = y).card : ℝ) ≤
        ((s.filter fun p => normalizedPair p = (x,y)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    exact hc.trans (card_normalized_fiber_le_two s (x,y))
  change (t.card : ℝ) ≤ _
  rw [Finset.card_eq_sum_card_fiberwise hcolors, Nat.cast_sum]
  calc
    _ ≤ ∑ _y ∈ smallerPartners s x, (2 : ℝ) := Finset.sum_le_sum hfib
    _ = _ := by simp [mul_comm]

/-- The factor two accounts for both orientations, without a symmetry premise on the mask. -/
theorem card_le_two_mul_largerStarts_mul
    (s : Finset (ℕ × ℕ)) (R : ℝ)
    (hpartners : ∀ x ∈ largerStarts s, ((smallerPartners s x).card : ℝ) ≤ R) :
    (s.card : ℝ) ≤ 2 * ((largerStarts s).card : ℝ) * R := by
  have hcolors : ∀ p ∈ s, max p.1 p.2 ∈ largerStarts s := by
    intro p hp
    exact Finset.mem_image.mpr ⟨p,hp,rfl⟩
  rw [Finset.card_eq_sum_card_fiberwise hcolors, Nat.cast_sum]
  calc
    _ ≤ ∑ _x ∈ largerStarts s, 2 * R := by
      apply Finset.sum_le_sum
      intro x hx
      exact (card_larger_fiber_le_two_partners s x).trans (by gcongr; exact hpartners x hx)
    _ = _ := by simp; ring

end
end PaperC.V282.OrderedPairCounting
