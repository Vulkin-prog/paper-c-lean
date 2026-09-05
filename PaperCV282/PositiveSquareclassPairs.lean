import PaperCV282.PolynomialPellCount
import PaperC.Diophantine.TerminalPartnerPell

/-!
# Two positive square roots with fixed squareclasses

Distinct squareclasses give the nonsquare Pell case. Equal squareclasses
are counted through the positive divisor `u+v` of the nonzero difference.
The two branches give one uniform polynomial-height result.
-/

namespace PaperC.V282.PositiveSquareclassPairs

open PellInput PolynomialPellCount DivisorSubpolynomial

noncomputable section

/-- Positive roots in an explicit height box for a fixed difference equation. -/
def positiveSquareclassBox (A C H : ℕ) (e : ℤ) (s : ℕ × ℕ) : Prop :=
  0 < s.1 ∧ 0 < s.2 ∧ s.1 ≤ H ∧ s.2 ≤ H ∧
    (A : ℤ) * (s.1 : ℤ) ^ 2 - (C : ℤ) * (s.2 : ℤ) ^ 2 = e

/-- Equal squareclasses have at most one positive solution for each divisor `u+v`. -/
theorem equal_squareclass_atMost_divisors {A H : ℕ} {e : ℤ}
    (hA : 0 < A) (he : e ≠ 0) :
    HasAtMostSolutionsReal (positiveSquareclassBox A A H e) (e.natAbs.divisors.card : ℝ) := by
  classical
  intro s hs
  let f : ℕ × ℕ → ℕ := fun p => p.1 + p.2
  have hfactor : ∀ p ∈ s,
      (A : ℤ) * ((p.1 : ℤ) - (p.2 : ℤ)) * ((p.1 : ℤ) + (p.2 : ℤ)) = e := by
    intro p hp
    have h := (hs p hp).2.2.2.2
    nlinarith only [h]
  have hf : Set.InjOn f (s : Set (ℕ × ℕ)) := by
    intro p hp q hq hpq
    have hp' := hs p hp
    have hpSum : 0 < (p.1 : ℤ) + (p.2 : ℤ) := by exact_mod_cast Nat.add_pos_left hp'.1 _
    have hsum : (p.1 : ℤ) + (p.2 : ℤ) = (q.1 : ℤ) + (q.2 : ℤ) := by exact_mod_cast hpq
    have hsame : ((A : ℤ) * ((p.1 : ℤ) + (p.2 : ℤ))) * ((p.1 : ℤ) - (p.2 : ℤ)) =
        ((A : ℤ) * ((p.1 : ℤ) + (p.2 : ℤ))) * ((q.1 : ℤ) - (q.2 : ℤ)) := by
      calc
        _ = e := by simpa only [mul_right_comm] using hfactor p hp
        _ = (A : ℤ) * ((q.1 : ℤ) - (q.2 : ℤ)) * ((q.1 : ℤ) + (q.2 : ℤ)) := (hfactor q hq).symm
        _ = _ := by rw [← hsum]; ring
    have hsub := mul_left_cancel₀
      (mul_ne_zero (by exact_mod_cast hA.ne') hpSum.ne') hsame
    apply Prod.ext <;> dsimp at * <;> omega
  have himage : s.image f ⊆ e.natAbs.divisors := by
    intro n hn
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hn
    apply Nat.mem_divisors.mpr
    refine ⟨Int.natCast_dvd.mp ?_, Int.natAbs_ne_zero.mpr he⟩
    refine ⟨(A : ℤ) * ((p.1 : ℤ) - (p.2 : ℤ)), ?_⟩
    dsimp [f]
    rw [← hfactor p hp]
    ring
  have hcard : s.card ≤ e.natAbs.divisors.card := by
    calc
      s.card = (s.image f).card := (Finset.card_image_iff.mpr hf).symm
      _ ≤ _ := Finset.card_le_card himage
  exact_mod_cast hcard

/-- A Pell bound transfers to positive natural roots without losing multiplicity. -/
theorem positiveSquareclassBox_atMost_of_pell {A C H : ℕ} {e : ℤ} {R : ℝ}
    (hcount : HasAtMostSolutionsReal (pellBox A C e H) R) :
    HasAtMostSolutionsReal (positiveSquareclassBox A C H e) R := by
  classical
  let f : ℕ × ℕ → ℤ × ℤ := fun p => ((p.1 : ℤ), (p.2 : ℤ))
  have hf : Function.Injective f := by
    intro p q hpq
    have hfirst := congrArg (fun z : ℤ × ℤ => z.1) hpq
    have hsecond := congrArg (fun z : ℤ × ℤ => z.2) hpq
    apply Prod.ext <;> dsimp [f] at * <;> omega
  intro s hs
  have himage : ∀ p ∈ s.image f, pellBox A C e H p := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    have h := hs q hq
    exact ⟨h.2.2.2.2, by simpa [f] using h.2.2.1, by simpa [f] using h.2.2.2.1⟩
  simpa only [Finset.card_image_of_injective _ hf] using hcount _ himage

/-- All positive squareclasses, including the equal case, have the same uniform power bound. -/
theorem positiveSquareclassBox_atMost_rpow_eventually
    (K : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ A C H : ℕ, ∀ e : ℤ,
      0 < A → 0 < C → Squarefree A → Squarefree C → e ≠ 0 →
      A ≤ M ^ K → C ≤ M ^ K → H ≤ M ^ K → e.natAbs ≤ M ^ K →
      HasAtMostSolutionsReal (positiveSquareclassBox A C H e) ((M : ℝ) ^ epsilon) := by
  obtain ⟨Mp, hp⟩ := pellBox_atMost_rpow_eventually K epsilon hepsilon
  obtain ⟨Md, hd⟩ := card_divisors_le_rpow_eventually K epsilon hepsilon
  refine ⟨max Mp Md, ?_⟩
  intro M hM A C H e hA hC hAsq hCsq he hAM hCM hHM heM
  by_cases hAC : A = C
  · subst C
    intro s hs
    exact (equal_squareclass_atMost_divisors hA he s hs).trans
      (hd M ((le_max_right _ _).trans hM) e.natAbs heM)
  · apply positiveSquareclassBox_atMost_of_pell
    exact hp M ((le_max_left _ _).trans hM) A C H e hA hC
      (TerminalPartnerPell.not_isSquare_ratio_of_squarefree_of_ne hA hC hAsq hCsq hAC)
      he hAM hCM hHM heM

end
end PaperC.V282.PositiveSquareclassPairs
