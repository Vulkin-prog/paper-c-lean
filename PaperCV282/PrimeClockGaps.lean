import PaperCV282.PrimeClockIntegerOvershoot
import Mathlib.Data.Nat.Factorial.Basic

/-! # Arbitrarily large integer overshoots from factorial prime gaps

These are deterministic gaps in the integer clock, while the prime-rank
clock remains exactly geometric. No prime number theorem is needed.
-/
namespace PaperC.V282.PrimeClockGaps

open MeasureTheory ProbabilityTheory Set InfiniteRademacher MicroscopicBorderEvents
open PrimeClockIntegerOvershoot

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

noncomputable section

/-- Equal prime counting across every interval without a prime. -/
theorem primeCounting_eq_of_no_primes {L K : ℕ} (hLK : L≤K)
    (hgap : ∀ p : ℕ,L<p → p≤K → ¬p.Prime) : Nat.primeCounting K=Nat.primeCounting L := by
  rw [← Nat.primesLE_card_eq_primeCounting,← Nat.primesLE_card_eq_primeCounting]
  congr 1
  ext p
  simp only [Nat.mem_primesLE]
  constructor
  · rintro ⟨hpK,hp⟩
    exact ⟨by by_contra hn;exact hgap p (by omega) hpK hp,hp⟩
  · rintro ⟨hpL,hp⟩
    exact ⟨hpL.trans hLK,hp⟩

/-- The integers m!+2,...,m!+m are all composite. -/
theorem factorial_gap_not_prime {m n : ℕ} (_hm : 2≤m)
    (hnlo : m.factorial+1<n) (hnhi : n≤m.factorial+m) : ¬n.Prime := by
  intro hn
  let d := n-m.factorial
  have hd : 2≤d := by dsimp [d];omega
  have hdm : d≤m := by dsimp [d];omega
  have hfac : d∣m.factorial := Nat.dvd_factorial (by omega) hdm
  have hsum : m.factorial+d=n := by dsimp [d];omega
  have hdiv : d∣n := by rw [← hsum];exact dvd_add hfac (dvd_refl d)
  have heq := (Nat.dvd_prime_two_le hn hd).mp hdiv
  have hfpos := Nat.factorial_pos m
  omega

/-- The factorial gap has exactly constant prime counting. -/
theorem factorial_gap_primeCounting (m : ℕ) (hm : 2≤m) :
    Nat.primeCounting (m.factorial+1+(m-1))=Nat.primeCounting (m.factorial+1) := by
  apply primeCounting_eq_of_no_primes (by omega)
  intro p hp hpmax
  exact factorial_gap_not_prime hm hp (by omega)

/-- Along the explicit factorial sequence the raw overshoot is large with probability one. -/
theorem factorial_gap_conditional_overshoot (m : ℕ) (hm : 2≤m) :
    (cond infiniteRademacherMeasure (borderEvent (m.factorial+1))).real
      {omega | m-1≤ initialRunLength omega-(m.factorial+1)} = 1 :=
  conditional_overshoot_one_of_primeCounting_eq (factorial_gap_primeCounting m hm)

/-- There is no uniform bounded additive overshoot scale, even along arbitrarily large borders. -/
theorem arbitrarily_large_conditional_overshoot (H Lzero : ℕ) :
    ∃ L : ℕ,Lzero≤L ∧ (cond infiniteRademacherMeasure (borderEvent L)).real
      {omega | H≤ initialRunLength omega-L}=1 := by
  let m := max (max (H+1) Lzero) 2
  have hm : 2≤m := le_max_right _ _
  have hH : H+1≤m := (le_max_left _ _).trans (le_max_left _ _)
  have hL : Lzero≤m := (le_max_right _ _).trans (le_max_left _ _)
  have hmfac : m≤m.factorial := Nat.self_le_factorial m
  refine ⟨m.factorial+1,by omega,?_⟩
  apply conditional_overshoot_one_of_primeCounting_eq
  apply primeCounting_eq_of_no_primes (by omega)
  intro p hp hpmax
  exact factorial_gap_not_prime hm hp (by omega)

end
end PaperC.V282.PrimeClockGaps
