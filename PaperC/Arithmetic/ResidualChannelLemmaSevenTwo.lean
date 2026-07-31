import PaperC.Arithmetic.DyadicPrimeReciprocalSums
import PaperC.Arithmetic.ResidualChannelSupport
import PaperC.Arithmetic.ResidualPrimeMass

/-!
# The finite effective form of Paper C, Lemma 7.2

Put `B = L+1` and `q = max(a,b)`.  The geometric part of the lemma gives

`E_p ≤ (1 + 8*q*B/p) * (1 + B/q)`.

The residual expression is nonzero, so every prime that actually occurs is
strictly smaller than `4*q*B`.  The dyadic interval

`(B, B * 2^(q+2)]`

therefore contains the complete residual-prime support.  Combining the
pointwise estimate with the reciprocal-prime shell bounds proves the explicit
finite version

`∑ E_p/p ≤ 896 * B / log₂ B`.

This is (7.4), with a fully effective absolute constant and with the natural
finite support made explicit.
-/

namespace PaperC

open Finset
open scoped BigOperators

namespace ResidualChannelLemmaSevenTwo

open DyadicPrimeReciprocalSums

/-- The dyadic prime range which contains every residual prime of the channel. -/
def residualPrimeRange (L a b : ℕ) : Finset ℕ :=
  dyadicPrimes (L + 1) (Nat.max a b + 2)

@[simp]
theorem mem_residualPrimeRange {L a b p : ℕ} :
    p ∈ residualPrimeRange L a b ↔
      p.Prime ∧ L + 1 < p ∧
        p ≤ (L + 1) * 2 ^ (Nat.max a b + 2) := by
  simp [residualPrimeRange]

/--
Every prime above `B=L+1` carrying a residual cell belongs to the finite
dyadic range used in the summation.
-/
theorem mem_residualPrimeRange_of_nonempty
    {L a b p : ℕ} {h : ℤ}
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (hm : 2 ≤ (channelCells L a b h).card)
    (hp : p.Prime) (hBp : L + 1 < p)
    (hnonempty : (residualPrimeCells L a b p h).Nonempty) :
    p ∈ residualPrimeRange L a b := by
  obtain ⟨cell, hcell⟩ := hnonempty
  have hpCutoff :
      p < 4 * Nat.max a b * (L + 1) :=
    prime_lt_four_mul_max_of_mem_residualPrimeCells
      ha hb hab hm hcell hp
  have hqPow : Nat.max a b ≤ 2 ^ Nat.max a b := by
    induction Nat.max a b with
    | zero => simp
    | succ n ih =>
        by_cases hn : n = 0
        · subst n
          norm_num
        · have hnPos : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
          calc
            n + 1 ≤ n + n := by omega
            _ ≤ 2 ^ n + 2 ^ n := Nat.add_le_add ih ih
            _ = 2 ^ (n + 1) := by
              rw [pow_succ]
              ring
  have hcutoffCover :
      4 * Nat.max a b * (L + 1) ≤
        (L + 1) * 2 ^ (Nat.max a b + 2) := by
    calc
      4 * Nat.max a b * (L + 1)
          ≤ 4 * 2 ^ Nat.max a b * (L + 1) :=
        Nat.mul_le_mul_right (L + 1)
          (Nat.mul_le_mul_left 4 hqPow)
      _ = (L + 1) * 2 ^ (Nat.max a b + 2) := by
        rw [pow_add]
        norm_num
        ring
  rw [mem_residualPrimeRange]
  exact ⟨hp, hBp, hpCutoff.le.trans hcutoffCover⟩

/-- The finite residual-prime mass occurring on the left side of (7.4). -/
def residualPrimeMass (L a b : ℕ) (h : ℤ) : ℚ :=
  ∑ p ∈ residualPrimeRange L a b,
    ((residualPrimeCells L a b p h).card : ℚ) / (p : ℚ)

/--
The chosen dyadic range is the complete support, not merely a convenient
truncation.  Once an ambient prime cutoff contains it, extending the sum to
all primes in `(L+1,X]` adds only zero terms.
-/
theorem residualPrimeMass_eq_sum_primesBetween
    {L a b X : ℕ} {h : ℤ}
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (hm : 2 ≤ (channelCells L a b h).card)
    (hX :
      (L + 1) * 2 ^ (Nat.max a b + 2) ≤ X) :
    residualPrimeMass L a b h =
      ∑ p ∈ primesBetween (L + 1) X,
        ((residualPrimeCells L a b p h).card : ℚ) / (p : ℚ) := by
  apply Finset.sum_subset
  · intro p hp
    rw [mem_residualPrimeRange] at hp
    rw [mem_primesBetween]
    exact ⟨hp.1, hp.2.1, hp.2.2.trans hX⟩
  · intro p hpBig hpSmall
    have hpData := mem_primesBetween.mp hpBig
    have hpAboveDyadic :
        (L + 1) * 2 ^ (Nat.max a b + 2) < p := by
      by_contra hpNot
      apply hpSmall
      rw [mem_residualPrimeRange]
      exact ⟨hpData.1, hpData.2.1, Nat.le_of_not_gt hpNot⟩
    have hcutoff :
        4 * Nat.max a b * (L + 1) ≤ p :=
      (four_mul_q_mul_B_le_dyadicCutoff
        (L + 1) (Nat.max a b)).trans hpAboveDyadic.le
    have hempty :
        residualPrimeCells L a b p h = ∅ :=
      residualPrimeCells_eq_empty_of_cutoff_le
        ha hb hab hm hpData.1 hcutoff
    simp [hempty]

/--
Effective finite form of (7.4).  The extra hypothesis `2 ≤ max(a,b)` is the
separation input used in the manuscript immediately after (7.3); the
geometric channel hypotheses themselves imply `max(a,b) ≤ L`.
-/
theorem residualPrimeMass_le
    {L a b : ℕ} {h : ℤ}
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (hqTwo : 2 ≤ Nat.max a b)
    (hB : 4 ≤ L + 1)
    (hm : 2 ≤ (channelCells L a b h).card) :
    residualPrimeMass L a b h ≤
      896 * (L + 1 : ℚ) / (Nat.log 2 (L + 1) : ℚ) := by
  let B : ℕ := L + 1
  let q : ℕ := Nat.max a b
  let K : ℕ := q + 2
  let P : Finset ℕ := residualPrimeRange L a b
  let E : ℕ → ℕ := fun p ↦ (residualPrimeCells L a b p h).card
  have hqPos : 0 < q := by omega
  have hBPos : 0 < B := by omega
  have hlogPosNat : 0 < Nat.log 2 B := by
    have hlogTwo : 2 ≤ Nat.log 2 B := by
      apply Nat.le_log_of_pow_le (by norm_num)
      norm_num
      exact hB
    omega
  have hP :
      ∀ p ∈ P, 0 < p := by
    intro p hpMem
    have hpData :
        p.Prime ∧ B < p ∧ p ≤ B * 2 ^ K := by
      simpa [P, B, K, q, residualPrimeRange] using
        (mem_dyadicPrimes.mp hpMem)
    exact hpData.1.pos
  have hpointwise :
      ∀ p ∈ P,
        (E p : ℚ) ≤
          (8 : ℚ) *
            (1 + (q : ℚ) * (B : ℚ) / (p : ℚ)) *
            (1 + (B : ℚ) / (q : ℚ)) := by
    intro p hpMem
    have hpPos : 0 < p := hP p hpMem
    have hraw :=
      residualPrimeCells_card_cast_le
        (L := L) (a := a) (b := b) (p := p) (h := h)
        ha hb hab hpPos hm
    have hxNonneg :
        0 ≤ (q : ℚ) * (B : ℚ) / (p : ℚ) := by positivity
    have hsecondNonneg :
        0 ≤ 1 + (B : ℚ) / (q : ℚ) := by positivity
    calc
      (E p : ℚ) ≤
          (1 + 8 * (q : ℚ) * (B : ℚ) / (p : ℚ)) *
            (1 + (B : ℚ) / (q : ℚ)) := by
        simpa [E, q, B] using hraw
      _ ≤
          ((8 : ℚ) *
              (1 + (q : ℚ) * (B : ℚ) / (p : ℚ))) *
            (1 + (B : ℚ) / (q : ℚ)) := by
        apply mul_le_mul_of_nonneg_right _ hsecondNonneg
        calc
          1 + 8 * (q : ℚ) * (B : ℚ) / (p : ℚ) =
              1 + 8 * ((q : ℚ) * (B : ℚ) / (p : ℚ)) := by ring
          _ ≤ 8 + 8 * ((q : ℚ) * (B : ℚ) / (p : ℚ)) := by
            norm_num
          _ = 8 * (1 + (q : ℚ) * (B : ℚ) / (p : ℚ)) := by
            ring
  have hmass :=
    PaperC.residualPrimeMass_natCast_le
      P E (8 : ℚ) (q : ℚ) (B : ℚ) hP hpointwise
  have hPDef :
      P = dyadicPrimes B K := by
    simp [P, residualPrimeRange, B, K, q]
  have hinv :
      (∑ p ∈ P, (1 : ℚ) / (p : ℚ)) ≤
        14 * (K : ℚ) / (Nat.log 2 B : ℚ) := by
    rw [hPDef]
    exact sum_inv_dyadicPrimes_le B K hB
  have hinvSq :
      (∑ p ∈ P, (1 : ℚ) / (p : ℚ) ^ 2) ≤
        28 / ((B : ℚ) * (Nat.log 2 B : ℚ)) := by
    rw [hPDef]
    exact sum_inv_sq_dyadicPrimes_le B K hB
  have hK : K ≤ 2 * q := by
    dsimp [K]
    omega
  have hqB :
      q ≤ B := by
    dsimp [q, B]
    have hqL :=
      channel_max_le_length_of_two_cells ha hb hab hm
    omega
  have hlogPos : (0 : ℚ) < (Nat.log 2 B : ℚ) := by
    exact_mod_cast hlogPosNat
  have hBPosQ : (0 : ℚ) < (B : ℚ) := by
    exact_mod_cast hBPos
  have hqPosQ : (0 : ℚ) < (q : ℚ) := by
    exact_mod_cast hqPos
  have hinvSimplified :
      (∑ p ∈ P, (1 : ℚ) / (p : ℚ)) ≤
        28 * (q : ℚ) / (Nat.log 2 B : ℚ) := by
    refine hinv.trans ?_
    apply div_le_div_of_nonneg_right
    · have hKQ : (K : ℚ) ≤ 2 * (q : ℚ) := by
        exact_mod_cast hK
      nlinarith
    · exact hlogPos.le
  have hsqScaled :
      (q : ℚ) * (B : ℚ) *
          (∑ p ∈ P, (1 : ℚ) / (p : ℚ) ^ 2) ≤
        28 * (q : ℚ) / (Nat.log 2 B : ℚ) := by
    calc
      (q : ℚ) * (B : ℚ) *
            (∑ p ∈ P, (1 : ℚ) / (p : ℚ) ^ 2)
          ≤ (q : ℚ) * (B : ℚ) *
              (28 / ((B : ℚ) * (Nat.log 2 B : ℚ))) :=
        mul_le_mul_of_nonneg_left hinvSq
          (mul_nonneg hqPosQ.le hBPosQ.le)
      _ = 28 * (q : ℚ) / (Nat.log 2 B : ℚ) := by
        field_simp
        ring
  have hinner :
      (∑ p ∈ P, (1 : ℚ) / (p : ℚ)) +
          (q : ℚ) * (B : ℚ) *
            (∑ p ∈ P, (1 : ℚ) / (p : ℚ) ^ 2) ≤
        56 * (q : ℚ) / (Nat.log 2 B : ℚ) := by
    calc
      (∑ p ∈ P, (1 : ℚ) / (p : ℚ)) +
            (q : ℚ) * (B : ℚ) *
              (∑ p ∈ P, (1 : ℚ) / (p : ℚ) ^ 2)
          ≤ 28 * (q : ℚ) / (Nat.log 2 B : ℚ) +
              28 * (q : ℚ) / (Nat.log 2 B : ℚ) :=
        add_le_add hinvSimplified hsqScaled
      _ = 56 * (q : ℚ) / (Nat.log 2 B : ℚ) := by ring
  have houterNonneg :
      0 ≤ (8 : ℚ) * (1 + (B : ℚ) / (q : ℚ)) := by positivity
  have hqBsum :
      (q : ℚ) + (B : ℚ) ≤ 2 * (B : ℚ) := by
    exact_mod_cast (show q + B ≤ 2 * B by omega)
  have hfinal :
      (8 : ℚ) * (1 + (B : ℚ) / (q : ℚ)) *
          (56 * (q : ℚ) / (Nat.log 2 B : ℚ)) ≤
        896 * (B : ℚ) / (Nat.log 2 B : ℚ) := by
    have heq :
        (8 : ℚ) * (1 + (B : ℚ) / (q : ℚ)) *
            (56 * (q : ℚ) / (Nat.log 2 B : ℚ)) =
          448 * ((q : ℚ) + (B : ℚ)) /
            (Nat.log 2 B : ℚ) := by
      field_simp
      ring
    rw [heq]
    apply div_le_div_of_nonneg_right
    · nlinarith
    · exact hlogPos.le
  calc
    residualPrimeMass L a b h =
        ∑ p ∈ P, (E p : ℚ) / (p : ℚ) := by
      simp [residualPrimeMass, P, E]
    _ ≤
        (8 : ℚ) * (1 + (B : ℚ) / (q : ℚ)) *
          ((∑ p ∈ P, (1 : ℚ) / (p : ℚ)) +
            (q : ℚ) * (B : ℚ) *
              ∑ p ∈ P, (1 : ℚ) / (p : ℚ) ^ 2) :=
      hmass
    _ ≤
        (8 : ℚ) * (1 + (B : ℚ) / (q : ℚ)) *
          (56 * (q : ℚ) / (Nat.log 2 B : ℚ)) :=
      mul_le_mul_of_nonneg_left hinner houterNonneg
    _ ≤ 896 * (B : ℚ) / (Nat.log 2 B : ℚ) :=
      hfinal
    _ = 896 * (L + 1 : ℚ) /
        (Nat.log 2 (L + 1) : ℚ) := by
      simp [B]

end ResidualChannelLemmaSevenTwo
end PaperC
