import PaperC.Affine.RationalChannelCode
import PaperC.Arithmetic.CanonicalChannel

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

/-!
# The canonical systematic rational code

This module packages Lemmas 5.1 and 5.2 into the objects used by the later
sections of the manuscript.  A finite alignment candidate is retained with
its proof of membership.  The optional canonical candidate is then turned
into the rational subspace `S_rat`; by definition the subspace is zero when
there is no candidate or when the selected channel contains at most one
exact unit.

The associated numbers

* `rationalSigma = dim S_rat`, and
* `residualTau = ρ - rationalSigma`

therefore implement the definitions immediately following Lemma 5.2,
including the degenerate branch isolated in Remark 5.3.
-/

namespace PaperC
namespace Affine
namespace CanonicalRationalCode

open RationalChannelCode

noncomputable section

/-- A reduced channel candidate bundled with its defining inequalities. -/
abbrev ReducedCandidate (x y B H : ℕ) :=
  {c : ℕ × ℕ // c ∈ reducedChannelCandidates x y B H}

/-- The positive first coefficient of a bundled candidate. -/
theorem candidate_fst_pos
    {x y B H : ℕ} (c : ReducedCandidate x y B H) :
    0 < c.1.1 :=
  (mem_reducedChannelCandidates.mp c.2).1

/-- The positive second coefficient of a bundled candidate. -/
theorem candidate_snd_pos
    {x y B H : ℕ} (c : ReducedCandidate x y B H) :
    0 < c.1.2 :=
  (mem_reducedChannelCandidates.mp c.2).2.1

/-- The candidate is primitive. -/
theorem candidate_coprime
    {x y B H : ℕ} (c : ReducedCandidate x y B H) :
    c.1.1.Coprime c.1.2 :=
  (mem_reducedChannelCandidates.mp c.2).2.2.2.2.1

/--
Canonical candidate with its membership proof retained.  This is a total
definition even below the asymptotic uniqueness threshold.
-/
noncomputable def canonicalReducedCandidate?
    (x y B H : ℕ) : Option (ReducedCandidate x y B H) :=
  if hs : (reducedChannelCandidates x y B H).Nonempty then
    some ⟨hs.choose, hs.choose_spec⟩
  else
    none

theorem canonicalReducedCandidate?_eq_none_iff
    {x y B H : ℕ} :
    canonicalReducedCandidate? x y B H = none ↔
      reducedChannelCandidates x y B H = ∅ := by
  classical
  by_cases hs : (reducedChannelCandidates x y B H).Nonempty
  · have hne : reducedChannelCandidates x y B H ≠ ∅ :=
      Finset.nonempty_iff_ne_empty.mp hs
    simp [canonicalReducedCandidate?, hs, hne]
  · have hempty : reducedChannelCandidates x y B H = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hs
    simp [canonicalReducedCandidate?, hs, hempty]

/--
The proof-carrying selector has exactly the same underlying optional pair as
`canonicalReducedChannel?`.
-/
theorem canonicalReducedCandidate?_map_val
    (x y B H : ℕ) :
    Option.map Subtype.val
        (canonicalReducedCandidate? x y B H) =
      canonicalReducedChannel? x y B H := by
  classical
  unfold canonicalReducedCandidate? canonicalReducedChannel?
  split <;> rfl

/--
Above the determinant threshold, the bundled canonical choice is every
candidate witness.
-/
theorem canonicalReducedCandidate?_eq_some_of_mem
    {x y B H : ℕ} (hx : 4 * H ^ 2 * B < x)
    {c : ℕ × ℕ}
    (hc : c ∈ reducedChannelCandidates x y B H) :
    canonicalReducedCandidate? x y B H =
      some (⟨c, hc⟩ : ReducedCandidate x y B H) := by
  classical
  unfold canonicalReducedCandidate?
  have hs : (reducedChannelCandidates x y B H).Nonempty :=
    ⟨c, hc⟩
  rw [dif_pos hs]
  congr 1
  apply Subtype.ext
  have hcard :=
    card_reducedChannelCandidates_le_one
      (x := x) (y := y) (B := B) (H := H) hx
  rw [Finset.card_le_one] at hcard
  exact hcard _ hs.choose_spec _ hc

/--
The rational subspace attached to one bundled candidate, before imposing
the manuscript's `m ≥ 2` activation rule.
-/
def rationalCodeForCandidate
    (M x y L B H : ℕ)
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (c : ReducedCandidate x y B H) :
    Submodule F₂ (RelationSpace (twoStartSystem M x y L)) :=
  rationalCode M x y L c.1.1 c.1.2
    (pairChannelError x y c.1.1 c.1.2)
    (candidate_fst_pos c) (candidate_snd_pos c)
    hx hy (by rfl)

/-- Exact-unit multiplicity of a bundled candidate in an offset box. -/
def candidateMultiplicity
    (L : ℕ) {x y B H : ℕ}
    (c : ReducedCandidate x y B H) : ℕ :=
  (channelCells L c.1.1 c.1.2
    (pairChannelError x y c.1.1 c.1.2)).card

/--
The canonical multiplicity `m_ex`.  It is zero when there is no aligned
candidate.
-/
noncomputable def canonicalMultiplicity
    (A L x y : ℕ) : ℕ :=
  match canonicalReducedCandidate?
      x y (L + 1) ((L + 1) ^ A) with
  | none => 0
  | some c => candidateMultiplicity L c

/-- A multiplicity at least two exposes the selected bundled candidate. -/
theorem exists_canonical_candidate_of_two_le_multiplicity
    {A L x y : ℕ}
    (hm : 2 ≤ canonicalMultiplicity A L x y) :
    ∃ c : ReducedCandidate
        x y (L + 1) ((L + 1) ^ A),
      canonicalReducedCandidate?
          x y (L + 1) ((L + 1) ^ A) = some c ∧
        2 ≤ candidateMultiplicity L c := by
  unfold canonicalMultiplicity at hm
  generalize hchoice :
      canonicalReducedCandidate?
        x y (L + 1) ((L + 1) ^ A) = choice at hm
  cases choice with
  | none =>
      simp only at hm
      omega
  | some c =>
      simp only at hm
      exact ⟨c, rfl, hm⟩

/-- A selected nontrivial candidate has height at most the offset length. -/
theorem candidate_max_le_length_of_two_units
    {L x y B H : ℕ}
    (c : ReducedCandidate x y B H)
    (hm : 2 ≤ candidateMultiplicity L c) :
    Nat.max c.1.1 c.1.2 ≤ L := by
  apply max_channelCoefficients_le_length
    (candidate_fst_pos c) (candidate_snd_pos c)
    (candidate_coprime c)
  rw [card_rationalChannelUnits_eq_channelCells]
  exact hm

/--
The systematic rational subspace `S_rat`.  It is definitionally zero when
there is no candidate or when the canonical candidate has at most one exact
unit.
-/
noncomputable def canonicalRationalCode
    (M A x y L : ℕ) (hx : 2 ≤ x) (hy : 2 ≤ y) :
    Submodule F₂ (RelationSpace (twoStartSystem M x y L)) :=
  match canonicalReducedCandidate?
      x y (L + 1) ((L + 1) ^ A) with
  | none => ⊥
  | some c =>
      if 2 ≤ candidateMultiplicity L c then
        rationalCodeForCandidate M x y L (L + 1) ((L + 1) ^ A)
          hx hy c
      else
        ⊥

/-- The manuscript's `σ(x,y) = dim S_rat`. -/
noncomputable def rationalSigma
    (M A x y L : ℕ) (hx : 2 ≤ x) (hy : 2 ≤ y) : ℕ :=
  Module.finrank F₂ (canonicalRationalCode M A x y L hx hy)

/-- The residual relation dimension `τ = ρ - σ`. -/
noncomputable def residualTau
    (M A x y L : ℕ) (hx : 2 ≤ x) (hy : 2 ≤ y) : ℕ :=
  relationRho (twoStartSystem M x y L) -
    rationalSigma M A x y L hx hy

/--
The code-theoretic definition of `σ` is exactly the elementary multiplicity
formula `max(m_ex-1,0)`, for every input (including below the uniqueness
threshold).
-/
theorem rationalSigma_eq_canonicalMultiplicity_sub_one
    (M A x y L : ℕ) (hx : 2 ≤ x) (hy : 2 ≤ y) :
    rationalSigma M A x y L hx hy =
      canonicalMultiplicity A L x y - 1 := by
  unfold rationalSigma canonicalRationalCode canonicalMultiplicity
  generalize hchoice :
      canonicalReducedCandidate?
        x y (L + 1) ((L + 1) ^ A) = choice
  cases choice with
  | none =>
      exact finrank_bot F₂
        (RelationSpace (twoStartSystem M x y L))
  | some c =>
      simp only
      let S : Submodule F₂
          (RelationSpace (twoStartSystem M x y L)) :=
        if 2 ≤ candidateMultiplicity L c then
          rationalCodeForCandidate M x y L (L + 1) ((L + 1) ^ A)
            hx hy c
        else
          ⊥
      change Module.finrank F₂ S = candidateMultiplicity L c - 1
      by_cases hm : 2 ≤ candidateMultiplicity L c
      · have hS :
            S = rationalCodeForCandidate M x y L (L + 1) ((L + 1) ^ A)
              hx hy c := by
          simp [S, hm]
        rw [(LinearEquiv.ofEq S _ hS).finrank_eq]
        have hmpos : 0 < candidateMultiplicity L c := by
          omega
        unfold rationalCodeForCandidate candidateMultiplicity
        exact
          finrank_rationalCode_eq_channelCells_card_sub_one
            (candidate_fst_pos c) (candidate_snd_pos c)
            hx hy (hheight := rfl)
            (hm := by
              simpa [candidateMultiplicity, pairChannelError] using hmpos)
      · have hS :
            S = (⊥ : Submodule F₂
              (RelationSpace (twoStartSystem M x y L))) := by
          simp [S, hm]
        rw [(LinearEquiv.ofEq S _ hS).finrank_eq, finrank_bot F₂
          (RelationSpace (twoStartSystem M x y L))]
        omega

/-- The rational subspace cannot exceed the full relation space. -/
theorem rationalSigma_le_relationRho
    (M A x y L : ℕ) (hx : 2 ≤ x) (hy : 2 ≤ y) :
    rationalSigma M A x y L hx hy ≤
      relationRho (twoStartSystem M x y L) := by
  unfold rationalSigma relationRho
  exact Submodule.finrank_le
    (canonicalRationalCode M A x y L hx hy)

/-- The defining codimension identity `ρ = σ + τ`. -/
theorem relationRho_eq_rationalSigma_add_residualTau
    (M A x y L : ℕ) (hx : 2 ≤ x) (hy : 2 ≤ y) :
    relationRho (twoStartSystem M x y L) =
      rationalSigma M A x y L hx hy +
        residualTau M A x y L hx hy := by
  unfold residualTau
  exact
    (Nat.add_sub_of_le
      (rationalSigma_le_relationRho M A x y L hx hy)).symm

/-- If the canonical channel has at most one unit, `S_rat` is zero. -/
theorem canonicalRationalCode_eq_bot_of_multiplicity_le_one
    {M A x y L : ℕ} {hx : 2 ≤ x} {hy : 2 ≤ y}
    (hm : canonicalMultiplicity A L x y ≤ 1) :
    canonicalRationalCode M A x y L hx hy = ⊥ := by
  unfold canonicalMultiplicity at hm
  unfold canonicalRationalCode
  generalize hchoice :
      canonicalReducedCandidate?
        x y (L + 1) ((L + 1) ^ A) = choice at *
  cases choice with
  | none =>
      rfl
  | some c =>
      simp only at hm
      change
        (if 2 ≤ candidateMultiplicity L c then
            rationalCodeForCandidate
              M x y L (L + 1) ((L + 1) ^ A) hx hy c
          else ⊥) = ⊥
      rw [if_neg (by omega)]

/--
Remark 5.3, dimension part: in the branch `m_ex ≤ 1`, no quotient is taken
and `(S_rat, σ, τ) = (0,0,ρ)`.
-/
theorem degenerate_canonical_channel
    {M A x y L : ℕ} {hx : 2 ≤ x} {hy : 2 ≤ y}
    (hm : canonicalMultiplicity A L x y ≤ 1) :
    canonicalRationalCode M A x y L hx hy = ⊥ ∧
      rationalSigma M A x y L hx hy = 0 ∧
      residualTau M A x y L hx hy =
        relationRho (twoStartSystem M x y L) := by
  have hcode :=
    canonicalRationalCode_eq_bot_of_multiplicity_le_one
      (M := M) (hx := hx) (hy := hy) hm
  have hsigma :
      rationalSigma M A x y L hx hy = 0 := by
    unfold rationalSigma
    rw [hcode]
    exact finrank_bot F₂
      (RelationSpace (twoStartSystem M x y L))
  refine ⟨hcode, hsigma, ?_⟩
  unfold residualTau
  rw [hsigma]
  omega

/--
At the determinant threshold, a nontrivial primitive channel is selected by
the canonical construction and its systematic code is unchanged.
-/
theorem canonicalRationalCode_eq_of_two_units
    {M A x y L a b : ℕ}
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (hA : 1 ≤ A)
    (hthreshold :
      4 * ((L + 1) ^ A) ^ 2 * (L + 1) < x)
    (hm :
      2 ≤ (channelCells L a b
        (pairChannelError x y a b)).card) :
    canonicalRationalCode M A x y L hx hy =
      rationalCode M x y L a b
        (pairChannelError x y a b)
        ha hb hx hy (by rfl) := by
  have hc :
      (a, b) ∈
        reducedChannelCandidates
          x y (L + 1) ((L + 1) ^ A) :=
    channel_mem_reducedCandidates_of_two_units
      ha hb hab hA rfl hm
  let c : ReducedCandidate
      x y (L + 1) ((L + 1) ^ A) :=
    ⟨(a, b), hc⟩
  have hchoice :
      canonicalReducedCandidate?
          x y (L + 1) ((L + 1) ^ A) =
        some c :=
    canonicalReducedCandidate?_eq_some_of_mem
      hthreshold hc
  unfold canonicalRationalCode
  rw [hchoice]
  change
    (if 2 ≤ candidateMultiplicity L c then
        rationalCodeForCandidate
          M x y L (L + 1) ((L + 1) ^ A) hx hy c
      else ⊥) =
      rationalCode M x y L a b
        (pairChannelError x y a b) ha hb hx hy (by rfl)
  rw [if_pos (show 2 ≤ candidateMultiplicity L c by
    simpa [candidateMultiplicity, c] using hm)]
  rfl

/--
Dimension formula for the selected nontrivial channel, in the integer-cell
notation of Lemma 5.1.
-/
theorem rationalSigma_eq_card_sub_one_of_two_units
    {M A x y L a b : ℕ}
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (hA : 1 ≤ A)
    (hthreshold :
      4 * ((L + 1) ^ A) ^ 2 * (L + 1) < x)
    (hm :
      2 ≤ (channelCells L a b
        (pairChannelError x y a b)).card) :
    rationalSigma M A x y L hx hy =
      (channelCells L a b
        (pairChannelError x y a b)).card - 1 := by
  unfold rationalSigma
  rw [canonicalRationalCode_eq_of_two_units
    (M := M) hx hy ha hb hab hA hthreshold hm]
  exact
    finrank_rationalCode_eq_channelCells_card_sub_one
      ha hb hx hy
      (hheight := rfl)
      (hm := Nat.zero_lt_of_lt hm)

/--
Literal coverage assertion of Lemma 5.2: if the systematic code of a
primitive channel is nonzero, then that channel is the canonical one above
the uniqueness threshold.
-/
theorem canonicalRationalCode_eq_of_rationalCode_ne_bot
    {M A x y L a b : ℕ}
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (hA : 1 ≤ A)
    (hthreshold :
      4 * ((L + 1) ^ A) ^ 2 * (L + 1) < x)
    (hcode :
      rationalCode M x y L a b
        (pairChannelError x y a b)
        ha hb hx hy (by rfl) ≠ ⊥) :
    canonicalRationalCode M A x y L hx hy =
      rationalCode M x y L a b
        (pairChannelError x y a b)
        ha hb hx hy (by rfl) := by
  have hm :
      2 ≤ (channelCells L a b
        (pairChannelError x y a b)).card :=
    (rationalCode_ne_bot_iff_two_le_channelCells_card
      ha hb hx hy rfl).mp hcode
  exact canonicalRationalCode_eq_of_two_units
    hx hy ha hb hab hA hthreshold hm

end

end CanonicalRationalCode
end Affine
end PaperC
