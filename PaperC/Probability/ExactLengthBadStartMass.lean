import PaperC.Probability.ExactLengthConditionalRank
import PaperC.Probability.BadStartMass
import PaperC.Probability.TerminalBadStartBound

set_option maxHeartbeats 1800000

/-!
# Removed-start mass for exact run lengths

This file supplies the finite summation step in Lemma 14.7.

For an exact excess `e`, put

`q = L + e + 1`, `Q = L + E + 1`, `W = Q + 1`,
and `Y = floor (W^2 log W)`.

The removed set `D(Q)` consists of starts whose length-`Q` non-root window
contains a `Y`-defective value.  We split it into

* starts whose shorter length-`q` support already contains a value defective
  at the base cutoff `W`; and
* the remaining removed starts.

On the first part the affine relation defect is bounded by the number of
base-defective non-root vertices, giving the weighted-defect contribution.
On the second part the exact-length rows have full rank, for every translated
right-hand side, and the probability is exactly `2⁻q`.  This gives the exact
finite analogue of the two cases in the manuscript:

`sum_{x in D(Q)} P(K_{x,e})
  <= (2 M_W(N,q) + #D(Q)) / 2^q`.

The implementation is slightly sharper than the presentation in the paper.
The paper counts all support vertices, including the root `x - 1`, and then
uses the even-boundary relation to subtract one.  The already formalized
injective interior-boundary map works directly with non-root vertices.
Consequently no defect assumption on the root is needed, while the final
weighted estimate loses only the harmless factor `2` in
`2 * (2^m - 1)`.  This is slightly weaker than the displayed constant in
the manuscript but has exactly the same uniform `o(1)` consequence.

The last theorem inserts the certified prime-sensitive bound for `#D(Q)` at
the literal terminal cutoff.  Everything here is finite; no asymptotic
bridge or placeholder is introduced.
-/

namespace PaperC
namespace ExactLengthBadStartMass

open scoped BigOperators

open Affine
open MixedLengthAffine
open ExactLengthConditionalRank
open BadStartCount
open BadStartMass
open TerminalPrimeCutoff
open TerminalBadStartBound

noncomputable section

/-! ## Unconditional exact-length probabilities -/

/--
Uniform finite-cylinder probability of the exact-length event with `q`
affine rows.
-/
def exactLengthProbability (N q x : ℕ) : ℚ :=
  by
    classical
    exact uniformEventProbability (M := dyadicCutoff N q)
      (fun ω => exactLengthAt ω x q)

/--
The event definition agrees with the affine fiber for `q ≥ 2`.
-/
theorem exactLengthProbability_eq_uniformSolutionProbability
    (N q x : ℕ) (hq : 2 ≤ q) :
    exactLengthProbability N q x =
      uniformSolutionProbability
        (startSystem (dyadicCutoff N q) x q)
        (exactLengthRhs q) := by
  classical
  unfold exactLengthProbability uniformEventProbability
    uniformSolutionProbability
  congr 1
  rw [Fintype.card_subtype]
  apply congrArg (fun n : ℕ => (n : ℚ))
  apply congrArg Finset.card
  ext ω
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact
    (startSystem_eq_exactLengthRhs_iff ω hq).symm

/--
Exact affine normalization of one unconditional exact-length event.
-/
theorem exactLengthProbability_eq_eta_mul_two_pow_rho_div
    (N q x : ℕ) (hq : 2 ≤ q) :
    exactLengthProbability N q x =
      ((relationEta
          (startSystem (dyadicCutoff N q) x q)
          (exactLengthRhs q) : ℚ) *
        (2 : ℚ) ^
          relationRho (startSystem (dyadicCutoff N q) x q)) /
        (2 : ℚ) ^ q := by
  rw [exactLengthProbability_eq_uniformSolutionProbability N q x hq,
    SectionTwelveMoments.uniformSolutionProbability_eq_eta_mul_two_pow_rho_div]
  congr 1
  simp

/-- Exact-length probabilities are nonnegative. -/
theorem exactLengthProbability_nonneg (N q x : ℕ) :
    0 ≤ exactLengthProbability N q x := by
  classical
  unfold exactLengthProbability uniformEventProbability
  positivity

/--
Any relation-defect bound gives the corresponding pointwise exact-length
probability bound.
-/
theorem exactLengthProbability_le_of_relationRho
    {N q x d : ℕ} (hq : 2 ≤ q)
    (hrho :
      relationRho (startSystem (dyadicCutoff N q) x q) ≤ d) :
    exactLengthProbability N q x ≤
      (2 : ℚ) ^ d / (2 : ℚ) ^ q := by
  rw [exactLengthProbability_eq_uniformSolutionProbability N q x hq]
  simpa using
    uniformSolutionProbability_le_two_pow_relation_bound
      (startSystem (dyadicCutoff N q) x q)
      (exactLengthRhs q) hrho

/--
At cutoff `B`, the exact-length probability is bounded by the number of
defective non-root support vertices.
-/
theorem exactLengthProbability_le_two_pow_defect_div
    {N q x B : ℕ}
    (hN : 2 ≤ N) (hx : x ∈ dyadicBlock N)
    (hq : 2 ≤ q) (hqB : q + 1 ≤ B) :
    exactLengthProbability N q x ≤
      (2 : ℚ) ^ (startDefectIndicesAt B x q).card /
        (2 : ℚ) ^ q := by
  apply exactLengthProbability_le_of_relationRho hq
  exact relationRho_startSystem_le_card_startDefectIndicesAt
    hN hx (by omega) hqB

/--
Outside the base bad set, the exact-length affine system has full row rank.
The conclusion is independent of the translated right-hand side.
-/
theorem exactLengthProbability_eq_baseline_of_not_bad
    {N q x B : ℕ}
    (hN : 2 ≤ N) (hx : x ∈ dyadicBlock N)
    (hq : 2 ≤ q) (hqB : q + 1 ≤ B)
    (hgood : x ∉ terminalBadStarts N q B) :
    exactLengthProbability N q x =
      (1 : ℚ) / (2 : ℚ) ^ q := by
  rw [exactLengthProbability_eq_uniformSolutionProbability N q x hq]
  simpa using
    uniformSolutionProbability_eq_inv_two_pow_of_relationRho_eq_zero
      (startSystem (dyadicCutoff N q) x q)
      (exactLengthRhs q)
      (relationRho_startSystem_eq_zero_of_not_bad
        hN hx (by omega) hqB hgood)

/--
Weighted pointwise estimate on a genuinely base-defective exact-length
start.
-/
theorem exactLengthProbability_le_two_mul_defectWeight_div
    {N q x B : ℕ}
    (hN : 2 ≤ N) (hx : x ∈ dyadicBlock N)
    (hq : 2 ≤ q) (hqB : q + 1 ≤ B)
    (hbad : x ∈ terminalBadStarts N q B) :
    exactLengthProbability N q x ≤
      (2 : ℚ) *
          (((2 : ℕ) ^ (startDefectIndicesAt B x q).card - 1 : ℕ) : ℚ) /
        (2 : ℚ) ^ q := by
  have hnonempty :
      (startDefectIndicesAt B x q).Nonempty :=
    (startDefectIndicesAt_nonempty_iff B x q).mpr
      (mem_terminalBadStarts.mp hbad).2
  have hcardPos :
      0 < (startDefectIndicesAt B x q).card :=
    Finset.card_pos.mpr hnonempty
  have hpowNat :=
    two_pow_le_two_mul_two_pow_sub_one hcardPos
  have hpowQ :
      (2 : ℚ) ^ (startDefectIndicesAt B x q).card ≤
        (2 : ℚ) *
          (((2 : ℕ) ^ (startDefectIndicesAt B x q).card - 1 : ℕ) : ℚ) := by
    exact_mod_cast hpowNat
  exact
    (exactLengthProbability_le_two_pow_defect_div
      hN hx hq hqB).trans
      (div_le_div_of_nonneg_right hpowQ (by positivity))

/-! ## Finite masses and the two-case split -/

/-- Exact-length probability mass over a finite set of starts. -/
def exactLengthProbabilityMass
    (N q : ℕ) (s : Finset ℕ) : ℚ :=
  ∑ x ∈ s, exactLengthProbability N q x

/--
The base-defective contribution is controlled by the same weighted defect
mass as in the ordinary-start calculation, now with the exact row count
`q`.
-/
theorem exactLengthProbabilityMass_terminalBadStarts_le_weight
    {N q B : ℕ}
    (hN : 2 ≤ N) (hq : 2 ≤ q) (hqB : q + 1 ≤ B) :
    exactLengthProbabilityMass N q (terminalBadStarts N q B) ≤
      2 * terminalDefectWeightMass N q B / (2 : ℚ) ^ q := by
  let w : ℕ → ℚ := fun x =>
    (((2 : ℕ) ^ (startDefectIndicesAt B x q).card - 1 : ℕ) : ℚ)
  have hsubset :
      terminalBadStarts N q B ⊆ dyadicBlock N := by
    intro x hx
    exact (mem_terminalBadStarts.mp hx).1
  have hsumSubset :
      (∑ x ∈ terminalBadStarts N q B, w x) ≤
        ∑ x ∈ dyadicBlock N, w x := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro x hx hnot
    dsimp only [w]
    positivity
  calc
    exactLengthProbabilityMass N q (terminalBadStarts N q B) ≤
        ∑ x ∈ terminalBadStarts N q B,
          (2 : ℚ) * w x / (2 : ℚ) ^ q := by
      apply Finset.sum_le_sum
      intro x hx
      exact exactLengthProbability_le_two_mul_defectWeight_div
        hN (mem_terminalBadStarts.mp hx).1 hq hqB hx
    _ = (2 / (2 : ℚ) ^ q) *
        (∑ x ∈ terminalBadStarts N q B, w x) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ ≤ (2 / (2 : ℚ) ^ q) *
        (∑ x ∈ dyadicBlock N, w x) := by
      exact mul_le_mul_of_nonneg_left hsumSubset (by positivity)
    _ = 2 * terminalDefectWeightMass N q B /
        (2 : ℚ) ^ q := by
      simp only [terminalDefectWeightMass, w]
      ring

/--
Increasing both the support length and the prime cutoff enlarges the bad
set.
-/
theorem terminalBadStarts_mono_length_cutoff
    {N q Q B Y : ℕ} (hqQ : q ≤ Q) (hBY : B ≤ Y) :
    terminalBadStarts N q B ⊆ terminalBadStarts N Q Y := by
  intro x hx
  obtain ⟨hxBlock, j, hj, hkernel⟩ :=
    mem_terminalBadStarts.mp hx
  exact mem_terminalBadStarts.mpr
    ⟨hxBlock, j, hj.trans_le hqQ,
      largeOddKernel_eq_one_mono hBY hkernel⟩

/--
The number of defective non-root vertices is monotone in the support
length.  The injection is the canonical inclusion `Fin q ↪ Fin Q`.
-/
theorem card_startDefectIndicesAt_le_of_le
    {B x q Q : ℕ} (hqQ : q ≤ Q) :
    (startDefectIndicesAt B x q).card ≤
      (startDefectIndicesAt B x Q).card := by
  apply Finset.card_le_card_of_injOn (Fin.castLE hqQ)
  · intro j hj
    rw [mem_startDefectIndicesAt]
    simpa using (mem_startDefectIndicesAt.mp hj)
  · intro i hi j hj hij
    exact Fin.castLE_injective hqQ hij

/-- The weighted defect mass is monotone in the support length. -/
theorem terminalDefectWeightMass_mono_length
    {N B q Q : ℕ} (hqQ : q ≤ Q) :
    terminalDefectWeightMass N q B ≤
      terminalDefectWeightMass N Q B := by
  unfold terminalDefectWeightMass
  apply Finset.sum_le_sum
  intro x hx
  exact_mod_cast
    Nat.sub_le_sub_right
      (Nat.pow_le_pow_right (by omega)
        (card_startDefectIndicesAt_le_of_le
          (B := B) (x := x) hqQ))
      1

/--
Exact two-case decomposition.  The starts that are removed at `(Q,Y)` but
are not base-defective on their actual support `(q,B)` all contribute
exactly the independent baseline.
-/
theorem exactLengthProbabilityMass_terminalBadStarts_eq_split
    {N q Q B Y : ℕ}
    (hN : 2 ≤ N) (hq : 2 ≤ q)
    (hqQ : q ≤ Q) (hqB : q + 1 ≤ B) (hBY : B ≤ Y) :
    exactLengthProbabilityMass N q (terminalBadStarts N Q Y) =
      exactLengthProbabilityMass N q (terminalBadStarts N q B) +
        (((terminalBadStarts N Q Y \ terminalBadStarts N q B).card : ℚ) /
          (2 : ℚ) ^ q) := by
  let DB := terminalBadStarts N q B
  let DY := terminalBadStarts N Q Y
  have hsubset : DB ⊆ DY :=
    terminalBadStarts_mono_length_cutoff hqQ hBY
  have hsplit :
      exactLengthProbabilityMass N q DY =
        exactLengthProbabilityMass N q DB +
          exactLengthProbabilityMass N q (DY \ DB) := by
    simp only [exactLengthProbabilityMass]
    rw [← Finset.sum_sdiff hsubset]
    ac_rfl
  have hremaining :
      exactLengthProbabilityMass N q (DY \ DB) =
        (((DY \ DB).card : ℚ) / (2 : ℚ) ^ q) := by
    simp only [exactLengthProbabilityMass]
    calc
      (∑ x ∈ DY \ DB, exactLengthProbability N q x) =
          ∑ _x ∈ DY \ DB, (1 : ℚ) / (2 : ℚ) ^ q := by
        apply Finset.sum_congr rfl
        intro x hx
        have hxDY : x ∈ DY := (Finset.mem_sdiff.mp hx).1
        have hxDB : x ∉ DB := (Finset.mem_sdiff.mp hx).2
        exact exactLengthProbability_eq_baseline_of_not_bad
          hN (mem_terminalBadStarts.mp hxDY).1 hq hqB hxDB
      _ = (((DY \ DB).card : ℚ) / (2 : ℚ) ^ q) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
  rw [hsplit, hremaining]

/--
Generic finite two-window estimate.  This is the reusable algebraic core of
Lemma 14.7 before inserting the manuscript parameters.
-/
theorem exactLengthProbabilityMass_terminalBadStarts_le_two_windows
    {N q Q B Y : ℕ}
    (hN : 2 ≤ N) (hq : 2 ≤ q)
    (hqQ : q ≤ Q) (hqB : q + 1 ≤ B) (hBY : B ≤ Y) :
    exactLengthProbabilityMass N q (terminalBadStarts N Q Y) ≤
      2 * terminalDefectWeightMass N q B / (2 : ℚ) ^ q +
        ((terminalBadStarts N Q Y).card : ℚ) / (2 : ℚ) ^ q := by
  rw [exactLengthProbabilityMass_terminalBadStarts_eq_split
    hN hq hqQ hqB hBY]
  apply add_le_add
  · exact exactLengthProbabilityMass_terminalBadStarts_le_weight
      hN hq hqB
  · apply div_le_div_of_nonneg_right
    · exact_mod_cast
        Finset.card_le_card
          (Finset.sdiff_subset :
            terminalBadStarts N Q Y \ terminalBadStarts N q B ⊆
              terminalBadStarts N Q Y)
    · positivity

/-! ## Manuscript specialization -/

/-- Common row count `Q = L + E + 1` in Lemma 14.7. -/
def commonExactRowCount (L E : ℕ) : ℕ :=
  excessRowCount L E

/-- Base private-prime cutoff `W = Q + 1` in Lemma 14.7. -/
def exactLengthBaseCutoff (L E : ℕ) : ℕ :=
  commonExactRowCount L E + 1

/--
The manuscript's removed set `D(Q)`, at
`Y_Q = floor ((Q+1)^2 log (Q+1))`.
-/
def removedExactLengthStarts
    (N L E : ℕ) : Finset ℕ :=
  terminalBadStarts N (commonExactRowCount L E)
    (terminalPrimeCutoff (exactLengthBaseCutoff L E))

/-- The base-defective part of `D(Q)` for the actual excess `e`. -/
def baseDefectiveExactLengthStarts
    (N L e E : ℕ) : Finset ℕ :=
  terminalBadStarts N (excessRowCount L e)
    (exactLengthBaseCutoff L E)

/-- The removed exact-length mass for a fixed excess `e`. -/
def removedExactLengthProbabilityMass
    (N L e E : ℕ) : ℚ :=
  exactLengthProbabilityMass N (excessRowCount L e)
    (removedExactLengthStarts N L E)

/--
The shorter base-defective set is contained in `D(Q)`.
-/
theorem baseDefectiveExactLengthStarts_subset_removed
    {N L e E : ℕ} (he : e ≤ E) :
    baseDefectiveExactLengthStarts N L e E ⊆
      removedExactLengthStarts N L E := by
  apply terminalBadStarts_mono_length_cutoff
  · simp only [baseDefectiveExactLengthStarts,
      removedExactLengthStarts, commonExactRowCount]
    simp [excessRowCount]
    omega
  · apply le_terminalPrimeCutoff
    simp [exactLengthBaseCutoff, commonExactRowCount, excessRowCount]

/--
Exact form of the defect/good-start split at the parameters of Lemma 14.7.
-/
theorem removedExactLengthProbabilityMass_eq_split
    {N L e E : ℕ}
    (hN : 2 ≤ N) (hL : 1 ≤ L) (he : e ≤ E) :
    removedExactLengthProbabilityMass N L e E =
      exactLengthProbabilityMass N (excessRowCount L e)
        (baseDefectiveExactLengthStarts N L e E) +
      (((removedExactLengthStarts N L E \
          baseDefectiveExactLengthStarts N L e E).card : ℚ) /
        (2 : ℚ) ^ excessRowCount L e) := by
  unfold removedExactLengthProbabilityMass
    removedExactLengthStarts baseDefectiveExactLengthStarts
  apply exactLengthProbabilityMass_terminalBadStarts_eq_split
  · exact hN
  · simp [excessRowCount]
    omega
  · simp [commonExactRowCount, excessRowCount]
    omega
  · simp [exactLengthBaseCutoff, commonExactRowCount, excessRowCount]
    omega
  · apply le_terminalPrimeCutoff
    simp [exactLengthBaseCutoff, commonExactRowCount, excessRowCount]

/--
Finite bound for a fixed exact excess, with the harmless factor `2` coming
from the direct non-root defect count:

`sum_{x in D(Q)} P(K_{x,e})
  <= (2 M_W(N,q_e) + #D(Q)) / 2^q_e`.
-/
theorem removedExactLengthProbabilityMass_le
    {N L e E : ℕ}
    (hN : 2 ≤ N) (hL : 1 ≤ L) (he : e ≤ E) :
    removedExactLengthProbabilityMass N L e E ≤
      2 * terminalDefectWeightMass N (excessRowCount L e)
          (exactLengthBaseCutoff L E) /
        (2 : ℚ) ^ excessRowCount L e +
      ((removedExactLengthStarts N L E).card : ℚ) /
        (2 : ℚ) ^ excessRowCount L e := by
  unfold removedExactLengthProbabilityMass
    removedExactLengthStarts
  apply exactLengthProbabilityMass_terminalBadStarts_le_two_windows
  · exact hN
  · simp [excessRowCount]
    omega
  · simp [commonExactRowCount, excessRowCount]
    omega
  · simp [exactLengthBaseCutoff, commonExactRowCount, excessRowCount]
    omega
  · apply le_terminalPrimeCutoff
    simp [exactLengthBaseCutoff, commonExactRowCount, excessRowCount]

/--
Compact form of the preceding bound, with the two contributions collected
over their common denominator.
-/
theorem removedExactLengthProbabilityMass_le_compact
    {N L e E : ℕ}
    (hN : 2 ≤ N) (hL : 1 ≤ L) (he : e ≤ E) :
    removedExactLengthProbabilityMass N L e E ≤
      (2 * terminalDefectWeightMass N (excessRowCount L e)
          (exactLengthBaseCutoff L E) +
        (removedExactLengthStarts N L E).card) /
      (2 : ℚ) ^ excessRowCount L e := by
  have h := removedExactLengthProbabilityMass_le hN hL he
  calc
    removedExactLengthProbabilityMass N L e E ≤
        2 * terminalDefectWeightMass N (excessRowCount L e)
            (exactLengthBaseCutoff L E) /
          (2 : ℚ) ^ excessRowCount L e +
        ((removedExactLengthStarts N L E).card : ℚ) /
          (2 : ℚ) ^ excessRowCount L e :=
      h
    _ =
        (2 * terminalDefectWeightMass N (excessRowCount L e)
            (exactLengthBaseCutoff L E) +
          (removedExactLengthStarts N L E).card) /
        (2 : ℚ) ^ excessRowCount L e := by
      ring

/-- Sum of the removed masses over all marked excesses `0 ≤ e ≤ E`. -/
def totalRemovedExactLengthProbabilityMass
    (N L E : ℕ) : ℚ :=
  ∑ e ∈ Finset.range (E + 1),
    removedExactLengthProbabilityMass N L e E

/--
Finite full form of Lemma 14.7.

All `E+1` exact-length masses are dominated by a single common-support
weighted mass and the single removed-set cardinality:

`sum_{e=0}^E sum_{x in D(Q)} P(K_{x,e})
  <= (E+1) (2 M_W(N,Q) + #D(Q)) / 2^(L+1)`.

This common envelope is a harmless finite coarsening of the sharper
per-excess estimate above.
-/
theorem totalRemovedExactLengthProbabilityMass_le
    {N L E : ℕ} (hN : 2 ≤ N) (hL : 1 ≤ L) :
    totalRemovedExactLengthProbabilityMass N L E ≤
      (E + 1 : ℚ) *
        (2 * terminalDefectWeightMass N (commonExactRowCount L E)
            (exactLengthBaseCutoff L E) +
          (removedExactLengthStarts N L E).card) /
        (2 : ℚ) ^ (L + 1) := by
  let commonNumerator : ℚ :=
    2 * terminalDefectWeightMass N (commonExactRowCount L E)
        (exactLengthBaseCutoff L E) +
      (removedExactLengthStarts N L E).card
  calc
    totalRemovedExactLengthProbabilityMass N L E ≤
        ∑ e ∈ Finset.range (E + 1),
          (2 * terminalDefectWeightMass N (excessRowCount L e)
              (exactLengthBaseCutoff L E) +
            (removedExactLengthStarts N L E).card) /
          (2 : ℚ) ^ excessRowCount L e := by
      unfold totalRemovedExactLengthProbabilityMass
      apply Finset.sum_le_sum
      intro e he
      apply removedExactLengthProbabilityMass_le_compact hN hL
      simp only [Finset.mem_range] at he
      omega
    _ ≤
        ∑ _e ∈ Finset.range (E + 1),
          commonNumerator / (2 : ℚ) ^ (L + 1) := by
      apply Finset.sum_le_sum
      intro e he
      have heE : e ≤ E := by
        simp only [Finset.mem_range] at he
        omega
      have hqQ :
          excessRowCount L e ≤ commonExactRowCount L E := by
        simp [commonExactRowCount, excessRowCount]
        omega
      have hmass :=
        terminalDefectWeightMass_mono_length
          (N := N) (B := exactLengthBaseCutoff L E) hqQ
      have hnum :
          2 * terminalDefectWeightMass N (excessRowCount L e)
                (exactLengthBaseCutoff L E) +
              ((removedExactLengthStarts N L E).card : ℚ) ≤
            commonNumerator := by
        dsimp only [commonNumerator]
        gcongr
      have hden :
          (2 : ℚ) ^ (L + 1) ≤
            (2 : ℚ) ^ excessRowCount L e := by
        apply pow_le_pow_right₀ (by norm_num)
        simp [excessRowCount]
      apply div_le_div₀
      · dsimp only [commonNumerator]
        unfold terminalDefectWeightMass
        positivity
      · exact hnum
      · positivity
      · exact hden
    _ =
        (E + 1 : ℚ) *
          (2 * terminalDefectWeightMass N (commonExactRowCount L E)
              (exactLengthBaseCutoff L E) +
            (removedExactLengthStarts N L E).card) /
          (2 : ℚ) ^ (L + 1) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      simp only [Finset.card_range, commonNumerator]
      push_cast
      ring

/--
Fully displayed real-valued bound after inserting the certified
prime-sensitive estimate for the cardinality of `D(Q)`.
-/
theorem removedExactLengthProbabilityMass_cast_le_terminalEnvelope
    {N L e E : ℕ}
    (hN : 2 ≤ N) (hL : 1 ≤ L) (he : e ≤ E)
    (hW : 16 ≤ exactLengthBaseCutoff L E) :
    ((removedExactLengthProbabilityMass N L e E : ℚ) : ℝ) ≤
      2 *
          ((terminalDefectWeightMass N (excessRowCount L e)
            (exactLengthBaseCutoff L E) : ℚ) : ℝ) /
        (2 : ℝ) ^ excessRowCount L e +
      (2 * commonExactRowCount L E *
          Real.sqrt (dyadicCutoff N (commonExactRowCount L E)) *
          Real.exp
            (terminalBadStartScaleExponent
              (exactLengthBaseCutoff L E))) /
        (2 : ℝ) ^ excessRowCount L e := by
  have hfinite :=
    removedExactLengthProbabilityMass_le hN hL he
  have hcast :
      ((removedExactLengthProbabilityMass N L e E : ℚ) : ℝ) ≤
        2 *
            ((terminalDefectWeightMass N (excessRowCount L e)
              (exactLengthBaseCutoff L E) : ℚ) : ℝ) /
          (2 : ℝ) ^ excessRowCount L e +
        ((removedExactLengthStarts N L E).card : ℝ) /
          (2 : ℝ) ^ excessRowCount L e := by
    have hcast' :
        ((removedExactLengthProbabilityMass N L e E : ℚ) : ℝ) ≤
          ((2 * terminalDefectWeightMass N (excessRowCount L e)
                (exactLengthBaseCutoff L E) /
              (2 : ℚ) ^ excessRowCount L e +
            ((removedExactLengthStarts N L E).card : ℚ) /
              (2 : ℚ) ^ excessRowCount L e : ℚ) : ℝ) :=
      Rat.cast_le.mpr hfinite
    push_cast at hcast'
    exact hcast'
  have hcard :
      ((removedExactLengthStarts N L E).card : ℝ) ≤
        2 * commonExactRowCount L E *
          Real.sqrt (dyadicCutoff N (commonExactRowCount L E)) *
          Real.exp
            (terminalBadStartScaleExponent
              (exactLengthBaseCutoff L E)) := by
    unfold removedExactLengthStarts
    exact card_terminalBadStarts_terminalPrimeCutoff_le_scale
      (show 1 ≤ N by omega) hW
  exact hcast.trans
    (add_le_add_left
      (div_le_div_of_nonneg_right hcard (by positivity)) _)

/--
Terminal-envelope form of the full finite sum over `0 ≤ e ≤ E`.

This is the strongest source-facing finite conclusion of the module: both
the defect/good-start split and the terminal cardinal estimate have already
been inserted, and only the weighted defect mass from Proposition 3.2
remains visible.
-/
theorem totalRemovedExactLengthProbabilityMass_cast_le_terminalEnvelope
    {N L E : ℕ}
    (hN : 2 ≤ N) (hL : 1 ≤ L)
    (hW : 16 ≤ exactLengthBaseCutoff L E) :
    ((totalRemovedExactLengthProbabilityMass N L E : ℚ) : ℝ) ≤
      (E + 1 : ℝ) *
        (2 *
            ((terminalDefectWeightMass N (commonExactRowCount L E)
              (exactLengthBaseCutoff L E) : ℚ) : ℝ) +
          2 * commonExactRowCount L E *
            Real.sqrt (dyadicCutoff N (commonExactRowCount L E)) *
            Real.exp
              (terminalBadStartScaleExponent
                (exactLengthBaseCutoff L E))) /
        (2 : ℝ) ^ (L + 1) := by
  have hfinite :=
    totalRemovedExactLengthProbabilityMass_le (E := E) hN hL
  have hcast :
      ((totalRemovedExactLengthProbabilityMass N L E : ℚ) : ℝ) ≤
        (E + 1 : ℝ) *
          (2 *
              ((terminalDefectWeightMass N (commonExactRowCount L E)
                (exactLengthBaseCutoff L E) : ℚ) : ℝ) +
            ((removedExactLengthStarts N L E).card : ℝ)) /
          (2 : ℝ) ^ (L + 1) := by
    have hcast' :
        ((totalRemovedExactLengthProbabilityMass N L E : ℚ) : ℝ) ≤
          (((E + 1 : ℚ) *
              (2 * terminalDefectWeightMass N
                    (commonExactRowCount L E)
                    (exactLengthBaseCutoff L E) +
                (removedExactLengthStarts N L E).card) /
              (2 : ℚ) ^ (L + 1) : ℚ) : ℝ) :=
      Rat.cast_le.mpr hfinite
    push_cast at hcast'
    exact hcast'
  have hcard :
      ((removedExactLengthStarts N L E).card : ℝ) ≤
        2 * commonExactRowCount L E *
          Real.sqrt (dyadicCutoff N (commonExactRowCount L E)) *
          Real.exp
            (terminalBadStartScaleExponent
              (exactLengthBaseCutoff L E)) := by
    unfold removedExactLengthStarts
    exact card_terminalBadStarts_terminalPrimeCutoff_le_scale
      (show 1 ≤ N by omega) hW
  calc
    ((totalRemovedExactLengthProbabilityMass N L E : ℚ) : ℝ) ≤
        (E + 1 : ℝ) *
          (2 *
              ((terminalDefectWeightMass N (commonExactRowCount L E)
                (exactLengthBaseCutoff L E) : ℚ) : ℝ) +
            ((removedExactLengthStarts N L E).card : ℝ)) /
          (2 : ℝ) ^ (L + 1) :=
      hcast
    _ ≤
        (E + 1 : ℝ) *
          (2 *
              ((terminalDefectWeightMass N (commonExactRowCount L E)
                (exactLengthBaseCutoff L E) : ℚ) : ℝ) +
            2 * commonExactRowCount L E *
              Real.sqrt (dyadicCutoff N (commonExactRowCount L E)) *
              Real.exp
                (terminalBadStartScaleExponent
                  (exactLengthBaseCutoff L E))) /
          (2 : ℝ) ^ (L + 1) := by
      gcongr

end

end ExactLengthBadStartMass
end PaperC
