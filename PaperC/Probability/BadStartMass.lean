import PaperC.Affine.StartDefectRank
import PaperC.Probability.BadStartCount
import PaperC.Probability.DefectFirstMoment
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Probability mass of terminal-cutoff bad starts

This module gives the exact finite assembly behind Lemma 13.4.  It works at
two cutoffs `B ≤ Y`.

* At the base cutoff `B`, the relation defect of a start is bounded by the
  number of `B`-defective non-root vertices.  Hence its probability is at
  most `2^m / 2^L`, and on the bad set this is at most
  `2 (2^m - 1) / 2^L`.
* Outside the base bad set, the start rows have full rank already at cutoff
  `B`, so the (unconditional finite-cylinder) probability is exactly `2^-L`.
* The `Y`-bad set splits into its intersection with the `B`-bad set and the
  remaining full-rank starts.

All conclusions below are finite equalities or inequalities.  The asymptotic
inputs `M_B = N^(1/2+o(1))` and `#D_Y = N^(1/2+o(1))` can therefore be
inserted without any hidden probabilistic step.
-/

namespace PaperC
namespace BadStartMass

open scoped BigOperators

open Affine
open BadStartCount
open DefectivePredicate
open LargeOddKernel

noncomputable section

/-- Defective non-root start vertices at an arbitrary prime cutoff `B`. -/
def startDefectIndicesAt
    (B x L : ℕ) : Finset (Fin L) := by
  classical
  exact Finset.univ.filter fun j ↦ HDefective B (x + j.1)

@[simp]
theorem mem_startDefectIndicesAt
    {B x L : ℕ} {j : Fin L} :
    j ∈ startDefectIndicesAt B x L ↔
      HDefective B (x + j.1) := by
  simp [startDefectIndicesAt]

/-- Defectivity is monotone when the permitted prime cutoff grows. -/
theorem hDefective_mono
    {B Y n : ℕ} (hBY : B ≤ Y)
    (h : HDefective B n) :
    HDefective Y n := by
  intro p hp hYp
  exact h p hp (lt_of_le_of_lt hBY hYp)

/-- Equivalently, a unit large kernel stays a unit at every larger cutoff. -/
theorem largeOddKernel_eq_one_mono
    {B Y n : ℕ} (hBY : B ≤ Y)
    (h : largeOddKernel B n = 1) :
    largeOddKernel Y n = 1 := by
  rw [largeOddKernel_eq_one_iff_hDefective] at h ⊢
  exact hDefective_mono hBY h

/-- The bad-start sets are monotone in the prime cutoff. -/
theorem terminalBadStarts_mono
    {N L B Y : ℕ} (hBY : B ≤ Y) :
    terminalBadStarts N L B ⊆
      terminalBadStarts N L Y := by
  intro x hx
  obtain ⟨hxBlock, j, hj, hkernel⟩ :=
    mem_terminalBadStarts.mp hx
  exact mem_terminalBadStarts.mpr
    ⟨hxBlock, j, hj,
      largeOddKernel_eq_one_mono hBY hkernel⟩

/--
The defect indices at the natural private-prime cutoff `L+1` are contained
in those at any larger cutoff.
-/
theorem startDefectIndices_subset_at
    {B x L : ℕ} (hLB : L + 1 ≤ B) :
    Affine.StartDefectRank.startDefectIndices x L ⊆
      startDefectIndicesAt B x L := by
  intro j hj
  have hjDefect :
      HDefective (L + 1) (x + j.1) := by
    simpa [Affine.StartDefectRank.startDefectIndices] using hj
  exact mem_startDefectIndicesAt.mpr
    (hDefective_mono hLB hjDefect)

/--
Private pivots above `L+1` bound the relation defect by the number of
vertices defective at any larger cutoff `B`.
-/
theorem relationRho_startSystem_le_card_startDefectIndicesAt
    {N x L B : ℕ}
    (hN : 2 ≤ N) (hx : x ∈ dyadicBlock N)
    (hL : 0 < L) (hLB : L + 1 ≤ B) :
    relationRho (startSystem (dyadicCutoff N L) x L) ≤
      (startDefectIndicesAt B x L).card := by
  have hrank :
      relationRho (startSystem (dyadicCutoff N L) x L) ≤
        (Affine.StartDefectRank.startDefectIndices x L).card := by
    unfold relationRho
    calc
      Module.finrank F₂
          (RelationSpace
            (startSystem (dyadicCutoff N L) x L)) ≤
          Module.finrank F₂
            ((j :
              ↥(Affine.StartDefectRank.startDefectIndices x L)) →
                F₂) :=
        LinearMap.finrank_le_finrank_of_injective
          (Affine.StartDefectRank.startDefectRestriction_injective
            hN hx hL)
      _ =
          (Affine.StartDefectRank.startDefectIndices x L).card := by
        rw [Module.finrank_fintype_fun_eq_card]
        simp
  exact hrank.trans
    (Finset.card_le_card (startDefectIndices_subset_at hLB))

/-- A start is bad exactly when its arbitrary-cutoff defect set is nonempty. -/
theorem startDefectIndicesAt_nonempty_iff
    (B x L : ℕ) :
    (startDefectIndicesAt B x L).Nonempty ↔
      ∃ j < L, largeOddKernel B (x + j) = 1 := by
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨j.1, j.2, ?_⟩
    rw [largeOddKernel_eq_one_iff_hDefective]
    exact mem_startDefectIndicesAt.mp hj
  · rintro ⟨j, hj, hkernel⟩
    let jf : Fin L := ⟨j, hj⟩
    refine ⟨jf, mem_startDefectIndicesAt.mpr ?_⟩
    rw [← largeOddKernel_eq_one_iff_hDefective]
    simpa [jf] using hkernel

/-- Outside the bad set, the relation defect is zero. -/
theorem relationRho_startSystem_eq_zero_of_not_bad
    {N x L B : ℕ}
    (hN : 2 ≤ N) (hx : x ∈ dyadicBlock N)
    (hL : 0 < L) (hLB : L + 1 ≤ B)
    (hgood : x ∉ terminalBadStarts N L B) :
    relationRho (startSystem (dyadicCutoff N L) x L) = 0 := by
  have hnoWitness :
      ¬∃ j < L, largeOddKernel B (x + j) = 1 := by
    intro h
    exact hgood (mem_terminalBadStarts.mpr ⟨hx, h⟩)
  have hindices :
      startDefectIndicesAt B x L = ∅ := by
    rw [← Finset.not_nonempty_iff_eq_empty,
      startDefectIndicesAt_nonempty_iff]
    exact hnoWitness
  have hrho :=
    relationRho_startSystem_le_card_startDefectIndicesAt
      hN hx hL hLB
  rw [hindices] at hrho
  simpa using hrho

/--
Outside the cutoff-`B` bad set, the exact finite-cylinder start probability
is the independent baseline `2^-L`.
-/
theorem startProbability_eq_baseline_of_not_bad
    {N x L B : ℕ}
    (hN : 2 ≤ N) (hx : x ∈ dyadicBlock N)
    (hL : 0 < L) (hLB : L + 1 ≤ B)
    (hgood : x ∉ terminalBadStarts N L B) :
    startProbability N L x =
      (1 : ℚ) / (2 : ℚ) ^ L := by
  let A := startSystem (dyadicCutoff N L) x L
  let b := startRhs L
  have hrho : relationRho A = 0 := by
    dsimp only [A]
    exact relationRho_startSystem_eq_zero_of_not_bad
      hN hx hL hLB hgood
  have hcharacter : relationCharacter A b = 0 := by
    by_contra hne
    have hpos := relationRho_pos_of_character_ne_zero A b hne
    omega
  have heta : relationEta A b = 1 :=
    (relationEta_eq_one_iff A b).mpr hcharacter
  rw [DefectFirstMoment.startProbability_eq_eta_mul_two_pow_rho_div
    N L x hL]
  dsimp only [A, b] at hrho heta
  rw [heta, hrho]
  norm_num

/-- Every start probability is nonnegative. -/
theorem startProbability_nonneg
    (N L x : ℕ) :
    0 ≤ startProbability N L x := by
  classical
  unfold startProbability uniformEventProbability
  positivity

/--
At cutoff `B`, the start probability is bounded by `2^m / 2^L`, where `m`
is the number of defective non-root vertices.
-/
theorem startProbability_le_two_pow_defect_div
    {N x L B : ℕ}
    (hN : 2 ≤ N) (hx : x ∈ dyadicBlock N)
    (hL : 0 < L) (hLB : L + 1 ≤ B) :
    startProbability N L x ≤
      (2 : ℚ) ^ (startDefectIndicesAt B x L).card /
        (2 : ℚ) ^ L := by
  rw [DefectFirstMoment.startProbability_eq_eta_mul_two_pow_rho_div
    N L x hL]
  have hrho :=
    relationRho_startSystem_le_card_startDefectIndicesAt
      hN hx hL hLB
  rcases relationEta_eq_zero_or_one
      (startSystem (dyadicCutoff N L) x L) (startRhs L) with
    heta | heta
  · rw [heta]
    have hnonneg :
        (0 : ℚ) ≤
          (2 : ℚ) ^ (startDefectIndicesAt B x L).card /
            (2 : ℚ) ^ L :=
      div_nonneg (by positivity) (by positivity)
    simpa only [Nat.cast_zero, zero_mul, zero_div] using hnonneg
  · rw [heta]
    simp only [Nat.cast_one, one_mul]
    exact div_le_div_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num) hrho)
      (by positivity)

/-- Elementary inequality used on a genuinely bad start. -/
theorem two_pow_le_two_mul_two_pow_sub_one
    {m : ℕ} (hm : 0 < m) :
    2 ^ m ≤ 2 * (2 ^ m - 1) := by
  have htwo : 2 ≤ 2 ^ m := by
    have hpow : 2 ^ 1 ≤ 2 ^ m :=
      Nat.pow_le_pow_right (by omega) hm
    simpa using hpow
  omega

/--
Pointwise weighted bound on a bad start:

`P(J_x=1) ≤ 2 (2^m_B(x)-1) / 2^L`.
-/
theorem startProbability_le_two_mul_defectWeight_div
    {N x L B : ℕ}
    (hN : 2 ≤ N) (hx : x ∈ dyadicBlock N)
    (hL : 0 < L) (hLB : L + 1 ≤ B)
    (hbad : x ∈ terminalBadStarts N L B) :
    startProbability N L x ≤
      (2 : ℚ) *
          (((2 : ℕ) ^ (startDefectIndicesAt B x L).card - 1 : ℕ) : ℚ) /
        (2 : ℚ) ^ L := by
  have hnonempty :
      (startDefectIndicesAt B x L).Nonempty :=
    (startDefectIndicesAt_nonempty_iff B x L).mpr
      (mem_terminalBadStarts.mp hbad).2
  have hcardPos :
      0 < (startDefectIndicesAt B x L).card :=
    Finset.card_pos.mpr hnonempty
  have hpowNat :=
    two_pow_le_two_mul_two_pow_sub_one hcardPos
  have hpowQ :
      (2 : ℚ) ^ (startDefectIndicesAt B x L).card ≤
        (2 : ℚ) *
          (((2 : ℕ) ^ (startDefectIndicesAt B x L).card - 1 : ℕ) : ℚ) := by
    exact_mod_cast hpowNat
  exact
    (startProbability_le_two_pow_defect_div
      hN hx hL hLB).trans
      (div_le_div_of_nonneg_right hpowQ (by positivity))

/-- Rational weighted defect mass over the full dyadic block. -/
def terminalDefectWeightMass
    (N L B : ℕ) : ℚ :=
  ∑ x ∈ dyadicBlock N,
    (((2 : ℕ) ^ (startDefectIndicesAt B x L).card - 1 : ℕ) : ℚ)

/-- Probability mass of starts whose index lies in a finite set. -/
def startProbabilityMass
    (N L : ℕ) (s : Finset ℕ) : ℚ :=
  ∑ x ∈ s, startProbability N L x

/--
The base-cutoff bad-start mass is controlled by the full weighted defect
mass, exactly as in the first half of Lemma 13.4.
-/
theorem startProbabilityMass_terminalBadStarts_le_weight
    {N L B : ℕ}
    (hN : 2 ≤ N) (hL : 0 < L)
    (hLB : L + 1 ≤ B) :
    startProbabilityMass N L (terminalBadStarts N L B) ≤
      2 * terminalDefectWeightMass N L B / (2 : ℚ) ^ L := by
  let w : ℕ → ℚ := fun x ↦
    (((2 : ℕ) ^ (startDefectIndicesAt B x L).card - 1 : ℕ) : ℚ)
  have hsubset :
      terminalBadStarts N L B ⊆ dyadicBlock N := by
    intro x hx
    exact (mem_terminalBadStarts.mp hx).1
  have hsumSubset :
      (∑ x ∈ terminalBadStarts N L B, w x) ≤
        ∑ x ∈ dyadicBlock N, w x := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro x hx hnot
    dsimp only [w]
    positivity
  calc
    startProbabilityMass N L (terminalBadStarts N L B) ≤
        ∑ x ∈ terminalBadStarts N L B,
          (2 : ℚ) * w x / (2 : ℚ) ^ L := by
      apply Finset.sum_le_sum
      intro x hx
      exact startProbability_le_two_mul_defectWeight_div
        hN (mem_terminalBadStarts.mp hx).1 hL hLB hx
    _ = (2 / (2 : ℚ) ^ L) *
        (∑ x ∈ terminalBadStarts N L B, w x) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ ≤ (2 / (2 : ℚ) ^ L) *
        (∑ x ∈ dyadicBlock N, w x) := by
      exact mul_le_mul_of_nonneg_left hsumSubset (by positivity)
    _ = 2 * terminalDefectWeightMass N L B /
        (2 : ℚ) ^ L := by
      simp only [terminalDefectWeightMass, w]
      ring

/--
Exact two-cutoff assembly behind Lemma 13.4:

`mass(D_Y) ≤ 2 M_B / 2^L + #D_Y / 2^L`.

The first summand is the weighted base-defect contribution; every
`Y`-bad but not `B`-bad start has full row rank and contributes exactly the
baseline.
-/
theorem startProbabilityMass_terminalBadStarts_le_two_cutoffs
    {N L B Y : ℕ}
    (hN : 2 ≤ N) (hL : 0 < L)
    (hLB : L + 1 ≤ B) (hBY : B ≤ Y) :
    startProbabilityMass N L (terminalBadStarts N L Y) ≤
      2 * terminalDefectWeightMass N L B / (2 : ℚ) ^ L +
        ((terminalBadStarts N L Y).card : ℚ) / (2 : ℚ) ^ L := by
  let DB := terminalBadStarts N L B
  let DY := terminalBadStarts N L Y
  have hsubset : DB ⊆ DY :=
    terminalBadStarts_mono hBY
  have hsplit :
      startProbabilityMass N L DY =
        startProbabilityMass N L DB +
          startProbabilityMass N L (DY \ DB) := by
    simp only [startProbabilityMass]
    rw [← Finset.sum_sdiff hsubset]
    ac_rfl
  have hbase :
      startProbabilityMass N L DB ≤
        2 * terminalDefectWeightMass N L B / (2 : ℚ) ^ L := by
    exact startProbabilityMass_terminalBadStarts_le_weight hN hL hLB
  have hremaining :
      startProbabilityMass N L (DY \ DB) =
        ((DY \ DB).card : ℚ) / (2 : ℚ) ^ L := by
    simp only [startProbabilityMass]
    calc
      (∑ x ∈ DY \ DB, startProbability N L x) =
          ∑ _x ∈ DY \ DB, (1 : ℚ) / (2 : ℚ) ^ L := by
        apply Finset.sum_congr rfl
        intro x hx
        have hxDY : x ∈ DY := (Finset.mem_sdiff.mp hx).1
        have hxDB : x ∉ DB := (Finset.mem_sdiff.mp hx).2
        exact startProbability_eq_baseline_of_not_bad
          hN (mem_terminalBadStarts.mp hxDY).1 hL hLB hxDB
      _ = ((DY \ DB).card : ℚ) / (2 : ℚ) ^ L := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
  have hcard :
      ((DY \ DB).card : ℚ) / (2 : ℚ) ^ L ≤
        (DY.card : ℚ) / (2 : ℚ) ^ L := by
    apply div_le_div_of_nonneg_right
    · exact_mod_cast
        Finset.card_le_card (Finset.sdiff_subset : DY \ DB ⊆ DY)
    · positivity
  rw [hsplit, hremaining]
  exact add_le_add hbase hcard

end

end BadStartMass
end PaperC
