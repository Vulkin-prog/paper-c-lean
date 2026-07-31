import PaperC.Arithmetic.PolynomialZoneLargePrimes
import PaperC.Arithmetic.PrimeNumberTheoremInput
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option maxHeartbeats 1200000

/-!
# The polynomial zone in Lemma 15.2

This module specializes the finite large-prime argument to the manuscript
window

`Vₓ = {x-1, x, …, x+L-1}`,  with `B = L+1`,

and connects the resulting count of nondefective vertices to the existing
finite-cylinder probability estimate implementing equation (15.1).

There is no new bridge in this file.  Its two non-elementary premises are
the external Laishram--Shorey statement and the source-level prime number
theorem, both imported through their registered input modules.
-/

namespace PaperC
namespace PolynomialZoneCritical

open LaishramShoreyInput
open PolynomialZoneLargePrimes
open DefectivePredicate
open PrimeNumberTheoremInput
open Filter

noncomputable section

/-- The exact number of large primes guaranteed by Laishram--Shorey. -/
def polynomialPrimeExcess (B : ℕ) : ℕ :=
  min
      (PrimesUpTo.count B +
        (3 * PrimesUpTo.count B) / 4 - 1)
      (PrimesUpTo.count (2 * B) - 1) -
    PrimesUpTo.count B

/-- The exact vertex rank after the losses `3` and `2` in Lemma 15.2. -/
def polynomialVertexRank (B : ℕ) : ℕ :=
  (polynomialPrimeExcess B - 3) / 2

/-- Nondefective non-root indices of a start star. -/
def startNondefectIndicesAt
    (B x L : ℕ) : Finset (Fin L) := by
  classical
  exact Finset.univ.filter fun j ↦
    ¬HDefective B (x + j.1)

/-- The same set represented by natural indices in `range L`. -/
def startNondefectNatIndicesAt
    (B x L : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range L).filter fun j ↦
    ¬HDefective B (x + j)

@[simp]
theorem mem_startNondefectIndicesAt
    {B x L : ℕ} {j : Fin L} :
    j ∈ startNondefectIndicesAt B x L ↔
      ¬HDefective B (x + j.1) := by
  simp [startNondefectIndicesAt]

@[simp]
theorem mem_startNondefectNatIndicesAt
    {B x L j : ℕ} :
    j ∈ startNondefectNatIndicesAt B x L ↔
      j < L ∧ ¬HDefective B (x + j) := by
  simp [startNondefectNatIndicesAt]

/-- The `Fin L` and `range L` presentations have the same cardinality. -/
theorem card_startNondefectNatIndicesAt_eq
    (B x L : ℕ) :
    (startNondefectNatIndicesAt B x L).card =
      (startNondefectIndicesAt B x L).card := by
  classical
  have himage :
      (startNondefectIndicesAt B x L).image
          (fun j : Fin L ↦ j.1) =
        startNondefectNatIndicesAt B x L := by
    ext i
    simp only [Finset.mem_image, mem_startNondefectIndicesAt,
      mem_startNondefectNatIndicesAt]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨j.2, hj⟩
    · rintro ⟨hi, hgood⟩
      exact ⟨⟨i, hi⟩, hgood, rfl⟩
  rw [← himage, Finset.card_image_of_injective]
  exact Fin.val_injective

/-- Defective and nondefective non-root indices partition `Fin L`. -/
theorem card_startDefect_add_card_startNondefect
    (B x L : ℕ) :
    (BadStartMass.startDefectIndicesAt B x L).card +
        (startNondefectIndicesAt B x L).card =
      L := by
  classical
  simpa [BadStartMass.startDefectIndicesAt,
    startNondefectIndicesAt] using
    (Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin L)))
      (p := fun j : Fin L ↦ HDefective B (x + j.1)))

/-!
## Comparing the complete and non-root windows
-/

/--
The complete window contains only one vertex outside the non-root start
window.  Hence its number of nondefective vertices is at most one plus the
non-root count.
-/
theorem card_complete_nondefective_le_one_add_start
    {x L : ℕ} (hx : 0 < x) :
    (nondefectiveWindowIndices (L + 1) (x - 1) (L + 1)).card ≤
      1 + (startNondefectIndicesAt (L + 1) x L).card := by
  classical
  let complete :=
    nondefectiveWindowIndices (L + 1) (x - 1) (L + 1)
  let positive := complete.filter fun i ↦ i ≠ 0
  have hcover : complete ⊆ insert 0 positive := by
    intro i hi
    by_cases hi0 : i = 0
    · simp [hi0]
    · exact Finset.mem_insert_of_mem
        (Finset.mem_filter.mpr ⟨hi, hi0⟩)
  have himage :
      positive.image (fun i ↦ i - 1) ⊆
        startNondefectNatIndicesAt (L + 1) x L := by
    intro j hj
    obtain ⟨i, hiPositive, rfl⟩ := Finset.mem_image.mp hj
    have hiData := Finset.mem_filter.mp hiPositive
    have hiComplete :=
      mem_nondefectiveWindowIndices.mp hiData.1
    have hlabel :
        (x - 1) + i = x + (i - 1) := by
      omega
    exact mem_startNondefectNatIndicesAt.mpr
      ⟨by omega, by simpa [hlabel] using hiComplete.2⟩
  have hinj :
      Set.InjOn (fun i : ℕ ↦ i - 1) (positive : Set ℕ) := by
    intro i hi j hj hij
    have hi0 := (Finset.mem_filter.mp hi).2
    have hj0 := (Finset.mem_filter.mp hj).2
    calc
      i = (i - 1) + 1 :=
        (Nat.sub_add_cancel
          (Nat.one_le_iff_ne_zero.mpr hi0)).symm
      _ = (j - 1) + 1 := congrArg (· + 1) hij
      _ = j :=
        Nat.sub_add_cancel
          (Nat.one_le_iff_ne_zero.mpr hj0)
  calc
    complete.card ≤ (insert 0 positive).card :=
      Finset.card_le_card hcover
    _ ≤ positive.card + 1 :=
      Finset.card_insert_le 0 positive
    _ = (positive.image (fun i ↦ i - 1)).card + 1 := by
      rw [Finset.card_image_of_injOn hinj]
    _ ≤ (startNondefectNatIndicesAt (L + 1) x L).card + 1 :=
      Nat.add_le_add_right (Finset.card_le_card himage) 1
    _ = 1 + (startNondefectIndicesAt (L + 1) x L).card := by
      rw [card_startNondefectNatIndicesAt_eq]
      omega

/--
If `r` complete vertices are nondefective, the number of defective non-root
vertices is at most `B-r`, with `B=L+1`.
-/
theorem card_startDefect_le_of_complete_nondefective
    {x L r : ℕ}
    (hx : 0 < x)
    (hr :
      r ≤
        (nondefectiveWindowIndices
          (L + 1) (x - 1) (L + 1)).card) :
    (BadStartMass.startDefectIndicesAt (L + 1) x L).card ≤
      L + 1 - r := by
  have hcomplete :=
    card_complete_nondefective_le_one_add_start (L := L) hx
  have hpartition :=
    card_startDefect_add_card_startNondefect (L + 1) x L
  omega

/-!
## Specialization of the finite Laishram--Shorey argument
-/

/--
The exact finite lower bound for the number of nondefective vertices in the
manuscript polynomial band `L+2 < x ≤ 2L²`.
-/
theorem laishramShorey_completeWindow_lower_bound
    (hLS : LaishramShoreyStatement)
    {x L : ℕ}
    (hleft : L + 2 < x)
    (hright : x ≤ 2 * L ^ 2) :
    (min
          (PrimesUpTo.count (L + 1) +
            (3 * PrimesUpTo.count (L + 1)) / 4 - 1)
          (PrimesUpTo.count (2 * (L + 1)) - 1) -
        PrimesUpTo.count (L + 1) - 3) / 2 ≤
      (nondefectiveWindowIndices
        (L + 1) (x - 1) (L + 1)).card := by
  have hL : 1 ≤ L := by
    nlinarith
  have hn : 0 < x - 1 := by omega
  have hk : 2 ≤ L + 1 := by omega
  have hnk : L + 1 < x - 1 := by omega
  have hquadratic :
      ∀ i < L + 1,
        (x - 1) + i ≤ 3 * (L + 1) ^ 2 := by
    intro i hi
    calc
      (x - 1) + i ≤ x + i := by omega
      _ ≤ 2 * L ^ 2 + L := by omega
      _ ≤ 3 * (L + 1) ^ 2 := by nlinarith
  have hcubic :
      ∀ i < L + 1,
        (x - 1) + i < (L + 1) ^ 3 := by
    intro i hi
    calc
      (x - 1) + i < x + i := by omega
      _ ≤ 2 * L ^ 2 + L := by omega
      _ < (L + 1) ^ 3 := by nlinarith
  exact laishramShorey_nondefectiveWindow_lower_bound
    hLS hn hk hnk hquadratic hcubic

/-!
## The explicit `c₃ B / log B` consequence of PNT

The manuscript next replaces the exact prime-counting rank by a constant
multiple of `B / log B`.  The following theorem derives that replacement
from the already registered source-level prime number theorem.  It introduces
no additional hypothesis or bridge.
-/

/--
PNT implies the quantitative lower bound

`polynomialVertexRank B ≥ (1/32) B / log B`

for all sufficiently large `B`.  The constant is deliberately conservative.
-/
theorem primeNumberTheorem_implies_polynomialVertexRank_lower
    (hpnt : PrimeNumberTheoremStatement) :
    ∃ B₀ : ℕ, ∀ B ≥ B₀,
      (1 / 32 : ℝ) *
          ((B : ℝ) / Real.log (B : ℝ)) ≤
        (polynomialVertexRank B : ℝ) := by
  have hpntLower :
      ∀ᶠ B : ℕ in atTop,
        (7 / 8 : ℝ) <
          (PrimesUpTo.count B : ℝ) *
            Real.log (B : ℝ) / (B : ℝ) :=
    hpnt.eventually (Ioi_mem_nhds (by norm_num))
  have hpntUpper :
      ∀ᶠ B : ℕ in atTop,
        (PrimesUpTo.count B : ℝ) *
            Real.log (B : ℝ) / (B : ℝ) <
          (9 / 8 : ℝ) :=
    hpnt.eventually (Iio_mem_nhds (by norm_num))
  obtain ⟨Blower, hBlower⟩ :=
    eventually_atTop.mp hpntLower
  have hpntLowerTwo :
      ∀ᶠ B : ℕ in atTop,
        (7 / 8 : ℝ) <
          (PrimesUpTo.count (2 * B) : ℝ) *
            Real.log ((2 * B : ℕ) : ℝ) /
              ((2 * B : ℕ) : ℝ) := by
    filter_upwards [eventually_ge_atTop Blower] with B hB
    exact hBlower (2 * B) (by omega)
  have hlogRatio :
      ∀ᶠ B : ℕ in atTop,
        5 * Real.log 2 ≤ Real.log (B : ℝ) :=
    (Real.tendsto_log_atTop.comp
      tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop (5 * Real.log 2))
  have hlogLinearRaw :
      ∀ᶠ B : ℕ in atTop,
        ‖Real.log (B : ℝ)‖ ≤
          (1 / 128 : ℝ) * ‖(B : ℝ)‖ :=
    tendsto_natCast_atTop_atTop.eventually
      (Real.isLittleO_log_id_atTop.bound (by norm_num))
  have heventually :
      ∀ᶠ B : ℕ in atTop,
        (1 / 32 : ℝ) *
            ((B : ℝ) / Real.log (B : ℝ)) ≤
          (polynomialVertexRank B : ℝ) := by
    filter_upwards
      [hpntLower, hpntUpper, hpntLowerTwo, hlogRatio,
        hlogLinearRaw, eventually_ge_atTop 2] with
        B hLower hUpper hLowerTwo hlogRatioB hlogLinearNorm hBtwo
    have hBpos : (0 : ℝ) < (B : ℝ) := by positivity
    have hlogPos : 0 < Real.log (B : ℝ) :=
      Real.log_pos (by exact_mod_cast hBtwo)
    have hlogLinear :
        Real.log (B : ℝ) ≤ (1 / 128 : ℝ) * (B : ℝ) := by
      rw [Real.norm_eq_abs, abs_of_pos hlogPos,
        Real.norm_eq_abs, abs_of_nonneg
          (Nat.cast_nonneg B)] at hlogLinearNorm
      exact hlogLinearNorm
    let t : ℝ := (B : ℝ) / Real.log (B : ℝ)
    have ht : 128 ≤ t := by
      dsimp only [t]
      rw [le_div_iff₀ hlogPos]
      nlinarith
    have hlogTwoB :
        Real.log ((2 * B : ℕ) : ℝ) ≤
          (6 / 5 : ℝ) * Real.log (B : ℝ) := by
      have hlogIdentity :
          Real.log ((2 * B : ℕ) : ℝ) =
            Real.log 2 + Real.log (B : ℝ) := by
        push_cast
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
          (ne_of_gt hBpos)]
      rw [hlogIdentity]
      nlinarith
    have hpiLower :
        (7 / 8 : ℝ) * t <
          (PrimesUpTo.count B : ℝ) := by
      dsimp only [t]
      rw [show
        (7 / 8 : ℝ) *
            ((B : ℝ) / Real.log (B : ℝ)) =
          ((7 / 8 : ℝ) * (B : ℝ)) /
            Real.log (B : ℝ) by ring]
      rw [div_lt_iff₀ hlogPos]
      rw [lt_div_iff₀ hBpos] at hLower
      nlinarith
    have hpiUpper :
        (PrimesUpTo.count B : ℝ) <
          (9 / 8 : ℝ) * t := by
      dsimp only [t]
      rw [show
        (9 / 8 : ℝ) *
            ((B : ℝ) / Real.log (B : ℝ)) =
          ((9 / 8 : ℝ) * (B : ℝ)) /
            Real.log (B : ℝ) by ring]
      rw [lt_div_iff₀ hlogPos]
      rw [div_lt_iff₀ hBpos] at hUpper
      nlinarith
    have htwoBpos : (0 : ℝ) < ((2 * B : ℕ) : ℝ) := by
      positivity
    have hpiTwoScaled :
        (7 / 8 : ℝ) * ((2 * B : ℕ) : ℝ) <
          (PrimesUpTo.count (2 * B) : ℝ) *
            Real.log ((2 * B : ℕ) : ℝ) := by
      rw [lt_div_iff₀ htwoBpos] at hLowerTwo
      exact hLowerTwo
    have hcastTwo :
        ((2 * B : ℕ) : ℝ) = 2 * (B : ℝ) := by
      norm_num
    have hpiTwoLog :
        (PrimesUpTo.count (2 * B) : ℝ) *
            Real.log ((2 * B : ℕ) : ℝ) ≤
          (PrimesUpTo.count (2 * B) : ℝ) *
            ((6 / 5 : ℝ) * Real.log (B : ℝ)) :=
      mul_le_mul_of_nonneg_left hlogTwoB
        (Nat.cast_nonneg _)
    have hpiTwoLower :
        (35 / 24 : ℝ) * t <
          (PrimesUpTo.count (2 * B) : ℝ) := by
      dsimp only [t]
      rw [show
        (35 / 24 : ℝ) *
            ((B : ℝ) / Real.log (B : ℝ)) =
          ((35 / 24 : ℝ) * (B : ℝ)) /
            Real.log (B : ℝ) by ring]
      rw [div_lt_iff₀ hlogPos]
      nlinarith [hcastTwo]
    have hgap :
        (1 / 3 : ℝ) * t <
          (PrimesUpTo.count (2 * B) : ℝ) -
            (PrimesUpTo.count B : ℝ) := by
      nlinarith
    let P : ℕ := PrimesUpTo.count B
    let Q : ℕ := PrimesUpTo.count (2 * B)
    let F : ℕ := (3 * P) / 4
    let A : ℕ := P + F - 1
    let C : ℕ := Q - 1
    have hfloorNat :
        3 * P ≤ 4 * F + 3 := by
      dsimp only [F]
      omega
    have hfloorReal :
        (3 : ℝ) * (P : ℝ) ≤
          4 * (F : ℝ) + 3 := by
      exact_mod_cast hfloorNat
    have hPIdent :
        (P : ℝ) = (PrimesUpTo.count B : ℝ) := by
      rfl
    have hQIdent :
        (Q : ℝ) =
          (PrimesUpTo.count (2 * B) : ℝ) := by
      rfl
    have hFpos : 1 ≤ F := by
      have hPbig : (8 : ℝ) < (P : ℝ) := by
        rw [hPIdent]
        nlinarith
      have hPbigNat : 8 < P := by
        exact_mod_cast hPbig
      dsimp only [F]
      omega
    have hQgap : P + 1 ≤ Q := by
      have hreal : (P : ℝ) + 1 < (Q : ℝ) := by
        rw [hPIdent, hQIdent]
        nlinarith
      exact_mod_cast hreal.le
    have hbranchA :
        (1 / 4 : ℝ) * t ≤
          (A : ℝ) - (P : ℝ) := by
      have hcastA :
          (A : ℝ) - (P : ℝ) =
            (F : ℝ) - 1 := by
        dsimp only [A]
        rw [Nat.cast_sub (by omega : 1 ≤ P + F)]
        push_cast
        ring
      rw [hcastA]
      rw [hPIdent] at hfloorReal
      nlinarith
    have hbranchC :
        (1 / 4 : ℝ) * t ≤
          (C : ℝ) - (P : ℝ) := by
      have hcastC :
          (C : ℝ) - (P : ℝ) =
            (Q : ℝ) - 1 - (P : ℝ) := by
        dsimp only [C]
        rw [Nat.cast_sub (by omega : 1 ≤ Q)]
        push_cast
        ring
      rw [hcastC, hPIdent, hQIdent]
      nlinarith
    have hPA : P ≤ A := by
      dsimp only [A]
      omega
    have hPC : P ≤ C := by
      dsimp only [C]
      omega
    have hPmin : P ≤ min A C :=
      le_min hPA hPC
    have hexcess :
        (1 / 4 : ℝ) * t ≤
          (polynomialPrimeExcess B : ℝ) := by
      have hmin :
          (1 / 4 : ℝ) * t ≤
            ((min A C : ℕ) : ℝ) - (P : ℝ) := by
        rw [Nat.cast_min, ← min_sub_sub_right]
        exact le_min hbranchA hbranchC
      have hdefinition :
          polynomialPrimeExcess B = min A C - P := by
        simp only [polynomialPrimeExcess, A, C, F, P, Q]
      rw [hdefinition, Nat.cast_sub hPmin]
      exact hmin
    have hexcessNat : 3 ≤ polynomialPrimeExcess B := by
      have hreal :
          (3 : ℝ) < (polynomialPrimeExcess B : ℝ) := by
        nlinarith
      exact_mod_cast hreal.le
    let E : ℕ := polynomialPrimeExcess B - 3
    let R : ℕ := E / 2
    have hhalfNat : E ≤ 2 * R + 1 := by
      dsimp only [R]
      omega
    have hhalfReal :
        (E : ℝ) ≤ 2 * (R : ℝ) + 1 := by
      exact_mod_cast hhalfNat
    have hcastE :
        (E : ℝ) =
          (polynomialPrimeExcess B : ℝ) - 3 := by
      dsimp only [E]
      rw [Nat.cast_sub hexcessNat]
      push_cast
      ring
    have hR :
        (1 / 32 : ℝ) * t ≤ (R : ℝ) := by
      rw [hcastE] at hhalfReal
      nlinarith
    have hRdefinition :
        R = polynomialVertexRank B := by
      rfl
    rw [← hRdefinition]
    exact hR
  exact eventually_atTop.mp heventually

/-!
Rank-level existence of a constant `c₃` as used in Lemma 15.2.  Combining
this eventual estimate with the Laishram--Shorey window bound and summing
the resulting probabilities is a separate remaining step.
-/
theorem exists_c3_polynomialVertexRank
    (hpnt : PrimeNumberTheoremStatement) :
    ∃ c₃ : ℝ, 0 < c₃ ∧
      ∃ B₀ : ℕ, ∀ B ≥ B₀,
        c₃ * ((B : ℝ) / Real.log (B : ℝ)) ≤
          (polynomialVertexRank B : ℝ) := by
  refine ⟨1 / 32, by norm_num, ?_⟩
  exact primeNumberTheorem_implies_polynomialVertexRank_lower hpnt

/-!
## Equation (15.1)
-/

/--
Finite probability consequence of equation (15.1): any lower bound `r` on
the number of nondefective complete vertices gives the displayed power-of-two
bound.  The loss of one is exactly the possible root vertex.
-/
theorem startProbability_le_of_complete_nondefective
    {x L r : ℕ}
    (hx : 2 ≤ x)
    (hL : 0 < L)
    (hr :
      r ≤
        (nondefectiveWindowIndices
          (L + 1) (x - 1) (L + 1)).card) :
    startProbability x L x ≤
      (2 : ℚ) ^ (L + 1 - r) / (2 : ℚ) ^ L := by
  have hxBlock : x ∈ dyadicBlock x := by
    simp only [dyadicBlock, Finset.mem_Ico]
    omega
  have hbase :=
    BadStartMass.startProbability_le_two_pow_defect_div
      (N := x) (x := x) (L := L) (B := L + 1)
      hx hxBlock hL le_rfl
  have hdefect :=
    card_startDefect_le_of_complete_nondefective
      (x := x) (L := L) (r := r) (by omega) hr
  exact hbase.trans
    (div_le_div_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num) hdefect)
      (by positivity))

/--
Pointwise polynomial-zone bound obtained by substituting the exact
Laishram--Shorey rank into (15.1).
-/
theorem laishramShorey_startProbability_bound
    (hLS : LaishramShoreyStatement)
    {x L : ℕ}
    (hleft : L + 2 < x)
    (hright : x ≤ 2 * L ^ 2) :
    startProbability x L x ≤
      (2 : ℚ) ^
          (L + 1 -
            ((min
                  (PrimesUpTo.count (L + 1) +
                    (3 * PrimesUpTo.count (L + 1)) / 4 - 1)
                  (PrimesUpTo.count (2 * (L + 1)) - 1) -
                PrimesUpTo.count (L + 1) - 3) / 2)) /
        (2 : ℚ) ^ L := by
  have hL : 0 < L := by
    nlinarith
  exact startProbability_le_of_complete_nondefective
    (by omega) hL
    (laishramShorey_completeWindow_lower_bound
      hLS hleft hright)

end

end PolynomialZoneCritical
end PaperC
