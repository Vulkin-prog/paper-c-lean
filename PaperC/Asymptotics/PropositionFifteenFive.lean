import PaperC.Arithmetic.BalasubramanianShoreyMaximum
import PaperC.Asymptotics.HighZoneTwoDefects
import PaperC.Asymptotics.LemmaFifteenThree
import PaperC.Asymptotics.LowZoneCritical
import PaperC.Asymptotics.PolynomialZoneSum
import PaperC.Asymptotics.DependencyEdgesCritical
import PaperC.Probability.BadStartMass
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option maxHeartbeats 1600000

/-!
# Proposition 15.5: truncating the deep dyadic blocks

This module isolates the exact finite first-moment assembly used in
Proposition 15.5.  In one dyadic block `[N,2N)`, starts whose complete
`B = L+1` window has at most one defective vertex contribute the independent
scale `O(N 2⁻ᴸ)`.  The remaining starts are counted by Lemma 15.3 and each is
weighted using the pointwise gap from Lemma 15.4.

The estimates are stated for the genuine finite-cylinder probabilities
`startProbability x L x`; no independence between different dyadic blocks is
used.
-/

namespace PaperC
namespace PropositionFifteenFive

open scoped BigOperators
open Filter
open BadStartMass
open BalasubramanianShoreyMaximum
open HighZoneTwoDefects

noncomputable section

/-- The real start probability in the smallest dyadic cylinder containing
the whole window based at `x`. -/
noncomputable def globalStartProbability (L x : ℕ) : ℝ :=
  (startProbability x L x : ℚ)

/-- First-moment mass of all starts in one complete dyadic block. -/
noncomputable def highBlockProbabilityMass (N L : ℕ) : ℝ :=
  ∑ x ∈ Finset.Ico N (2 * N), globalStartProbability L x

/-- Defective non-root vertices inject into the complete manuscript window
`{x-1, ..., x+L-1}` by the offset map `j ↦ j+2`. -/
theorem card_startDefectIndicesAt_le_defectiveOffsets
    {x L : ℕ} (hx : 2 ≤ x) :
    (startDefectIndicesAt (L + 1) x L).card ≤
      (defectiveOffsets (L + 1) (x - 2)).card := by
  classical
  let offset : Fin L → ℕ := fun j ↦ j.1 + 2
  have hoffset : Function.Injective offset := by
    intro i j hij
    apply Fin.ext
    dsimp only [offset] at hij
    omega
  have hsubset :
      (startDefectIndicesAt (L + 1) x L).image offset ⊆
        defectiveOffsets (L + 1) (x - 2) := by
    intro d hd
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hd
    rw [mem_defectiveOffsets]
    have hjdef :
        DefectivePredicate.HDefective (L + 1) (x + j.1) :=
      mem_startDefectIndicesAt.mp hj
    have hjlt : j.1 < L := j.2
    dsimp only [offset]
    refine ⟨by omega, by omega, ?_⟩
    rw [show x - 2 + (j.1 + 2) = x + j.1 by omega]
    exact hjdef
  calc
    (startDefectIndicesAt (L + 1) x L).card =
        ((startDefectIndicesAt (L + 1) x L).image offset).card := by
      symm
      exact Finset.card_image_of_injective _ hoffset
    _ ≤ (defectiveOffsets (L + 1) (x - 2)).card :=
      Finset.card_le_card hsubset

/-- Real form of the private-prime pointwise estimate (15.1), with the
complete-window defect count as exponent. -/
theorem globalStartProbability_le_defectiveWindow
    {x L : ℕ} (hx : 2 ≤ x) (hL : 0 < L) :
    globalStartProbability L x ≤
      (2 : ℝ) ^
          (defectiveOffsets (L + 1) (x - 2)).card /
        (2 : ℝ) ^ L := by
  have hxBlock : x ∈ dyadicBlock x := by
    simp only [dyadicBlock, Finset.mem_Ico]
    omega
  have hq :=
    startProbability_le_two_pow_defect_div
      (N := x) (x := x) (L := L) (B := L + 1)
      hx hxBlock hL le_rfl
  have hcast := (Rat.cast_le (K := ℝ)).2 hq
  push_cast at hcast
  unfold globalStartProbability
  exact hcast.trans
    (div_le_div_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num)
        (card_startDefectIndicesAt_le_defectiveOffsets hx))
      (by positivity))

/-- A window with at most one defect has start probability at most
`2 / 2^L`.  The harmless factor two avoids any extra rank argument. -/
theorem globalStartProbability_le_baseline_of_card_le_one
    {x L : ℕ} (hx : 2 ≤ x) (hL : 0 < L)
    (hcard :
      (defectiveOffsets (L + 1) (x - 2)).card ≤ 1) :
    globalStartProbability L x ≤
      2 / (2 : ℝ) ^ L := by
  exact (globalStartProbability_le_defectiveWindow hx hL).trans
    (div_le_div_of_nonneg_right
      (by
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcard with hzero | hone
        · simp [hzero]
        · simp [hone])
      (by positivity))

/-- Lemma 15.4 may be inserted directly as a real exponent bound. -/
theorem globalStartProbability_le_of_real_defect_bound
    {x L : ℕ} (hx : 2 ≤ x) (hL : 0 < L)
    {u : ℝ}
    (hcard :
      ((defectiveOffsets (L + 1) (x - 2)).card : ℝ) ≤ u) :
    globalStartProbability L x ≤
      (2 : ℝ) ^ u / (2 : ℝ) ^ L := by
  have hfinite :=
    globalStartProbability_le_defectiveWindow hx hL
  calc
    globalStartProbability L x ≤
        (2 : ℝ) ^
            (defectiveOffsets (L + 1) (x - 2)).card /
          (2 : ℝ) ^ L := hfinite
    _ =
        (2 : ℝ) ^
            ((defectiveOffsets (L + 1) (x - 2)).card : ℝ) /
          (2 : ℝ) ^ L := by
      rw [Real.rpow_natCast]
    _ ≤ (2 : ℝ) ^ u / (2 : ℝ) ^ L := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hcard

/-- The two-defect population is exactly the exceptional set inside the
dyadic block. -/
theorem mem_twoDefectWindowStarts_iff
    {N L x : ℕ} :
    x ∈ twoDefectWindowStarts (L + 1) N ↔
      x ∈ Finset.Ico N (2 * N) ∧
        2 ≤ (defectiveOffsets (L + 1) (x - 2)).card := by
  simp only [mem_twoDefectWindowStarts, Finset.mem_Ico]
  aesop

/-- Every global start probability is nonnegative. -/
theorem globalStartProbability_nonneg (L x : ℕ) :
    0 ≤ globalStartProbability L x := by
  unfold globalStartProbability
  exact Rat.cast_nonneg.mpr
    (startProbability_nonneg x L x)

/--
Finite high-block estimate behind Proposition 15.5.

The ordinary starts cost at most `2 N / 2^L`.  If every exceptional
two-defect start has complete-window defect count at most the real number
`u`, the exceptional mass costs at most

`#exceptional * 2^u / 2^L`.
-/
theorem highBlockProbabilityMass_le
    {N L : ℕ} {u : ℝ}
    (hN : 2 ≤ N) (hL : 0 < L)
    (hmax :
      ∀ x ∈ twoDefectWindowStarts (L + 1) N,
        ((defectiveOffsets (L + 1) (x - 2)).card : ℝ) ≤ u) :
    highBlockProbabilityMass N L ≤
      (N : ℝ) * (2 / (2 : ℝ) ^ L) +
        ((twoDefectWindowStarts (L + 1) N).card : ℝ) *
          ((2 : ℝ) ^ u / (2 : ℝ) ^ L) := by
  classical
  let block := Finset.Ico N (2 * N)
  let exceptional := twoDefectWindowStarts (L + 1) N
  have hsubset : exceptional ⊆ block := by
    intro x hx
    exact (mem_twoDefectWindowStarts_iff.mp hx).1
  have hordinary :
      ∑ x ∈ block \ exceptional, globalStartProbability L x ≤
        ((block \ exceptional).card : ℝ) *
          (2 / (2 : ℝ) ^ L) := by
    calc
      ∑ x ∈ block \ exceptional, globalStartProbability L x ≤
          ∑ _x ∈ block \ exceptional,
            (2 / (2 : ℝ) ^ L) := by
        apply Finset.sum_le_sum
        intro x hx
        have hxBlock : x ∈ block := (Finset.mem_sdiff.mp hx).1
        have hxNot : x ∉ exceptional := (Finset.mem_sdiff.mp hx).2
        have hxLower : N ≤ x :=
          (Finset.mem_Ico.mp (by simpa only [block] using hxBlock)).1
        have hxTwo : 2 ≤ x := hN.trans hxLower
        have hcard :
            (defectiveOffsets (L + 1) (x - 2)).card ≤ 1 := by
          have hnotTwo :
              ¬ 2 ≤
                (defectiveOffsets (L + 1) (x - 2)).card := by
            intro htwo
            apply hxNot
            exact mem_twoDefectWindowStarts_iff.mpr
              ⟨hxBlock, htwo⟩
          omega
        exact globalStartProbability_le_baseline_of_card_le_one
          hxTwo hL hcard
      _ =
          ((block \ exceptional).card : ℝ) *
            (2 / (2 : ℝ) ^ L) := by simp
  have hexceptional :
      ∑ x ∈ exceptional, globalStartProbability L x ≤
        (exceptional.card : ℝ) *
          ((2 : ℝ) ^ u / (2 : ℝ) ^ L) := by
    calc
      ∑ x ∈ exceptional, globalStartProbability L x ≤
          ∑ _x ∈ exceptional,
            ((2 : ℝ) ^ u / (2 : ℝ) ^ L) := by
        apply Finset.sum_le_sum
        intro x hx
        have hxBlock := (mem_twoDefectWindowStarts_iff.mp hx).1
        have hxLower : N ≤ x :=
          (Finset.mem_Ico.mp hxBlock).1
        exact globalStartProbability_le_of_real_defect_bound
          (hN.trans hxLower) hL (hmax x hx)
      _ =
          (exceptional.card : ℝ) *
            ((2 : ℝ) ^ u / (2 : ℝ) ^ L) := by simp
  have hordinaryCard :
      ((block \ exceptional).card : ℝ) ≤ (N : ℝ) := by
    have hcard :
        (block \ exceptional).card ≤ block.card :=
      Finset.card_le_card Finset.sdiff_subset
    have hblockCard : block.card = N := by
      dsimp only [block]
      rw [Nat.card_Ico]
      omega
    rw [hblockCard] at hcard
    exact_mod_cast hcard
  have hbaselineNonneg :
      0 ≤ 2 / (2 : ℝ) ^ L := by positivity
  unfold highBlockProbabilityMass
  change
    (∑ x ∈ block, globalStartProbability L x) ≤
      (N : ℝ) * (2 / (2 : ℝ) ^ L) +
        (exceptional.card : ℝ) *
          ((2 : ℝ) ^ u / (2 : ℝ) ^ L)
  rw [← Finset.sum_sdiff hsubset]
  calc
    (∑ x ∈ block \ exceptional, globalStartProbability L x) +
          ∑ x ∈ exceptional, globalStartProbability L x ≤
        ((block \ exceptional).card : ℝ) *
            (2 / (2 : ℝ) ^ L) +
          (exceptional.card : ℝ) *
            ((2 : ℝ) ^ u / (2 : ℝ) ^ L) :=
      add_le_add hordinary hexceptional
    _ ≤
        (N : ℝ) * (2 / (2 : ℝ) ^ L) +
          (exceptional.card : ℝ) *
            ((2 : ℝ) ^ u / (2 : ℝ) ^ L) := by
      gcongr

/--
The finite block estimate with an arbitrary real upper bound for the
exceptional population.  This is the direct insertion point for Lemma 15.3.
-/
theorem highBlockProbabilityMass_le_of_exceptional_card_le
    {N L : ℕ} {u countBound : ℝ}
    (hN : 2 ≤ N) (hL : 0 < L)
    (hmax :
      ∀ x ∈ twoDefectWindowStarts (L + 1) N,
        ((defectiveOffsets (L + 1) (x - 2)).card : ℝ) ≤ u)
    (hcount :
      ((twoDefectWindowStarts (L + 1) N).card : ℝ) ≤
        countBound) :
    highBlockProbabilityMass N L ≤
      (N : ℝ) * (2 / (2 : ℝ) ^ L) +
        countBound * ((2 : ℝ) ^ u / (2 : ℝ) ^ L) := by
  have hweight :
      0 ≤ (2 : ℝ) ^ u / (2 : ℝ) ^ L := by positivity
  exact (highBlockProbabilityMass_le hN hL hmax).trans
    (add_le_add_right
      (mul_le_mul_of_nonneg_right hcount hweight) _)

/--
Concrete insertion of Lemma 15.4 into the finite block estimate.
Only the published Balasubramanian--Shorey statement is an input.
-/
theorem balasubramanianShorey_highBlockProbabilityMass_le
    (hBS : BalasubramanianShoreyInput.BalasubramanianShoreyStatement) :
    ∃ θ₀ : ℝ, ∃ B₀ : ℕ, ∀ L ≥ B₀, ∀ N,
      2 ≤ N →
      0 < L →
      (L + 1) ^ 2 + 2 < N →
      highBlockProbabilityMass N L ≤
        (N : ℝ) * (2 / (2 : ℝ) ^ L) +
          ((twoDefectWindowStarts (L + 1) N).card : ℝ) *
            (((2 : ℝ) ^
                (((L + 1 : ℕ) : ℝ) -
                  BalasubramanianShoreyInput.gap (L + 1) θ₀)) /
              (2 : ℝ) ^ L) := by
  obtain ⟨θ₀, B₀, hmaximum⟩ :=
    defectiveWindow_card_le_complement_gap_eventually hBS
  refine ⟨θ₀, B₀, ?_⟩
  intro L hL N hN hLpos hhigh
  apply highBlockProbabilityMass_le hN hLpos
  intro x hx
  have hxBlock := (mem_twoDefectWindowStarts_iff.mp hx).1
  have hxLower : N ≤ x :=
    (Finset.mem_Ico.mp hxBlock).1
  exact hmaximum (L + 1) (by omega) x
    (hhigh.trans_le hxLower)

/--
Joint insertion of Lemmas 15.3 and 15.4 into every high dyadic block.

The constant and threshold are uniform simultaneously for all
`2 L² ≤ N ≤ M`, with `L` in the manuscript critical window at height `M`.
The two remaining summands are exactly the geometric baseline and the
exceptional envelope whose decay is proved in
`PropositionFifteenFiveDecay`.
-/
theorem highBlockProbabilityMass_le_uniform_height_range
    {C : ℝ} (hC : 0 ≤ C)
    (hpnt : PrimeNumberTheoremInput.PrimeNumberTheoremStatement)
    (hPell : PellInput.GeneralizedPellPolynomialBoxStatement)
    (hBS :
      BalasubramanianShoreyInput.BalasubramanianShoreyStatement) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ θ₀ : ℝ,
      ∃ M₀ : ℕ, ∀ M ≥ M₀, ∀ L,
        CriticalRunWindow.InRunLengthWindow C M L →
        ∀ N : ℕ, 2 * L ^ 2 ≤ N → N ≤ M →
          highBlockProbabilityMass N L ≤
            (N : ℝ) * (2 / (2 : ℝ) ^ L) +
              Real.exp
                  (K * ((L : ℝ) / Real.log (L : ℝ))) *
                ((2 : ℝ) ^
                    (((L + 1 : ℕ) : ℝ) -
                      BalasubramanianShoreyInput.gap (L + 1) θ₀) /
                  (2 : ℝ) ^ L) := by
  obtain ⟨K, hK, Mcount, hcount⟩ :=
    LemmaFifteenThree.lemma_fifteen_three_uniform_height_range
      hC hpnt hPell
  obtain ⟨θ₀, BBS, hmaximum⟩ :=
    defectiveWindow_card_le_complement_gap_eventually hBS
  obtain ⟨Mheight, hheight⟩ :=
    DependencyEdgesCritical.runLengthAddOne_tends_to_infinity
      hC (max BBS 5)
  refine ⟨K, hK, θ₀, max Mcount Mheight, ?_⟩
  intro M hM L hrun N hNlower hNupper
  have hMcount : Mcount ≤ M :=
    (le_max_left Mcount Mheight).trans hM
  have hMheight : Mheight ≤ M :=
    (le_max_right Mcount Mheight).trans hM
  have hheightL :
      max BBS 5 ≤ L + 1 :=
    hheight M hMheight L hrun
  have hBBS : BBS ≤ L + 1 :=
    (le_max_left BBS 5).trans hheightL
  have hLfour : 4 ≤ L := by
    have : 5 ≤ L + 1 :=
      (le_max_right BBS 5).trans hheightL
    omega
  have hLpos : 0 < L := by omega
  have hNtwo : 2 ≤ N := by
    have : 2 * 4 ^ 2 ≤ N := by
      exact
        (Nat.mul_le_mul_left 2
          (Nat.pow_le_pow_left hLfour 2)).trans hNlower
    omega
  have hhigh : (L + 1) ^ 2 + 2 < N := by
    have hlocal : (L + 1) ^ 2 + 2 < 2 * L ^ 2 := by
      nlinarith
    exact hlocal.trans_le hNlower
  apply highBlockProbabilityMass_le_of_exceptional_card_le
    hNtwo hLpos
  · intro x hx
    have hxBlock := (mem_twoDefectWindowStarts_iff.mp hx).1
    have hxLower : N ≤ x :=
      (Finset.mem_Ico.mp hxBlock).1
    exact hmaximum (L + 1) hBBS x
      (hhigh.trans_le hxLower)
  · exact hcount M hMcount L hrun N hNlower hNupper

end

end PropositionFifteenFive
end PaperC
