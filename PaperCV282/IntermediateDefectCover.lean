import PaperCV282.PostQuadraticStartBounds
import PaperC.Asymptotics.HighZoneTwoDefects
import PaperC.Diophantine.PellDivisorEnvelope

/-! # Global finite cover of intermediate two-defect starts

The upper ambient height is independent of every start's lower height.
No lower comparability with that ambient height is required.
-/
namespace PaperC.V282.IntermediateDefectCover

open HighZoneTwoDefects BalasubramanianShoreyMaximum
open SquarefreeSmoothCount DefectivePredicate ComponentNormalization DefectCounting
open WindowValues PellInput

noncomputable section

/-- Every high two-defect start belongs to the actual nonsingular Pell cover. -/
theorem full_interval_bases_subset_paired {B M : ℕ} {s : Finset ℕ}
    (hBM : B ≤ M)
    (hs : ∀ x ∈ s, B ^ 2 + 2 < x ∧ x ≤ 2 * M ∧
      2 ≤ (defectIndices B x B).card) :
    s.image (fun x => x - 2) ⊆
      distinctPairedDefectStarts (squarefreeSmoothUpTo B (3 * M))
        (Finset.Icc 1 B) (3 * M) (2 * M) := by  classical
  intro windowBase hwindowBase
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hwindowBase
  have hxData := hs x hx
  have hxtwo : 2 ≤ x := by omega
  have hcard :
      1 < (defectiveOffsets B (x - 2)).card := by
    rw [← PostQuadraticStartBounds.card_full_defects_eq_offsets hxtwo]
    omega
  obtain ⟨i₁, hi₁, i₂, hi₂, hiMe⟩ :=
    Finset.one_lt_card.mp hcard
  have hi₁Data := mem_defectiveOffsets.mp hi₁
  have hi₂Data := mem_defectiveOffsets.mp hi₂
  let base := x - 2
  let n₁ := base + i₁
  let n₂ := base + i₂
  let d₁ := squarefreeKernel n₁
  let d₂ := squarefreeKernel n₂
  let a := canonicalSquarePart n₁
  let b := canonicalSquarePart n₂
  have hbase : base = x - 2 := rfl
  have hn₁pos : 0 < n₁ := by
    dsimp [n₁, base]
    omega
  have hn₂pos : 0 < n₂ := by
    dsimp [n₂, base]
    omega
  have hn₁upper : n₁ ≤ 3 * M := by
    dsimp [n₁, base]
    omega
  have hn₂upper : n₂ ≤ 3 * M := by
    dsimp [n₂, base]
    omega
  have hdecomp₁ :
      n₁ = d₁ * a ^ 2 := by
    simpa [d₁, a] using
      (canonical_squarefree_decomposition hn₁pos).2.2.2
  have hdecomp₂ :
      n₂ = d₂ * b ^ 2 := by
    simpa [d₂, b] using
      (canonical_squarefree_decomposition hn₂pos).2.2.2
  have hd₁mem :
      d₁ ∈ squarefreeSmoothUpTo B (3 * M) := by
    rw [mem_squarefreeSmoothUpTo]
    refine ⟨(canonical_squarefree_decomposition hn₁pos).1,
      (squarefreeKernel_le hn₁pos).trans hn₁upper,
      (canonical_squarefree_decomposition hn₁pos).2.1, ?_⟩
    exact squarefreeKernel_isSmoothAt_of_hDefective hi₁Data.2.2
  have hd₂mem :
      d₂ ∈ squarefreeSmoothUpTo B (3 * M) := by
    rw [mem_squarefreeSmoothUpTo]
    refine ⟨(canonical_squarefree_decomposition hn₂pos).1,
      (squarefreeKernel_le hn₂pos).trans hn₂upper,
      (canonical_squarefree_decomposition hn₂pos).2.1, ?_⟩
    exact squarefreeKernel_isSmoothAt_of_hDefective hi₂Data.2.2
  have hdMe : d₁ ≠ d₂ := by
    intro hdEq
    have hbaseHigh : B ^ 2 < base := by
      dsimp [base]
      omega
    apply equal_kernel_offsets_impossible
      (s := d₁) (a := a) (b := b)
      (B := B) (base := base) (i₁ := i₁) (i₂ := i₂)
      (canonical_squarefree_decomposition hn₁pos).1
      hi₁Data.2.1 hi₂Data.2.1 hiMe
    · simpa [n₁] using hdecomp₁
    · simpa [n₂, hdEq] using hdecomp₂
    · exact hbaseHigh
  have haBound : a ≤ 3 * M :=
    (canonicalSquarePart_le_self hn₁pos).trans hn₁upper
  have hbBound : b ≤ 3 * M :=
    (canonicalSquarePart_le_self hn₂pos).trans hn₂upper
  have hbaseBound : base < 2 * M := by
    dsimp [base]
    omega
  rw [distinctPairedDefectStarts]
  apply Finset.mem_biUnion.mpr
  refine ⟨d₁, hd₁mem, ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨d₂, Finset.mem_erase.mpr ⟨hdMe.symm, hd₂mem⟩, ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨i₁, Finset.mem_Icc.mpr ⟨hi₁Data.1, hi₁Data.2.1⟩, ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨i₂, Finset.mem_erase.mpr
    ⟨hiMe.symm, Finset.mem_Icc.mpr
      ⟨hi₂Data.1, hi₂Data.2.1⟩⟩, ?_⟩
  rw [startsForParameters]
  apply Finset.mem_image.mpr
  let w : MultipleDefects.TwoDefectWitness :=
    { start := base
      leftRoot := a
      rightRoot := b }
  refine ⟨w, ?_, rfl⟩
  rw [mem_boundedTwoDefectWitnesses]
  refine ⟨hbaseBound, ?_⟩
  exact ⟨by simpa [w, n₁] using hdecomp₁,
    by simpa [w, n₂] using hdecomp₂,
    by simpa [w] using haBound,
    by simpa [w] using hbBound⟩


/-- A single global height box counts every finite high two-defect family.
The only unproved input is the source-shaped Nicolas--Robin divisor inequality. -/
theorem finite_two_defect_count (hNR : NicolasRobinDivisorLogBoundStatement) :
    ∃ c : ℝ, 0 ≤ c ∧ ∃ Mzero : ℕ, ∀ B M : ℕ,
      Mzero ≤ 3 * M → B ≤ M → ∀ s : Finset ℕ,
      (∀ x ∈ s, B ^ 2 + 2 < x ∧ x ≤ 2 * M ∧
        2 ≤ (defectIndices B x B).card) →
      (s.card : ℝ) ≤ (
        (squarefreeSmoothUpTo B (3 * M)).card : ℝ) ^ 2 *
        (B : ℝ) ^ 2 * expLogLogBound c (3 * M) := by
  have hTwo :=
    MultipleDefects.twoDefectPolynomialBox_of_generalizedPell (generalizedPellPolynomialBox_of_divisorLogBound hNR)
  obtain ⟨c, hc, N₀, hN₀⟩ := hTwo 1 (by omega)
  refine ⟨c, hc, N₀, ?_⟩
  intro B M hthreshold hBN s hs
  let D := squarefreeSmoothUpTo B (3 * M)
  let I := Finset.Icc 1 B
  have hcount :
      ∀ d₁ ∈ D, ∀ d₂ ∈ D, d₁ ≠ d₂ →
        ∀ i₁ ∈ I, ∀ i₂ ∈ I, i₁ ≠ i₂ →
          PellInput.HasAtMostSolutionsReal
            (MultipleDefects.twoDefectWitnessBox
              d₁ d₂ i₁ i₂ (3 * M))
            (PellInput.expLogLogBound c (3 * M)) := by
    intro d₁ hd₁ d₂ hd₂ hdne i₁ hi₁ i₂ hi₂ hine
    have hd₁Data := mem_squarefreeSmoothUpTo.mp hd₁
    have hd₂Data := mem_squarefreeSmoothUpTo.mp hd₂
    have hi₁Data : 1 ≤ i₁ ∧ i₁ ≤ B := by
      simpa [I] using Finset.mem_Icc.mp hi₁
    have hi₂Data : 1 ≤ i₂ ∧ i₂ ≤ B := by
      simpa [I] using Finset.mem_Icc.mp hi₂
    have hdelta :
        Int.natAbs ((i₁ : ℤ) - (i₂ : ℤ)) ≤ (3 * M) ^ 1 := by
      calc
        Int.natAbs ((i₁ : ℤ) - (i₂ : ℤ))
            ≤ Int.natAbs (i₁ : ℤ) + Int.natAbs (i₂ : ℤ) :=
          Int.natAbs_sub_le _ _
        _ = i₁ + i₂ := by simp
        _ ≤ (3 * M) ^ 1 := by
          simp only [pow_one]
          omega
    have hd₁Bound : d₁ ≤ (3 * M) ^ 1 := by
      simpa only [pow_one] using hd₁Data.2.1
    have hd₂Bound : d₂ ≤ (3 * M) ^ 1 := by
      simpa only [pow_one] using hd₂Data.2.1
    simpa only [pow_one] using
      (hN₀ (3 * M) hthreshold d₁ d₂ i₁ i₂
        hd₁Data.1 hd₂Data.1
        hd₁Data.2.2.1 hd₂Data.2.2.1
        (TerminalPartnerPell.not_isSquare_ratio_of_squarefree_of_ne
          hd₁Data.1 hd₂Data.1
          hd₁Data.2.2.1 hd₂Data.2.2.1 hdne)
        hine
        hd₁Bound hd₂Bound hdelta)
  have hcover := full_interval_bases_subset_paired hBN hs
  have hinj : Set.InjOn (fun x : ℕ => x - 2) s := by
    intro x hx y hy hxy
    have := hs x hx
    have := hs y hy
    change x - 2 = y - 2 at hxy
    omega
  have hc : ((s.image (fun x => x - 2)).card : ℝ) ≤
      (distinctPairedDefectStarts D I (3 * M) (2 * M)).card := by
    exact_mod_cast Finset.card_le_card hcover
  rw [Finset.card_image_of_injOn hinj] at hc
  have hfinite := card_distinctPairedDefectStarts_le
    (D := D) (I := I) (H := 3 * M) (X := 2 * M)
    (R := expLogLogBound c (3 * M)) (Real.exp_pos _).le hcount
  exact hc.trans (by simpa [D, I, Nat.card_Icc] using hfinite)

end
end PaperC.V282.IntermediateDefectCover
