import PaperC.Arithmetic.BalasubramanianShoreyMaximum
import PaperC.Asymptotics.SquarefreeSmoothCritical
import PaperC.Diophantine.ComponentNormalization
import PaperC.Diophantine.MultipleDefects
import PaperC.Diophantine.TerminalPartnerPell
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option maxHeartbeats 1600000

/-!
# Two-defect windows in the high zone

This module assembles the finite arithmetic reduction in Lemma 15.3.
For a fixed pair of squarefree smooth kernels and a fixed pair of offsets,
the existing Pell interface counts all possible starts.  Four finite unions
then sum over the two kernels and the two offsets.

The second part connects this abstract union to actual `B`-defective windows.
The canonical odd-support decomposition supplies the squarefree smooth
kernels and square parameters.  In the genuine high zone equal kernels are
impossible for two distinct offsets, by the elementary gap between two
distinct squares.

No new bridge is introduced.  The only conditional input is the already
registered internal generalized-Pell statement.
-/

namespace PaperC
namespace HighZoneTwoDefects

open scoped BigOperators
open DefectCounting DefectivePredicate
open SquarefreeSmoothCount
open BalasubramanianShoreyMaximum
open ComponentNormalization

noncomputable section

/-! ## A finite family for one parameter quadruple -/

/--
All witnesses with start `< X` and square parameters at most `H`, for one
fixed pair of kernels and offsets.
-/
def boundedTwoDefectWitnesses
    (d₁ d₂ i₁ i₂ H X : ℕ) :
    Finset MultipleDefects.TwoDefectWitness := by
  classical
  let raw :
      Finset (ℕ × ℕ × ℕ) :=
    (Finset.range X).product
      ((Finset.range (H + 1)).product
        (Finset.range (H + 1)))
  exact
    (raw.image fun data ↦
      { start := data.1
        leftRoot := data.2.1
        rightRoot := data.2.2 }).filter
      (MultipleDefects.twoDefectWitnessBox d₁ d₂ i₁ i₂ H)

@[simp]
theorem mem_boundedTwoDefectWitnesses
    {d₁ d₂ i₁ i₂ H X : ℕ}
    {w : MultipleDefects.TwoDefectWitness} :
    w ∈ boundedTwoDefectWitnesses d₁ d₂ i₁ i₂ H X ↔
      w.start < X ∧
        MultipleDefects.twoDefectWitnessBox
          d₁ d₂ i₁ i₂ H w := by
  classical
  constructor
  · intro hw
    have hfilter :=
      Finset.mem_filter.mp hw
    refine ⟨?_, hfilter.2⟩
    obtain ⟨data, hdata, rfl⟩ :=
      Finset.mem_image.mp hfilter.1
    have hraw := Finset.mem_product.mp hdata
    have hstart : data.1 < X :=
      Finset.mem_range.mp hraw.1
    exact hstart
  · rintro ⟨hstart, hbox⟩
    apply Finset.mem_filter.mpr
    refine ⟨?_, hbox⟩
    apply Finset.mem_image.mpr
    refine ⟨(w.start, w.leftRoot, w.rightRoot), ?_, ?_⟩
    · apply Finset.mem_product.mpr
      refine ⟨Finset.mem_range.mpr hstart, ?_⟩
      apply Finset.mem_product.mpr
      exact ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hbox.2.2.1),
        Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hbox.2.2.2)⟩
    · cases w
      rfl

/-- Starts represented by the bounded witness family. -/
def startsForParameters
    (d₁ d₂ i₁ i₂ H X : ℕ) : Finset ℕ :=
  (boundedTwoDefectWitnesses d₁ d₂ i₁ i₂ H X).image
    MultipleDefects.TwoDefectWitness.start

/--
Any real finite Pell bound for one parameter quadruple bounds the number of
starts represented by that quadruple.
-/
theorem card_startsForParameters_le
    {d₁ d₂ i₁ i₂ H X : ℕ} {R : ℝ}
    (hcount :
      PellInput.HasAtMostSolutionsReal
        (MultipleDefects.twoDefectWitnessBox d₁ d₂ i₁ i₂ H)
        R) :
    ((startsForParameters d₁ d₂ i₁ i₂ H X).card : ℝ) ≤ R := by
  have hfamily :
      ((boundedTwoDefectWitnesses d₁ d₂ i₁ i₂ H X).card : ℝ) ≤ R :=
    hcount _ fun w hw ↦
      (mem_boundedTwoDefectWitnesses.mp hw).2
  have hcardNat :
      (startsForParameters d₁ d₂ i₁ i₂ H X).card ≤
        (boundedTwoDefectWitnesses d₁ d₂ i₁ i₂ H X).card :=
    Finset.card_image_le
  have hcardReal :
      ((startsForParameters d₁ d₂ i₁ i₂ H X).card : ℝ) ≤
        ((boundedTwoDefectWitnesses d₁ d₂ i₁ i₂ H X).card : ℝ) := by
    exact_mod_cast hcardNat
  exact hcardReal.trans hfamily

/-! ## Summation over kernels and offsets -/

/--
The finite union of all starts arising from kernels in `D` and offsets in
`I`.
-/
def pairedDefectStarts
    (D I : Finset ℕ) (H X : ℕ) : Finset ℕ :=
  D.biUnion fun d₁ ↦
    D.biUnion fun d₂ ↦
      I.biUnion fun i₁ ↦
        I.biUnion fun i₂ ↦
          startsForParameters d₁ d₂ i₁ i₂ H X

/--
Four applications of the finite-union bound.  This is the exact finite
assembly behind the factor
`(#kernels)^2 * (#offsets)^2 * (Pell bound)`.
-/
theorem card_pairedDefectStarts_le
    {D I : Finset ℕ} {H X : ℕ} {R : ℝ}
    (hcount :
      ∀ d₁ ∈ D, ∀ d₂ ∈ D, ∀ i₁ ∈ I, ∀ i₂ ∈ I,
        PellInput.HasAtMostSolutionsReal
          (MultipleDefects.twoDefectWitnessBox
            d₁ d₂ i₁ i₂ H)
          R) :
    ((pairedDefectStarts D I H X).card : ℝ) ≤
      (D.card : ℝ) ^ 2 * (I.card : ℝ) ^ 2 * R := by
  classical
  have h₂ :
      ∀ d₁ ∈ D, ∀ d₂ ∈ D, ∀ i₁ ∈ I,
        (((I.biUnion fun i₂ ↦
            startsForParameters d₁ d₂ i₁ i₂ H X).card : ℕ) : ℝ) ≤
          (I.card : ℝ) * R := by
    intro d₁ hd₁ d₂ hd₂ i₁ hi₁
    calc
      (((I.biUnion fun i₂ ↦
          startsForParameters d₁ d₂ i₁ i₂ H X).card : ℕ) : ℝ)
          ≤ (∑ i₂ ∈ I,
              (startsForParameters d₁ d₂ i₁ i₂ H X).card : ℕ) := by
            exact_mod_cast Finset.card_biUnion_le
      _ = ∑ i₂ ∈ I,
            ((startsForParameters d₁ d₂ i₁ i₂ H X).card : ℝ) := by
          norm_cast
      _ ≤ ∑ _i₂ ∈ I, R := by
          exact Finset.sum_le_sum fun i₂ hi₂ ↦
            card_startsForParameters_le
              (hcount d₁ hd₁ d₂ hd₂ i₁ hi₁ i₂ hi₂)
      _ = (I.card : ℝ) * R := by simp
  have h₁ :
      ∀ d₁ ∈ D, ∀ d₂ ∈ D,
        (((I.biUnion fun i₁ ↦
            I.biUnion fun i₂ ↦
              startsForParameters d₁ d₂ i₁ i₂ H X).card : ℕ) : ℝ) ≤
          (I.card : ℝ) ^ 2 * R := by
    intro d₁ hd₁ d₂ hd₂
    calc
      (((I.biUnion fun i₁ ↦
          I.biUnion fun i₂ ↦
            startsForParameters d₁ d₂ i₁ i₂ H X).card : ℕ) : ℝ)
          ≤ (∑ i₁ ∈ I,
              (I.biUnion fun i₂ ↦
                startsForParameters d₁ d₂ i₁ i₂ H X).card : ℕ) := by
            exact_mod_cast Finset.card_biUnion_le
      _ = ∑ i₁ ∈ I,
            (((I.biUnion fun i₂ ↦
              startsForParameters d₁ d₂ i₁ i₂ H X).card : ℕ) : ℝ) := by
          norm_cast
      _ ≤ ∑ _i₁ ∈ I, (I.card : ℝ) * R := by
          exact Finset.sum_le_sum fun i₁ hi₁ ↦ h₂ d₁ hd₁ d₂ hd₂ i₁ hi₁
      _ = (I.card : ℝ) ^ 2 * R := by
          simp
          ring
  have hd₂ :
      ∀ d₁ ∈ D,
        (((D.biUnion fun d₂ ↦
            I.biUnion fun i₁ ↦
              I.biUnion fun i₂ ↦
                startsForParameters d₁ d₂ i₁ i₂ H X).card : ℕ) : ℝ) ≤
          (D.card : ℝ) * (I.card : ℝ) ^ 2 * R := by
    intro d₁ hd₁
    calc
      (((D.biUnion fun d₂ ↦
          I.biUnion fun i₁ ↦
            I.biUnion fun i₂ ↦
              startsForParameters d₁ d₂ i₁ i₂ H X).card : ℕ) : ℝ)
          ≤ (∑ d₂ ∈ D,
              (I.biUnion fun i₁ ↦
                I.biUnion fun i₂ ↦
                  startsForParameters d₁ d₂ i₁ i₂ H X).card : ℕ) := by
            exact_mod_cast Finset.card_biUnion_le
      _ = ∑ d₂ ∈ D,
            (((I.biUnion fun i₁ ↦
              I.biUnion fun i₂ ↦
                startsForParameters d₁ d₂ i₁ i₂ H X).card : ℕ) : ℝ) := by
          norm_cast
      _ ≤ ∑ _d₂ ∈ D, (I.card : ℝ) ^ 2 * R := by
          exact Finset.sum_le_sum fun d₂ hd₂ ↦ h₁ d₁ hd₁ d₂ hd₂
      _ = (D.card : ℝ) * (I.card : ℝ) ^ 2 * R := by
          simp
          ring
  calc
    ((pairedDefectStarts D I H X).card : ℝ)
        ≤ (∑ d₁ ∈ D,
            (D.biUnion fun d₂ ↦
              I.biUnion fun i₁ ↦
                I.biUnion fun i₂ ↦
                  startsForParameters d₁ d₂ i₁ i₂ H X).card : ℕ) := by
          exact_mod_cast Finset.card_biUnion_le
    _ = ∑ d₁ ∈ D,
          (((D.biUnion fun d₂ ↦
            I.biUnion fun i₁ ↦
              I.biUnion fun i₂ ↦
                startsForParameters d₁ d₂ i₁ i₂ H X).card : ℕ) : ℝ) := by
        norm_cast
    _ ≤ ∑ _d₁ ∈ D,
          (D.card : ℝ) * (I.card : ℝ) ^ 2 * R := by
        exact Finset.sum_le_sum fun d₁ hd₁ ↦ hd₂ d₁ hd₁
    _ = (D.card : ℝ) ^ 2 * (I.card : ℝ) ^ 2 * R := by
        simp
        ring

/--
The subfamily relevant to Pell: both the kernels and the offsets are
distinct.  `erase` makes these side conditions structural rather than
propositional filters.
-/
def distinctPairedDefectStarts
    (D I : Finset ℕ) (H X : ℕ) : Finset ℕ :=
  D.biUnion fun d₁ ↦
    (D.erase d₁).biUnion fun d₂ ↦
      I.biUnion fun i₁ ↦
        (I.erase i₁).biUnion fun i₂ ↦
          startsForParameters d₁ d₂ i₁ i₂ H X

/--
Finite Pell assembly with precisely the two nonsingularity conditions used
in Lemma 15.3.
-/
theorem card_distinctPairedDefectStarts_le
    {D I : Finset ℕ} {H X : ℕ} {R : ℝ}
    (hR : 0 ≤ R)
    (hcount :
      ∀ d₁ ∈ D, ∀ d₂ ∈ D, d₁ ≠ d₂ →
        ∀ i₁ ∈ I, ∀ i₂ ∈ I, i₁ ≠ i₂ →
          PellInput.HasAtMostSolutionsReal
            (MultipleDefects.twoDefectWitnessBox
              d₁ d₂ i₁ i₂ H)
            R) :
    ((distinctPairedDefectStarts D I H X).card : ℝ) ≤
      (D.card : ℝ) ^ 2 * (I.card : ℝ) ^ 2 * R := by
  classical
  have hi₂ :
      ∀ d₁ ∈ D, ∀ d₂ ∈ D, d₁ ≠ d₂ →
        ∀ i₁ ∈ I,
          (((I.erase i₁).biUnion fun i₂ ↦
              startsForParameters d₁ d₂ i₁ i₂ H X).card : ℝ) ≤
            (I.card : ℝ) * R := by
    intro d₁ hd₁ d₂ hd₂ hdne i₁ hi₁
    have herase : ((I.erase i₁).card : ℝ) ≤ (I.card : ℝ) := by
      exact_mod_cast Finset.card_erase_le
    calc
      (((I.erase i₁).biUnion fun i₂ ↦
          startsForParameters d₁ d₂ i₁ i₂ H X).card : ℝ)
          ≤ ∑ i₂ ∈ I.erase i₁,
              ((startsForParameters d₁ d₂ i₁ i₂ H X).card : ℝ) := by
            rw [← Nat.cast_sum]
            exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _i₂ ∈ I.erase i₁, R := by
          apply Finset.sum_le_sum
          intro i₂ hi₂
          exact card_startsForParameters_le
            (hcount d₁ hd₁ d₂ hd₂ hdne i₁ hi₁ i₂
              (Finset.mem_of_mem_erase hi₂)
              (Finset.ne_of_mem_erase hi₂).symm)
      _ = ((I.erase i₁).card : ℝ) * R := by simp
      _ ≤ (I.card : ℝ) * R :=
        mul_le_mul_of_nonneg_right herase hR
  have hi₁ :
      ∀ d₁ ∈ D, ∀ d₂ ∈ D, d₁ ≠ d₂ →
        ((I.biUnion (fun i₁ ↦
            (I.erase i₁).biUnion (fun i₂ ↦
              startsForParameters d₁ d₂ i₁ i₂ H X))).card : ℝ) ≤
          (I.card : ℝ) ^ 2 * R := by
    intro d₁ hd₁ d₂ hd₂ hdne
    calc
      ((I.biUnion (fun i₁ ↦
          (I.erase i₁).biUnion (fun i₂ ↦
            startsForParameters d₁ d₂ i₁ i₂ H X))).card : ℝ)
          ≤ ∑ i₁ ∈ I,
              (((I.erase i₁).biUnion (fun i₂ ↦
                startsForParameters d₁ d₂ i₁ i₂ H X)).card : ℝ) := by
            rw [← Nat.cast_sum]
            exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _i₁ ∈ I, (I.card : ℝ) * R := by
          exact Finset.sum_le_sum fun i₁ hi₁mem ↦
            hi₂ d₁ hd₁ d₂ hd₂ hdne i₁ hi₁mem
      _ = (I.card : ℝ) ^ 2 * R := by
          simp
          ring
  have hd₂ :
      ∀ d₁ ∈ D,
        (((D.erase d₁).biUnion (fun d₂ ↦
            I.biUnion (fun i₁ ↦
              (I.erase i₁).biUnion (fun i₂ ↦
                startsForParameters d₁ d₂ i₁ i₂ H X)))).card : ℝ) ≤
          (D.card : ℝ) * (I.card : ℝ) ^ 2 * R := by
    intro d₁ hd₁
    have hnonneg : 0 ≤ (I.card : ℝ) ^ 2 * R :=
      mul_nonneg (sq_nonneg _) hR
    have herase : (((D.erase d₁).card : ℕ) : ℝ) ≤ (D.card : ℝ) := by
      exact_mod_cast Finset.card_erase_le
    calc
      (((D.erase d₁).biUnion (fun d₂ ↦
          I.biUnion (fun i₁ ↦
            (I.erase i₁).biUnion (fun i₂ ↦
              startsForParameters d₁ d₂ i₁ i₂ H X)))).card : ℝ)
          ≤ ∑ d₂ ∈ D.erase d₁,
              ((I.biUnion (fun i₁ ↦
                (I.erase i₁).biUnion (fun i₂ ↦
                  startsForParameters d₁ d₂ i₁ i₂ H X))).card : ℝ) := by
            rw [← Nat.cast_sum]
            exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _d₂ ∈ D.erase d₁, (I.card : ℝ) ^ 2 * R := by
          apply Finset.sum_le_sum
          intro d₂ hd₂mem
          exact hi₁ d₁ hd₁ d₂ (Finset.mem_of_mem_erase hd₂mem)
            (Finset.ne_of_mem_erase hd₂mem).symm
      _ = ((D.erase d₁).card : ℝ) * ((I.card : ℝ) ^ 2 * R) := by simp
      _ ≤ (D.card : ℝ) * ((I.card : ℝ) ^ 2 * R) :=
        mul_le_mul_of_nonneg_right herase hnonneg
      _ = (D.card : ℝ) * (I.card : ℝ) ^ 2 * R := by ring
  calc
    ((distinctPairedDefectStarts D I H X).card : ℝ)
        ≤ ∑ d₁ ∈ D,
            (((D.erase d₁).biUnion (fun d₂ ↦
              I.biUnion (fun i₁ ↦
                (I.erase i₁).biUnion (fun i₂ ↦
                  startsForParameters d₁ d₂ i₁ i₂ H X)))).card : ℝ) := by
          rw [← Nat.cast_sum]
          exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _d₁ ∈ D,
          (D.card : ℝ) * (I.card : ℝ) ^ 2 * R := by
        exact Finset.sum_le_sum fun d₁ hd₁ ↦ hd₂ d₁ hd₁
    _ = (D.card : ℝ) ^ 2 * (I.card : ℝ) ^ 2 * R := by
        simp
        ring

/-! ## Canonical kernels of actual defective windows -/

/-- The canonical squarefree kernel of a defective integer is `B`-smooth. -/
theorem squarefreeKernel_isSmoothAt_of_hDefective
    {B n : ℕ} (hn : HDefective B n) :
    BalasubramanianShoreyInput.IsSmoothAt B
      (squarefreeKernel n) := by
  intro p hp
  have hprimeFactors :
      (squarefreeKernel n).primeFactors = oddPrimeSupport n := by
    simpa [squarefreeKernel] using
      (Nat.primeFactors_prod
        (s := oddPrimeSupport n)
        (fun q hq ↦ prime_of_mem_oddPrimeSupport' hq))
  have hpSupport : p ∈ oddPrimeSupport n := by
    rwa [hprimeFactors] at hp
  exact
    (mem_smallPrimesUpTo.mp
      (oddPrimeSupport_subset_smallPrimesUpTo hn hpSupport)).2

/-- The canonical square parameter of a positive integer is no larger than it. -/
theorem canonicalSquarePart_le_self
    {n : ℕ} (hn : 0 < n) :
    canonicalSquarePart n ≤ n := by
  have hdata := canonical_squarefree_decomposition hn
  have hs : 0 < squarefreeKernel n := hdata.1
  have ha :
      canonicalSquarePart n ≤ canonicalSquarePart n ^ 2 :=
    Nat.le_pow (by norm_num)
  calc
    canonicalSquarePart n ≤ canonicalSquarePart n ^ 2 := ha
    _ ≤ squarefreeKernel n * canonicalSquarePart n ^ 2 :=
      Nat.le_mul_of_pos_left _ hs
    _ = n := hdata.2.2.2.symm

private theorem equal_kernel_offsets_impossible_ordered
    {base i₁ i₂ s a b B : ℕ}
    (hs : 0 < s)
    (hi₂ : i₂ ≤ B)
    (hleft : base + i₁ = s * a ^ 2)
    (hright : base + i₂ = s * b ^ 2)
    (hhigh : B ^ 2 < base)
    (horder : i₁ < i₂) :
    False := by
  have habSq : a ^ 2 < b ^ 2 := by
    rw [← Nat.mul_lt_mul_left hs, ← hleft, ← hright]
    omega
  have hab : a < b :=
    (Nat.pow_lt_pow_iff_left (by norm_num : (2 : ℕ) ≠ 0)).mp habSq
  have hsbSquare :
      s * b ^ 2 ≤ (s * b) ^ 2 := by
    calc
      s * b ^ 2 ≤ s * (s * b ^ 2) :=
        Nat.le_mul_of_pos_left _ hs
      _ = (s * b) ^ 2 := by ring
  have hBsbSq : B ^ 2 < (s * b) ^ 2 := by
    apply lt_of_lt_of_le _ hsbSquare
    calc
      B ^ 2 < base := hhigh
      _ ≤ base + i₂ := Nat.le_add_right _ _
      _ = s * b ^ 2 := hright
  have hBsb : B < s * b :=
    (Nat.pow_lt_pow_iff_left (by norm_num : (2 : ℕ) ≠ 0)).mp hBsbSq
  have habGap : a ^ 2 + b ≤ b ^ 2 := by
    nlinarith
  have hstep :
      s * a ^ 2 + s * b ≤ s * b ^ 2 := by
    calc
      s * a ^ 2 + s * b = s * (a ^ 2 + b) := by ring
      _ ≤ s * b ^ 2 := Nat.mul_le_mul_left s habGap
  have hoffsetGap : s * b ≤ i₂ - i₁ := by
    omega
  have : B < i₂ - i₁ :=
    lt_of_lt_of_le hBsb hoffsetGap
  omega

/--
Two decompositions with the same positive kernel and distinct offsets cannot
occur when the common base already exceeds `B²`.
-/
theorem equal_kernel_offsets_impossible
    {base i₁ i₂ s a b B : ℕ}
    (hs : 0 < s)
    (hi₁ : i₁ ≤ B) (hi₂ : i₂ ≤ B)
    (hneq : i₁ ≠ i₂)
    (hleft : base + i₁ = s * a ^ 2)
    (hright : base + i₂ = s * b ^ 2)
    (hhigh : B ^ 2 < base) :
    False := by
  rcases lt_or_gt_of_ne hneq with horder | horder
  · exact equal_kernel_offsets_impossible_ordered
      hs hi₂ hleft hright hhigh horder
  · exact equal_kernel_offsets_impossible_ordered
      hs hi₁ hright hleft hhigh horder

/-- Starts in `[N,2N)` whose complete length-`B` window has two defects. -/
def twoDefectWindowStarts (B N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ico N (2 * N)).filter fun x ↦
    2 ≤ (defectiveOffsets B (x - 2)).card

@[simp]
theorem mem_twoDefectWindowStarts {B N x : ℕ} :
    x ∈ twoDefectWindowStarts B N ↔
      N ≤ x ∧ x < 2 * N ∧
        2 ≤ (defectiveOffsets B (x - 2)).card := by
  simp [twoDefectWindowStarts, and_assoc]

/--
Every genuine high-zone window with two defects belongs to the finite
distinct-kernel/distinct-offset Pell union.

The convenient sufficient high-zone hypothesis `B² + 2 < N` is slightly
stronger than the manuscript's `2L² ≤ N` after `B=L+1`, and is harmless for
the asymptotic range.
-/
theorem twoDefectWindowBases_subset_distinctPaired
    {B N : ℕ}
    (hN : 2 ≤ N)
    (hBN : B ≤ N)
    (hhigh : B ^ 2 + 2 < N) :
    (twoDefectWindowStarts B N).image (fun x ↦ x - 2) ⊆
      distinctPairedDefectStarts
        (squarefreeSmoothUpTo B (3 * N))
        (Finset.Icc 1 B)
        (3 * N) (2 * N) := by
  classical
  intro windowBase hwindowBase
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hwindowBase
  have hxData := mem_twoDefectWindowStarts.mp hx
  have hcard :
      1 < (defectiveOffsets B (x - 2)).card := by
    omega
  obtain ⟨i₁, hi₁, i₂, hi₂, hiNe⟩ :=
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
  have hn₁upper : n₁ ≤ 3 * N := by
    dsimp [n₁, base]
    omega
  have hn₂upper : n₂ ≤ 3 * N := by
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
      d₁ ∈ squarefreeSmoothUpTo B (3 * N) := by
    rw [mem_squarefreeSmoothUpTo]
    refine ⟨(canonical_squarefree_decomposition hn₁pos).1,
      (squarefreeKernel_le hn₁pos).trans hn₁upper,
      (canonical_squarefree_decomposition hn₁pos).2.1, ?_⟩
    exact squarefreeKernel_isSmoothAt_of_hDefective hi₁Data.2.2
  have hd₂mem :
      d₂ ∈ squarefreeSmoothUpTo B (3 * N) := by
    rw [mem_squarefreeSmoothUpTo]
    refine ⟨(canonical_squarefree_decomposition hn₂pos).1,
      (squarefreeKernel_le hn₂pos).trans hn₂upper,
      (canonical_squarefree_decomposition hn₂pos).2.1, ?_⟩
    exact squarefreeKernel_isSmoothAt_of_hDefective hi₂Data.2.2
  have hdNe : d₁ ≠ d₂ := by
    intro hdEq
    have hbaseHigh : B ^ 2 < base := by
      dsimp [base]
      omega
    apply equal_kernel_offsets_impossible
      (s := d₁) (a := a) (b := b)
      (B := B) (base := base) (i₁ := i₁) (i₂ := i₂)
      (canonical_squarefree_decomposition hn₁pos).1
      hi₁Data.2.1 hi₂Data.2.1 hiNe
    · simpa [n₁] using hdecomp₁
    · simpa [n₂, hdEq] using hdecomp₂
    · exact hbaseHigh
  have haBound : a ≤ 3 * N :=
    (canonicalSquarePart_le_self hn₁pos).trans hn₁upper
  have hbBound : b ≤ 3 * N :=
    (canonicalSquarePart_le_self hn₂pos).trans hn₂upper
  have hbaseBound : base < 2 * N := by
    dsimp [base]
    omega
  rw [distinctPairedDefectStarts]
  apply Finset.mem_biUnion.mpr
  refine ⟨d₁, hd₁mem, ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨d₂, Finset.mem_erase.mpr ⟨hdNe.symm, hd₂mem⟩, ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨i₁, Finset.mem_Icc.mpr ⟨hi₁Data.1, hi₁Data.2.1⟩, ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨i₂, Finset.mem_erase.mpr
    ⟨hiNe.symm, Finset.mem_Icc.mpr
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

/-- Subtracting two is injective on the high-zone block. -/
theorem card_twoDefectWindowBases_eq
    {B N : ℕ} (hN : 2 ≤ N) :
    ((twoDefectWindowStarts B N).image (fun x ↦ x - 2)).card =
      (twoDefectWindowStarts B N).card := by
  rw [Finset.card_image_iff]
  intro x hx y hy hxy
  have hxLower := (mem_twoDefectWindowStarts.mp hx).1
  have hyLower := (mem_twoDefectWindowStarts.mp hy).1
  change x - 2 = y - 2 at hxy
  omega

/-!
## Conditional finite form of Lemma 15.3
-/

/--
The registered internal generalized-Pell bridge yields the complete finite
high-zone count

`# two-defect starts ≤ Ψ♭(3N,B)^2 * B^2 *
  exp(c log(3N)/loglog(3N))`.

The remaining passage to `exp(O_C(L/log L))` is purely analytic: insert the
PNT squarefree-smooth bound and the critical relations `B=L+1`,
`log N = O_C(L)`.
-/
theorem generalizedPell_implies_twoDefectWindow_bound
    (hPell : PellInput.GeneralizedPellPolynomialBoxStatement) :
    ∃ c : ℝ, 0 ≤ c ∧
      ∃ N₀ : ℕ, ∀ B N : ℕ,
        N₀ ≤ 3 * N →
        2 ≤ N →
        B ≤ N →
        B ^ 2 + 2 < N →
        ((twoDefectWindowStarts B N).card : ℝ) ≤
          ((squarefreeSmoothUpTo B (3 * N)).card : ℝ) ^ 2 *
            (B : ℝ) ^ 2 *
            PellInput.expLogLogBound c (3 * N) := by
  have hTwo :=
    MultipleDefects.twoDefectPolynomialBox_of_generalizedPell hPell
  obtain ⟨c, hc, N₀, hN₀⟩ := hTwo 1 (by omega)
  refine ⟨c, hc, N₀, ?_⟩
  intro B N hthreshold hN hBN hhigh
  let D := squarefreeSmoothUpTo B (3 * N)
  let I := Finset.Icc 1 B
  have hcount :
      ∀ d₁ ∈ D, ∀ d₂ ∈ D, d₁ ≠ d₂ →
        ∀ i₁ ∈ I, ∀ i₂ ∈ I, i₁ ≠ i₂ →
          PellInput.HasAtMostSolutionsReal
            (MultipleDefects.twoDefectWitnessBox
              d₁ d₂ i₁ i₂ (3 * N))
            (PellInput.expLogLogBound c (3 * N)) := by
    intro d₁ hd₁ d₂ hd₂ hdne i₁ hi₁ i₂ hi₂ hine
    have hd₁Data := mem_squarefreeSmoothUpTo.mp hd₁
    have hd₂Data := mem_squarefreeSmoothUpTo.mp hd₂
    have hi₁Data : 1 ≤ i₁ ∧ i₁ ≤ B := by
      simpa [I] using Finset.mem_Icc.mp hi₁
    have hi₂Data : 1 ≤ i₂ ∧ i₂ ≤ B := by
      simpa [I] using Finset.mem_Icc.mp hi₂
    have hdelta :
        Int.natAbs ((i₁ : ℤ) - (i₂ : ℤ)) ≤ (3 * N) ^ 1 := by
      calc
        Int.natAbs ((i₁ : ℤ) - (i₂ : ℤ))
            ≤ Int.natAbs (i₁ : ℤ) + Int.natAbs (i₂ : ℤ) :=
          Int.natAbs_sub_le _ _
        _ = i₁ + i₂ := by simp
        _ ≤ (3 * N) ^ 1 := by
          simp only [pow_one]
          omega
    have hd₁Bound : d₁ ≤ (3 * N) ^ 1 := by
      simpa only [pow_one] using hd₁Data.2.1
    have hd₂Bound : d₂ ≤ (3 * N) ^ 1 := by
      simpa only [pow_one] using hd₂Data.2.1
    simpa only [pow_one] using
      (hN₀ (3 * N) hthreshold d₁ d₂ i₁ i₂
        hd₁Data.1 hd₂Data.1
        hd₁Data.2.2.1 hd₂Data.2.2.1
        (TerminalPartnerPell.not_isSquare_ratio_of_squarefree_of_ne
          hd₁Data.1 hd₂Data.1
          hd₁Data.2.2.1 hd₂Data.2.2.1 hdne)
        hine
        hd₁Bound hd₂Bound hdelta)
  have hcover :=
    twoDefectWindowBases_subset_distinctPaired
      (B := B) (N := N) hN hBN hhigh
  have hcardCover :
      (((twoDefectWindowStarts B N).image
        (fun x ↦ x - 2)).card : ℝ) ≤
        ((distinctPairedDefectStarts D I
          (3 * N) (2 * N)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hcover
  have hfinite :=
    card_distinctPairedDefectStarts_le
      (D := D) (I := I) (H := 3 * N) (X := 2 * N)
      (R := PellInput.expLogLogBound c (3 * N))
      (Real.exp_pos _).le hcount
  calc
    ((twoDefectWindowStarts B N).card : ℝ) =
        (((twoDefectWindowStarts B N).image
          (fun x ↦ x - 2)).card : ℝ) := by
      exact_mod_cast (card_twoDefectWindowBases_eq
        (B := B) (N := N) hN).symm
    _ ≤ ((distinctPairedDefectStarts D I
          (3 * N) (2 * N)).card : ℝ) :=
      hcardCover
    _ ≤ (D.card : ℝ) ^ 2 * (I.card : ℝ) ^ 2 *
          PellInput.expLogLogBound c (3 * N) :=
      hfinite
    _ = ((squarefreeSmoothUpTo B (3 * N)).card : ℝ) ^ 2 *
          (B : ℝ) ^ 2 *
          PellInput.expLogLogBound c (3 * N) := by
      simp [D, I, Nat.card_Icc]

end
end HighZoneTwoDefects
end PaperC
