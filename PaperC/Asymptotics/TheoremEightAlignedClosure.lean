import PaperC.Asymptotics.AlignedRungeGrowth
import PaperC.Coding.TheoremEightHammingBudget
import PaperC.Combinatorics.AlignedDeepCoreExtraction
import PaperC.Analysis.CriticalWindowScale

set_option maxHeartbeats 1800000

/-!
# Eventual closure of the aligned deep core

This file joins the finite Section 8 proof to its two numerical branches.
The integral Hamming radius uses dyadic logarithms, whereas the Runge growth
lemma is stated with real logarithms.  The first two lemmas certify the
comparison between those denominators.  The final theorem then excludes,
uniformly in the manuscript run-length window, the aligned part of the
remaining deep core

`3 * (L + 1) < 16 * c#`.

No component family, code word, polynomial or asymptotic inequality remains
as a premise of that theorem.
-/

namespace PaperC
namespace TheoremEightAlignedClosure

open Affine.CanonicalRationalCode
open AlignedCoreExclusion
open AlignedDeepCoreExtraction
open CanonicalResidualComponents
open TheoremEightHammingBudget

noncomputable section

/--
For the large values relevant to the Hamming radius, the two real logarithms
are bounded by their integral dyadic counterparts.
-/
theorem real_log_product_le_dyadic_log_product
    {B : ℕ}
    (hloglog :
      16384 ≤ Nat.log 2 (Nat.log 2 B)) :
    Real.log B * Real.log (Real.log B) ≤
      (Nat.log 2 B : ℝ) *
        (Nat.log 2 (Nat.log 2 B) : ℝ) := by
  let L := Nat.log 2 B
  let ell := Nat.log 2 L
  have hell : 8 ≤ ell := by
    dsimp only [ell, L]
    omega
  have hLne : L ≠ 0 := by
    have hellpos : 0 < ell := by omega
    have : 2 ≤ L := (Nat.log_pos_iff.mp hellpos).1
    omega
  have hpowEll : 2 ^ ell ≤ L :=
    Nat.pow_log_le_self 2 hLne
  have hL8 : 8 ≤ L := by
    calc
      8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ ell :=
        Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ L := hpowEll
  have hB8 : 8 ≤ B :=
    hL8.trans (Nat.log_le_self 2 B)
  have hlogB :
      Real.log B ≤ (L : ℝ) := by
    simpa only [L] using
      CriticalWindowScale.real_log_le_nat_log_two hB8
  have hlogL :
      Real.log L ≤ (ell : ℝ) := by
    simpa only [ell] using
      CriticalWindowScale.real_log_le_nat_log_two hL8
  have hlogBpos : 0 < Real.log (B : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < B by omega)
  have hlogEight :
      (1 : ℝ) < Real.log 8 := by
    have hlogTwo := Real.log_two_gt_d9
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
    linarith
  have hlogEightLe :
      Real.log 8 ≤ Real.log B := by
    apply Real.log_le_log
    · norm_num
    · exact_mod_cast hB8
  have honeLogB : (1 : ℝ) < Real.log B :=
    hlogEight.trans_le hlogEightLe
  have hloglogBpos :
      0 < Real.log (Real.log B) :=
    Real.log_pos honeLogB
  have hloglogB :
      Real.log (Real.log B) ≤ (ell : ℝ) := by
    calc
      Real.log (Real.log B) ≤ Real.log L := by
        apply Real.log_le_log hlogBpos
        exact hlogB
      _ ≤ (ell : ℝ) := hlogL
  calc
    Real.log B * Real.log (Real.log B) ≤
        (L : ℝ) * Real.log (Real.log B) :=
      mul_le_mul_of_nonneg_right hlogB hloglogBpos.le
    _ ≤ (L : ℝ) * (ell : ℝ) :=
      mul_le_mul_of_nonneg_left hloglogB (Nat.cast_nonneg L)
    _ =
        (Nat.log 2 B : ℝ) *
          (Nat.log 2 (Nat.log 2 B) : ℝ) := rfl

/--
The integral radius therefore has the real-logarithmic upper bound consumed
by `AlignedRungeGrowth`, with the same explicit constant `65`.
-/
theorem componentHammingRadius_cast_le_real_log
    {B : ℕ}
    (hloglog :
      16384 ≤ Nat.log 2 (Nat.log 2 B)) :
    (componentHammingRadius B : ℝ) ≤
      65 * (B : ℝ) /
        (Real.log B * Real.log (Real.log B)) := by
  have hdyadic :=
    componentHammingRadius_cast_le hloglog
  have hden :=
    real_log_product_le_dyadic_log_product hloglog
  have hrealDenPos :
      0 < Real.log B * Real.log (Real.log B) := by
    have hB8 : 8 ≤ B := by
      let L := Nat.log 2 B
      let ell := Nat.log 2 L
      have hell : 8 ≤ ell := by
        dsimp only [ell, L]
        omega
      have hLne : L ≠ 0 := by
        have hellpos : 0 < ell := by omega
        have : 2 ≤ L := (Nat.log_pos_iff.mp hellpos).1
        omega
      have hL8 : 8 ≤ L := by
        calc
          8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ ell :=
            Nat.pow_le_pow_right (by omega) (by omega)
          _ ≤ L := Nat.pow_log_le_self 2 hLne
      exact hL8.trans (Nat.log_le_self 2 B)
    have hlogBpos : 0 < Real.log (B : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < B by omega))
    have hlogEight :
        (1 : ℝ) < Real.log 8 := by
      have hlogTwo := Real.log_two_gt_d9
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      norm_num
      linarith
    have hlogEightLe :
        Real.log 8 ≤ Real.log B := by
      apply Real.log_le_log
      · norm_num
      · exact_mod_cast hB8
    have hloglogBpos :
        0 < Real.log (Real.log B) :=
      Real.log_pos (hlogEight.trans_le hlogEightLe)
    positivity
  have hdyadicDenPos :
      0 <
        (Nat.log 2 B : ℝ) *
          (Nat.log 2 (Nat.log 2 B) : ℝ) := by
    have hfirst :
        0 < Nat.log 2 (Nat.log 2 B) := by omega
    have hsecond :
        0 < Nat.log 2 B := by
      have : 2 ≤ Nat.log 2 B :=
        (Nat.log_pos_iff.mp hfirst).1
      omega
    positivity
  exact hdyadic.trans
    (div_le_div_of_nonneg_left
      (by positivity)
      hrealDenPos hden)

-- Keep the threshold symbolic here: external kernels can otherwise try to
-- normalize the astronomically large closed double-exponential threshold.
private opaque alignedHammingNumerics_eventually_of_threshold
    (T : ℕ) (hT : 16384 ≤ T)
    {C : ℝ} (hC : 0 ≤ C) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L,
      CriticalRunWindow.InRunLengthWindow C N L →
      64 ≤ L + 1 ∧
      (componentHammingRadius (L + 1) : ℝ) ≤
        65 * (L + 1 : ℕ) /
          (Real.log (L + 1 : ℕ) *
            Real.log (Real.log (L + 1 : ℕ))) ∧
      ∀ m, (L + 1) / 16 ≤ m →
        1 ≤ componentHammingRadius (L + 1) ∧
        2 * componentHammingRadius (L + 1) ≤ m ∧
        PrimesUpTo.count (L + 1) + 2 ≤ m ∧
        2 * componentHammingRadius (L + 1) *
            2 ^ ((PrimesUpTo.count (L + 1) + 2) /
              componentHammingRadius (L + 1) + 1) ≤ m := by
  let K : ℕ := 2 ^ (2 ^ T)
  obtain ⟨Nwindow, hNwindow⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  obtain ⟨Nadm, hNadm⟩ :=
    CriticalWeightedDefect.admissible_eventually
      CriticalRunWindow.lowerConstant_pos
      CriticalRunWindow.lowerConstant_lt_upperConstant
  obtain ⟨Nheight, hNheight⟩ :=
    CriticalWeightedDefect.height_tends_to_infinity
      (c₂ := CriticalRunWindow.upperConstant)
      CriticalRunWindow.lowerConstant_pos K
  obtain ⟨Nheight64, hNheight64⟩ :=
    CriticalWeightedDefect.height_tends_to_infinity
      (c₂ := CriticalRunWindow.upperConstant)
      CriticalRunWindow.lowerConstant_pos 64
  refine
    ⟨max Nwindow (max Nadm (max Nheight Nheight64)), ?_⟩
  intro N hN L hrun
  have hNwindowN : Nwindow ≤ N :=
    (le_max_left _ _).trans hN
  have hNtail : max Nadm (max Nheight Nheight64) ≤ N :=
    (le_max_right _ _).trans hN
  have hNadmN : Nadm ≤ N :=
    (le_max_left _ _).trans hNtail
  have hNheights : max Nheight Nheight64 ≤ N :=
    (le_max_right _ _).trans hNtail
  have hNheightN : Nheight ≤ N :=
    (le_max_left _ _).trans hNheights
  have hNheight64N : Nheight64 ≤ N :=
    (le_max_right _ _).trans hNheights
  have hfirst :=
    hNwindow N hNwindowN L hrun
  have hadmissible :
      CriticalWeightedDefect.Admissible
        CriticalRunWindow.lowerConstant
        CriticalRunWindow.upperConstant N (L + 1) :=
    hNadm N hNadmN (L + 1) hfirst.1
  have hheight : K ≤ L + 1 :=
    hNheight N hNheightN (L + 1) hadmissible
  have hB64 : 64 ≤ L + 1 :=
    hNheight64 N hNheight64N (L + 1) hadmissible
  have hfirstLog :
      2 ^ T ≤ Nat.log 2 (L + 1) := by
    apply Nat.le_log_of_pow_le Nat.one_lt_two
    simpa only [K] using hheight
  have hthresholdLog :
      T ≤ Nat.log 2 (Nat.log 2 (L + 1)) :=
    Nat.le_log_of_pow_le Nat.one_lt_two hfirstLog
  have hloglog :
      16384 ≤ Nat.log 2 (Nat.log 2 (L + 1)) :=
    hT.trans hthresholdLog
  refine
    ⟨hB64,
      componentHammingRadius_cast_le_real_log hloglog, ?_⟩
  intro m hm
  exact componentHammingRadius_conditions_of_loglog hloglog hm

/--
Uniform package for the Hamming branch: the fixed radius has the correct
real order and satisfies all four finite code inequalities as soon as the
component family has cardinality at least `B/16`.
-/
theorem alignedHammingNumerics_eventually
    {C : ℝ} (hC : 0 ≤ C) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L,
      CriticalRunWindow.InRunLengthWindow C N L →
      64 ≤ L + 1 ∧
      (componentHammingRadius (L + 1) : ℝ) ≤
        65 * (L + 1 : ℕ) /
          (Real.log (L + 1 : ℕ) *
            Real.log (Real.log (L + 1 : ℕ))) ∧
      ∀ m, (L + 1) / 16 ≤ m →
        1 ≤ componentHammingRadius (L + 1) ∧
        2 * componentHammingRadius (L + 1) ≤ m ∧
        PrimesUpTo.count (L + 1) + 2 ≤ m ∧
        2 * componentHammingRadius (L + 1) *
            2 ^ ((PrimesUpTo.count (L + 1) + 2) /
              componentHammingRadius (L + 1) + 1) ≤ m :=
  alignedHammingNumerics_eventually_of_threshold 16384 le_rfl hC

/--
Eventual exclusion of the aligned part of the deep core appearing after the
Section 7 partition.

The quantifier order is uniform in `N,L,H,x,y` and in the bundled reduced
candidate.  The only mathematical premise left is membership in that deep
core, expressed by the literal integer inequality `3B < 16c#`.
-/
theorem no_aligned_deep_core_eventually
    {C : ℝ} (hC : 0 ≤ C) (A : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L,
      CriticalRunWindow.InRunLengthWindow C N L →
      ∀ H, 1 ≤ H → H ≤ (L + 1) ^ A →
      ∀ x : ℕ, x ∈ dyadicBlock N →
      ∀ y : ℕ, y ∈ dyadicBlock N →
      ∀ c : ReducedCandidate x y (L + 1) H,
        3 * (L + 1) <
          16 *
            (residualComponents x y L c.1.1 c.1.2
              (pairChannelError x y c.1.1 c.1.2)).card →
        False := by
  obtain ⟨Nhamming, hHamming⟩ :=
    alignedHammingNumerics_eventually hC
  obtain ⟨Nrunge, hRunge⟩ :=
    AlignedRungeGrowth.rungeNumerics_eventually
      hC (by norm_num : (0 : ℝ) ≤ 65) A
  refine ⟨max 2 (max Nhamming Nrunge), ?_⟩
  intro N hN L hwindow H hH hHupper x hx y hy c hdensity
  have hNtwo : 2 ≤ N :=
    (le_max_left _ _).trans hN
  have hNtail : max Nhamming Nrunge ≤ N :=
    (le_max_right _ _).trans hN
  have hNhamming : Nhamming ≤ N :=
    (le_max_left _ _).trans hNtail
  have hNrunge : Nrunge ≤ N :=
    (le_max_right _ _).trans hNtail
  have hxLower : N ≤ x :=
    (Finset.mem_Ico.mp (by simpa [dyadicBlock] using hx)).1
  have hyLower : N ≤ y :=
    (Finset.mem_Ico.mp (by simpa [dyadicBlock] using hy)).1
  have hxTwo : 2 ≤ x := hNtwo.trans hxLower
  have hyTwo : 2 ≤ y := hNtwo.trans hyLower
  obtain ⟨hB64, htReal, hconditions⟩ :=
    hHamming N hNhamming L hwindow
  have hfamily :=
    one_sixteenth_le_card_smallExactFreeResidualComponents_of_candidate
      c hxTwo hyTwo (by omega) hdensity
  obtain ⟨ht, hmt, hrows, hvolume⟩ :=
    hconditions
      (smallExactFreeResidualComponents
        x y L c.1.1 c.1.2
          (pairChannelError x y c.1.1 c.1.2) 43).card
      hfamily
  obtain ⟨hRungeRange, hbase⟩ :=
    hRunge N hNrunge L hwindow H hH hHupper
      (componentHammingRadius (L + 1)) htReal
      c.1.1 (candidate_fst_pos c) x hx
  exact
    no_candidate_aligned_core_of_finite_conditions
      (K := 43) c hxTwo hyTwo ht hmt hrows hvolume
      hbase hRungeRange

end

end TheoremEightAlignedClosure
end PaperC
