import PaperC.Asymptotics.HighZoneTwoDefects

set_option maxHeartbeats 2400000

/-!
# Equal-kernel two-defect starts on a bounded-ratio interval

This module isolates the `d₁ = d₂` branch in Lemma 17.25.  For two
representations

`u+i₁ = d a²`, `u+i₂ = d b²`,

Lean records the exact factorization

`(a-b)(a+b) = (i₁-i₂)/d`.

For distinct offsets bounded by `B`, both square roots are at most `B`.
Consequently a fixed kernel and a fixed ordered pair of offsets contribute
at most `B+1` starts.  A finite union over one squarefree `B`-smooth kernel
and two offsets therefore costs at most

`#D * (#I)² * (B+1)`.

The final section connects this abstract union to canonical decompositions
of actual defective values in `[N,M)`.  In the genuine high zone
`B²+1 < N`, the equal-kernel population is empty.  Thus this branch needs
neither Evertse--Silverman nor generalized Pell; the remaining arithmetic
work in Lemma 17.25 lies entirely in the distinct-kernel branch.
-/

namespace PaperC
namespace BoundedRatioTwoDefectStarts

open DefectCounting
open DefectivePredicate
open HighZoneTwoDefects
open SquarefreeSmoothCount
open ComponentNormalization

noncomputable section

/-! ## Exact factorization and a fixed-parameter count -/

/--
The two equal-kernel defect equations give the exact difference-of-squares
factorization over the integers.
-/
theorem equalKernelWitness_factorization
    {d i₁ i₂ H : ℕ}
    {w : MultipleDefects.TwoDefectWitness}
    (hd : d ≠ 0)
    (hw :
      MultipleDefects.twoDefectWitnessBox
        d d i₁ i₂ H w) :
    ((w.leftRoot : ℤ) - (w.rightRoot : ℤ)) *
        ((w.leftRoot : ℤ) + (w.rightRoot : ℤ)) =
      ((i₁ : ℤ) - (i₂ : ℤ)) / (d : ℤ) := by
  have hpell :=
    MultipleDefects.twoDefectWitness_maps_to_pell hw
  unfold PellInput.pellBox PellInput.pellEquation at hpell
  exact
    MultipleDefects.equal_coefficient_factorization
      (by exact_mod_cast hd) hpell.1

private theorem roots_le_of_offsets_lt
    {d i₁ i₂ H B : ℕ}
    {w : MultipleDefects.TwoDefectWitness}
    (hd : 0 < d)
    (hi₂ : i₂ ≤ B)
    (horder : i₁ < i₂)
    (hw :
      MultipleDefects.twoDefectWitnessBox
        d d i₁ i₂ H w) :
    w.leftRoot ≤ B ∧ w.rightRoot ≤ B := by
  let a := w.leftRoot
  let b := w.rightRoot
  have hleft : w.start + i₁ = d * a ^ 2 := hw.1
  have hright : w.start + i₂ = d * b ^ 2 := hw.2.1
  have habSq : a ^ 2 < b ^ 2 := by
    rw [← Nat.mul_lt_mul_left hd, ← hleft, ← hright]
    omega
  have hab : a < b :=
    (Nat.pow_lt_pow_iff_left
      (by norm_num : (2 : ℕ) ≠ 0)).mp habSq
  have habGap : a ^ 2 + b ≤ b ^ 2 := by
    nlinarith
  have hstep :
      d * a ^ 2 + d * b ≤ d * b ^ 2 := by
    calc
      d * a ^ 2 + d * b =
          d * (a ^ 2 + b) := by ring
      _ ≤ d * b ^ 2 :=
        Nat.mul_le_mul_left d habGap
  have hdb : d * b ≤ i₂ - i₁ := by
    omega
  have hb : b ≤ B := by
    calc
      b ≤ d * b := Nat.le_mul_of_pos_left b hd
      _ ≤ i₂ - i₁ := hdb
      _ ≤ B := by omega
  exact ⟨hab.le.trans hb, hb⟩

/--
For equal positive kernels and distinct offsets in `[0,B]`, both roots are
at most `B`, independently of the ambient box height.
-/
theorem equalKernelWitness_roots_le
    {d i₁ i₂ H B : ℕ}
    {w : MultipleDefects.TwoDefectWitness}
    (hd : 0 < d)
    (hi₁ : i₁ ≤ B) (hi₂ : i₂ ≤ B)
    (hne : i₁ ≠ i₂)
    (hw :
      MultipleDefects.twoDefectWitnessBox
        d d i₁ i₂ H w) :
    w.leftRoot ≤ B ∧ w.rightRoot ≤ B := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact roots_le_of_offsets_lt
      hd hi₂ hlt hw
  · have hswap :
        MultipleDefects.twoDefectWitnessBox
          d d i₂ i₁ H
          { start := w.start
            leftRoot := w.rightRoot
            rightRoot := w.leftRoot } := by
      exact ⟨hw.2.1, hw.1, hw.2.2.2, hw.2.2.1⟩
    have hroots :=
      roots_le_of_offsets_lt
        hd hi₁ hgt hswap
    exact ⟨hroots.2, hroots.1⟩

/--
For a fixed positive kernel and fixed offsets, the first square root
determines the whole two-defect witness.
-/
theorem leftRoot_injective_on_equalKernelWitnessBox
    {d i₁ i₂ H : ℕ}
    (hd : 0 < d)
    {u v : MultipleDefects.TwoDefectWitness}
    (hu :
      MultipleDefects.twoDefectWitnessBox
        d d i₁ i₂ H u)
    (hv :
      MultipleDefects.twoDefectWitnessBox
        d d i₁ i₂ H v)
    (hroot : u.leftRoot = v.leftRoot) :
    u = v := by
  have hstart : u.start = v.start := by
    have huLeft := hu.1
    have hvLeft := hv.1
    rw [hroot] at huLeft
    omega
  have hrightSquares :
      u.rightRoot ^ 2 = v.rightRoot ^ 2 := by
    have hmul :
        d * u.rightRoot ^ 2 =
          d * v.rightRoot ^ 2 := by
      calc
        d * u.rightRoot ^ 2 = u.start + i₂ :=
          hu.2.1.symm
        _ = v.start + i₂ := by rw [hstart]
        _ = d * v.rightRoot ^ 2 := hv.2.1
    exact Nat.eq_of_mul_eq_mul_left hd hmul
  have hright :
      u.rightRoot = v.rightRoot :=
    Nat.pow_left_injective
      (by decide : 2 ≠ 0) hrightSquares
  cases u
  cases v
  simp_all

/--
The equal-kernel witness predicate has at most `B+1` solutions for one
kernel and one ordered pair of distinct offsets.
-/
theorem equalKernelWitnessBox_atMost
    {d i₁ i₂ H B : ℕ}
    (hd : 0 < d)
    (hi₁ : i₁ ≤ B) (hi₂ : i₂ ≤ B)
    (hne : i₁ ≠ i₂) :
    PellInput.HasAtMostSolutionsReal
      (MultipleDefects.twoDefectWitnessBox
        d d i₁ i₂ H)
      (B + 1 : ℝ) := by
  intro s hs
  let root :
      MultipleDefects.TwoDefectWitness → ℕ :=
    fun w ↦ w.leftRoot
  have hinjective :
      ∀ ⦃u⦄, u ∈ s → ∀ ⦃v⦄, v ∈ s →
        root u = root v → u = v := by
    intro u hu v hv huv
    exact
      leftRoot_injective_on_equalKernelWitnessBox
        hd (hs u hu) (hs v hv) huv
  have hsubset :
      s.image root ⊆ Finset.range (B + 1) := by
    intro a ha
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp ha
    rw [Finset.mem_range]
    exact Nat.lt_succ_iff.mpr
      (equalKernelWitness_roots_le
        hd hi₁ hi₂ hne (hs w hw)).1
  have hcard :
      s.card ≤ B + 1 := by
    calc
      s.card = (s.image root).card := by
        symm
        rw [Finset.card_image_iff]
        exact hinjective
      _ ≤ (Finset.range (B + 1)).card :=
        Finset.card_le_card hsubset
      _ = B + 1 := Finset.card_range _
  exact_mod_cast hcard

/--
The starts represented by one equal-kernel parameter tuple also have
cardinality at most `B+1`.
-/
theorem card_equalKernelStartsForParameters_le
    {d i₁ i₂ H X B : ℕ}
    (hd : 0 < d)
    (hi₁ : i₁ ≤ B) (hi₂ : i₂ ≤ B)
    (hne : i₁ ≠ i₂) :
    ((startsForParameters
      d d i₁ i₂ H X).card : ℝ) ≤
      (B + 1 : ℝ) :=
  card_startsForParameters_le
    (equalKernelWitnessBox_atMost
      hd hi₁ hi₂ hne)

/-! ## Union over one smooth kernel and two offsets -/

/--
Finite union of the equal-kernel starts.  The erasure makes the offsets
structurally distinct.
-/
def equalKernelPairedDefectStarts
    (D I : Finset ℕ) (H X : ℕ) :
    Finset ℕ :=
  D.biUnion fun d ↦
    I.biUnion fun i₁ ↦
      (I.erase i₁).biUnion fun i₂ ↦
        startsForParameters d d i₁ i₂ H X

/--
Exact finite union bound for the equal-kernel branch:

`# ≤ #D · (#I)² · (B+1)`.
-/
theorem card_equalKernelPairedDefectStarts_le
    {D I : Finset ℕ} {H X B : ℕ}
    (hDpos : ∀ d ∈ D, 0 < d)
    (hI : ∀ i ∈ I, i ≤ B) :
    ((equalKernelPairedDefectStarts
      D I H X).card : ℝ) ≤
      (D.card : ℝ) *
        (I.card : ℝ) ^ 2 *
          (B + 1 : ℝ) := by
  classical
  have hi₂ :
      ∀ d ∈ D, ∀ i₁ ∈ I,
        (((I.erase i₁).biUnion fun i₂ ↦
          startsForParameters d d i₁ i₂ H X).card : ℝ) ≤
          (I.card : ℝ) * (B + 1 : ℝ) := by
    intro d hd i₁ hi₁
    have hboundNonneg : 0 ≤ (B + 1 : ℝ) := by positivity
    have herase :
        (((I.erase i₁).card : ℕ) : ℝ) ≤
          (I.card : ℝ) := by
      exact_mod_cast Finset.card_erase_le
    calc
      (((I.erase i₁).biUnion fun i₂ ↦
          startsForParameters d d i₁ i₂ H X).card : ℝ) ≤
          ∑ i₂ ∈ I.erase i₁,
            ((startsForParameters
              d d i₁ i₂ H X).card : ℝ) := by
        rw [← Nat.cast_sum]
        exact_mod_cast Finset.card_biUnion_le
      _ ≤
          ∑ _i₂ ∈ I.erase i₁,
            (B + 1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i₂ hi₂mem
        exact
          card_equalKernelStartsForParameters_le
            (hDpos d hd) (hI i₁ hi₁)
            (hI i₂ (Finset.mem_of_mem_erase hi₂mem))
            (Finset.ne_of_mem_erase hi₂mem).symm
      _ =
          ((I.erase i₁).card : ℝ) *
            (B + 1 : ℝ) := by
        simp
        ring
      _ ≤
          (I.card : ℝ) * (B + 1 : ℝ) :=
        mul_le_mul_of_nonneg_right
          herase hboundNonneg
  have hi₁ :
      ∀ d ∈ D,
        ((I.biUnion fun i₁ ↦
          (I.erase i₁).biUnion fun i₂ ↦
            startsForParameters
              d d i₁ i₂ H X).card : ℝ) ≤
          (I.card : ℝ) ^ 2 *
            (B + 1 : ℝ) := by
    intro d hd
    calc
      ((I.biUnion fun i₁ ↦
          (I.erase i₁).biUnion fun i₂ ↦
            startsForParameters
              d d i₁ i₂ H X).card : ℝ) ≤
          ∑ i₁ ∈ I,
            (((I.erase i₁).biUnion fun i₂ ↦
              startsForParameters
                d d i₁ i₂ H X).card : ℝ) := by
        rw [← Nat.cast_sum]
        exact_mod_cast Finset.card_biUnion_le
      _ ≤
          ∑ _i₁ ∈ I,
            (I.card : ℝ) *
              (B + 1 : ℝ) := by
        exact Finset.sum_le_sum fun i₁ hi₁mem ↦
          hi₂ d hd i₁ hi₁mem
      _ =
          (I.card : ℝ) ^ 2 *
            (B + 1 : ℝ) := by
        simp
        ring
  calc
    ((equalKernelPairedDefectStarts
        D I H X).card : ℝ) ≤
        ∑ d ∈ D,
          ((I.biUnion fun i₁ ↦
            (I.erase i₁).biUnion fun i₂ ↦
              startsForParameters
                d d i₁ i₂ H X).card : ℝ) := by
      rw [← Nat.cast_sum]
      exact_mod_cast Finset.card_biUnion_le
    _ ≤
        ∑ _d ∈ D,
          (I.card : ℝ) ^ 2 *
            (B + 1 : ℝ) := by
      exact Finset.sum_le_sum fun d hd ↦
        hi₁ d hd
    _ =
        (D.card : ℝ) *
          (I.card : ℝ) ^ 2 *
            (B + 1 : ℝ) := by
      simp
      ring

/--
Specialization to all squarefree `B`-smooth kernels up to `X` and all
offsets in `[0,B]`.
-/
theorem card_equalKernelSmoothStarts_le
    (B H X : ℕ) :
    ((equalKernelPairedDefectStarts
      (squarefreeSmoothUpTo B X)
      (Finset.range (B + 1))
      H X).card : ℝ) ≤
      ((squarefreeSmoothUpTo B X).card : ℝ) *
        (B + 1 : ℝ) ^ 3 := by
  have hfinite :=
    card_equalKernelPairedDefectStarts_le
      (D := squarefreeSmoothUpTo B X)
      (I := Finset.range (B + 1))
      (H := H) (X := X) (B := B)
      (fun d hd ↦
        (mem_squarefreeSmoothUpTo.mp hd).1)
      (fun i hi ↦ by
        rw [Finset.mem_range] at hi
        omega)
  calc
    ((equalKernelPairedDefectStarts
        (squarefreeSmoothUpTo B X)
        (Finset.range (B + 1))
        H X).card : ℝ) ≤
        ((squarefreeSmoothUpTo B X).card : ℝ) *
          ((Finset.range (B + 1)).card : ℝ) ^ 2 *
            (B + 1 : ℝ) :=
      hfinite
    _ =
        ((squarefreeSmoothUpTo B X).card : ℝ) *
          (B + 1 : ℝ) ^ 3 := by
      simp only [Finset.card_range, Nat.cast_add,
        Nat.cast_one]
      ring

/-! ## Actual equal-kernel defective bases -/

/--
Bases below `M` admitting two distinct offsets in `[0,B]` at which the
values are `B`-defective and have the same canonical squarefree kernel.

The lower condition is written as `N ≤ base + 1`, matching the shifted
window coordinates used in the bounded-ratio argument.
-/
def equalKernelDefectBases
    (N M B : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range M).filter fun base ↦
    N ≤ base + 1 ∧
      ∃ i₁ ∈ Finset.range (B + 1),
      ∃ i₂ ∈ Finset.range (B + 1),
        i₁ ≠ i₂ ∧
          HDefective B (base + i₁) ∧
          HDefective B (base + i₂) ∧
          squarefreeKernel (base + i₁) =
            squarefreeKernel (base + i₂)

@[simp]
theorem mem_equalKernelDefectBases
    {N M B base : ℕ} :
    base ∈ equalKernelDefectBases N M B ↔
      base < M ∧
        N ≤ base + 1 ∧
        ∃ i₁ ∈ Finset.range (B + 1),
        ∃ i₂ ∈ Finset.range (B + 1),
          i₁ ≠ i₂ ∧
            HDefective B (base + i₁) ∧
            HDefective B (base + i₂) ∧
            squarefreeKernel (base + i₁) =
              squarefreeKernel (base + i₂) := by
  classical
  simp [equalKernelDefectBases, and_assoc]

/--
Every actual equal-kernel base is represented by the finite union over
squarefree `B`-smooth kernels and distinct offsets.  The canonical square
parts themselves provide the two roots.
-/
theorem equalKernelDefectBases_subset_smoothStarts
    {N M B : ℕ}
    (hN : 2 ≤ N) :
    equalKernelDefectBases N M B ⊆
      equalKernelPairedDefectStarts
        (squarefreeSmoothUpTo B (M + B))
        (Finset.range (B + 1))
        (M + B) M := by
  classical
  intro base hbase
  rw [mem_equalKernelDefectBases] at hbase
  rcases hbase with
    ⟨hbaseM, hbaseN, i₁, hi₁, i₂, hi₂, hne,
      hdef₁, hdef₂, hkernel⟩
  have hi₁B : i₁ ≤ B := by
    rw [Finset.mem_range] at hi₁
    omega
  have hi₂B : i₂ ≤ B := by
    rw [Finset.mem_range] at hi₂
    omega
  have hn₁ : 0 < base + i₁ := by omega
  have hn₂ : 0 < base + i₂ := by omega
  have hn₁Bound : base + i₁ ≤ M + B := by omega
  have hn₂Bound : base + i₂ ≤ M + B := by omega
  have hdecomp₁ :=
    canonical_squarefree_decomposition hn₁
  have hdecomp₂ :=
    canonical_squarefree_decomposition hn₂
  have hkernelMem :
      squarefreeKernel (base + i₁) ∈
        squarefreeSmoothUpTo B (M + B) := by
    rw [mem_squarefreeSmoothUpTo]
    exact
      ⟨hdecomp₁.1,
        (squarefreeKernel_le hn₁).trans hn₁Bound,
        hdecomp₁.2.1,
        squarefreeKernel_isSmoothAt_of_hDefective hdef₁⟩
  have hleftRootBound :
      canonicalSquarePart (base + i₁) ≤ M + B :=
    (canonicalSquarePart_le_self hn₁).trans hn₁Bound
  have hrightRootBound :
      canonicalSquarePart (base + i₂) ≤ M + B :=
    (canonicalSquarePart_le_self hn₂).trans hn₂Bound
  let w : MultipleDefects.TwoDefectWitness :=
    { start := base
      leftRoot := canonicalSquarePart (base + i₁)
      rightRoot := canonicalSquarePart (base + i₂) }
  have hbox :
      MultipleDefects.twoDefectWitnessBox
        (squarefreeKernel (base + i₁))
        (squarefreeKernel (base + i₁))
        i₁ i₂ (M + B) w := by
    refine
      ⟨hdecomp₁.2.2.2, ?_,
        hleftRootBound, hrightRootBound⟩
    rw [hkernel]
    exact hdecomp₂.2.2.2
  unfold equalKernelPairedDefectStarts
  rw [Finset.mem_biUnion]
  refine
    ⟨squarefreeKernel (base + i₁), hkernelMem, ?_⟩
  rw [Finset.mem_biUnion]
  refine ⟨i₁, hi₁, ?_⟩
  rw [Finset.mem_biUnion]
  refine
    ⟨i₂, Finset.mem_erase.mpr ⟨hne.symm, hi₂⟩, ?_⟩
  unfold startsForParameters
  apply Finset.mem_image.mpr
  refine ⟨w, ?_, rfl⟩
  rw [mem_boundedTwoDefectWitnesses]
  exact ⟨hbaseM, hbox⟩

/--
Finite quantitative form of the preceding cover.  Before using the
high-zone separation, the equal-kernel bases cost at most one smooth-kernel
factor and three factors of size `B+1`.
-/
theorem card_equalKernelDefectBases_le
    {N M B : ℕ}
    (hN : 2 ≤ N) :
    ((equalKernelDefectBases N M B).card : ℝ) ≤
      ((squarefreeSmoothUpTo B (M + B)).card : ℝ) *
        (B + 1 : ℝ) ^ 3 := by
  have hcover :
      ((equalKernelDefectBases N M B).card : ℝ) ≤
        ((equalKernelPairedDefectStarts
          (squarefreeSmoothUpTo B (M + B))
          (Finset.range (B + 1))
          (M + B) M).card : ℝ) := by
    exact_mod_cast Finset.card_le_card
      (equalKernelDefectBases_subset_smoothStarts hN)
  have hunion :=
    card_equalKernelPairedDefectStarts_le
      (D := squarefreeSmoothUpTo B (M + B))
      (I := Finset.range (B + 1))
      (H := M + B) (X := M) (B := B)
      (fun d hd ↦
        (mem_squarefreeSmoothUpTo.mp hd).1)
      (fun i hi ↦ by
        rw [Finset.mem_range] at hi
        omega)
  calc
    ((equalKernelDefectBases N M B).card : ℝ) ≤
        ((equalKernelPairedDefectStarts
          (squarefreeSmoothUpTo B (M + B))
          (Finset.range (B + 1))
          (M + B) M).card : ℝ) :=
      hcover
    _ ≤
        ((squarefreeSmoothUpTo B (M + B)).card : ℝ) *
          ((Finset.range (B + 1)).card : ℝ) ^ 2 *
            (B + 1 : ℝ) :=
      hunion
    _ =
        ((squarefreeSmoothUpTo B (M + B)).card : ℝ) *
          (B + 1 : ℝ) ^ 3 := by
      simp only [Finset.card_range, Nat.cast_add,
        Nat.cast_one]
      ring

/--
In the genuine high zone, the actual equal-kernel branch is empty.
This is the exact `d₁ = d₂` discharge in Lemma 17.25.
-/
theorem equalKernelDefectBases_eq_empty
    {N M B : ℕ}
    (hhigh : B ^ 2 + 1 < N) :
    equalKernelDefectBases N M B = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro base hbase
  rw [mem_equalKernelDefectBases] at hbase
  rcases hbase with
    ⟨_hbaseM, hbaseN, i₁, hi₁, i₂, hi₂, hne,
      hdef₁, hdef₂, hkernel⟩
  have hi₁B : i₁ ≤ B := by
    rw [Finset.mem_range] at hi₁
    omega
  have hi₂B : i₂ ≤ B := by
    rw [Finset.mem_range] at hi₂
    omega
  have hn₁ : 0 < base + i₁ := by omega
  have hn₂ : 0 < base + i₂ := by omega
  have hdecomp₁ :=
    canonical_squarefree_decomposition hn₁
  have hdecomp₂ :=
    canonical_squarefree_decomposition hn₂
  have hright :
      base + i₂ =
        squarefreeKernel (base + i₁) *
          canonicalSquarePart (base + i₂) ^ 2 := by
    rw [hkernel]
    exact hdecomp₂.2.2.2
  have hbaseHigh : B ^ 2 < base := by omega
  exact
    HighZoneTwoDefects.equal_kernel_offsets_impossible
      hdecomp₁.1 hi₁B hi₂B hne
      hdecomp₁.2.2.2 hright hbaseHigh

end

end BoundedRatioTwoDefectStarts
end PaperC
