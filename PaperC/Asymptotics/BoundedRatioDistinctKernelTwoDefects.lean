import PaperC.Asymptotics.HighZoneTwoDefects
import PaperC.Arithmetic.ChebyshevPrimeCount
import PaperC.Asymptotics.CriticalRationalMassEnvelopes
import PaperC.Asymptotics.DependencyEdgesCritical
import PaperC.Asymptotics.ExpLogDivLogLog
import Mathlib.Data.Int.Lemmas

set_option maxHeartbeats 3200000

/-!
# Distinct-kernel two-defect bases on bounded-ratio intervals

This module closes the `d₁ ≠ d₂` branch in Lemma 17.25.  An actual base
carrying two distinct defective offsets is sent, through the canonical
squarefree decompositions of the two values, to the finite family
`HighZoneTwoDefects.distinctPairedDefectStarts`.

The existing generalized-Pell hypothesis then supplies the count for every
fixed pair of kernels and offsets.  The four finite unions are summed
explicitly by `card_distinctPairedDefectStarts_le`, producing

`#D² * (B+1)² * exp(c log A / log log A)`.

Here `D` is the set of squarefree `B`-smooth kernels in a chosen polynomial
ambient box.  The final section uses the unconditional Chebyshev prime-count
bound already formalized in the repository.  Thus, in the critical
run-length window and uniformly for bounded-ratio endpoints, the whole
distinct-kernel population is `N^o(1)` under the sole existing generalized
Pell hypothesis.  No new bridge is introduced.
-/

namespace PaperC
namespace BoundedRatioDistinctKernelTwoDefects

open DefectCounting
open DefectivePredicate
open HighZoneTwoDefects
open SquarefreeSmoothCount
open ComponentNormalization

noncomputable section

/-! ## The actual distinct-kernel population -/

/--
Bases below `M` carrying two distinct offsets in `[0,B]`, both defective,
whose canonical squarefree kernels are distinct.
-/
def distinctKernelDefectBases
    (N M B : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range M).filter fun base ↦
    N ≤ base + 1 ∧
      ∃ i₁ ∈ Finset.range (B + 1),
      ∃ i₂ ∈ Finset.range (B + 1),
        i₁ ≠ i₂ ∧
          HDefective B (base + i₁) ∧
          HDefective B (base + i₂) ∧
          squarefreeKernel (base + i₁) ≠
            squarefreeKernel (base + i₂)

@[simp]
theorem mem_distinctKernelDefectBases
    {N M B base : ℕ} :
    base ∈ distinctKernelDefectBases N M B ↔
      base < M ∧
        N ≤ base + 1 ∧
        ∃ i₁ ∈ Finset.range (B + 1),
        ∃ i₂ ∈ Finset.range (B + 1),
          i₁ ≠ i₂ ∧
            HDefective B (base + i₁) ∧
            HDefective B (base + i₂) ∧
            squarefreeKernel (base + i₁) ≠
              squarefreeKernel (base + i₂) := by
  classical
  simp [distinctKernelDefectBases, and_assoc]

/--
Canonical decomposition covers the actual population by the existing
finite distinct-kernel Pell union, in any ambient box containing `M+B`.
-/
theorem distinctKernelDefectBases_subset_distinctPaired
    {N M B Y : ℕ}
    (hN : 2 ≤ N)
    (hY : M + B ≤ Y) :
    distinctKernelDefectBases N M B ⊆
      distinctPairedDefectStarts
        (squarefreeSmoothUpTo B Y)
        (Finset.range (B + 1))
        Y M := by
  classical
  intro base hbase
  rw [mem_distinctKernelDefectBases] at hbase
  rcases hbase with
    ⟨hbaseM, hbaseN, i₁, hi₁, i₂, hi₂, hiNe,
      hdef₁, hdef₂, hkernelNe⟩
  have hi₁B : i₁ ≤ B := by
    rw [Finset.mem_range] at hi₁
    omega
  have hi₂B : i₂ ≤ B := by
    rw [Finset.mem_range] at hi₂
    omega
  let n₁ := base + i₁
  let n₂ := base + i₂
  let d₁ := squarefreeKernel n₁
  let d₂ := squarefreeKernel n₂
  let a := canonicalSquarePart n₁
  let b := canonicalSquarePart n₂
  have hn₁pos : 0 < n₁ := by
    dsimp [n₁]
    omega
  have hn₂pos : 0 < n₂ := by
    dsimp [n₂]
    omega
  have hn₁Bound : n₁ ≤ Y := by
    dsimp [n₁]
    omega
  have hn₂Bound : n₂ ≤ Y := by
    dsimp [n₂]
    omega
  have hdecomp₁ : n₁ = d₁ * a ^ 2 := by
    simpa [d₁, a] using
      (canonical_squarefree_decomposition hn₁pos).2.2.2
  have hdecomp₂ : n₂ = d₂ * b ^ 2 := by
    simpa [d₂, b] using
      (canonical_squarefree_decomposition hn₂pos).2.2.2
  have hd₁Mem : d₁ ∈ squarefreeSmoothUpTo B Y := by
    rw [mem_squarefreeSmoothUpTo]
    refine
      ⟨(canonical_squarefree_decomposition hn₁pos).1,
        (squarefreeKernel_le hn₁pos).trans hn₁Bound,
        (canonical_squarefree_decomposition hn₁pos).2.1, ?_⟩
    exact squarefreeKernel_isSmoothAt_of_hDefective hdef₁
  have hd₂Mem : d₂ ∈ squarefreeSmoothUpTo B Y := by
    rw [mem_squarefreeSmoothUpTo]
    refine
      ⟨(canonical_squarefree_decomposition hn₂pos).1,
        (squarefreeKernel_le hn₂pos).trans hn₂Bound,
        (canonical_squarefree_decomposition hn₂pos).2.1, ?_⟩
    exact squarefreeKernel_isSmoothAt_of_hDefective hdef₂
  have hdNe : d₁ ≠ d₂ := by
    simpa [d₁, d₂, n₁, n₂] using hkernelNe
  have haBound : a ≤ Y :=
    (canonicalSquarePart_le_self hn₁pos).trans hn₁Bound
  have hbBound : b ≤ Y :=
    (canonicalSquarePart_le_self hn₂pos).trans hn₂Bound
  rw [distinctPairedDefectStarts]
  apply Finset.mem_biUnion.mpr
  refine ⟨d₁, hd₁Mem, ?_⟩
  apply Finset.mem_biUnion.mpr
  refine
    ⟨d₂, Finset.mem_erase.mpr ⟨hdNe.symm, hd₂Mem⟩, ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨i₁, hi₁, ?_⟩
  apply Finset.mem_biUnion.mpr
  refine
    ⟨i₂, Finset.mem_erase.mpr ⟨hiNe.symm, hi₂⟩, ?_⟩
  rw [startsForParameters]
  apply Finset.mem_image.mpr
  let w : MultipleDefects.TwoDefectWitness :=
    { start := base
      leftRoot := a
      rightRoot := b }
  refine ⟨w, ?_, rfl⟩
  rw [mem_boundedTwoDefectWitnesses]
  refine ⟨hbaseM, ?_⟩
  exact
    ⟨by simpa [w, n₁] using hdecomp₁,
      by simpa [w, n₂] using hdecomp₂,
      by simpa [w] using haBound,
      by simpa [w] using hbBound⟩

/-! ## Explicit finite Pell summation -/

/--
Polynomial-ambient finite form of the distinct-kernel count.

For every positive polynomial exponent `K`, the sole registered generalized
Pell hypothesis gives one constant `c` and one threshold, uniformly in the
bounded-ratio endpoints and in `B`.  The four finite sums contribute exactly
two smooth-kernel factors and two offset factors.
-/
theorem generalizedPell_implies_distinctKernelDefectBases_polynomial_bound
    (hPell : PellInput.GeneralizedPellPolynomialBoxStatement) :
    ∀ K : ℕ, 0 < K →
      ∃ c : ℝ, 0 ≤ c ∧
        ∃ A₀ : ℕ, ∀ A ≥ A₀, ∀ N M B : ℕ,
          2 ≤ N →
          M + B ≤ A ^ K →
          ((distinctKernelDefectBases N M B).card : ℝ) ≤
            ((squarefreeSmoothUpTo B (A ^ K)).card : ℝ) ^ 2 *
              (B + 1 : ℝ) ^ 2 *
              PellInput.expLogLogBound c A := by
  intro K hK
  have hTwo :=
    MultipleDefects.twoDefectPolynomialBox_of_generalizedPell
      hPell
  obtain ⟨c, hc, A₀, hA₀⟩ := hTwo K hK
  refine ⟨c, hc, A₀, ?_⟩
  intro A hA N M B hN hambient
  let D := squarefreeSmoothUpTo B (A ^ K)
  let I := Finset.range (B + 1)
  have hcount :
      ∀ d₁ ∈ D, ∀ d₂ ∈ D, d₁ ≠ d₂ →
        ∀ i₁ ∈ I, ∀ i₂ ∈ I, i₁ ≠ i₂ →
          PellInput.HasAtMostSolutionsReal
            (MultipleDefects.twoDefectWitnessBox
              d₁ d₂ i₁ i₂ (A ^ K))
            (PellInput.expLogLogBound c A) := by
    intro d₁ hd₁ d₂ hd₂ hdNe
      i₁ hi₁ i₂ hi₂ hiNe
    have hd₁Data := mem_squarefreeSmoothUpTo.mp hd₁
    have hd₂Data := mem_squarefreeSmoothUpTo.mp hd₂
    have hi₁B : i₁ ≤ B := by
      simpa only [I, Finset.mem_range,
        Nat.lt_succ_iff] using hi₁
    have hi₂B : i₂ ≤ B := by
      simpa only [I, Finset.mem_range,
        Nat.lt_succ_iff] using hi₂
    have hdeltaB :
        Int.natAbs ((i₁ : ℤ) - (i₂ : ℤ)) ≤ B :=
      Int.natAbs_coe_sub_coe_le_of_le hi₁B hi₂B
    have hdelta :
        Int.natAbs ((i₁ : ℤ) - (i₂ : ℤ)) ≤
          A ^ K := by
      exact hdeltaB.trans (by omega)
    exact
      hA₀ A hA d₁ d₂ i₁ i₂
        hd₁Data.1 hd₂Data.1
        hd₁Data.2.2.1 hd₂Data.2.2.1
        (TerminalPartnerPell.not_isSquare_ratio_of_squarefree_of_ne
          hd₁Data.1 hd₂Data.1
          hd₁Data.2.2.1 hd₂Data.2.2.1 hdNe)
        hiNe hd₁Data.2.1 hd₂Data.2.1 hdelta
  have hcover :=
    distinctKernelDefectBases_subset_distinctPaired
      (N := N) (M := M) (B := B) (Y := A ^ K)
      hN hambient
  have hcardCover :
      ((distinctKernelDefectBases N M B).card : ℝ) ≤
        ((distinctPairedDefectStarts
          D I (A ^ K) M).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hcover
  have hfinite :=
    card_distinctPairedDefectStarts_le
      (D := D) (I := I) (H := A ^ K) (X := M)
      (R := PellInput.expLogLogBound c A)
      (Real.exp_pos _).le hcount
  calc
    ((distinctKernelDefectBases N M B).card : ℝ) ≤
        ((distinctPairedDefectStarts
          D I (A ^ K) M).card : ℝ) :=
      hcardCover
    _ ≤
        (D.card : ℝ) ^ 2 *
          (I.card : ℝ) ^ 2 *
          PellInput.expLogLogBound c A :=
      hfinite
    _ =
        ((squarefreeSmoothUpTo B (A ^ K)).card : ℝ) ^ 2 *
          (B + 1 : ℝ) ^ 2 *
          PellInput.expLogLogBound c A := by
      simp [D, I]

/-! ## Unconditional smooth-kernel envelope -/

/--
The Chebyshev envelope for the number of squarefree `B`-smooth kernels.
It depends only on `B`, not on the height cutoff.
-/
noncomputable def smoothKernelChebyshevEnvelope
    (B : ℕ) : ℝ :=
  Real.exp
    ((7 * Real.log 2) *
      ((B : ℝ) / (Nat.log 2 B : ℝ)))

/--
The repository's elementary Chebyshev estimate, rather than PNT, makes the
squarefree smooth-kernel count subexponential at the required scale.
-/
theorem card_squarefreeSmoothUpTo_le_smoothKernelChebyshevEnvelope
    {B X : ℕ}
    (hB : 4 ≤ B) :
    ((squarefreeSmoothUpTo B X).card : ℝ) ≤
      smoothKernelChebyshevEnvelope B := by
  have hcardNat :=
    card_squarefreeSmoothUpTo_le_two_pow B X
  have hcardReal :
      ((squarefreeSmoothUpTo B X).card : ℝ) ≤
        (2 : ℝ) ^ (smallPrimesUpTo B).card := by
    exact_mod_cast hcardNat
  have hcountNat :=
    ChebyshevPrimeCount.count_le_seven_mul_div_log hB
  have hcountReal :
      ((smallPrimesUpTo B).card : ℝ) ≤
        (7 : ℝ) * (B : ℝ) /
          (Nat.log 2 B : ℝ) := by
    rw [← PrimeCountBridge.count_eq_card_smallPrimesUpTo]
    calc
      (PrimesUpTo.count B : ℝ) ≤
          (((7 * B) / Nat.log 2 B : ℕ) : ℝ) := by
        exact_mod_cast hcountNat
      _ ≤
          ((7 * B : ℕ) : ℝ) /
            (Nat.log 2 B : ℝ) :=
        Nat.cast_div_le
      _ =
          (7 : ℝ) * (B : ℝ) /
            (Nat.log 2 B : ℝ) := by
        norm_num
  have hlogTwoNonneg :
      0 ≤ Real.log (2 : ℝ) :=
    (Real.log_pos one_lt_two).le
  have hscaled :=
    mul_le_mul_of_nonneg_right hcountReal
      hlogTwoNonneg
  calc
    ((squarefreeSmoothUpTo B X).card : ℝ) ≤
        (2 : ℝ) ^ (smallPrimesUpTo B).card :=
      hcardReal
    _ =
        Real.exp
          (((smallPrimesUpTo B).card : ℝ) *
            Real.log 2) := by
      calc
        (2 : ℝ) ^ (smallPrimesUpTo B).card =
            (Real.exp (Real.log 2)) ^
              (smallPrimesUpTo B).card := by
          rw [Real.exp_log]
          norm_num
        _ =
            Real.exp
              (((smallPrimesUpTo B).card : ℝ) *
                Real.log 2) :=
          (Real.exp_nat_mul
            (Real.log 2)
            (smallPrimesUpTo B).card).symm
    _ ≤
        Real.exp
          ((7 * Real.log 2) *
            ((B : ℝ) /
              (Nat.log 2 B : ℝ))) := by
      apply Real.exp_le_exp.mpr
      calc
        ((smallPrimesUpTo B).card : ℝ) *
              Real.log 2 ≤
            ((7 : ℝ) * (B : ℝ) /
              (Nat.log 2 B : ℝ)) *
                Real.log 2 :=
          hscaled
        _ =
            (7 * Real.log 2) *
              ((B : ℝ) /
                (Nat.log 2 B : ℝ)) := by
          ring
    _ = smoothKernelChebyshevEnvelope B := rfl

/-! ## Uniform `N^o(1)` closure -/

/--
Three-parameter reciprocal-power formulation of a subpolynomial bound,
uniform in bounded-ratio endpoints and in the critical run length.
-/
def UniformSubpolynomialInBoundedRatioWindow
    (C : ℝ) (κ₀ : ℕ)
    (f : ℕ → ℕ → ℕ → ℝ) : Prop :=
  ∀ k : ℕ, 0 < k →
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ M L,
      2 * N ≤ M →
      M ≤ κ₀ * N →
      CriticalRunWindow.InRunLengthWindow C N L →
      |f N M L| ^ k ≤ (N : ℝ)

/-- The unconditional Chebyshev smooth-kernel envelope is `N^o(1)`. -/
theorem smoothKernelChebyshevEnvelope_uniformSubpolynomial
    {C : ℝ} (hC : 0 ≤ C) :
    UniformSubpolynomialOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun _ L ↦
        smoothKernelChebyshevEnvelope (L + 1)) := by
  have hcoefficient :
      0 ≤ (7 : ℝ) * Real.log 2 := by
    positivity
  have hcore :=
    ExpLogDivLogLog.criticalRunWindow_exp_height_div_natLog_uniformSubpolynomial
      hC hcoefficient
  convert hcore using 1
  funext N L
  unfold smoothKernelChebyshevEnvelope
  norm_num only [Nat.cast_add, Nat.cast_one]
  ring_nf

/-- The generalized-Pell exponential loss itself is uniformly `N^o(1)`. -/
theorem expLogLogBound_uniformSubpolynomial
    {C c : ℝ} (hc : 0 ≤ c) :
    UniformSubpolynomialOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun N _ ↦ PellInput.expLogLogBound c N) := by
  have hcore :=
    ExpLogDivLogLog.uniformSubpolynomialOn_exp_log_div_loglog_eventually
      (CriticalRunWindow.InRunLengthWindow C)
      (fun N _ ↦
        c * Real.log N /
          Real.log (Real.log N))
      c hc
      (by
        refine ⟨0, ?_⟩
        intro N _hN L _hwindow
        exact le_rfl)
  simpa only [PellInput.expLogLogBound] using hcore

/--
Common subpolynomial envelope for two smooth kernels, two offsets and one
Pell fibre.
-/
noncomputable def distinctKernelTwoDefectResidual
    (c : ℝ) (N L : ℕ) : ℝ :=
  4 *
    smoothKernelChebyshevEnvelope (L + 1) ^ 2 *
    (((L + 1 : ℕ) : ℝ)) ^ 2 *
    PellInput.expLogLogBound c N

theorem distinctKernelTwoDefectResidual_uniformSubpolynomial
    {C c : ℝ} (hC : 0 ≤ C) (hc : 0 ≤ c) :
    UniformSubpolynomialOn
      (CriticalRunWindow.InRunLengthWindow C)
      (distinctKernelTwoDefectResidual c) := by
  have hsmooth :=
    smoothKernelChebyshevEnvelope_uniformSubpolynomial hC
  have hsmoothSq :=
    ExpSqrtLog.uniformSubpolynomialOn_mul
      hsmooth hsmooth
  have hheight :=
    CriticalRationalMassEnvelopes.runLengthAddOne_uniformSubpolynomial
      hC
  have hheightSq :=
    ExpSqrtLog.uniformSubpolynomialOn_mul
      hheight hheight
  have hpell :=
    expLogLogBound_uniformSubpolynomial
      (C := C) hc
  have hproduct :=
    ExpSqrtLog.uniformSubpolynomialOn_mul
      (ExpSqrtLog.uniformSubpolynomialOn_mul
        hsmoothSq hheightSq)
      hpell
  unfold distinctKernelTwoDefectResidual
  simpa only [pow_two, mul_assoc] using
    ExpSqrtLog.uniformSubpolynomialOn_const_mul
      4 hproduct

/--
Uniform finite domination by the preceding residual.  The ambient Pell box
is `N²`; bounded ratio and the critical window eventually place `M+B`
inside that box.
-/
theorem generalizedPell_implies_card_distinctKernelDefectBases_le_residual
    {C : ℝ} (hC : 0 ≤ C) (κ₀ : ℕ)
    (hPell : PellInput.GeneralizedPellPolynomialBoxStatement) :
    ∃ c : ℝ, 0 ≤ c ∧
      ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ M L,
        2 * N ≤ M →
        M ≤ κ₀ * N →
        CriticalRunWindow.InRunLengthWindow C N L →
        ((distinctKernelDefectBases
          N M (L + 1)).card : ℝ) ≤
          distinctKernelTwoDefectResidual c N L := by
  have hpolynomial :=
    generalizedPell_implies_distinctKernelDefectBases_polynomial_bound
      hPell 2 (by omega)
  obtain ⟨c, hc, Npell, hpell⟩ := hpolynomial
  obtain ⟨Nwindow, hwindow⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  obtain ⟨Nadm, hadm⟩ :=
    CriticalWeightedDefect.admissible_eventually
      CriticalRunWindow.lowerConstant_pos
      CriticalRunWindow.lowerConstant_lt_upperConstant
  obtain ⟨Nfour, hfour⟩ :=
    DependencyEdgesCritical.runLengthAddOne_tends_to_infinity
      hC 4
  refine
    ⟨c, hc,
      max Npell
        (max Nwindow
          (max Nadm
            (max Nfour (max (κ₀ + 1) 2)))),
      ?_⟩
  intro N hN M L _hNM hMκ hrun
  have hNpell : Npell ≤ N :=
    (le_max_left _ _).trans hN
  have htail :
      max Nwindow
        (max Nadm
          (max Nfour (max (κ₀ + 1) 2))) ≤ N :=
    (le_max_right _ _).trans hN
  have hNwindow : Nwindow ≤ N :=
    (le_max_left _ _).trans htail
  have htail₂ :
      max Nadm
        (max Nfour (max (κ₀ + 1) 2)) ≤ N :=
    (le_max_right _ _).trans htail
  have hNadm : Nadm ≤ N :=
    (le_max_left _ _).trans htail₂
  have htail₃ :
      max Nfour (max (κ₀ + 1) 2) ≤ N :=
    (le_max_right _ _).trans htail₂
  have hNfour : Nfour ≤ N :=
    (le_max_left _ _).trans htail₃
  have htail₄ : max (κ₀ + 1) 2 ≤ N :=
    (le_max_right _ _).trans htail₃
  have hκN : κ₀ + 1 ≤ N :=
    (le_max_left _ _).trans htail₄
  have hNtwo : 2 ≤ N :=
    (le_max_right _ _).trans htail₄
  have hcritical :
      CriticalWindowParameters.InCriticalWindow
        CriticalRunWindow.lowerConstant
        CriticalRunWindow.upperConstant
        N (L + 1) :=
    (hwindow N hNwindow L hrun).1
  have hAdm :
      CriticalWeightedDefect.Admissible
        CriticalRunWindow.lowerConstant
        CriticalRunWindow.upperConstant
        N (L + 1) :=
    hadm N hNadm (L + 1) hcritical
  have hBLeN : L + 1 ≤ N := by
    have htwo :
        2 * (L + 1) ≤ N :=
      CriticalWindowParameters.two_mul_H_le_N_of_criticalWindow
        hAdm.1 hAdm.2.2.2.1
    omega
  have hambient :
      M + (L + 1) ≤ N ^ 2 := by
    calc
      M + (L + 1) ≤ κ₀ * N + N :=
        Nat.add_le_add hMκ hBLeN
      _ = (κ₀ + 1) * N := by
        simp only [Nat.add_mul, one_mul]
      _ ≤ N * N :=
        Nat.mul_le_mul_right N hκN
      _ = N ^ 2 := by ring
  have hfinite :=
    hpell N hNpell N M (L + 1)
      hNtwo hambient
  have hBfour : 4 ≤ L + 1 :=
    hfour N hNfour L hrun
  have hkernel :=
    card_squarefreeSmoothUpTo_le_smoothKernelChebyshevEnvelope
      (X := N ^ 2) hBfour
  let D : ℝ :=
    ((squarefreeSmoothUpTo (L + 1) (N ^ 2)).card : ℝ)
  let E : ℝ :=
    smoothKernelChebyshevEnvelope (L + 1)
  have hDnonneg : 0 ≤ D := by
    dsimp [D]
    positivity
  have hEnonneg : 0 ≤ E := by
    dsimp [E, smoothKernelChebyshevEnvelope]
    positivity
  have hDE : D ≤ E := by
    simpa only [D, E] using hkernel
  have hDsq : D ^ 2 ≤ E ^ 2 := by
    nlinarith
      [mul_nonneg (sub_nonneg.mpr hDE)
        (add_nonneg hDnonneg hEnonneg)]
  have hoffset :
      ((((L + 1) + 1 : ℕ) : ℝ)) ≤
        2 * (((L + 1 : ℕ) : ℝ)) := by
    exact_mod_cast
      (show (L + 1) + 1 ≤ 2 * (L + 1) by omega)
  have hoffsetSq :
      ((((L + 1) + 1 : ℕ) : ℝ)) ^ 2 ≤
        (2 * (((L + 1 : ℕ) : ℝ))) ^ 2 := by
    nlinarith
  have hpellNonneg :
      0 ≤ PellInput.expLogLogBound c N := by
    unfold PellInput.expLogLogBound
    positivity
  calc
    ((distinctKernelDefectBases
        N M (L + 1)).card : ℝ) ≤
        D ^ 2 *
          ((((L + 1) + 1 : ℕ) : ℝ)) ^ 2 *
          PellInput.expLogLogBound c N := by
      simpa only [D, Nat.cast_add, Nat.cast_one] using
        hfinite
    _ ≤
        E ^ 2 *
          ((((L + 1) + 1 : ℕ) : ℝ)) ^ 2 *
          PellInput.expLogLogBound c N := by
      apply mul_le_mul_of_nonneg_right
      · apply mul_le_mul_of_nonneg_right hDsq
        positivity
      · exact hpellNonneg
    _ ≤
        E ^ 2 *
          (2 * (((L + 1 : ℕ) : ℝ))) ^ 2 *
          PellInput.expLogLogBound c N := by
      apply mul_le_mul_of_nonneg_right
      · exact
          mul_le_mul_of_nonneg_left
            hoffsetSq (sq_nonneg E)
      · exact hpellNonneg
    _ =
        distinctKernelTwoDefectResidual c N L := by
      unfold distinctKernelTwoDefectResidual
      dsimp [E]
      ring

/--
Distinct-kernel two-defect bases are uniformly `N^o(1)` on bounded-ratio
critical windows.  Generalized Pell is the only hypothesis.
-/
theorem distinctKernelDefectBases_uniformSubpolynomial
    {C : ℝ} (hC : 0 ≤ C) (κ₀ : ℕ)
    (hPell : PellInput.GeneralizedPellPolynomialBoxStatement) :
    UniformSubpolynomialInBoundedRatioWindow C κ₀
      (fun N M L ↦
        ((distinctKernelDefectBases
          N M (L + 1)).card : ℝ)) := by
  obtain ⟨c, hc, Nbound, hbound⟩ :=
    generalizedPell_implies_card_distinctKernelDefectBases_le_residual
      hC κ₀ hPell
  have hresidual :=
    distinctKernelTwoDefectResidual_uniformSubpolynomial
      hC hc
  intro k hk
  obtain ⟨Nresidual, hNresidual⟩ :=
    hresidual k hk
  refine ⟨max Nbound Nresidual, ?_⟩
  intro N hN M L hNM hMκ hrun
  have hcard :=
    hbound N ((le_max_left _ _).trans hN)
      M L hNM hMκ hrun
  have hcardNonneg :
      0 ≤
        ((distinctKernelDefectBases
          N M (L + 1)).card : ℝ) := by
    positivity
  have hresidualNonneg :
      0 ≤ distinctKernelTwoDefectResidual c N L := by
    unfold distinctKernelTwoDefectResidual
    unfold smoothKernelChebyshevEnvelope
      PellInput.expLogLogBound
    positivity
  have habs :
      |((distinctKernelDefectBases
          N M (L + 1)).card : ℝ)| ≤
        |distinctKernelTwoDefectResidual c N L| := by
    simpa only [abs_of_nonneg hcardNonneg,
      abs_of_nonneg hresidualNonneg] using hcard
  exact
    (pow_le_pow_left₀ (abs_nonneg _) habs k).trans
      (hNresidual N
        ((le_max_right _ _).trans hN)
        L hrun)

end

end BoundedRatioDistinctKernelTwoDefects
end PaperC
