import PaperC.Arithmetic.TerminalKernelCount
import PaperC.Arithmetic.TerminalMatching
import PaperC.Asymptotics.CriticalRationalMassEnvelopes
import PaperC.Asymptotics.CriticalChannelPowers
import PaperC.Asymptotics.ExpSqrtLog
import PaperC.Asymptotics.RationalPowerLittleO
import PaperC.Combinatorics.BoundedRatioGeometry
import PaperC.Combinatorics.BoundedRatioCanonicalTerminalPopulation
import PaperC.Combinatorics.TerminalClosureCounting

set_option maxHeartbeats 1800000

/-!
# Bounded-ratio terminal closure

This module isolates the endpoint-uniform arithmetic and asymptotic steps in
Lemmas 17.29--17.30.  It deliberately does not define the terminal
population: that definition belongs to the ordered sector partition.

The finite content proved here is:

* complete-boundary labels attached to starts in `[N,M)` are at most
  `(κ₀+1)N`;
* their cross determinant is at most
  `2(κ₀+1)N(L+1)`;
* determinant divisibility and nonvanishing turn this into a product bound
  for two component kernels;
* above the integral square-root threshold there is at most one exceptional
  kernel;
* the set of possible nonexceptional kernel labels has an explicit
  `N^(3/4+o(1))` envelope in the critical run-length window.

The last section gives population-independent transfers from a first-start
count and a fixed-first-start partner bound to the unweighted and weighted
terminal estimates.  Consequently, connecting a concrete canonical
terminal population only requires the incidence/fibre maps; no further
analytic estimate is hidden here.
-/

namespace PaperC
namespace BoundedRatioTerminalClosure

open scoped BigOperators
open Affine
open BoundedRatioGeometry
open BoundedRatioCanonicalTerminalPopulation

noncomputable section

/-! ## The bounded-ratio determinant budget -/

/-- The determinant budget from replacement R2κ. -/
def determinantBudget (κ₀ N L : ℕ) : ℕ :=
  2 * (κ₀ + 1) * N * (L + 1)

/-- An integral threshold strictly above the square root of the budget. -/
def kernelThreshold (κ₀ N L : ℕ) : ℕ :=
  Nat.sqrt (determinantBudget κ₀ N L) + 1

/-- Common upper cutoff for every complete-boundary label. -/
def terminalLabelCutoff (κ₀ N : ℕ) : ℕ :=
  (κ₀ + 1) * N

/--
Every complete-boundary label based at a start in `[N,M)` is below the
endpoint-independent cutoff `(κ₀+1)N`.
-/
theorem startCompleteVertexLabel_le_terminalLabelCutoff
    {κ₀ N M L x : ℕ}
    (hN : 2 ≤ N)
    (hMκ : M ≤ κ₀ * N)
    (hL : L ≤ N)
    (hx : x ∈ boundedRatioBlock N M)
    (v : Fin (L + 1)) :
    startCompleteVertexLabel x L v ≤
      terminalLabelCutoff κ₀ N := by
  have hxN : 2 ≤ x :=
    hN.trans (mem_boundedRatioBlock.mp hx).1
  have hxM : x < M :=
    (mem_boundedRatioBlock.mp hx).2
  unfold terminalLabelCutoff
  have hMN : M + L ≤ κ₀ * N + N :=
    Nat.add_le_add hMκ hL
  have hcutoff : M + L ≤ (κ₀ + 1) * N := by
    calc
      M + L ≤ κ₀ * N + N := hMN
      _ = (κ₀ + 1) * N := by ring
  simp only [startCompleteVertexLabel]
  by_cases hv : v.1 = 0
  · simp [hv]
    omega
  · simp [hv]
    have hvlt := v.2
    omega

/--
Bounded-ratio form of the metric determinant estimate in Lemma 17.29.
-/
theorem abs_crossDeterminant_startCompleteVertexLabel_le
    {κ₀ N M L x y : ℕ}
    (hN : 2 ≤ N)
    (hMκ : M ≤ κ₀ * N)
    (hL : L ≤ N)
    (hx : x ∈ boundedRatioBlock N M)
    (hy : y ∈ boundedRatioBlock N M)
    (is js it jt : Fin (L + 1)) :
    |TerminalMatching.crossDeterminant
        (startCompleteVertexLabel x L is)
        (startCompleteVertexLabel y L js)
        (startCompleteVertexLabel x L it)
        (startCompleteVertexLabel y L jt)| ≤
      ((determinantBudget κ₀ N L : ℕ) : ℤ) := by
  have hxOne : 1 ≤ x :=
    (hN.trans (mem_boundedRatioBlock.mp hx).1).trans' (by omega)
  have hyOne : 1 ≤ y :=
    (hN.trans (mem_boundedRatioBlock.mp hy).1).trans' (by omega)
  have hbase :=
    TerminalMatching.abs_crossDeterminant_le
      (startCompleteVertexLabel_le_terminalLabelCutoff
        hN hMκ hL hx is)
      (startCompleteVertexLabel_le_terminalLabelCutoff
        hN hMκ hL hy js)
      (show
        Nat.dist
            (startCompleteVertexLabel x L it)
            (startCompleteVertexLabel x L is) ≤
          L + 1 by
        have hlt :=
          Affine.RelationalPrimeAssignment.startCompleteVertexLabel_dist_lt
            hxOne it is
        omega)
      (show
        Nat.dist
            (startCompleteVertexLabel y L jt)
            (startCompleteVertexLabel y L js) ≤
          L + 1 by
        have hlt :=
          Affine.RelationalPrimeAssignment.startCompleteVertexLabel_dist_lt
            hyOne jt js
        omega)
  simpa [terminalLabelCutoff, determinantBudget, Nat.mul_assoc] using hbase

/-! ## Divisibility, nonvanishing, and the exceptional kernel -/

/--
If a positive natural number divides a nonzero integer, it is at most the
absolute value of that integer.
-/
theorem natCast_le_abs_of_dvd
    {d Δ : ℤ}
    (hd : 0 < d)
    (hΔ : Δ ≠ 0)
    (hdiv : d ∣ Δ) :
    d ≤ |Δ| := by
  obtain ⟨q, rfl⟩ := hdiv
  have hq : q ≠ 0 := by
    intro hq
    simp [hq] at hΔ
  have hone : (1 : ℤ) ≤ |q| :=
    Int.one_le_abs hq
  calc
    d = |d| * 1 := by
      rw [abs_of_pos hd, mul_one]
    _ ≤ |d| * |q| :=
      mul_le_mul_of_nonneg_left hone (abs_nonneg d)
    _ = |d * q| := by
      rw [abs_mul]

/--
The divisibility output of the two-component kernel package, together with
canonical nonalignment and the metric estimate, gives the numerical product
bound used in Lemma 17.30.
-/
theorem kernel_product_le_of_dvd_crossDeterminant
    {Rs Rt K Xs Ys Xt Yt : ℕ}
    (hRs : 1 < Rs)
    (hRt : 1 < Rt)
    (hne :
      TerminalMatching.crossDeterminant Xs Ys Xt Yt ≠ 0)
    (hdvd :
      (((Rs * Rt : ℕ) : ℤ) ∣
        TerminalMatching.crossDeterminant Xs Ys Xt Yt))
    (habs :
      |TerminalMatching.crossDeterminant Xs Ys Xt Yt| ≤
        (K : ℤ)) :
    Rs * Rt ≤ K := by
  have hprodPos : (0 : ℤ) < ((Rs * Rt : ℕ) : ℤ) := by
    exact_mod_cast Nat.mul_pos (by omega) (by omega)
  have hlower :=
    natCast_le_abs_of_dvd hprodPos hne hdvd
  exact_mod_cast hlower.trans habs

/-- The determinant budget lies strictly below the square of the threshold. -/
theorem determinantBudget_lt_kernelThreshold_sq
    (κ₀ N L : ℕ) :
    determinantBudget κ₀ N L <
      kernelThreshold κ₀ N L ^ 2 := by
  exact Nat.lt_succ_sqrt' (determinantBudget κ₀ N L)

/--
At most one component kernel can exceed the integral square-root threshold.
This statement is independent of how component indices are represented.
-/
theorem card_filter_kernel_above_threshold_le_one
    {ι : Type*}
    (indices : Finset ι)
    (factor : ι → ℕ)
    (κ₀ N L : ℕ)
    (hpair :
      ∀ ⦃s t : ι⦄, s ∈ indices → t ∈ indices → s ≠ t →
        factor s * factor t ≤ determinantBudget κ₀ N L) :
    (indices.filter fun t ↦
      kernelThreshold κ₀ N L < factor t).card ≤ 1 := by
  apply TerminalClosureCounting.card_filter_large_le_one
  intro s t hs ht hst
  exact
    (hpair hs ht hst).trans
      (determinantBudget_lt_kernelThreshold_sq κ₀ N L).le

/-! ## Counting the possible nonexceptional kernel labels -/

/--
The endpoint-independent set of possible nonexceptional kernel labels.
The cutoff contains every complete-boundary label for starts in `[N,M)`.
-/
def possibleKernelValues (κ₀ N L : ℕ) : Finset ℕ :=
  TerminalKernelCount.boundedLargeKernelValues
    (L + 1) (kernelThreshold κ₀ N L)
    (terminalLabelCutoff κ₀ N)

/-- Direct finite specialization of the large-kernel counting lemma. -/
theorem card_possibleKernelValues_cast_le_exp
    (κ₀ N L : ℕ) :
    ((possibleKernelValues κ₀ N L).card : ℝ) ≤
      2 * Real.sqrt (terminalLabelCutoff κ₀ N) *
        Real.sqrt (kernelThreshold κ₀ N L) *
        Real.exp (2 * Real.sqrt ((L + 1 : ℕ) : ℝ)) := by
  simpa only [possibleKernelValues] using
    TerminalKernelCount.card_boundedLargeKernelValues_cast_le_exp
      (L + 1) (kernelThreshold κ₀ N L)
      (terminalLabelCutoff κ₀ N)

/-! ## Incidence with first starts -/

/-- A number occurs as a complete-boundary label at the start `x`. -/
def IsCompleteBoundaryLabel (L x n : ℕ) : Prop :=
  ∃ i : Fin (L + 1),
    startCompleteVertexLabel x L i = n

/-- Starts in `[N,M)` which expose the complete-boundary label `n`. -/
def completeBoundaryLabelStarts
    (N M L n : ℕ) : Finset ℕ := by
  classical
  exact
    (boundedRatioBlock N M).filter fun x ↦
      IsCompleteBoundaryLabel L x n

/-- At a fixed offset, a positive start is determined by its label. -/
theorem eq_of_startCompleteVertexLabel_eq_at_fixed_offset
    {L x y : ℕ} (i : Fin (L + 1))
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hlabel :
      startCompleteVertexLabel x L i =
        startCompleteVertexLabel y L i) :
    x = y := by
  simp only [startCompleteVertexLabel] at hlabel
  by_cases hi : i.1 = 0
  · simp [hi] at hlabel
    omega
  · simp [hi] at hlabel
    omega

/--
One numerical label belongs to at most `L+1` complete boundaries.  This is
the right-fibre estimate in the incidence count of Lemma 17.30.
-/
theorem card_completeBoundaryLabelStarts_le
    {N M L n : ℕ} (hN : 1 ≤ N) :
    (completeBoundaryLabelStarts N M L n).card ≤ L + 1 := by
  classical
  let fibre : Fin (L + 1) → Finset ℕ :=
    fun i ↦
      (boundedRatioBlock N M).filter fun x ↦
        startCompleteVertexLabel x L i = n
  have hfibre :
      ∀ i : Fin (L + 1), (fibre i).card ≤ 1 := by
    intro i
    rw [Finset.card_le_one]
    intro x hx y hy
    have hxData := Finset.mem_filter.mp hx
    have hyData := Finset.mem_filter.mp hy
    have hxOne : 1 ≤ x := by
      have hxLower := (mem_boundedRatioBlock.mp hxData.1).1
      exact hN.trans hxLower
    have hyOne : 1 ≤ y := by
      have hyLower := (mem_boundedRatioBlock.mp hyData.1).1
      exact hN.trans hyLower
    exact
      eq_of_startCompleteVertexLabel_eq_at_fixed_offset
        i hxOne hyOne (hxData.2.trans hyData.2.symm)
  have hdecomp :
      completeBoundaryLabelStarts N M L n =
        (Finset.univ : Finset (Fin (L + 1))).biUnion fibre := by
    ext x
    simp only [completeBoundaryLabelStarts, Finset.mem_filter,
      Finset.mem_biUnion, Finset.mem_univ, true_and, fibre,
      IsCompleteBoundaryLabel]
    constructor
    · rintro ⟨hx, i, hi⟩
      exact ⟨i, hx, hi⟩
    · rintro ⟨i, hx, hi⟩
      exact ⟨hx, i, hi⟩
  rw [hdecomp]
  calc
    ((Finset.univ : Finset (Fin (L + 1))).biUnion fibre).card ≤
        ∑ i : Fin (L + 1), (fibre i).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin (L + 1), 1 :=
      Finset.sum_le_sum fun i _ ↦ hfibre i
    _ = L + 1 := by simp

/-- Bounded-kernel labels incident with one first start. -/
def incidentPossibleKernelValues
    (κ₀ N L x : ℕ) : Finset ℕ := by
  classical
  exact
    (possibleKernelValues κ₀ N L).filter fun n ↦
      IsCompleteBoundaryLabel L x n

/--
Abstract incidence closure for first starts.  The only population-specific
input is the lower bound saying that every represented start supplies at
least `m` distinct bounded-kernel labels.
-/
theorem card_firstStarts_le_twice_possibleKernelValues
    {κ₀ N M L m : ℕ}
    (firstStarts : Finset ℕ)
    (hN : 1 ≤ N)
    (hfirstBlock : firstStarts ⊆ boundedRatioBlock N M)
    (hmPos : 0 < L + 1)
    (hhalf : L + 1 ≤ 2 * m)
    (hlower :
      ∀ x ∈ firstStarts,
        m ≤ (incidentPossibleKernelValues κ₀ N L x).card) :
    firstStarts.card ≤
      2 * (possibleKernelValues κ₀ N L).card := by
  classical
  apply
    TerminalClosureCounting.card_left_le_twice_card_right
      firstStarts (possibleKernelValues κ₀ N L)
      (fun x n ↦ IsCompleteBoundaryLabel L x n)
      (L + 1) m hmPos hhalf (by
        simpa only [incidentPossibleKernelValues] using hlower)
  intro n hn
  calc
    (firstStarts.filter fun x ↦
        IsCompleteBoundaryLabel L x n).card ≤
        (completeBoundaryLabelStarts N M L n).card := by
      apply Finset.card_le_card
      intro x hx
      have hxData := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr
        ⟨hfirstBlock hxData.1, hxData.2⟩
    _ ≤ L + 1 :=
      card_completeBoundaryLabelStarts_le hN

/-- The integral threshold has square at most four times its budget. -/
theorem kernelThreshold_sq_le_four_mul_determinantBudget
    {κ₀ N L : ℕ} (hN : 0 < N) :
    kernelThreshold κ₀ N L ^ 2 ≤
      4 * determinantBudget κ₀ N L := by
  have hbudget : 0 < determinantBudget κ₀ N L := by
    unfold determinantBudget
    positivity
  have hsqrtPos :
      1 ≤ Nat.sqrt (determinantBudget κ₀ N L) :=
    Nat.sqrt_pos.2 hbudget
  have hsqrtSq :
      Nat.sqrt (determinantBudget κ₀ N L) ^ 2 ≤
        determinantBudget κ₀ N L :=
    Nat.sqrt_le' _
  unfold kernelThreshold
  nlinarith

/--
The subpolynomial factor left after extracting the three-quarter power of
`N` from the kernel-value count.
-/
def terminalKernelCountResidual
    (κ₀ _N L : ℕ) : ℝ :=
  (128 * (κ₀ + 1 : ℝ) ^ 3) *
    (((L + 1 : ℕ) : ℝ) *
      Real.exp (8 * Real.sqrt ((L + 1 : ℕ) : ℝ)))

/-- Fourth-power finite estimate underlying the `N^(3/4+o(1))` count. -/
theorem card_possibleKernelValues_fourth_power_le
    {κ₀ N L : ℕ} (hN : 0 < N) :
    |((possibleKernelValues κ₀ N L).card : ℝ)| ^ 4 ≤
      (N : ℝ) ^ 3 *
        |terminalKernelCountResidual κ₀ N L| := by
  let X := terminalLabelCutoff κ₀ N
  let T := kernelThreshold κ₀ N L
  let D := determinantBudget κ₀ N L
  let E : ℝ :=
    Real.exp (2 * Real.sqrt ((L + 1 : ℕ) : ℝ))
  have hfinite :
      ((possibleKernelValues κ₀ N L).card : ℝ) ≤
        2 * Real.sqrt X * Real.sqrt T * E := by
    simpa only [X, T, E] using
      card_possibleKernelValues_cast_le_exp κ₀ N L
  have hcountNonneg :
      0 ≤ ((possibleKernelValues κ₀ N L).card : ℝ) := by
    positivity
  have hrhsNonneg :
      0 ≤ 2 * Real.sqrt X * Real.sqrt T * E := by
    dsimp only [E]
    positivity
  have hpow :
      ((possibleKernelValues κ₀ N L).card : ℝ) ^ 4 ≤
        (2 * Real.sqrt X * Real.sqrt T * E) ^ 4 :=
    pow_le_pow_left₀ hcountNonneg hfinite 4
  have hsqrtX :
      Real.sqrt X ^ 4 = (X : ℝ) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul,
      Real.sq_sqrt (by positivity)]
  have hsqrtT :
      Real.sqrt T ^ 4 = (T : ℝ) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul,
      Real.sq_sqrt (by positivity)]
  have hTsqNat :
      T ^ 2 ≤ 4 * D := by
    simpa only [T, D] using
      (kernelThreshold_sq_le_four_mul_determinantBudget
        (κ₀ := κ₀) (L := L) hN)
  have hTsq :
      (T : ℝ) ^ 2 ≤ 4 * (D : ℝ) := by
    exact_mod_cast hTsqNat
  have hresNonneg :
      0 ≤ terminalKernelCountResidual κ₀ N L := by
    unfold terminalKernelCountResidual
    positivity
  have hEpow :
      Real.exp (2 * Real.sqrt ((L + 1 : ℕ) : ℝ)) ^ 4 =
        Real.exp (8 * Real.sqrt ((L + 1 : ℕ) : ℝ)) := by
    calc
      Real.exp (2 * Real.sqrt ((L + 1 : ℕ) : ℝ)) ^ 4 =
          Real.exp
            ((4 : ℝ) *
              (2 * Real.sqrt ((L + 1 : ℕ) : ℝ))) :=
        (Real.exp_nat_mul
          (2 * Real.sqrt ((L + 1 : ℕ) : ℝ)) 4).symm
      _ = Real.exp (8 * Real.sqrt ((L + 1 : ℕ) : ℝ)) := by
        congr 1
        ring
  rw [abs_of_nonneg hcountNonneg, abs_of_nonneg hresNonneg]
  calc
    ((possibleKernelValues κ₀ N L).card : ℝ) ^ 4 ≤
        (2 * Real.sqrt X * Real.sqrt T * E) ^ 4 :=
      hpow
    _ = 16 * (X : ℝ) ^ 2 * (T : ℝ) ^ 2 * E ^ 4 := by
      rw [mul_pow, mul_pow, mul_pow, hsqrtX, hsqrtT]
      norm_num
    _ ≤ 16 * (X : ℝ) ^ 2 * (4 * (D : ℝ)) * E ^ 4 := by
      gcongr
    _ = (N : ℝ) ^ 3 *
          terminalKernelCountResidual κ₀ N L := by
      dsimp only [X, D, E]
      unfold terminalLabelCutoff determinantBudget
        terminalKernelCountResidual
      rw [hEpow]
      norm_num
      ring

/-!
The repository's generic rational-power helper currently exposes the
cube specialization.  The identical fourth-power argument is recorded
locally because the exponent in Lemma 17.30 is `3/4`.
-/
theorem uniformRationalPower_of_fourth_bound
    {p : ℕ}
    {admissible : ℕ → ℕ → Prop}
    {f s : ℕ → ℕ → ℝ}
    (hs : UniformSubpolynomialOn admissible s)
    (hbound :
      ∃ N₁ : ℕ, ∀ N ≥ N₁, ∀ L, admissible N L →
        |f N L| ^ 4 ≤ (N : ℝ) ^ p * |s N L|) :
    UniformRationalPowerSubpolynomialOn p 4 admissible f := by
  intro k hk
  obtain ⟨Ns, hNs⟩ := hs k hk
  obtain ⟨Nb, hNb⟩ := hbound
  refine ⟨max Ns Nb, ?_⟩
  intro N hN L hNL
  have hNsN : Ns ≤ N :=
    (le_max_left _ _).trans hN
  have hNbN : Nb ≤ N :=
    (le_max_right _ _).trans hN
  calc
    |f N L| ^ (4 * k) =
        (|f N L| ^ 4) ^ k := by
      rw [pow_mul]
    _ ≤ ((N : ℝ) ^ p * |s N L|) ^ k :=
      pow_le_pow_left₀ (by positivity)
        (hNb N hNbN L hNL) k
    _ = (N : ℝ) ^ (p * k) * |s N L| ^ k := by
      rw [mul_pow, pow_mul]
    _ ≤ (N : ℝ) ^ (p * k) * (N : ℝ) :=
      mul_le_mul_of_nonneg_left
        (hNs N hNsN L hNL) (by positivity)
    _ = (N : ℝ) ^ (p * k + 1) := by
      rw [pow_succ]

/-- The exponential term in the kernel-count residual is subpolynomial. -/
theorem exp_eight_sqrt_runLength_uniformSubpolynomial
    {C : ℝ} (hC : 0 ≤ C) :
    UniformSubpolynomialOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun _ L =>
        Real.exp (8 * Real.sqrt ((L + 1 : ℕ) : ℝ))) := by
  have hupperNonneg :
      0 ≤ CriticalRunWindow.upperConstant :=
    (CriticalRunWindow.lowerConstant_pos.trans
      CriticalRunWindow.lowerConstant_lt_upperConstant).le
  obtain ⟨Nwindow, hwindow⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  let admissibleLarge : ℕ → ℕ → Prop :=
    fun N L ↦
      CriticalRunWindow.InRunLengthWindow C N L ∧ Nwindow ≤ N
  have hlarge :
      UniformSubpolynomialOn admissibleLarge
        (fun _ L =>
          Real.exp (8 * Real.sqrt ((L + 1 : ℕ) : ℝ))) := by
    apply
      ExpSqrtLog.uniformSubpolynomialOn_exp_sqrt_of_le_log
        admissibleLarge (fun _ L => L + 1)
        8 CriticalRunWindow.upperConstant (by norm_num)
        hupperNonneg
    intro N L hNL
    exact (hwindow N hNL.2 L hNL.1).1.2.2.2
  intro k hk
  obtain ⟨Nlarge, hNlarge⟩ := hlarge k hk
  refine ⟨max Nwindow Nlarge, ?_⟩
  intro N hN L hrun
  exact
    hNlarge N ((le_max_right _ _).trans hN) L
      ⟨hrun, (le_max_left _ _).trans hN⟩

/-- The residual in the fourth-power count is uniformly subpolynomial. -/
theorem terminalKernelCountResidual_uniformSubpolynomial
    {C : ℝ} (hC : 0 ≤ C) (κ₀ : ℕ) :
    UniformSubpolynomialOn
      (CriticalRunWindow.InRunLengthWindow C)
      (terminalKernelCountResidual κ₀) := by
  have hlinear :=
    CriticalRationalMassEnvelopes.runLengthAddOne_uniformSubpolynomial hC
  have hexponential :=
    exp_eight_sqrt_runLength_uniformSubpolynomial hC
  have hproduct :
      UniformSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C)
        (fun N L =>
          ((L + 1 : ℕ) : ℝ) *
            Real.exp (8 * Real.sqrt ((L + 1 : ℕ) : ℝ))) :=
    ExpSqrtLog.uniformSubpolynomialOn_mul hlinear hexponential
  simpa only [terminalKernelCountResidual] using
    ExpSqrtLog.uniformSubpolynomialOn_const_mul
      (128 * (κ₀ + 1 : ℝ) ^ 3) hproduct

/--
The number of possible nonexceptional kernel labels is
`N^(3/4+o_{C,κ₀}(1))`.
-/
theorem card_possibleKernelValues_uniformThreeQuarter
    {C : ℝ} (hC : 0 ≤ C) (κ₀ : ℕ) :
    UniformRationalPowerSubpolynomialOn 3 4
      (CriticalRunWindow.InRunLengthWindow C)
      (fun N L => ((possibleKernelValues κ₀ N L).card : ℝ)) := by
  apply uniformRationalPower_of_fourth_bound
    (terminalKernelCountResidual_uniformSubpolynomial hC κ₀)
  refine ⟨1, ?_⟩
  intro N hN L _hrun
  exact card_possibleKernelValues_fourth_power_le (by omega)

/-! ## From a terminal-cardinality envelope to the public sector mass -/

/--
Once the literal terminal population has a common endpoint-independent
`N^(3/4+o(1))` cardinality envelope, its public seventh-sector mass is
uniformly `o(N²)`.

This theorem packages the last weighted transfer in Lemma 17.30.  The
remaining population-specific work is precisely the hypothesis `hcard`;
the finite weight bound, the factor `2^(L+1)=O_C(N)`, and the conversion to
the public sector are all discharged here.
-/
theorem rankTerminalSector_uniformLittleO_of_card_envelope
    {C : ℝ} (κ₀ A : ℕ) (K : ℝ)
    (cardEnvelope : ℕ → ℕ → ℝ)
    (henvelope :
      UniformRationalPowerSubpolynomialOn 3 4
        (CriticalRunWindow.InRunLengthWindow C)
        cardEnvelope)
    (hcard :
      ∀ N M L (hNtwo : 2 ≤ N),
        2 * N ≤ M →
        M ≤ κ₀ * N →
        CriticalRunWindow.InRunLengthWindow C N L →
        ((BoundedRatioCanonicalTerminalPopulation.boundedRankTerminalPairs
            N M A L hNtwo K).card : ℝ) ≤
          |cardEnvelope N L|) :
    PropositionSixteenOne.UniformLittleOInBoundedRatioWindow C κ₀
      (PropositionSixteenOne.sectorResidualMass A
        (BoundedRatioCanonicalTerminalPopulation.boundedRankTerminalPredicate
          A K)
        .terminal) := by
  have hsmallPow :=
    UniformRationalPower.littleO_natPower_of_lt
      (p := 3) (q := 4) (r := 1) (by omega) henvelope
  have hsmall :
      UniformLittleOOn
        (CriticalRunWindow.InRunLengthWindow C)
        cardEnvelope
        (fun N _ ↦ (N : ℝ)) := by
    simpa only [pow_one] using hsmallPow
  intro ε hε
  let balance := CriticalRunWindow.balanceConstant C
  let denominator : ℝ := 8 * balance + 1
  have hbalance : 0 ≤ balance := by
    dsimp only [balance]
    exact CriticalRunWindow.balanceConstant_nonneg C
  have hdenominator : 0 < denominator := by
    dsimp only [denominator]
    positivity
  have hsmallEpsilon : 0 < ε / denominator :=
    div_pos hε hdenominator
  obtain ⟨Ncard, hNcard⟩ :=
    hsmall (ε / denominator) hsmallEpsilon
  refine ⟨max 2 Ncard, ?_⟩
  intro N hN M L hNM hMκ hrun
  have hNtwo : 2 ≤ N :=
    (le_max_left _ _).trans hN
  have hNcardN : Ncard ≤ N :=
    (le_max_right _ _).trans hN
  have hNpos : 0 < N := by omega
  have hcardFinite :=
    hcard N M L hNtwo hNM hMκ hrun
  have hcardSmall :
      |cardEnvelope N L| ≤
        (ε / denominator) * (N : ℝ) := by
    simpa only [abs_of_nonneg
      (show 0 ≤ (N : ℝ) by positivity)] using
      hNcard N hNcardN L hrun
  have hpower :=
    CriticalChannelPowers.two_pow_runLength_le_balance_mul
      hNpos hrun
  have hweight :
      ((4 * 2 ^ (L + 1) : ℕ) : ℝ) ≤
        (8 * balance) * (N : ℝ) := by
    calc
      ((4 * 2 ^ (L + 1) : ℕ) : ℝ) =
          8 * (2 : ℝ) ^ L := by
        push_cast
        rw [pow_succ]
        ring
      _ ≤ 8 * (balance * (N : ℝ)) :=
        mul_le_mul_of_nonneg_left hpower (by norm_num)
      _ = (8 * balance) * (N : ℝ) := by ring
  have hmassNat :=
    boundedRankTerminalResidualMass_le_card_mul_weight
        (N := N) (M := M) (A := A) (L := L) hNtwo K
  have hmassCast :
      ((boundedRankTerminalResidualMass
          N M A L hNtwo K : ℕ) : ℝ) ≤
        ((boundedRankTerminalPairs
            N M A L hNtwo K).card : ℝ) *
          ((4 * 2 ^ (L + 1) : ℕ) : ℝ) := by
    exact_mod_cast hmassNat
  have hmassNonneg :
      0 ≤
        ((boundedRankTerminalResidualMass
          N M A L hNtwo K : ℕ) : ℝ) := by
    positivity
  have htarget :
      ((boundedRankTerminalResidualMass
          N M A L hNtwo K : ℕ) : ℝ) ≤
        ε * (N : ℝ) ^ 2 := by
    calc
      ((boundedRankTerminalResidualMass
          N M A L hNtwo K : ℕ) : ℝ) ≤
          ((boundedRankTerminalPairs
            N M A L hNtwo K).card : ℝ) *
            ((4 * 2 ^ (L + 1) : ℕ) : ℝ) :=
        hmassCast
      _ ≤ |cardEnvelope N L| *
            ((4 * 2 ^ (L + 1) : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right hcardFinite (by positivity)
      _ ≤ ((ε / denominator) * (N : ℝ)) *
            ((8 * balance) * (N : ℝ)) :=
        mul_le_mul hcardSmall hweight
          (by positivity) (by positivity)
      _ ≤ ε * (N : ℝ) ^ 2 := by
        have hratio :
            (ε / denominator) * (8 * balance) ≤ ε := by
          rw [div_mul_eq_mul_div]
          apply (div_le_iff₀ hdenominator).2
          dsimp only [denominator]
          nlinarith [mul_pos hε hdenominator]
        calc
          ((ε / denominator) * (N : ℝ)) *
                ((8 * balance) * (N : ℝ)) =
              ((ε / denominator) * (8 * balance)) *
                (N : ℝ) ^ 2 := by ring
          _ ≤ ε * (N : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_right hratio (by positivity)
  rw [PropositionSixteenOne.sectorResidualMass, dif_pos hNtwo]
  rw [←
    boundedRankTerminalResidualMass_eq_sectorResidualMassNat
        hNtwo K]
  rw [abs_of_nonneg hmassNonneg,
    abs_of_nonneg (by positivity : 0 ≤ (N : ℝ) ^ 2)]
  exact htarget

end

end BoundedRatioTerminalClosure
end PaperC
