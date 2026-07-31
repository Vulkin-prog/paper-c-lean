import PaperC.Asymptotics.BoundedRatioSteinChen
import PaperC.Asymptotics.TerminalBadStartsCritical

set_option maxHeartbeats 1800000

/-!
# Terminal bad starts on bounded-ratio intervals

This module transports the cardinal part of Lemmas 17.33--17.34 from the
dyadic block to the literal interval `[N,M)` used by Proposition 16.1.

The finite argument keeps a witnessing incidence `(x,j)` for every bad
start and injects it by

`(x,j) ↦ (x+j,j)`

into the product of the unit terminal-kernel values up to `M+L` and the
offset interval `{0,...,L-1}`.  The exact terminal-kernel estimate therefore
gives the same prime-sensitive bound as in Section 13, with `sqrt (M+L)` in
place of `sqrt (2N+L)`.

At the terminal cutoff and under `M ≤ κ₀N`, this is
`N^(1/2+o_C(1))`, uniformly in `M` and in the critical run-length window.
Consequently both the cardinal itself is `o(N)` (hence `o(N²)`) and its
Poisson-parameter contribution `#D / 2^L` is `o(1)`.

No probability-mass statement is introduced here.  The weighted mass of
bad starts is the separate content of Lemma 17.33; the cardinal injection
below does not control those weights and hence cannot certify that claim
without an additional formal argument.
-/

namespace PaperC
namespace BoundedRatioBadStarts

open scoped BigOperators

open BadStartCount
open BoundedRatioSteinChen
open PrimeReciprocalSqrtSum
open PropositionSixteenOne
open TerminalBadStartBound
open TerminalBadStartsCritical
open TerminalKernelCount
open TerminalPrimeCutoff

noncomputable section

local instance (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-! ## Finite incidence bound -/

/-- Incidences retaining a bounded-ratio bad start and a witnessing offset. -/
noncomputable def boundedTerminalBadStartIncidences
    (N M L Y : ℕ) : Finset (ℕ × ℕ) :=
  ((boundedRatioBlock N M).product (Finset.range L)).filter fun xj ↦
    LargeOddKernel.largeOddKernel Y (xj.1 + xj.2) = 1

@[simp]
theorem mem_boundedTerminalBadStartIncidences
    {N M L Y : ℕ} {xj : ℕ × ℕ} :
    xj ∈ boundedTerminalBadStartIncidences N M L Y ↔
      xj.1 ∈ boundedRatioBlock N M ∧
        xj.2 < L ∧
          LargeOddKernel.largeOddKernel Y (xj.1 + xj.2) = 1 := by
  simp [boundedTerminalBadStartIncidences, and_assoc]

/-- Projection of the incidence set is exactly the bounded-ratio bad set. -/
theorem image_fst_boundedTerminalBadStartIncidences
    (N M L Y : ℕ) :
    (boundedTerminalBadStartIncidences N M L Y).image Prod.fst =
      boundedTerminalBadStarts N M L Y := by
  ext x
  simp only [Finset.mem_image, mem_boundedTerminalBadStartIncidences,
    mem_boundedTerminalBadStarts]
  constructor
  · rintro ⟨xj, ⟨hxj, hj, hkernel⟩, rfl⟩
    exact ⟨hxj, ⟨xj.2, hj, hkernel⟩⟩
  · rintro ⟨hx, ⟨j, hj, hkernel⟩⟩
    exact ⟨(x, j), ⟨hx, hj, hkernel⟩, rfl⟩

/-- Every bounded-ratio bad start has an incidence witness. -/
theorem card_boundedTerminalBadStarts_le_incidences
    (N M L Y : ℕ) :
    (boundedTerminalBadStarts N M L Y).card ≤
      (boundedTerminalBadStartIncidences N M L Y).card := by
  rw [← image_fst_boundedTerminalBadStartIncidences N M L Y]
  exact Finset.card_image_le

/--
The recoded incidences lie among unit terminal-kernel values up to the
literal cylinder cutoff `M+L`.
-/
theorem image_terminalBadIncidenceCode_bounded_subset
    {N M L Y : ℕ} (hN : 1 ≤ N) :
    (boundedTerminalBadStartIncidences N M L Y).image
        terminalBadIncidenceCode ⊆
      (unitLargeKernelValues Y (boundedRatioCutoff M L)).product
        (Finset.range L) := by
  intro nj hnj
  obtain ⟨xj, hxj, rfl⟩ := Finset.mem_image.mp hnj
  have hxj' := mem_boundedTerminalBadStartIncidences.mp hxj
  change (xj.1 + xj.2, xj.2) ∈
    (unitLargeKernelValues Y (boundedRatioCutoff M L)).product
      (Finset.range L)
  apply Finset.mem_product.mpr
  refine ⟨mem_unitLargeKernelValues.mpr ⟨?_, ?_, hxj'.2.2⟩, ?_⟩
  · have hxLower : N ≤ xj.1 :=
      (mem_boundedRatioBlock.mp hxj'.1).1
    omega
  · exact startWindow_le_boundedRatioCutoff hxj'.1 hxj'.2.1.le
  · simpa using hxj'.2.1

/-- Exact incidence bound supplied by the injective recoding. -/
theorem card_boundedTerminalBadStartIncidences_le
    {N M L Y : ℕ} (hN : 1 ≤ N) :
    (boundedTerminalBadStartIncidences N M L Y).card ≤
      (unitLargeKernelValues Y (boundedRatioCutoff M L)).card * L := by
  calc
    (boundedTerminalBadStartIncidences N M L Y).card =
        ((boundedTerminalBadStartIncidences N M L Y).image
          terminalBadIncidenceCode).card := by
      rw [Finset.card_image_iff.mpr]
      intro a _ha b _hb hab
      exact terminalBadIncidenceCode_injective hab
    _ ≤ ((unitLargeKernelValues Y (boundedRatioCutoff M L)).product
          (Finset.range L)).card :=
      Finset.card_le_card
        (image_terminalBadIncidenceCode_bounded_subset hN)
    _ = (unitLargeKernelValues Y (boundedRatioCutoff M L)).card * L := by
      simp

/-- Finite counting core on the literal interval `[N,M)`. -/
theorem card_boundedTerminalBadStarts_le
    {N M L Y : ℕ} (hN : 1 ≤ N) :
    (boundedTerminalBadStarts N M L Y).card ≤
      L * (unitLargeKernelValues Y (boundedRatioCutoff M L)).card := by
  calc
    (boundedTerminalBadStarts N M L Y).card ≤
        (boundedTerminalBadStartIncidences N M L Y).card :=
      card_boundedTerminalBadStarts_le_incidences N M L Y
    _ ≤ (unitLargeKernelValues Y (boundedRatioCutoff M L)).card * L :=
      card_boundedTerminalBadStartIncidences_le hN
    _ = L * (unitLargeKernelValues Y (boundedRatioCutoff M L)).card :=
      Nat.mul_comm _ _

/--
Prime-sensitive finite bound on `[N,M)` obtained from `TerminalKernelCount`.
-/
theorem card_boundedTerminalBadStarts_cast_le_eulerProduct
    {N M L Y : ℕ} (hN : 1 ≤ N) :
    ((boundedTerminalBadStarts N M L Y).card : ℝ) ≤
      2 * L * Real.sqrt (boundedRatioCutoff M L) *
        ∏ p ∈ DefectCounting.smallPrimesUpTo Y,
          (1 + (Real.sqrt p)⁻¹) := by
  have hcard :=
    card_boundedTerminalBadStarts_le
      (N := N) (M := M) (L := L) (Y := Y) hN
  have hkernel :=
    card_boundedLargeKernelValues_cast_le
      Y 1 (boundedRatioCutoff M L)
  rw [← unitLargeKernelValues_eq_bounded
    Y (boundedRatioCutoff M L)] at hkernel
  norm_num at hkernel
  calc
    ((boundedTerminalBadStarts N M L Y).card : ℝ) ≤
        (L : ℝ) *
          ((unitLargeKernelValues Y
            (boundedRatioCutoff M L)).card : ℝ) := by
      exact_mod_cast hcard
    _ ≤ (L : ℝ) *
        (2 * Real.sqrt (boundedRatioCutoff M L) *
          ∏ p ∈ DefectCounting.smallPrimesUpTo Y,
            (1 + (Real.sqrt p)⁻¹)) := by
      exact mul_le_mul_of_nonneg_left hkernel (Nat.cast_nonneg L)
    _ = 2 * L * Real.sqrt (boundedRatioCutoff M L) *
        ∏ p ∈ DefectCounting.smallPrimesUpTo Y,
          (1 + (Real.sqrt p)⁻¹) := by
      ring

/-- Exact terminal-cutoff envelope before simplifying its exponent. -/
theorem card_boundedTerminalBadStarts_terminalPrimeCutoff_le
    {N M L B : ℕ} (hN : 1 ≤ N) (hB : 16 ≤ B) :
    ((boundedTerminalBadStarts N M L
      (terminalPrimeCutoff B)).card : ℝ) ≤
      2 * L * Real.sqrt (boundedRatioCutoff M L) *
        Real.exp (terminalBadStartPrimeExponent B) := by
  let Y := terminalPrimeCutoff B
  have hY : 16 ≤ Y := by
    simpa only [Y] using sixteen_le_terminalPrimeCutoff hB
  have hcount :=
    card_boundedTerminalBadStarts_cast_le_eulerProduct
      (N := N) (M := M) (L := L) (Y := Y) hN
  have hproduct :=
    prod_smallPrimesUpTo_one_add_inv_sqrt_le_primeSensitive_two_mul hY
  have hprefactor :
      0 ≤ 2 * (L : ℝ) * Real.sqrt (boundedRatioCutoff M L) := by
    positivity
  calc
    ((boundedTerminalBadStarts N M L
        (terminalPrimeCutoff B)).card : ℝ) =
        ((boundedTerminalBadStarts N M L Y).card : ℝ) := rfl
    _ ≤ 2 * L * Real.sqrt (boundedRatioCutoff M L) *
          ∏ p ∈ DefectCounting.smallPrimesUpTo Y,
            (1 + (Real.sqrt p)⁻¹) :=
      hcount
    _ ≤ 2 * L * Real.sqrt (boundedRatioCutoff M L) *
          Real.exp
            (2 * Real.sqrt (rootCutoff Y) +
              56 * Real.sqrt (2 * Y) /
                ((Nat.log 2 Y / 2 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hproduct hprefactor
    _ = 2 * L * Real.sqrt (boundedRatioCutoff M L) *
          Real.exp (terminalBadStartPrimeExponent B) := by
      simp only [terminalBadStartPrimeExponent, Y]

/-- Readable finite terminal estimate on `[N,M)`. -/
theorem card_boundedTerminalBadStarts_terminalPrimeCutoff_le_readable
    {N M L B : ℕ} (hN : 1 ≤ N) (hB : 16 ≤ B) :
    ((boundedTerminalBadStarts N M L
      (terminalPrimeCutoff B)).card : ℝ) ≤
      2 * L * Real.sqrt (boundedRatioCutoff M L) *
        Real.exp (terminalBadStartReadableExponent B) := by
  calc
    ((boundedTerminalBadStarts N M L
        (terminalPrimeCutoff B)).card : ℝ) ≤
        2 * L * Real.sqrt (boundedRatioCutoff M L) *
          Real.exp (terminalBadStartPrimeExponent B) :=
      card_boundedTerminalBadStarts_terminalPrimeCutoff_le hN hB
    _ ≤ 2 * L * Real.sqrt (boundedRatioCutoff M L) *
          Real.exp (terminalBadStartReadableExponent B) := by
      apply mul_le_mul_of_nonneg_left
      · exact Real.exp_le_exp.mpr
          ((terminalBadStartPrimeExponent_le_scaleExponent hB).trans
            (terminalBadStartScaleExponent_le_readableExponent hB))
      · positivity

/-! ## Uniform bounded-ratio asymptotics -/

/--
Three-parameter form of `N^(1/2+o(1))`, uniform on bounded-ratio intervals.
-/
def UniformHalfPowerSubpolynomialInBoundedRatioWindow
    (C : ℝ) (κ₀ : ℕ)
    (f : ℕ → ℕ → ℕ → ℝ) : Prop :=
  ∀ k : ℕ, 0 < k →
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ M L,
      2 * N ≤ M →
      M ≤ κ₀ * N →
      CriticalRunWindow.InRunLengthWindow C N L →
      |f N M L| ^ (2 * k) ≤ (N : ℝ) ^ (k + 1)

/-- Uniform bounded-ratio little-oh with the linear scale `N`. -/
def UniformLittleOLinearInBoundedRatioWindow
    (C : ℝ) (κ₀ : ℕ)
    (f : ℕ → ℕ → ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ M L,
      2 * N ≤ M →
      M ≤ κ₀ * N →
      CriticalRunWindow.InRunLengthWindow C N L →
      |f N M L| ≤ ε * |(N : ℝ)|

/-- Uniform convergence to zero on bounded-ratio critical windows. -/
def UniformLittleOOneInBoundedRatioWindow
    (C : ℝ) (κ₀ : ℕ)
    (f : ℕ → ℕ → ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ M L,
      2 * N ≤ M →
      M ≤ κ₀ * N →
      CriticalRunWindow.InRunLengthWindow C N L →
      |f N M L| ≤ ε

/-- Subpolynomial factor left after extracting `sqrt N`. -/
noncomputable def boundedTerminalBadStartResidual
    (κ₀ : ℕ) (_N L : ℕ) : ℝ :=
  2 * Real.sqrt (κ₀ + 1) *
    ((((L + 1 : ℕ) : ℝ)) *
      Real.exp (terminalBadStartReadableExponent (L + 1)))

theorem boundedTerminalBadStartResidual_uniformSubpolynomial
    {C : ℝ} (hC : 0 ≤ C) (κ₀ : ℕ) :
    UniformSubpolynomialOn
      (CriticalRunWindow.InRunLengthWindow C)
      (boundedTerminalBadStartResidual κ₀) := by
  have hheight :=
    CriticalRationalMassEnvelopes.runLengthAddOne_uniformSubpolynomial hC
  have hexponential :=
    terminalExponentFactor_uniformSubpolynomial hC
  unfold boundedTerminalBadStartResidual
  simpa only [Nat.cast_add, Nat.cast_one, mul_assoc] using
    ExpSqrtLog.uniformSubpolynomialOn_const_mul
      (2 * Real.sqrt (κ₀ + 1))
      (ExpSqrtLog.uniformSubpolynomialOn_mul hheight hexponential)

/-- A two-parameter envelope dominating every admissible endpoint `M`. -/
noncomputable def boundedTerminalBadStartCardEnvelope
    (κ₀ N L : ℕ) : ℝ :=
  Real.sqrt N * boundedTerminalBadStartResidual κ₀ N L

theorem boundedTerminalBadStartCardEnvelope_uniformHalfPower
    {C : ℝ} (hC : 0 ≤ C) (κ₀ : ℕ) :
    UniformHalfPowerSubpolynomialOn
      (CriticalRunWindow.InRunLengthWindow C)
      (boundedTerminalBadStartCardEnvelope κ₀) := by
  apply UniformHalfPower.of_sqrt_mul_subpolynomial
    (boundedTerminalBadStartResidual_uniformSubpolynomial hC κ₀)
  refine ⟨0, ?_⟩
  intro N _hN L _hrun
  unfold boundedTerminalBadStartCardEnvelope
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]

/--
Eventually, the finite bounded-ratio cardinal is dominated by the uniform
half-power envelope.
-/
theorem card_boundedTerminalBadStarts_terminalCutoff_le_envelope
    {C : ℝ} (hC : 0 ≤ C) (κ₀ : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ M L,
      2 * N ≤ M →
      M ≤ κ₀ * N →
      CriticalRunWindow.InRunLengthWindow C N L →
      ((boundedTerminalBadStarts N M L
        (terminalPrimeCutoff (L + 1))).card : ℝ) ≤
        boundedTerminalBadStartCardEnvelope κ₀ N L := by
  obtain ⟨Nwindow, hwindow⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  obtain ⟨Nadm, hadm⟩ :=
    CriticalWeightedDefect.admissible_eventually
      CriticalRunWindow.lowerConstant_pos
      CriticalRunWindow.lowerConstant_lt_upperConstant
  obtain ⟨Nsixteen, hsixteen⟩ :=
    DependencyEdgesCritical.runLengthAddOne_tends_to_infinity hC 16
  refine ⟨max Nwindow (max Nadm Nsixteen), ?_⟩
  intro N hN M L _hNM hMκ hrun
  have hw :=
    hwindow N ((le_max_left _ _).trans hN) L hrun
  have hNtail :
      max Nadm Nsixteen ≤ N :=
    (le_max_right Nwindow (max Nadm Nsixteen)).trans hN
  have hAdm :=
    hadm N ((le_max_left Nadm Nsixteen).trans hNtail)
      (L + 1) hw.1
  have hB :
      16 ≤ L + 1 :=
    hsixteen N ((le_max_right Nadm Nsixteen).trans hNtail) L hrun
  have htwoB : 2 * (L + 1) ≤ N :=
    CriticalWindowParameters.two_mul_H_le_N_of_criticalWindow
      hAdm.1 hAdm.2.2.2.1
  have hcutoff :
      boundedRatioCutoff M L ≤ (κ₀ + 1) * N := by
    unfold boundedRatioCutoff
    calc
      M + L ≤ κ₀ * N + N :=
        Nat.add_le_add hMκ (by omega)
      _ = (κ₀ + 1) * N := by
        simp only [Nat.add_mul, one_mul]
  have hsqrtCutoff :
      Real.sqrt (boundedRatioCutoff M L) ≤
        Real.sqrt (κ₀ + 1) * Real.sqrt N := by
    calc
      Real.sqrt (boundedRatioCutoff M L) ≤
          Real.sqrt ((((κ₀ + 1) * N : ℕ) : ℝ)) := by
        apply Real.sqrt_le_sqrt
        exact_mod_cast hcutoff
      _ = Real.sqrt (κ₀ + 1) * Real.sqrt N := by
        rw [Nat.cast_mul,
          Real.sqrt_mul (Nat.cast_nonneg (κ₀ + 1))]
        norm_num only [Nat.cast_add, Nat.cast_one]
  have hfinite :=
    card_boundedTerminalBadStarts_terminalPrimeCutoff_le_readable
      (N := N) (M := M) (L := L) (B := L + 1)
      (by omega) hB
  calc
    ((boundedTerminalBadStarts N M L
        (terminalPrimeCutoff (L + 1))).card : ℝ) ≤
        2 * L * Real.sqrt (boundedRatioCutoff M L) *
          Real.exp (terminalBadStartReadableExponent (L + 1)) :=
      hfinite
    _ ≤
        2 * (L + 1) *
          (Real.sqrt (κ₀ + 1) * Real.sqrt N) *
          Real.exp (terminalBadStartReadableExponent (L + 1)) := by
      gcongr
      exact_mod_cast Nat.le_succ L
    _ = boundedTerminalBadStartCardEnvelope κ₀ N L := by
      unfold boundedTerminalBadStartCardEnvelope
        boundedTerminalBadStartResidual
      norm_num only [Nat.cast_add, Nat.cast_one]
      ring

/-- The terminal bad-start cardinal is uniformly `N^(1/2+o_C(1))`. -/
theorem boundedTerminalBadStarts_terminalCutoff_uniformHalfPower
    {C : ℝ} (hC : 0 ≤ C) (κ₀ : ℕ) :
    UniformHalfPowerSubpolynomialInBoundedRatioWindow C κ₀
      (fun N M L =>
        ((boundedTerminalBadStarts N M L
          (terminalPrimeCutoff (L + 1))).card : ℝ)) := by
  have hEnvelope :=
    boundedTerminalBadStartCardEnvelope_uniformHalfPower hC κ₀
  obtain ⟨Nbound, hbound⟩ :=
    card_boundedTerminalBadStarts_terminalCutoff_le_envelope hC κ₀
  intro k hk
  obtain ⟨Nhalf, hhalf⟩ := hEnvelope k hk
  refine ⟨max Nbound Nhalf, ?_⟩
  intro N hN M L hNM hMκ hrun
  have hb :=
    hbound N ((le_max_left _ _).trans hN) M L hNM hMκ hrun
  have hh :=
    hhalf N ((le_max_right _ _).trans hN) L hrun
  have hnonneg :
      0 ≤
        ((boundedTerminalBadStarts N M L
          (terminalPrimeCutoff (L + 1))).card : ℝ) := by
    positivity
  have hEnvelopeNonneg :
      0 ≤ boundedTerminalBadStartCardEnvelope κ₀ N L := by
    unfold boundedTerminalBadStartCardEnvelope
      boundedTerminalBadStartResidual
    positivity
  change
    |((boundedTerminalBadStarts N M L
      (terminalPrimeCutoff (L + 1))).card : ℝ)| ^ (2 * k) ≤
      (N : ℝ) ^ (k + 1)
  rw [abs_of_nonneg hEnvelopeNonneg] at hh
  rw [abs_of_nonneg hnonneg]
  exact (pow_le_pow_left₀ hnonneg hb _).trans hh

/-- Stronger linear little-oh consequence of the half-power estimate. -/
theorem boundedTerminalBadStarts_terminalCutoff_uniformLittleOLinear
    {C : ℝ} (hC : 0 ≤ C) (κ₀ : ℕ) :
    UniformLittleOLinearInBoundedRatioWindow C κ₀
      (fun N M L =>
        ((boundedTerminalBadStarts N M L
          (terminalPrimeCutoff (L + 1))).card : ℝ)) := by
  have hEnvelopeHalf :=
    boundedTerminalBadStartCardEnvelope_uniformHalfPower hC κ₀
  have hEnvelopeRational :
      UniformRationalPowerSubpolynomialOn 1 2
        (CriticalRunWindow.InRunLengthWindow C)
        (boundedTerminalBadStartCardEnvelope κ₀) := by
    simpa [UniformHalfPowerSubpolynomialOn,
      UniformRationalPowerSubpolynomialOn] using hEnvelopeHalf
  have hEnvelopeLinear :
      UniformLittleOOn
        (CriticalRunWindow.InRunLengthWindow C)
        (boundedTerminalBadStartCardEnvelope κ₀)
        (fun N _ ↦ (N : ℝ)) := by
    simpa only [pow_one] using
      (UniformRationalPower.littleO_natPower_of_lt
        (p := 1) (q := 2) (r := 1) (by omega) hEnvelopeRational)
  obtain ⟨Nbound, hbound⟩ :=
    card_boundedTerminalBadStarts_terminalCutoff_le_envelope hC κ₀
  intro ε hε
  obtain ⟨Nlinear, hlinear⟩ := hEnvelopeLinear ε hε
  refine ⟨max Nbound Nlinear, ?_⟩
  intro N hN M L hNM hMκ hrun
  have hb :=
    hbound N ((le_max_left _ _).trans hN) M L hNM hMκ hrun
  have hl :=
    hlinear N ((le_max_right _ _).trans hN) L hrun
  have hcardNonneg :
      0 ≤
        ((boundedTerminalBadStarts N M L
          (terminalPrimeCutoff (L + 1))).card : ℝ) := by
    positivity
  have hEnvelopeNonneg :
      0 ≤ boundedTerminalBadStartCardEnvelope κ₀ N L := by
    unfold boundedTerminalBadStartCardEnvelope
      boundedTerminalBadStartResidual
    positivity
  change
    |((boundedTerminalBadStarts N M L
      (terminalPrimeCutoff (L + 1))).card : ℝ)| ≤
      ε * |(N : ℝ)|
  change
    |boundedTerminalBadStartCardEnvelope κ₀ N L| ≤
      ε * |(N : ℝ)| at hl
  rw [abs_of_nonneg hEnvelopeNonneg] at hl
  rw [abs_of_nonneg hcardNonneg]
  exact hb.trans hl

/--
Compatibility with Proposition 16.1's existing (weaker) quadratic little-oh
interface.
-/
theorem boundedTerminalBadStarts_terminalCutoff_uniformLittleO
    {C : ℝ} (hC : 0 ≤ C) (κ₀ : ℕ) :
    UniformLittleOInBoundedRatioWindow C κ₀
      (fun N M L =>
        ((boundedTerminalBadStarts N M L
          (terminalPrimeCutoff (L + 1))).card : ℝ)) := by
  have hlinear :=
    boundedTerminalBadStarts_terminalCutoff_uniformLittleOLinear hC κ₀
  intro ε hε
  obtain ⟨Nlinear, hlinearBound⟩ := hlinear ε hε
  refine ⟨max Nlinear 1, ?_⟩
  intro N hN M L hNM hMκ hrun
  have hl :=
    hlinearBound N ((le_max_left _ _).trans hN)
      M L hNM hMκ hrun
  have hNone : 1 ≤ N := (le_max_right Nlinear 1).trans hN
  have hNnonneg : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have hcardNonneg :
      0 ≤
        ((boundedTerminalBadStarts N M L
          (terminalPrimeCutoff (L + 1))).card : ℝ) := by
    positivity
  rw [abs_of_nonneg hcardNonneg, abs_of_nonneg hNnonneg] at hl
  change
    |((boundedTerminalBadStarts N M L
      (terminalPrimeCutoff (L + 1))).card : ℝ)| ≤
      ε * |(N : ℝ) ^ 2|
  rw [abs_of_nonneg hcardNonneg]
  calc
    ((boundedTerminalBadStarts N M L
        (terminalPrimeCutoff (L + 1))).card : ℝ) ≤
        ε * (N : ℝ) :=
      hl
    _ ≤ ε * |(N : ℝ) ^ 2| := by
      rw [abs_of_nonneg (sq_nonneg (N : ℝ))]
      apply mul_le_mul_of_nonneg_left _ hε.le
      nlinarith [show (1 : ℝ) ≤ N by exact_mod_cast hNone]

/-- The normalized cardinal contribution is uniformly `o(1)`. -/
theorem normalized_boundedTerminalBadStarts_uniformLittleOOne
    {C : ℝ} (hC : 0 ≤ C) (κ₀ : ℕ) :
    UniformLittleOOneInBoundedRatioWindow C κ₀
      (fun N M L =>
        ((boundedTerminalBadStarts N M L
          (terminalPrimeCutoff (L + 1))).card : ℝ) /
            (2 : ℝ) ^ L) := by
  have hcount :=
    boundedTerminalBadStarts_terminalCutoff_uniformLittleOLinear hC κ₀
  have hbalancePos :
      0 < CriticalRunWindow.balanceConstant C := by
    unfold CriticalRunWindow.balanceConstant
    positivity
  obtain ⟨Nwindow, hwindow⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  intro ε hε
  obtain ⟨Ncount, hcountBound⟩ :=
    hcount (ε / CriticalRunWindow.balanceConstant C)
      (div_pos hε hbalancePos)
  refine ⟨max Nwindow Ncount, ?_⟩
  intro N hN M L hNM hMκ hrun
  have hw :=
    hwindow N ((le_max_left _ _).trans hN) L hrun
  have hc :=
    hcountBound N ((le_max_right _ _).trans hN)
      M L hNM hMκ hrun
  have hNnonneg : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have hpowPos : (0 : ℝ) < (2 : ℝ) ^ L := by positivity
  have hcardNonneg :
      0 ≤
        ((boundedTerminalBadStarts N M L
          (terminalPrimeCutoff (L + 1))).card : ℝ) := by
    positivity
  simp only [abs_div, abs_of_nonneg hcardNonneg,
    abs_of_pos hpowPos, abs_of_nonneg hNnonneg] at hc ⊢
  calc
    ((boundedTerminalBadStarts N M L
          (terminalPrimeCutoff (L + 1))).card : ℝ) /
          (2 : ℝ) ^ L ≤
        ((ε / CriticalRunWindow.balanceConstant C) * (N : ℝ)) /
          (2 : ℝ) ^ L :=
      div_le_div_of_nonneg_right hc hpowPos.le
    _ =
        (ε / CriticalRunWindow.balanceConstant C) *
          ((N : ℝ) / (2 : ℝ) ^ L) := by
      ring
    _ ≤
        (ε / CriticalRunWindow.balanceConstant C) *
          CriticalRunWindow.balanceConstant C :=
      mul_le_mul_of_nonneg_left hw.2.2
        (div_nonneg hε.le hbalancePos.le)
    _ = ε := by
      field_simp

end

end BoundedRatioBadStarts
end PaperC
