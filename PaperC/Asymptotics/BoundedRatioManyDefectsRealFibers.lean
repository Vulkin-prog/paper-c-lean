import PaperC.Asymptotics.BoundedRatioManyDefectsFibers

set_option maxHeartbeats 3600000

/-!
# Real-valued fixed-fibre envelopes for Lemma 17.26

The finite reductions in `BoundedRatioManyDefectsFibers` use a common
natural-valued bound for every fixed-base/fixed-shape fibre.  That is a
convenient exact interface, but the three degree branches of Lemma 17.21
naturally produce real asymptotic envelopes.  Passing each branch through a
ceiling before assembling them is mathematically irrelevant and obscures the
source proof.

This module repeats only the final finite summation after coercion to
`ℝ`.  It proves that a common nonnegative real envelope for the fixed fibres
is enough for Lemma 17.26.  No counting input and no Diophantine hypothesis is
added.
-/

namespace PaperC
namespace BoundedRatioManyDefectsRealFibers

open BoundedRatioComponentHosts
open BoundedRatioDistinctKernelTwoDefects
open BoundedRatioManyDefectsFibers
open BoundedRatioManyDefectsReduction
open PropositionSixteenOne

noncomputable section

/-! ## Exact real-valued finite summation -/

/--
Real-valued version of the left fixed-base/fixed-shape summation.
-/
theorem card_leftTwoDefectActiveHosts_cast_le_of_baseShapeFibers
    {N M A L : ℕ} (hN : 2 ≤ N)
    (terminal : TerminalPredicateFamily)
    (Q : ℝ)
    (hfiber :
      ∀ base ∈ twoDefectBaseCover N M (L + 1),
      ∀ shape ∈ boundedOffsetShapes L 10,
        ((leftBaseShapeFiber
          N M A L 10 base shape).card : ℝ) ≤ Q) :
    ((leftTwoDefectActiveHosts
        N M A L hN terminal).card : ℝ) ≤
      ((twoDefectBaseCover N M (L + 1)).card : ℝ) *
        ((boundedOffsetShapes L 10).card : ℝ) * Q := by
  classical
  calc
    ((leftTwoDefectActiveHosts
        N M A L hN terminal).card : ℝ) ≤
        (((twoDefectBaseCover N M (L + 1)).biUnion fun base =>
          (boundedOffsetShapes L 10).biUnion fun shape =>
            leftBaseShapeFiber
              N M A L 10 base shape).card : ℝ) := by
      exact_mod_cast
        Finset.card_le_card
          (leftTwoDefectActiveHosts_subset_baseShapeFibers
            hN terminal)
    _ ≤
        ∑ base ∈ twoDefectBaseCover N M (L + 1),
          (((boundedOffsetShapes L 10).biUnion fun shape =>
            leftBaseShapeFiber
              N M A L 10 base shape).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    _ ≤
        ∑ base ∈ twoDefectBaseCover N M (L + 1),
          ∑ shape ∈ boundedOffsetShapes L 10,
            ((leftBaseShapeFiber
              N M A L 10 base shape).card : ℝ) := by
      apply Finset.sum_le_sum
      intro base hbase
      exact_mod_cast Finset.card_biUnion_le
    _ ≤
        ∑ _base ∈ twoDefectBaseCover N M (L + 1),
          ∑ _shape ∈ boundedOffsetShapes L 10, Q := by
      apply Finset.sum_le_sum
      intro base hbase
      exact Finset.sum_le_sum fun shape hshape =>
        hfiber base hbase shape hshape
    _ =
        ((twoDefectBaseCover N M (L + 1)).card : ℝ) *
          ((boundedOffsetShapes L 10).card : ℝ) * Q := by
      simp
      ring

/-- Symmetric real-valued finite summation. -/
theorem card_rightTwoDefectActiveHosts_cast_le_of_baseShapeFibers
    {N M A L : ℕ} (hN : 2 ≤ N)
    (terminal : TerminalPredicateFamily)
    (Q : ℝ)
    (hfiber :
      ∀ base ∈ twoDefectBaseCover N M (L + 1),
      ∀ shape ∈ boundedOffsetShapes L 10,
        ((rightBaseShapeFiber
          N M A L 10 base shape).card : ℝ) ≤ Q) :
    ((rightTwoDefectActiveHosts
        N M A L hN terminal).card : ℝ) ≤
      ((twoDefectBaseCover N M (L + 1)).card : ℝ) *
        ((boundedOffsetShapes L 10).card : ℝ) * Q := by
  classical
  calc
    ((rightTwoDefectActiveHosts
        N M A L hN terminal).card : ℝ) ≤
        (((twoDefectBaseCover N M (L + 1)).biUnion fun base =>
          (boundedOffsetShapes L 10).biUnion fun shape =>
            rightBaseShapeFiber
              N M A L 10 base shape).card : ℝ) := by
      exact_mod_cast
        Finset.card_le_card
          (rightTwoDefectActiveHosts_subset_baseShapeFibers
            hN terminal)
    _ ≤
        ∑ base ∈ twoDefectBaseCover N M (L + 1),
          (((boundedOffsetShapes L 10).biUnion fun shape =>
            rightBaseShapeFiber
              N M A L 10 base shape).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    _ ≤
        ∑ base ∈ twoDefectBaseCover N M (L + 1),
          ∑ shape ∈ boundedOffsetShapes L 10,
            ((rightBaseShapeFiber
              N M A L 10 base shape).card : ℝ) := by
      apply Finset.sum_le_sum
      intro base hbase
      exact_mod_cast Finset.card_biUnion_le
    _ ≤
        ∑ _base ∈ twoDefectBaseCover N M (L + 1),
          ∑ _shape ∈ boundedOffsetShapes L 10, Q := by
      apply Finset.sum_le_sum
      intro base hbase
      exact Finset.sum_le_sum fun shape hshape =>
        hfiber base hbase shape hshape
    _ =
        ((twoDefectBaseCover N M (L + 1)).card : ℝ) *
          ((boundedOffsetShapes L 10).card : ℝ) * Q := by
      simp
      ring

/--
High-zone real-valued bound for the two oriented host populations, with the
polynomial shape overcount made explicit.
-/
theorem orientedHostCover_cast_le_explicit_of_distinctBaseShapeFibers
    {N M A L : ℕ} (hN : 2 ≤ N)
    (terminal : TerminalPredicateFamily)
    (hhigh : (L + 1) ^ 2 + 1 < N)
    (Q : ℝ) (hQ : 0 ≤ Q)
    (hleft :
      ∀ base ∈ distinctKernelDefectBases N M (L + 1),
      ∀ shape ∈ boundedOffsetShapes L 10,
        ((leftBaseShapeFiber
          N M A L 10 base shape).card : ℝ) ≤ Q)
    (hright :
      ∀ base ∈ distinctKernelDefectBases N M (L + 1),
      ∀ shape ∈ boundedOffsetShapes L 10,
        ((rightBaseShapeFiber
          N M A L 10 base shape).card : ℝ) ≤ Q) :
    (((leftTwoDefectActiveHosts
        N M A L hN terminal).card +
      (rightTwoDefectActiveHosts
        N M A L hN terminal).card : ℕ) : ℝ) ≤
      2 *
        (((distinctKernelDefectBases
            N M (L + 1)).card : ℝ) *
          (((11 * (L + 1) ^ 10) ^ 2 : ℕ) : ℝ) * Q) := by
  have hcover :=
    twoDefectBaseCover_eq_distinctKernel
      (N := N) (M := M) hhigh
  have hleftBound :=
    card_leftTwoDefectActiveHosts_cast_le_of_baseShapeFibers
      (N := N) (M := M) (A := A) (L := L)
      hN terminal Q (by
        intro base hbase shape hshape
        exact hleft base (by simpa only [hcover] using hbase)
          shape hshape)
  have hrightBound :=
    card_rightTwoDefectActiveHosts_cast_le_of_baseShapeFibers
      (N := N) (M := M) (A := A) (L := L)
      hN terminal Q (by
        intro base hbase shape hshape
        exact hright base (by simpa only [hcover] using hbase)
          shape hshape)
  rw [hcover] at hleftBound hrightBound
  have hshapes :
      ((boundedOffsetShapes L 10).card : ℝ) ≤
        (((11 * (L + 1) ^ 10) ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast card_boundedOffsetShapes_le L 10
  rw [Nat.cast_add]
  calc
    ((leftTwoDefectActiveHosts
        N M A L hN terminal).card : ℝ) +
        ((rightTwoDefectActiveHosts
          N M A L hN terminal).card : ℝ) ≤
        2 *
          (((distinctKernelDefectBases
              N M (L + 1)).card : ℝ) *
            ((boundedOffsetShapes L 10).card : ℝ) * Q) := by
      linarith [hleftBound, hrightBound]
    _ ≤
        2 *
          (((distinctKernelDefectBases
              N M (L + 1)).card : ℝ) *
            (((11 * (L + 1) ^ 10) ^ 2 : ℕ) : ℝ) * Q) := by
      gcongr

/-! ## Asymptotic closure -/

/--
Real-envelope form of Lemma 17.26.

Once every fixed-base/fixed-shape fibre is eventually bounded by one
nonnegative `N^(1/2+o(1))` real envelope, the already certified
two-defect-base count and residual-weight estimate close the fifth sector.
-/
theorem manyDefectsSector_rates_of_baseShapeFiberRealEnvelope
    {C : ℝ} (hC : 0 ≤ C) (κ₀ A : ℕ)
    (terminal : TerminalPredicateFamily)
    (hPell : PellInput.GeneralizedPellPolynomialBoxStatement)
    (fiberEnvelope : ℕ → ℕ → ℝ)
    (hfiberRate :
      UniformHalfPowerSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C)
        fiberEnvelope)
    (hfiberNonneg : ∀ N L, 0 ≤ fiberEnvelope N L)
    (hfiberDom :
      ∃ N₁ : ℕ, ∀ N ≥ N₁, ∀ M L,
        2 * N ≤ M →
        M ≤ κ₀ * N →
        CriticalRunWindow.InRunLengthWindow C N L →
        (∀ base ∈
            distinctKernelDefectBases N M (L + 1),
          ∀ shape ∈ boundedOffsetShapes L 10,
            ((leftBaseShapeFiber
              N M A L 10 base shape).card : ℝ) ≤
                fiberEnvelope N L) ∧
        (∀ base ∈
            distinctKernelDefectBases N M (L + 1),
          ∀ shape ∈ boundedOffsetShapes L 10,
            ((rightBaseShapeFiber
              N M A L 10 base shape).card : ℝ) ≤
                fiberEnvelope N L)) :
    UniformRationalPowerInBoundedRatioWindow 3 2 C κ₀
        (sectorResidualMass A terminal .manyDefects) ∧
      UniformLittleOInBoundedRatioWindow C κ₀
        (sectorResidualMass A terminal .manyDefects) := by
  obtain ⟨c, hc, Nbase, hbase⟩ :=
    generalizedPell_implies_card_distinctKernelDefectBases_le_residual
      hC κ₀ hPell
  obtain ⟨Nfiber, hfiber⟩ := hfiberDom
  obtain ⟨Nhigh, hhigh⟩ :=
    twoDefect_highZone_eventually hC
  let subpolynomialFactor : ℕ → ℕ → ℝ :=
    fun N L =>
      2 *
        (distinctKernelTwoDefectResidual c N L *
          componentShapeEnvelope N L)
  let hostEnvelope : ℕ → ℕ → ℝ :=
    fun N L =>
      subpolynomialFactor N L *
        fiberEnvelope N L
  have hbaseRate :=
    distinctKernelTwoDefectResidual_uniformSubpolynomial
      hC hc
  have hshapeRate :=
    componentShapeEnvelope_uniformSubpolynomial hC
  have hfactorRate :
      UniformSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C)
        subpolynomialFactor := by
    simpa only [subpolynomialFactor] using
      ExpSqrtLog.uniformSubpolynomialOn_const_mul 2
        (ExpSqrtLog.uniformSubpolynomialOn_mul
          hbaseRate hshapeRate)
  have hhostRate :
      UniformHalfPowerSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C)
        hostEnvelope := by
    have hproduct :=
      UniformHalfPower.mul_subpolynomial
        hfiberRate hfactorRate
    simpa only [hostEnvelope, mul_comm] using hproduct
  have hhostNonneg :
      ∀ N L, 0 ≤ hostEnvelope N L := by
    intro N L
    dsimp only [hostEnvelope, subpolynomialFactor]
    exact mul_nonneg
      (mul_nonneg (by positivity)
        (mul_nonneg (by
          unfold distinctKernelTwoDefectResidual
            smoothKernelChebyshevEnvelope
            PellInput.expLogLogBound
          positivity) (by
          unfold componentShapeEnvelope
          positivity)))
      (hfiberNonneg N L)
  have hhostDom :
      ∃ N₁ : ℕ, ∀ N ≥ N₁, ∀ M L,
        2 * N ≤ M →
        M ≤ κ₀ * N →
        CriticalRunWindow.InRunLengthWindow C N L →
        orientedHostCoverCount A terminal N M L ≤
          hostEnvelope N L := by
    refine
      ⟨max Nbase (max Nfiber (max Nhigh 2)), ?_⟩
    intro N hN M L hNM hMκ hrun
    have hNbase :
        Nbase ≤ N :=
      (le_max_left _ _).trans hN
    have htail :
        max Nfiber (max Nhigh 2) ≤ N :=
      (le_max_right _ _).trans hN
    have hNfiber :
        Nfiber ≤ N :=
      (le_max_left _ _).trans htail
    have htail₂ :
        max Nhigh 2 ≤ N :=
      (le_max_right _ _).trans htail
    have hNhigh :
        Nhigh ≤ N :=
      (le_max_left _ _).trans htail₂
    have hNtwo :
        2 ≤ N :=
      (le_max_right _ _).trans htail₂
    have hbaseBound :=
      hbase N hNbase M L hNM hMκ hrun
    have hfibers :=
      hfiber N hNfiber M L hNM hMκ hrun
    have hfinite :=
      orientedHostCover_cast_le_explicit_of_distinctBaseShapeFibers
        hNtwo terminal (hhigh N hNhigh L hrun)
        (fiberEnvelope N L) (hfiberNonneg N L)
        hfibers.1 hfibers.2
    simp only [orientedHostCoverCount, dif_pos hNtwo]
    calc
      (((leftTwoDefectActiveHosts
            N M A L hNtwo terminal).card +
          (rightTwoDefectActiveHosts
            N M A L hNtwo terminal).card : ℕ) : ℝ) ≤
          2 *
            (((distinctKernelDefectBases
                N M (L + 1)).card : ℝ) *
              (((11 * (L + 1) ^ 10) ^ 2 : ℕ) : ℝ) *
              fiberEnvelope N L) :=
        hfinite
      _ =
          2 *
            (((distinctKernelDefectBases
                N M (L + 1)).card : ℝ) *
              componentShapeEnvelope N L) *
            fiberEnvelope N L := by
        unfold componentShapeEnvelope
        push_cast
        ring
      _ ≤
          2 *
            (distinctKernelTwoDefectResidual c N L *
              componentShapeEnvelope N L) *
            fiberEnvelope N L := by
        apply mul_le_mul_of_nonneg_right _ (hfiberNonneg N L)
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact mul_le_mul_of_nonneg_right hbaseBound (by
          unfold componentShapeEnvelope
          positivity)
      _ = hostEnvelope N L := by
        rfl
  exact
    manyDefectsSector_rates_of_orientedHostEnvelope
      hC κ₀ A terminal hhostRate hhostNonneg hhostDom

/--
Source-exact `N^(3/2+o)` consequence of a common real fixed-fibre
envelope.
-/
theorem manyDefectsSector_uniformThreeHalves_of_baseShapeFiberRealEnvelope
    {C : ℝ} (hC : 0 ≤ C) (κ₀ A : ℕ)
    (terminal : TerminalPredicateFamily)
    (hPell : PellInput.GeneralizedPellPolynomialBoxStatement)
    (fiberEnvelope : ℕ → ℕ → ℝ)
    (hfiberRate :
      UniformHalfPowerSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C)
        fiberEnvelope)
    (hfiberNonneg : ∀ N L, 0 ≤ fiberEnvelope N L)
    (hfiberDom :
      ∃ N₁ : ℕ, ∀ N ≥ N₁, ∀ M L,
        2 * N ≤ M →
        M ≤ κ₀ * N →
        CriticalRunWindow.InRunLengthWindow C N L →
        (∀ base ∈
            distinctKernelDefectBases N M (L + 1),
          ∀ shape ∈ boundedOffsetShapes L 10,
            ((leftBaseShapeFiber
              N M A L 10 base shape).card : ℝ) ≤
                fiberEnvelope N L) ∧
        (∀ base ∈
            distinctKernelDefectBases N M (L + 1),
          ∀ shape ∈ boundedOffsetShapes L 10,
            ((rightBaseShapeFiber
              N M A L 10 base shape).card : ℝ) ≤
                fiberEnvelope N L)) :
    UniformRationalPowerInBoundedRatioWindow 3 2 C κ₀
      (sectorResidualMass A terminal .manyDefects) :=
  (manyDefectsSector_rates_of_baseShapeFiberRealEnvelope
    hC κ₀ A terminal hPell fiberEnvelope
    hfiberRate hfiberNonneg hfiberDom).1

/--
Quadratic little-oh consequence of a common real fixed-fibre envelope.
-/
theorem manyDefectsSector_uniformLittleO_of_baseShapeFiberRealEnvelope
    {C : ℝ} (hC : 0 ≤ C) (κ₀ A : ℕ)
    (terminal : TerminalPredicateFamily)
    (hPell : PellInput.GeneralizedPellPolynomialBoxStatement)
    (fiberEnvelope : ℕ → ℕ → ℝ)
    (hfiberRate :
      UniformHalfPowerSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C)
        fiberEnvelope)
    (hfiberNonneg : ∀ N L, 0 ≤ fiberEnvelope N L)
    (hfiberDom :
      ∃ N₁ : ℕ, ∀ N ≥ N₁, ∀ M L,
        2 * N ≤ M →
        M ≤ κ₀ * N →
        CriticalRunWindow.InRunLengthWindow C N L →
        (∀ base ∈
            distinctKernelDefectBases N M (L + 1),
          ∀ shape ∈ boundedOffsetShapes L 10,
            ((leftBaseShapeFiber
              N M A L 10 base shape).card : ℝ) ≤
                fiberEnvelope N L) ∧
        (∀ base ∈
            distinctKernelDefectBases N M (L + 1),
          ∀ shape ∈ boundedOffsetShapes L 10,
            ((rightBaseShapeFiber
              N M A L 10 base shape).card : ℝ) ≤
                fiberEnvelope N L)) :
    UniformLittleOInBoundedRatioWindow C κ₀
      (sectorResidualMass A terminal .manyDefects) :=
  (manyDefectsSector_rates_of_baseShapeFiberRealEnvelope
    hC κ₀ A terminal hPell fiberEnvelope
    hfiberRate hfiberNonneg hfiberDom).2

/-- Registered historical-interface wrapper for the real fibre closure. -/
theorem manyDefectsSectorStability_of_baseShapeFiberRealEnvelope
    {C : ℝ} (hC : 0 ≤ C) (κ₀ A : ℕ)
    (terminal : TerminalPredicateFamily)
    (fiberEnvelope : ℕ → ℕ → ℝ)
    (hfiberRate :
      UniformHalfPowerSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C)
        fiberEnvelope)
    (hfiberNonneg : ∀ N L, 0 ≤ fiberEnvelope N L)
    (hfiberDom :
      ∃ N₁ : ℕ, ∀ N ≥ N₁, ∀ M L,
        2 * N ≤ M →
        M ≤ κ₀ * N →
        CriticalRunWindow.InRunLengthWindow C N L →
        (∀ base ∈
            distinctKernelDefectBases N M (L + 1),
          ∀ shape ∈ boundedOffsetShapes L 10,
            ((leftBaseShapeFiber
              N M A L 10 base shape).card : ℝ) ≤
                fiberEnvelope N L) ∧
        (∀ base ∈
            distinctKernelDefectBases N M (L + 1),
          ∀ shape ∈ boundedOffsetShapes L 10,
            ((rightBaseShapeFiber
              N M A L 10 base shape).card : ℝ) ≤
                fiberEnvelope N L)) :
    ManyDefectsSectorStabilityStatement
      C κ₀ A terminal := by
  intro _hES hPell
  exact
    manyDefectsSector_uniformLittleO_of_baseShapeFiberRealEnvelope
      hC κ₀ A terminal hPell fiberEnvelope
      hfiberRate hfiberNonneg hfiberDom

end

end BoundedRatioManyDefectsRealFibers
end PaperC
