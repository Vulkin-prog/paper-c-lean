import PaperC.Asymptotics.BoundedRatioManyDefectsDegreeTwoSum
import PaperC.Asymptotics.BoundedRatioManyDefectsRealFibers

set_option maxHeartbeats 3600000

/-!
# Assembly of the three mobile-degree branches in Lemma 17.26

The fixed-base/fixed-shape reduction has three mutually exclusive mobile
degrees.  Degree one already has a uniform `N^(1/2+o(1))` envelope, while
generalized Pell gives (possibly different) uniformly subpolynomial
envelopes for the two oriented degree-two branches.

This module leaves only the degree-at-least-three estimate abstract.  Given
one nonnegative uniformly subpolynomial envelope for that branch, the four
factors

* the common degree-one envelope;
* the left Pell residual;
* the right Pell residual;
* the degree-at-least-three envelope

are multiplied.  Eventual lower bounds by one make this product dominate
each individual branch, avoiding finite maxima and additive losses.
-/

namespace PaperC
namespace BoundedRatioManyDefectsDegreeAssembly

open BoundedRatioComponentHosts
open BoundedRatioDistinctKernelTwoDefects
open BoundedRatioManyDefectsDegreeTwoSum
open BoundedRatioManyDefectsFibers
open BoundedRatioManyDefectsFixedFibers
open BoundedRatioManyDefectsRealFibers
open PropositionSixteenOne

noncomputable section

/-! ## The common product envelope -/

/--
Product envelope for all three mobile-degree branches.  The two Pell
constants are kept separate because the left and right polynomial-box
statements produce independent existential constants.
-/
noncomputable def degreeAssemblyEnvelope
    (κ₀ : ℕ) (cLeft cRight : ℝ)
    (highEnvelope : ℕ → ℕ → ℝ)
    (N L : ℕ) : ℝ :=
  degreeOneFixedFiberEnvelope κ₀ N L *
    degreeTwoFixedFiberResidual κ₀ cLeft N L *
    degreeTwoFixedFiberResidual κ₀ cRight N L *
    highEnvelope N L

/-- The degree-one factor is nonnegative. -/
theorem degreeOneFixedFiberEnvelope_nonneg
    (κ₀ N L : ℕ) :
    0 ≤ degreeOneFixedFiberEnvelope κ₀ N L := by
  unfold degreeOneFixedFiberEnvelope
    smoothKernelChebyshevEnvelope
  positivity

/--
As soon as `N ≥ 1`, the degree-one factor is at least one.  This is the
elementary lower bound needed to let a product dominate the degree-two and
higher-degree branches.
-/
theorem one_le_degreeOneFixedFiberEnvelope
    (κ₀ L : ℕ) {N : ℕ} (hN : 1 ≤ N) :
    1 ≤ degreeOneFixedFiberEnvelope κ₀ N L := by
  have hsqrtN :
      1 ≤ Real.sqrt (N : ℝ) := by
    apply Real.one_le_sqrt.mpr
    exact_mod_cast hN
  have hsqrtK :
      1 ≤ Real.sqrt ((κ₀ : ℝ) + 1) := by
    apply Real.one_le_sqrt.mpr
    have hkappaNonneg : (0 : ℝ) ≤ (κ₀ : ℝ) :=
      Nat.cast_nonneg κ₀
    linarith
  have hsmooth :
      1 ≤ smoothKernelChebyshevEnvelope (L + 1) := by
    unfold smoothKernelChebyshevEnvelope
    rw [Real.one_le_exp_iff]
    have hlogTwo :
        0 ≤ Real.log (2 : ℝ) :=
      (Real.log_pos (by norm_num)).le
    have hratio :
        0 ≤ (((L + 1 : ℕ) : ℝ) /
          (Nat.log 2 (L + 1) : ℝ)) := by
      positivity
    positivity
  have hresidual :
      1 ≤
        (2 * Real.sqrt ((κ₀ : ℝ) + 1)) *
          smoothKernelChebyshevEnvelope (L + 1) := by
    have htwoSqrt :
        1 ≤ 2 * Real.sqrt ((κ₀ : ℝ) + 1) := by
      nlinarith
    exact one_le_mul_of_one_le_of_one_le htwoSqrt hsmooth
  unfold degreeOneFixedFiberEnvelope
  exact one_le_mul_of_one_le_of_one_le hsqrtN hresidual

/-- The full product is nonnegative when the abstract high-degree factor is. -/
theorem degreeAssemblyEnvelope_nonneg
    (κ₀ : ℕ) {cLeft cRight : ℝ}
    {highEnvelope : ℕ → ℕ → ℝ}
    (hhighNonneg : ∀ N L, 0 ≤ highEnvelope N L)
    (N L : ℕ) :
    0 ≤
      degreeAssemblyEnvelope
        κ₀ cLeft cRight highEnvelope N L := by
  have hdegreeOne :
      0 ≤ degreeOneFixedFiberEnvelope κ₀ N L :=
    degreeOneFixedFiberEnvelope_nonneg κ₀ N L
  have hdegreeTwoLeft :
      0 ≤ degreeTwoFixedFiberResidual κ₀ cLeft N L := by
    unfold degreeTwoFixedFiberResidual
      degreeTwoSignedDivisorEnvelope
      smoothKernelChebyshevEnvelope
      PellInput.expLogLogBound
    positivity
  have hdegreeTwoRight :
      0 ≤ degreeTwoFixedFiberResidual κ₀ cRight N L := by
    unfold degreeTwoFixedFiberResidual
      degreeTwoSignedDivisorEnvelope
      smoothKernelChebyshevEnvelope
      PellInput.expLogLogBound
    positivity
  unfold degreeAssemblyEnvelope
  exact
    mul_nonneg
      (mul_nonneg
        (mul_nonneg hdegreeOne hdegreeTwoLeft)
        hdegreeTwoRight)
      (hhighNonneg N L)

/--
The product keeps the degree-one `N^(1/2+o(1))` rate: the two Pell
residuals and the abstract high-degree residual are all subpolynomial.
-/
theorem degreeAssemblyEnvelope_uniformHalfPower
    {C : ℝ} (hC : 0 ≤ C) (κ₀ : ℕ)
    {cLeft cRight : ℝ}
    (hcLeft : 0 ≤ cLeft) (hcRight : 0 ≤ cRight)
    (highEnvelope : ℕ → ℕ → ℝ)
    (hhighRate :
      UniformSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C)
        highEnvelope) :
    UniformHalfPowerSubpolynomialOn
      (CriticalRunWindow.InRunLengthWindow C)
      (degreeAssemblyEnvelope
        κ₀ cLeft cRight highEnvelope) := by
  have hdegreeOne :=
    degreeOneFixedFiberEnvelope_uniformHalfPower hC κ₀
  have hdegreeTwoLeft :=
    degreeTwoFixedFiberResidual_uniformSubpolynomial
      hC hcLeft κ₀
  have hdegreeTwoRight :=
    degreeTwoFixedFiberResidual_uniformSubpolynomial
      hC hcRight κ₀
  have hleftProduct :=
    UniformHalfPower.mul_subpolynomial
      hdegreeOne hdegreeTwoLeft
  have hbothPell :=
    UniformHalfPower.mul_subpolynomial
      hleftProduct hdegreeTwoRight
  have hall :=
    UniformHalfPower.mul_subpolynomial
      hbothPell hhighRate
  change
    UniformHalfPowerSubpolynomialOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun N L =>
        degreeOneFixedFiberEnvelope κ₀ N L *
          degreeTwoFixedFiberResidual κ₀ cLeft N L *
          degreeTwoFixedFiberResidual κ₀ cRight N L *
          highEnvelope N L)
  exact hall

/-! ## Direct closure of the many-defects sector -/

/--
Assembly of the degree-one, degree-two and degree-at-least-three fixed
fibres.

The higher-degree hypotheses deliberately have the same local geometry as
the fixed-fibre estimates: `L ≤ N`, membership in the size-ten shape
container, and mobile degree at least three.  The theorem itself obtains
`L ≤ N` and `4 ≤ L+1` eventually from the critical run-length window.
-/
theorem manyDefectsSector_rates_of_degreeAssembly
    {C : ℝ} (hC : 0 ≤ C) (κ₀ A : ℕ)
    (terminal : TerminalPredicateFamily)
    (hPell : PellInput.GeneralizedPellPolynomialBoxStatement)
    (highEnvelope : ℕ → ℕ → ℝ)
    (hhighRate :
      UniformSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C)
        highEnvelope)
    (hhighNonneg :
      ∀ N L, 0 ≤ highEnvelope N L)
    (hhighOne :
      ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L,
        1 ≤ highEnvelope N L)
    (hhighLeft :
      ∀ {N M L base : ℕ},
        2 ≤ N →
        M ≤ κ₀ * N →
        L ≤ N →
        ∀ (shape :
          Finset (Fin (L + 1)) × Finset (Fin (L + 1))),
          shape ∈ boundedOffsetShapes L 10 →
          3 ≤ shape.2.card →
          ((leftBaseShapeFiber
            N M A L 10 base shape).card : ℝ) ≤
              highEnvelope N L)
    (hhighRight :
      ∀ {N M L base : ℕ},
        2 ≤ N →
        M ≤ κ₀ * N →
        L ≤ N →
        ∀ (shape :
          Finset (Fin (L + 1)) × Finset (Fin (L + 1))),
          shape ∈ boundedOffsetShapes L 10 →
          3 ≤ shape.1.card →
          ((rightBaseShapeFiber
            N M A L 10 base shape).card : ℝ) ≤
              highEnvelope N L) :
    UniformRationalPowerInBoundedRatioWindow 3 2 C κ₀
        (sectorResidualMass A terminal .manyDefects) ∧
      UniformLittleOInBoundedRatioWindow C κ₀
        (sectorResidualMass A terminal .manyDefects) := by
  obtain ⟨cLeft, hcLeft, NpellLeft, hpellLeft⟩ :=
    generalizedPell_implies_card_left_degreeTwoFiber_le_residual
      hPell κ₀ 10
  obtain ⟨cRight, hcRight, NpellRight, hpellRight⟩ :=
    generalizedPell_implies_card_right_degreeTwoFiber_le_residual
      hPell κ₀ 10
  obtain ⟨NoneLeft, honeLeft⟩ :=
    degreeTwoFixedFiberResidual_eventually_one_le
      hcLeft κ₀
  obtain ⟨NoneRight, honeRight⟩ :=
    degreeTwoFixedFiberResidual_eventually_one_le
      hcRight κ₀
  obtain ⟨NhighOne, hhighOne⟩ := hhighOne
  have hheightRate :=
    CriticalRationalMassEnvelopes.runLengthAddOne_uniformSubpolynomial
      hC
  obtain ⟨Nheight, hheight⟩ :=
    hheightRate 1 (by omega)
  obtain ⟨Nfour, hfour⟩ :=
    DependencyEdgesCritical.runLengthAddOne_tends_to_infinity
      hC 4
  let fiberEnvelope : ℕ → ℕ → ℝ :=
    degreeAssemblyEnvelope
      κ₀ cLeft cRight highEnvelope
  have hfiberRate :
      UniformHalfPowerSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C)
        fiberEnvelope := by
    simpa only [fiberEnvelope] using
      degreeAssemblyEnvelope_uniformHalfPower
        hC κ₀ hcLeft hcRight highEnvelope hhighRate
  have hfiberNonneg :
      ∀ N L, 0 ≤ fiberEnvelope N L := by
    intro N L
    simpa only [fiberEnvelope] using
      degreeAssemblyEnvelope_nonneg
        κ₀ hhighNonneg N L
  have hfiberDom :
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
                fiberEnvelope N L) := by
    refine
      ⟨max NpellLeft
        (max NpellRight
          (max NoneLeft
            (max NoneRight
              (max NhighOne
                (max Nheight (max Nfour 2)))))),
        ?_⟩
    intro N hN M L hNM hMκ hrun
    have hNpellLeft :
        NpellLeft ≤ N :=
      (le_max_left _ _).trans hN
    have htail₁ :
        max NpellRight
          (max NoneLeft
            (max NoneRight
              (max NhighOne
                (max Nheight (max Nfour 2))))) ≤ N :=
      (le_max_right _ _).trans hN
    have hNpellRight :
        NpellRight ≤ N :=
      (le_max_left _ _).trans htail₁
    have htail₂ :
        max NoneLeft
          (max NoneRight
            (max NhighOne
              (max Nheight (max Nfour 2)))) ≤ N :=
      (le_max_right _ _).trans htail₁
    have hNoneLeft :
        NoneLeft ≤ N :=
      (le_max_left _ _).trans htail₂
    have htail₃ :
        max NoneRight
          (max NhighOne
            (max Nheight (max Nfour 2))) ≤ N :=
      (le_max_right _ _).trans htail₂
    have hNoneRight :
        NoneRight ≤ N :=
      (le_max_left _ _).trans htail₃
    have htail₄ :
        max NhighOne
          (max Nheight (max Nfour 2)) ≤ N :=
      (le_max_right _ _).trans htail₃
    have hNhighOne :
        NhighOne ≤ N :=
      (le_max_left _ _).trans htail₄
    have htail₅ :
        max Nheight (max Nfour 2) ≤ N :=
      (le_max_right _ _).trans htail₄
    have hNheight :
        Nheight ≤ N :=
      (le_max_left _ _).trans htail₅
    have htail₆ :
        max Nfour 2 ≤ N :=
      (le_max_right _ _).trans htail₅
    have hNfour :
        Nfour ≤ N :=
      (le_max_left _ _).trans htail₆
    have hNtwo :
        2 ≤ N :=
      (le_max_right _ _).trans htail₆
    have hheightReal :
        (((L + 1 : ℕ) : ℝ)) ≤ (N : ℝ) := by
      have hbound :=
        hheight N hNheight L hrun
      have hnonneg :
          0 ≤ (((L + 1 : ℕ) : ℝ)) := by
        positivity
      simpa only [abs_of_nonneg hnonneg, pow_one] using hbound
    have hheightNat :
        L + 1 ≤ N := by
      exact_mod_cast hheightReal
    have hL : L ≤ N := by
      omega
    have hBfour :
        4 ≤ L + 1 :=
      hfour N hNfour L hrun
    have hdegreeOneOne :
        1 ≤ degreeOneFixedFiberEnvelope κ₀ N L :=
      one_le_degreeOneFixedFiberEnvelope
        κ₀ L (show 1 ≤ N by omega)
    have hdegreeTwoLeftOne :
        1 ≤
          degreeTwoFixedFiberResidual
            κ₀ cLeft N L :=
      honeLeft N hNoneLeft L
    have hdegreeTwoRightOne :
        1 ≤
          degreeTwoFixedFiberResidual
            κ₀ cRight N L :=
      honeRight N hNoneRight L
    have hhighEnvelopeOne :
        1 ≤ highEnvelope N L :=
      hhighOne N hNhighOne L
    have hdegreeOneNonneg :
        0 ≤ degreeOneFixedFiberEnvelope κ₀ N L :=
      degreeOneFixedFiberEnvelope_nonneg κ₀ N L
    have hdegreeTwoLeftNonneg :
        0 ≤
          degreeTwoFixedFiberResidual
            κ₀ cLeft N L := by
      unfold degreeTwoFixedFiberResidual
        degreeTwoSignedDivisorEnvelope
        smoothKernelChebyshevEnvelope
        PellInput.expLogLogBound
      positivity
    have hdegreeTwoRightNonneg :
        0 ≤
          degreeTwoFixedFiberResidual
            κ₀ cRight N L := by
      unfold degreeTwoFixedFiberResidual
        degreeTwoSignedDivisorEnvelope
        smoothKernelChebyshevEnvelope
        PellInput.expLogLogBound
      positivity
    have hhighEnvelopeNonneg :
        0 ≤ highEnvelope N L :=
      hhighNonneg N L
    constructor
    · intro base _hbase shape hshape
      have hshapeData :=
        mem_boundedOffsetShapes.mp hshape
      have hmobilePos :
          0 < shape.2.card :=
        Finset.card_pos.mpr hshapeData.2.1
      by_cases hone : shape.2.card = 1
      · have hfinite :=
          card_leftBaseShapeFiber_degree_one_cast_le_envelope
            (κ₀ := κ₀) (M := M) (A := A)
            (K := 10) (base := base)
            hNtwo hMκ hL hBfour shape hone
        calc
          ((leftBaseShapeFiber
              N M A L 10 base shape).card : ℝ) ≤
              degreeOneFixedFiberEnvelope κ₀ N L :=
            hfinite
          _ ≤
              degreeOneFixedFiberEnvelope κ₀ N L *
                degreeTwoFixedFiberResidual
                  κ₀ cLeft N L := by
            simpa only [mul_one] using
              mul_le_mul_of_nonneg_left
                hdegreeTwoLeftOne hdegreeOneNonneg
          _ ≤
              (degreeOneFixedFiberEnvelope κ₀ N L *
                degreeTwoFixedFiberResidual
                  κ₀ cLeft N L) *
                degreeTwoFixedFiberResidual
                  κ₀ cRight N L := by
            simpa only [mul_one] using
              mul_le_mul_of_nonneg_left
                hdegreeTwoRightOne
                (mul_nonneg hdegreeOneNonneg
                  hdegreeTwoLeftNonneg)
          _ ≤
              (degreeOneFixedFiberEnvelope κ₀ N L *
                degreeTwoFixedFiberResidual
                  κ₀ cLeft N L *
                degreeTwoFixedFiberResidual
                  κ₀ cRight N L) *
                highEnvelope N L := by
            simpa only [mul_one] using
              mul_le_mul_of_nonneg_left
                hhighEnvelopeOne
                (mul_nonneg
                  (mul_nonneg hdegreeOneNonneg
                    hdegreeTwoLeftNonneg)
                  hdegreeTwoRightNonneg)
          _ = fiberEnvelope N L := by
            rfl
      · by_cases htwo : shape.2.card = 2
        · have hfinite :=
            hpellLeft N hNpellLeft M A L base
              hNM hMκ hL hBfour shape htwo
          calc
            ((leftBaseShapeFiber
                N M A L 10 base shape).card : ℝ) ≤
                degreeTwoFixedFiberResidual
                  κ₀ cLeft N L :=
              hfinite
            _ ≤
                degreeOneFixedFiberEnvelope κ₀ N L *
                  degreeTwoFixedFiberResidual
                    κ₀ cLeft N L := by
              simpa only [one_mul] using
                mul_le_mul_of_nonneg_right
                  hdegreeOneOne hdegreeTwoLeftNonneg
            _ ≤
                (degreeOneFixedFiberEnvelope κ₀ N L *
                  degreeTwoFixedFiberResidual
                    κ₀ cLeft N L) *
                  degreeTwoFixedFiberResidual
                    κ₀ cRight N L := by
              simpa only [mul_one] using
                mul_le_mul_of_nonneg_left
                  hdegreeTwoRightOne
                  (mul_nonneg hdegreeOneNonneg
                    hdegreeTwoLeftNonneg)
            _ ≤
                (degreeOneFixedFiberEnvelope κ₀ N L *
                  degreeTwoFixedFiberResidual
                    κ₀ cLeft N L *
                  degreeTwoFixedFiberResidual
                    κ₀ cRight N L) *
                  highEnvelope N L := by
              simpa only [mul_one] using
                mul_le_mul_of_nonneg_left
                  hhighEnvelopeOne
                  (mul_nonneg
                    (mul_nonneg hdegreeOneNonneg
                      hdegreeTwoLeftNonneg)
                    hdegreeTwoRightNonneg)
            _ = fiberEnvelope N L := by
              rfl
        · have hthree :
              3 ≤ shape.2.card := by
            omega
          have hfinite :=
            hhighLeft (base := base) hNtwo hMκ hL
              shape hshape hthree
          have hbaseOne :
              1 ≤
                degreeOneFixedFiberEnvelope κ₀ N L *
                  degreeTwoFixedFiberResidual
                    κ₀ cLeft N L *
                  degreeTwoFixedFiberResidual
                    κ₀ cRight N L :=
            one_le_mul_of_one_le_of_one_le
              (one_le_mul_of_one_le_of_one_le
                hdegreeOneOne hdegreeTwoLeftOne)
              hdegreeTwoRightOne
          calc
            ((leftBaseShapeFiber
                N M A L 10 base shape).card : ℝ) ≤
                highEnvelope N L :=
              hfinite
            _ ≤
                (degreeOneFixedFiberEnvelope κ₀ N L *
                  degreeTwoFixedFiberResidual
                    κ₀ cLeft N L *
                  degreeTwoFixedFiberResidual
                    κ₀ cRight N L) *
                  highEnvelope N L := by
              simpa only [one_mul] using
                mul_le_mul_of_nonneg_right
                  hbaseOne hhighEnvelopeNonneg
            _ = fiberEnvelope N L := by
              rfl
    · intro base _hbase shape hshape
      have hshapeData :=
        mem_boundedOffsetShapes.mp hshape
      have hmobilePos :
          0 < shape.1.card :=
        Finset.card_pos.mpr hshapeData.1
      by_cases hone : shape.1.card = 1
      · have hfinite :=
          card_rightBaseShapeFiber_degree_one_cast_le_envelope
            (κ₀ := κ₀) (M := M) (A := A)
            (K := 10) (base := base)
            hNtwo hMκ hL hBfour shape hone
        calc
          ((rightBaseShapeFiber
              N M A L 10 base shape).card : ℝ) ≤
              degreeOneFixedFiberEnvelope κ₀ N L :=
            hfinite
          _ ≤
              degreeOneFixedFiberEnvelope κ₀ N L *
                degreeTwoFixedFiberResidual
                  κ₀ cLeft N L := by
            simpa only [mul_one] using
              mul_le_mul_of_nonneg_left
                hdegreeTwoLeftOne hdegreeOneNonneg
          _ ≤
              (degreeOneFixedFiberEnvelope κ₀ N L *
                degreeTwoFixedFiberResidual
                  κ₀ cLeft N L) *
                degreeTwoFixedFiberResidual
                  κ₀ cRight N L := by
            simpa only [mul_one] using
              mul_le_mul_of_nonneg_left
                hdegreeTwoRightOne
                (mul_nonneg hdegreeOneNonneg
                  hdegreeTwoLeftNonneg)
          _ ≤
              (degreeOneFixedFiberEnvelope κ₀ N L *
                degreeTwoFixedFiberResidual
                  κ₀ cLeft N L *
                degreeTwoFixedFiberResidual
                  κ₀ cRight N L) *
                highEnvelope N L := by
            simpa only [mul_one] using
              mul_le_mul_of_nonneg_left
                hhighEnvelopeOne
                (mul_nonneg
                  (mul_nonneg hdegreeOneNonneg
                    hdegreeTwoLeftNonneg)
                  hdegreeTwoRightNonneg)
          _ = fiberEnvelope N L := by
            rfl
      · by_cases htwo : shape.1.card = 2
        · have hfinite :=
            hpellRight N hNpellRight M A L base
              hNM hMκ hL hBfour shape htwo
          have hleftProductOne :
              1 ≤
                degreeOneFixedFiberEnvelope κ₀ N L *
                  degreeTwoFixedFiberResidual
                    κ₀ cLeft N L :=
            one_le_mul_of_one_le_of_one_le
              hdegreeOneOne hdegreeTwoLeftOne
          calc
            ((rightBaseShapeFiber
                N M A L 10 base shape).card : ℝ) ≤
                degreeTwoFixedFiberResidual
                  κ₀ cRight N L :=
              hfinite
            _ ≤
                (degreeOneFixedFiberEnvelope κ₀ N L *
                  degreeTwoFixedFiberResidual
                    κ₀ cLeft N L) *
                  degreeTwoFixedFiberResidual
                    κ₀ cRight N L := by
              simpa only [one_mul] using
                mul_le_mul_of_nonneg_right
                  hleftProductOne hdegreeTwoRightNonneg
            _ ≤
                (degreeOneFixedFiberEnvelope κ₀ N L *
                  degreeTwoFixedFiberResidual
                    κ₀ cLeft N L *
                  degreeTwoFixedFiberResidual
                    κ₀ cRight N L) *
                  highEnvelope N L := by
              simpa only [mul_one] using
                mul_le_mul_of_nonneg_left
                  hhighEnvelopeOne
                  (mul_nonneg
                    (mul_nonneg hdegreeOneNonneg
                      hdegreeTwoLeftNonneg)
                    hdegreeTwoRightNonneg)
            _ = fiberEnvelope N L := by
              rfl
        · have hthree :
              3 ≤ shape.1.card := by
            omega
          have hfinite :=
            hhighRight (base := base) hNtwo hMκ hL
              shape hshape hthree
          have hbaseOne :
              1 ≤
                degreeOneFixedFiberEnvelope κ₀ N L *
                  degreeTwoFixedFiberResidual
                    κ₀ cLeft N L *
                  degreeTwoFixedFiberResidual
                    κ₀ cRight N L :=
            one_le_mul_of_one_le_of_one_le
              (one_le_mul_of_one_le_of_one_le
                hdegreeOneOne hdegreeTwoLeftOne)
              hdegreeTwoRightOne
          calc
            ((rightBaseShapeFiber
                N M A L 10 base shape).card : ℝ) ≤
                highEnvelope N L :=
              hfinite
            _ ≤
                (degreeOneFixedFiberEnvelope κ₀ N L *
                  degreeTwoFixedFiberResidual
                    κ₀ cLeft N L *
                  degreeTwoFixedFiberResidual
                    κ₀ cRight N L) *
                  highEnvelope N L := by
              simpa only [one_mul] using
                mul_le_mul_of_nonneg_right
                  hbaseOne hhighEnvelopeNonneg
            _ = fiberEnvelope N L := by
              rfl
  exact
    manyDefectsSector_rates_of_baseShapeFiberRealEnvelope
      hC κ₀ A terminal hPell fiberEnvelope
      hfiberRate hfiberNonneg hfiberDom

/--
Source-exact `N^(3/2+o)` consequence of the three mobile-degree branch
assembly.
-/
theorem manyDefectsSector_uniformThreeHalves_of_degreeAssembly
    {C : ℝ} (hC : 0 ≤ C) (κ₀ A : ℕ)
    (terminal : TerminalPredicateFamily)
    (hPell : PellInput.GeneralizedPellPolynomialBoxStatement)
    (highEnvelope : ℕ → ℕ → ℝ)
    (hhighRate :
      UniformSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C)
        highEnvelope)
    (hhighNonneg :
      ∀ N L, 0 ≤ highEnvelope N L)
    (hhighOne :
      ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L,
        1 ≤ highEnvelope N L)
    (hhighLeft :
      ∀ {N M L base : ℕ},
        2 ≤ N →
        M ≤ κ₀ * N →
        L ≤ N →
        ∀ (shape :
          Finset (Fin (L + 1)) × Finset (Fin (L + 1))),
          shape ∈ boundedOffsetShapes L 10 →
          3 ≤ shape.2.card →
          ((leftBaseShapeFiber
            N M A L 10 base shape).card : ℝ) ≤
              highEnvelope N L)
    (hhighRight :
      ∀ {N M L base : ℕ},
        2 ≤ N →
        M ≤ κ₀ * N →
        L ≤ N →
        ∀ (shape :
          Finset (Fin (L + 1)) × Finset (Fin (L + 1))),
          shape ∈ boundedOffsetShapes L 10 →
          3 ≤ shape.1.card →
          ((rightBaseShapeFiber
            N M A L 10 base shape).card : ℝ) ≤
              highEnvelope N L) :
    UniformRationalPowerInBoundedRatioWindow 3 2 C κ₀
      (sectorResidualMass A terminal .manyDefects) :=
  (manyDefectsSector_rates_of_degreeAssembly
    hC κ₀ A terminal hPell highEnvelope
    hhighRate hhighNonneg hhighOne hhighLeft hhighRight).1

/--
Quadratic little-oh consequence of the three mobile-degree branch assembly.
-/
theorem manyDefectsSector_uniformLittleO_of_degreeAssembly
    {C : ℝ} (hC : 0 ≤ C) (κ₀ A : ℕ)
    (terminal : TerminalPredicateFamily)
    (hPell : PellInput.GeneralizedPellPolynomialBoxStatement)
    (highEnvelope : ℕ → ℕ → ℝ)
    (hhighRate :
      UniformSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C)
        highEnvelope)
    (hhighNonneg :
      ∀ N L, 0 ≤ highEnvelope N L)
    (hhighOne :
      ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L,
        1 ≤ highEnvelope N L)
    (hhighLeft :
      ∀ {N M L base : ℕ},
        2 ≤ N →
        M ≤ κ₀ * N →
        L ≤ N →
        ∀ (shape :
          Finset (Fin (L + 1)) × Finset (Fin (L + 1))),
          shape ∈ boundedOffsetShapes L 10 →
          3 ≤ shape.2.card →
          ((leftBaseShapeFiber
            N M A L 10 base shape).card : ℝ) ≤
              highEnvelope N L)
    (hhighRight :
      ∀ {N M L base : ℕ},
        2 ≤ N →
        M ≤ κ₀ * N →
        L ≤ N →
        ∀ (shape :
          Finset (Fin (L + 1)) × Finset (Fin (L + 1))),
          shape ∈ boundedOffsetShapes L 10 →
          3 ≤ shape.1.card →
          ((rightBaseShapeFiber
            N M A L 10 base shape).card : ℝ) ≤
              highEnvelope N L) :
    UniformLittleOInBoundedRatioWindow C κ₀
      (sectorResidualMass A terminal .manyDefects) :=
  (manyDefectsSector_rates_of_degreeAssembly
    hC κ₀ A terminal hPell highEnvelope
    hhighRate hhighNonneg hhighOne hhighLeft hhighRight).2

end

end BoundedRatioManyDefectsDegreeAssembly
end PaperC
