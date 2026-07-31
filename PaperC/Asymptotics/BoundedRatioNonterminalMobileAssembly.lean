import PaperC.Asymptotics.BoundedRatioManyDefectsDegreeTwoSum
import PaperC.Asymptotics.BoundedRatioManyDefectsEvertseSum
import PaperC.Asymptotics.BoundedRatioNonterminalRealHosts
import PaperC.Asymptotics.LinearPower

set_option maxHeartbeats 3600000

/-!
# Mobile-fibre assembly for the moderate branch of Lemma 17.28

For one fixed base and one fixed component shape, the mobile degree in the
nonterminal host disjunction is at least two.  Generalized Pell handles
degree two, with independent constants in the two orientations, while
Evertse--Silverman handles every degree between three and ten.

This file multiplies the three nonnegative, eventually-at-least-one
residuals.  The resulting fixed-fibre envelope is uniformly `N^o(1)`.
After multiplying by the interval width and the polynomial shape count, the
complete moderate host population is `N^(1+o(1))`, conditional only on a
separate linear-subpolynomial envelope for the two-singleton shapes.
-/

namespace PaperC

namespace UniformLinear

/--
Multiplying a linear-subpolynomial quantity by a subpolynomial quantity
preserves the linear-subpolynomial rate.
-/
theorem subpolynomial_mul
    {admissible : ℕ → ℕ → Prop}
    {s f : ℕ → ℕ → ℝ}
    (hs : UniformSubpolynomialOn admissible s)
    (hf : UniformLinearSubpolynomialOn admissible f) :
    UniformLinearSubpolynomialOn admissible
      (fun N L => s N L * f N L) := by
  intro k hk
  have htwok : 0 < 2 * k :=
    Nat.mul_pos (by omega) hk
  obtain ⟨Ns, hNs⟩ := hs (2 * k) htwok
  obtain ⟨Nf, hNf⟩ := hf (2 * k) htwok
  refine ⟨max Ns Nf, ?_⟩
  intro N hN L hNL
  have hsBound :
      |s N L| ^ (2 * k) ≤ (N : ℝ) :=
    hNs N ((le_max_left _ _).trans hN) L hNL
  have hfBound :
      |f N L| ^ (2 * k) ≤
        (N : ℝ) ^ (2 * k + 1) :=
    hNf N ((le_max_right _ _).trans hN) L hNL
  have hsq :
      (|s N L * f N L| ^ k) ^ 2 ≤
        ((N : ℝ) ^ (k + 1)) ^ 2 := by
    calc
      (|s N L * f N L| ^ k) ^ 2 =
          |s N L| ^ (2 * k) *
            |f N L| ^ (2 * k) := by
        rw [abs_mul, mul_pow, mul_pow]
        simp only [← pow_mul]
        congr 2 <;> omega
      _ ≤
          (N : ℝ) *
            (N : ℝ) ^ (2 * k + 1) :=
        mul_le_mul hsBound hfBound
          (by positivity) (by positivity)
      _ = ((N : ℝ) ^ (k + 1)) ^ 2 := by
        calc
          (N : ℝ) * (N : ℝ) ^ (2 * k + 1) =
              (N : ℝ) ^ (2 * k + 1) * (N : ℝ) := by
            ring
          _ = (N : ℝ) ^ ((2 * k + 1) + 1) :=
            (pow_succ _ _).symm
          _ = (N : ℝ) ^ ((k + 1) * 2) := by
            congr 1
            omega
          _ = ((N : ℝ) ^ (k + 1)) ^ 2 :=
            pow_mul _ _ _
  exact
    (sq_le_sq₀ (by positivity)
      (show 0 ≤ (N : ℝ) ^ (k + 1) by positivity)).mp hsq

/--
The pointwise maximum of two nonnegative linear-subpolynomial envelopes is
again linear-subpolynomial.
-/
theorem max_of_nonnegative
    {admissible : ℕ → ℕ → Prop}
    {f g : ℕ → ℕ → ℝ}
    (hf : UniformLinearSubpolynomialOn admissible f)
    (hg : UniformLinearSubpolynomialOn admissible g)
    (hfNonneg : ∀ N L, 0 ≤ f N L)
    (hgNonneg : ∀ N L, 0 ≤ g N L) :
    UniformLinearSubpolynomialOn admissible
      (fun N L => max (f N L) (g N L)) := by
  intro k hk
  obtain ⟨Nf, hNf⟩ := hf k hk
  obtain ⟨Ng, hNg⟩ := hg k hk
  refine ⟨max Nf Ng, ?_⟩
  intro N hN L hNL
  have hfBound :=
    hNf N ((le_max_left _ _).trans hN) L hNL
  have hgBound :=
    hNg N ((le_max_right _ _).trans hN) L hNL
  rw [abs_of_nonneg (hfNonneg N L)] at hfBound
  rw [abs_of_nonneg (hgNonneg N L)] at hgBound
  rw [abs_of_nonneg
    (le_max_of_le_left (hfNonneg N L))]
  by_cases hfg : f N L ≤ g N L
  · simpa only [max_eq_right hfg] using hgBound
  · have hgf : g N L ≤ f N L :=
      (lt_of_not_ge hfg).le
    simpa only [max_eq_left hgf] using hfBound

end UniformLinear

namespace BoundedRatioNonterminalMobileAssembly

open BoundedRatioComponentHosts
open BoundedRatioDistinctKernelTwoDefects
open BoundedRatioManyDefectsDegreeTwoSum
open BoundedRatioManyDefectsEvertseSum
open BoundedRatioManyDefectsFibers
open BoundedRatioNonterminalHostCounts
open BoundedRatioNonterminalRealHosts
open EvertseSilvermanInput
open PropositionSixteenOne

noncomputable section

/-! ## One common envelope for every mobile degree at least two -/

/--
Product of the left and right degree-two residuals and the common
degree-at-least-three Evertse residual.
-/
noncomputable def mobileDegreeAtLeastTwoEnvelope
    (κ₀ : ℕ) (cLeft cRight : ℝ)
    (N L : ℕ) : ℝ :=
  degreeTwoFixedFiberResidual κ₀ cLeft N L *
    degreeTwoFixedFiberResidual κ₀ cRight N L *
    (evertseCommonFixedFiberResidual κ₀ N L : ℝ)

/-- The common mobile envelope is pointwise nonnegative. -/
theorem mobileDegreeAtLeastTwoEnvelope_nonneg
    (κ₀ : ℕ) (cLeft cRight : ℝ)
    (N L : ℕ) :
    0 ≤ mobileDegreeAtLeastTwoEnvelope
      κ₀ cLeft cRight N L := by
  unfold mobileDegreeAtLeastTwoEnvelope
    degreeTwoFixedFiberResidual
    degreeTwoSignedDivisorEnvelope
    smoothKernelChebyshevEnvelope
    PellInput.expLogLogBound
  positivity

/-- All three fixed residual factors are uniformly subpolynomial. -/
theorem mobileDegreeAtLeastTwoEnvelope_uniformSubpolynomial
    {C : ℝ} (hC : 0 ≤ C) (κ₀ : ℕ)
    {cLeft cRight : ℝ}
    (hcLeft : 0 ≤ cLeft) (hcRight : 0 ≤ cRight) :
    UniformSubpolynomialOn
      (CriticalRunWindow.InRunLengthWindow C)
      (mobileDegreeAtLeastTwoEnvelope
        κ₀ cLeft cRight) := by
  have hleft :=
    degreeTwoFixedFiberResidual_uniformSubpolynomial
      hC hcLeft κ₀
  have hright :=
    degreeTwoFixedFiberResidual_uniformSubpolynomial
      hC hcRight κ₀
  have hevertse :=
    evertseCommonFixedFiberResidual_uniformSubpolynomial
      hC κ₀
  have hproduct :=
    ExpSqrtLog.uniformSubpolynomialOn_mul
      (ExpSqrtLog.uniformSubpolynomialOn_mul
        hleft hright)
      hevertse
  change
    UniformSubpolynomialOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun N L =>
        degreeTwoFixedFiberResidual κ₀ cLeft N L *
          degreeTwoFixedFiberResidual κ₀ cRight N L *
          (evertseCommonFixedFiberResidual κ₀ N L : ℝ))
  exact hproduct

/--
The common mobile product is eventually at least one; the threshold is
uniform in the run length.
-/
theorem mobileDegreeAtLeastTwoEnvelope_eventually_one_le
    (κ₀ : ℕ) {cLeft cRight : ℝ}
    (hcLeft : 0 ≤ cLeft) (hcRight : 0 ≤ cRight) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L,
      1 ≤ mobileDegreeAtLeastTwoEnvelope
        κ₀ cLeft cRight N L := by
  obtain ⟨Nleft, hleft⟩ :=
    degreeTwoFixedFiberResidual_eventually_one_le
      hcLeft κ₀
  obtain ⟨Nright, hright⟩ :=
    degreeTwoFixedFiberResidual_eventually_one_le
      hcRight κ₀
  refine ⟨max Nleft Nright, ?_⟩
  intro N hN L
  have hleftOne :=
    hleft N ((le_max_left _ _).trans hN) L
  have hrightOne :=
    hright N ((le_max_right _ _).trans hN) L
  have hevertseNat :=
    one_le_evertseCommonFixedFiberResidual κ₀ N L
  have hevertse :
      (1 : ℝ) ≤
        (evertseCommonFixedFiberResidual κ₀ N L : ℝ) := by
    exact_mod_cast hevertseNat
  unfold mobileDegreeAtLeastTwoEnvelope
  exact
    one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le
        hleftOne hrightOne)
      hevertse

/--
Evertse--Silverman and generalized Pell produce one common
subpolynomial envelope for every fixed-base fibre whose mobile degree is at
least two, in either orientation.
-/
theorem
    evertseSilverman_generalizedPell_imply_exists_mobileDegreeAtLeastTwoEnvelope
    {C : ℝ} (hC : 0 ≤ C) (κ₀ : ℕ)
    (hES : EvertseSilvermanAbscissaStatement)
    (hPell : PellInput.GeneralizedPellPolynomialBoxStatement) :
    ∃ cLeft cRight : ℝ,
      0 ≤ cLeft ∧ 0 ≤ cRight ∧
      UniformSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C)
        (mobileDegreeAtLeastTwoEnvelope
          κ₀ cLeft cRight) ∧
      (∀ N L,
        0 ≤ mobileDegreeAtLeastTwoEnvelope
          κ₀ cLeft cRight N L) ∧
      ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ M A L,
        2 * N ≤ M →
        M ≤ κ₀ * N →
        CriticalRunWindow.InRunLengthWindow C N L →
        (∀ shape ∈ boundedOffsetShapes L 10,
          2 ≤ shape.2.card →
          ∀ base ∈ boundedStartBases N M,
            ((leftBaseShapeFiber
              N M A L 10 base shape).card : ℝ) ≤
              mobileDegreeAtLeastTwoEnvelope
                κ₀ cLeft cRight N L) ∧
        (∀ shape ∈ boundedOffsetShapes L 10,
          2 ≤ shape.1.card →
          ∀ base ∈ boundedStartBases N M,
            ((rightBaseShapeFiber
              N M A L 10 base shape).card : ℝ) ≤
              mobileDegreeAtLeastTwoEnvelope
                κ₀ cLeft cRight N L) := by
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
  have hheightRate :=
    CriticalRationalMassEnvelopes.runLengthAddOne_uniformSubpolynomial
      hC
  obtain ⟨Nheight, hheight⟩ :=
    hheightRate 1 (by omega)
  obtain ⟨Nfour, hfour⟩ :=
    DependencyEdgesCritical.runLengthAddOne_tends_to_infinity
      hC 4
  refine
    ⟨cLeft, cRight, hcLeft, hcRight,
      mobileDegreeAtLeastTwoEnvelope_uniformSubpolynomial
        hC κ₀ hcLeft hcRight,
      mobileDegreeAtLeastTwoEnvelope_nonneg
        κ₀ cLeft cRight,
      max NpellLeft
        (max NpellRight
          (max NoneLeft
            (max NoneRight
              (max Nheight (max Nfour 2))))),
      ?_⟩
  intro N hN M A L hNM hMκ hrun
  have hNpellLeft : NpellLeft ≤ N :=
    (le_max_left _ _).trans hN
  have htail₁ :
      max NpellRight
        (max NoneLeft
          (max NoneRight
            (max Nheight (max Nfour 2)))) ≤ N :=
    (le_max_right _ _).trans hN
  have hNpellRight : NpellRight ≤ N :=
    (le_max_left _ _).trans htail₁
  have htail₂ :
      max NoneLeft
        (max NoneRight
          (max Nheight (max Nfour 2))) ≤ N :=
    (le_max_right _ _).trans htail₁
  have hNoneLeft : NoneLeft ≤ N :=
    (le_max_left _ _).trans htail₂
  have htail₃ :
      max NoneRight
        (max Nheight (max Nfour 2)) ≤ N :=
    (le_max_right _ _).trans htail₂
  have hNoneRight : NoneRight ≤ N :=
    (le_max_left _ _).trans htail₃
  have htail₄ :
      max Nheight (max Nfour 2) ≤ N :=
    (le_max_right _ _).trans htail₃
  have hNheight : Nheight ≤ N :=
    (le_max_left _ _).trans htail₄
  have htail₅ :
      max Nfour 2 ≤ N :=
    (le_max_right _ _).trans htail₄
  have hNfour : Nfour ≤ N :=
    (le_max_left _ _).trans htail₅
  have hNtwo : 2 ≤ N :=
    (le_max_right _ _).trans htail₅
  have hheightReal :
      (((L + 1 : ℕ) : ℝ)) ≤ (N : ℝ) := by
    have hbound :=
      hheight N hNheight L hrun
    have hnonneg :
        0 ≤ (((L + 1 : ℕ) : ℝ)) := by
      positivity
    simpa only [abs_of_nonneg hnonneg, pow_one] using hbound
  have hheightNat : L + 1 ≤ N := by
    exact_mod_cast hheightReal
  have hL : L ≤ N := by
    omega
  have hBfour : 4 ≤ L + 1 :=
    hfour N hNfour L hrun
  have hleftOne :
      1 ≤ degreeTwoFixedFiberResidual
        κ₀ cLeft N L :=
    honeLeft N hNoneLeft L
  have hrightOne :
      1 ≤ degreeTwoFixedFiberResidual
        κ₀ cRight N L :=
    honeRight N hNoneRight L
  have hevertseOne :
      (1 : ℝ) ≤
        (evertseCommonFixedFiberResidual κ₀ N L : ℝ) := by
    exact_mod_cast
      one_le_evertseCommonFixedFiberResidual κ₀ N L
  have hleftNonneg :
      0 ≤ degreeTwoFixedFiberResidual
        κ₀ cLeft N L := by
    unfold degreeTwoFixedFiberResidual
      degreeTwoSignedDivisorEnvelope
      smoothKernelChebyshevEnvelope
      PellInput.expLogLogBound
    positivity
  have hrightNonneg :
      0 ≤ degreeTwoFixedFiberResidual
        κ₀ cRight N L := by
    unfold degreeTwoFixedFiberResidual
      degreeTwoSignedDivisorEnvelope
      smoothKernelChebyshevEnvelope
      PellInput.expLogLogBound
    positivity
  have hevertseNonneg :
      0 ≤
        (evertseCommonFixedFiberResidual κ₀ N L : ℝ) := by
    positivity
  constructor
  · intro shape hshape hdegree base _hbase
    by_cases htwo : shape.2.card = 2
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
            degreeTwoFixedFiberResidual κ₀ cLeft N L *
              degreeTwoFixedFiberResidual κ₀ cRight N L := by
          simpa only [mul_one] using
            mul_le_mul_of_nonneg_left
              hrightOne hleftNonneg
        _ ≤
            (degreeTwoFixedFiberResidual κ₀ cLeft N L *
              degreeTwoFixedFiberResidual κ₀ cRight N L) *
              (evertseCommonFixedFiberResidual κ₀ N L : ℝ) := by
          simpa only [mul_one] using
            mul_le_mul_of_nonneg_left
              hevertseOne
              (mul_nonneg hleftNonneg hrightNonneg)
        _ =
            mobileDegreeAtLeastTwoEnvelope
              κ₀ cLeft cRight N L := rfl
    · have hthree : 3 ≤ shape.2.card := by
        omega
      have hfiniteNat :=
        card_leftBaseShapeFiber_degree_at_least_three_le_common
          hES (κ₀ := κ₀) (M := M)
            (A := A) (base := base)
            hNtwo hMκ hL shape hshape hthree
      have hfinite :
          ((leftBaseShapeFiber
            N M A L 10 base shape).card : ℝ) ≤
            (evertseCommonFixedFiberResidual κ₀ N L : ℝ) := by
        exact_mod_cast hfiniteNat
      have hpairOne :
          (1 : ℝ) ≤
            degreeTwoFixedFiberResidual κ₀ cLeft N L *
              degreeTwoFixedFiberResidual κ₀ cRight N L :=
        one_le_mul_of_one_le_of_one_le
          hleftOne hrightOne
      calc
        ((leftBaseShapeFiber
            N M A L 10 base shape).card : ℝ) ≤
            (evertseCommonFixedFiberResidual κ₀ N L : ℝ) :=
          hfinite
        _ ≤
            (degreeTwoFixedFiberResidual κ₀ cLeft N L *
              degreeTwoFixedFiberResidual κ₀ cRight N L) *
              (evertseCommonFixedFiberResidual κ₀ N L : ℝ) := by
          simpa only [one_mul] using
            mul_le_mul_of_nonneg_right
              hpairOne hevertseNonneg
        _ =
            mobileDegreeAtLeastTwoEnvelope
              κ₀ cLeft cRight N L := rfl
  · intro shape hshape hdegree base _hbase
    by_cases htwo : shape.1.card = 2
    · have hfinite :=
        hpellRight N hNpellRight M A L base
          hNM hMκ hL hBfour shape htwo
      have hleftRightOne :
          (1 : ℝ) ≤
            degreeTwoFixedFiberResidual κ₀ cLeft N L :=
        hleftOne
      calc
        ((rightBaseShapeFiber
            N M A L 10 base shape).card : ℝ) ≤
            degreeTwoFixedFiberResidual
              κ₀ cRight N L :=
          hfinite
        _ ≤
            degreeTwoFixedFiberResidual κ₀ cLeft N L *
              degreeTwoFixedFiberResidual κ₀ cRight N L := by
          simpa only [one_mul] using
            mul_le_mul_of_nonneg_right
              hleftRightOne hrightNonneg
        _ ≤
            (degreeTwoFixedFiberResidual κ₀ cLeft N L *
              degreeTwoFixedFiberResidual κ₀ cRight N L) *
              (evertseCommonFixedFiberResidual κ₀ N L : ℝ) := by
          simpa only [mul_one] using
            mul_le_mul_of_nonneg_left
              hevertseOne
              (mul_nonneg hleftNonneg hrightNonneg)
        _ =
            mobileDegreeAtLeastTwoEnvelope
              κ₀ cLeft cRight N L := rfl
    · have hthree : 3 ≤ shape.1.card := by
        omega
      have hfiniteNat :=
        card_rightBaseShapeFiber_degree_at_least_three_le_common
          hES (κ₀ := κ₀) (M := M)
            (A := A) (base := base)
            hNtwo hMκ hL shape hshape hthree
      have hfinite :
          ((rightBaseShapeFiber
            N M A L 10 base shape).card : ℝ) ≤
            (evertseCommonFixedFiberResidual κ₀ N L : ℝ) := by
        exact_mod_cast hfiniteNat
      have hpairOne :
          (1 : ℝ) ≤
            degreeTwoFixedFiberResidual κ₀ cLeft N L *
              degreeTwoFixedFiberResidual κ₀ cRight N L :=
        one_le_mul_of_one_le_of_one_le
          hleftOne hrightOne
      calc
        ((rightBaseShapeFiber
            N M A L 10 base shape).card : ℝ) ≤
            (evertseCommonFixedFiberResidual κ₀ N L : ℝ) :=
          hfinite
        _ ≤
            (degreeTwoFixedFiberResidual κ₀ cLeft N L *
              degreeTwoFixedFiberResidual κ₀ cRight N L) *
              (evertseCommonFixedFiberResidual κ₀ N L : ℝ) := by
          simpa only [one_mul] using
            mul_le_mul_of_nonneg_right
              hpairOne hevertseNonneg
        _ =
            mobileDegreeAtLeastTwoEnvelope
              κ₀ cLeft cRight N L := rfl

/-! ## The endpoint-independent moderate host envelope -/

/--
The source disjunction contributes the polynomial number of offset shapes
times the maximum of:

* the separate two-singleton shape bound `Q₂`;
* one interval width, bounded by `κ₀ N`, times the mobile fixed-fibre
  envelope.
-/
noncomputable def moderateNonterminalHostEnvelope
    (κ₀ : ℕ) (cLeft cRight : ℝ)
    (Q₂ : ℕ → ℕ → ℝ)
    (N L : ℕ) : ℝ :=
  componentShapeEnvelope N L *
    max (Q₂ N L)
      ((κ₀ : ℝ) * (N : ℝ) *
        mobileDegreeAtLeastTwoEnvelope
          κ₀ cLeft cRight N L)

/-- Pointwise nonnegativity of the moderate host envelope. -/
theorem moderateNonterminalHostEnvelope_nonneg
    (κ₀ : ℕ) (cLeft cRight : ℝ)
    (Q₂ : ℕ → ℕ → ℝ)
    (hQ₂Nonneg : ∀ N L, 0 ≤ Q₂ N L)
    (N L : ℕ) :
    0 ≤ moderateNonterminalHostEnvelope
      κ₀ cLeft cRight Q₂ N L := by
  unfold moderateNonterminalHostEnvelope
    componentShapeEnvelope
  apply mul_nonneg
  · positivity
  · exact le_max_of_le_left (hQ₂Nonneg N L)

/--
If the two-singleton contribution is `N^(1+o(1))`, then the complete
moderate host envelope has the same rate.
-/
theorem moderateNonterminalHostEnvelope_uniformLinear
    {C : ℝ} (hC : 0 ≤ C) (κ₀ : ℕ)
    {cLeft cRight : ℝ}
    (hcLeft : 0 ≤ cLeft) (hcRight : 0 ≤ cRight)
    (Q₂ : ℕ → ℕ → ℝ)
    (hQ₂Rate :
      UniformLinearSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C) Q₂)
    (hQ₂Nonneg : ∀ N L, 0 ≤ Q₂ N L) :
    UniformLinearSubpolynomialOn
      (CriticalRunWindow.InRunLengthWindow C)
      (moderateNonterminalHostEnvelope
        κ₀ cLeft cRight Q₂) := by
  have hmobile :=
    mobileDegreeAtLeastTwoEnvelope_uniformSubpolynomial
      hC κ₀ hcLeft hcRight
  let scaledMobile : ℕ → ℕ → ℝ :=
    fun N L =>
      (κ₀ : ℝ) *
        mobileDegreeAtLeastTwoEnvelope
          κ₀ cLeft cRight N L
  have hscaledMobile :
      UniformSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C)
        scaledMobile := by
    simpa only [scaledMobile] using
      ExpSqrtLog.uniformSubpolynomialOn_const_mul
        (κ₀ : ℝ) hmobile
  let linearMobile : ℕ → ℕ → ℝ :=
    fun N L =>
      (κ₀ : ℝ) * (N : ℝ) *
        mobileDegreeAtLeastTwoEnvelope
          κ₀ cLeft cRight N L
  have hlinearMobile :
      UniformLinearSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C)
        linearMobile := by
    apply UniformLinear.of_linear_mul_subpolynomial
      hscaledMobile
    refine ⟨0, ?_⟩
    intro N _hN L _hrun
    have hmobileNonneg :=
      mobileDegreeAtLeastTwoEnvelope_nonneg
        κ₀ cLeft cRight N L
    have hleft :
        0 ≤ linearMobile N L := by
      dsimp only [linearMobile]
      positivity
    have hright :
        0 ≤ scaledMobile N L := by
      dsimp only [scaledMobile]
      positivity
    rw [abs_of_nonneg hleft, abs_of_nonneg hright]
    dsimp only [linearMobile, scaledMobile]
    ring_nf
    exact le_rfl
  have hlinearMobileNonneg :
      ∀ N L, 0 ≤ linearMobile N L := by
    intro N L
    dsimp only [linearMobile]
    have :=
      mobileDegreeAtLeastTwoEnvelope_nonneg
        κ₀ cLeft cRight N L
    positivity
  have hmaximum :
      UniformLinearSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C)
        (fun N L =>
          max (Q₂ N L) (linearMobile N L)) :=
    UniformLinear.max_of_nonnegative
      hQ₂Rate hlinearMobile hQ₂Nonneg
      hlinearMobileNonneg
  have hshapes :=
    componentShapeEnvelope_uniformSubpolynomial hC
  have hproduct :=
    UniformLinear.subpolynomial_mul
      hshapes hmaximum
  change
    UniformLinearSubpolynomialOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun N L =>
        componentShapeEnvelope N L *
          max (Q₂ N L)
            ((κ₀ : ℝ) * (N : ℝ) *
              mobileDegreeAtLeastTwoEnvelope
                κ₀ cLeft cRight N L))
  exact hproduct

/--
Conditional closure of the moderate host count.

The only remaining input is a nonnegative `N^(1+o(1))` envelope `Q₂` for
each fixed two-singleton shape.  Evertse--Silverman and generalized Pell
then supply the mobile-degree branch, and the exact real source
disjunction produces one endpoint-independent host envelope for `K = 10`.
-/
theorem
    evertseSilverman_generalizedPell_imply_exists_moderateNonterminalHostEnvelope
    {C : ℝ} (hC : 0 ≤ C) (κ₀ A : ℕ)
    (hES : EvertseSilvermanAbscissaStatement)
    (hPell : PellInput.GeneralizedPellPolynomialBoxStatement)
    (Q₂ : ℕ → ℕ → ℝ)
    (hQ₂Rate :
      UniformLinearSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C) Q₂)
    (hQ₂Nonneg : ∀ N L, 0 ≤ Q₂ N L)
    (hQ₂Dom :
      ∃ N₂ : ℕ, ∀ N ≥ N₂, ∀ M L,
        2 * N ≤ M →
        M ≤ κ₀ * N →
        CriticalRunWindow.InRunLengthWindow C N L →
        ∀ shape ∈ boundedOffsetShapes L 10,
          shape.1.card + shape.2.card = 2 →
          ((boundedComponentHostsOfShape
            N M A L 10 shape).card : ℝ) ≤
            Q₂ N L) :
    ∃ hostEnvelope : ℕ → ℕ → ℝ,
      UniformLinearSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C)
        hostEnvelope ∧
      (∀ N L, 0 ≤ hostEnvelope N L) ∧
      ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ M L,
        2 * N ≤ M →
        M ≤ κ₀ * N →
        CriticalRunWindow.InRunLengthWindow C N L →
        ((boundedComponentHosts
          N M A L 10).card : ℝ) ≤
            hostEnvelope N L := by
  obtain
      ⟨cLeft, cRight, hcLeft, hcRight,
        hmobileRate, hmobileNonneg,
        Nmobile, hmobileDom⟩ :=
    evertseSilverman_generalizedPell_imply_exists_mobileDegreeAtLeastTwoEnvelope
      hC κ₀ hES hPell
  obtain ⟨Ntwo, htwo⟩ := hQ₂Dom
  let hostEnvelope : ℕ → ℕ → ℝ :=
    moderateNonterminalHostEnvelope
      κ₀ cLeft cRight Q₂
  have hhostRate :
      UniformLinearSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C)
        hostEnvelope := by
    simpa only [hostEnvelope] using
      moderateNonterminalHostEnvelope_uniformLinear
        hC κ₀ hcLeft hcRight Q₂
          hQ₂Rate hQ₂Nonneg
  have hhostNonneg :
      ∀ N L, 0 ≤ hostEnvelope N L := by
    intro N L
    simpa only [hostEnvelope] using
      moderateNonterminalHostEnvelope_nonneg
        κ₀ cLeft cRight Q₂ hQ₂Nonneg N L
  refine
    ⟨hostEnvelope, hhostRate, hhostNonneg,
      max 2 (max Nmobile Ntwo), ?_⟩
  intro N hN M L hNM hMκ hrun
  have hNtwoBase : 2 ≤ N :=
    (le_max_left _ _).trans hN
  have htail :
      max Nmobile Ntwo ≤ N :=
    (le_max_right _ _).trans hN
  have hNmobile : Nmobile ≤ N :=
    (le_max_left _ _).trans htail
  have hNtwo : Ntwo ≤ N :=
    (le_max_right _ _).trans htail
  obtain ⟨hleft, hright⟩ :=
    hmobileDom N hNmobile M A L
      hNM hMκ hrun
  have hsource :=
    card_boundedComponentHosts_cast_le_sourceDisjunction
      hNtwoBase
      (Q₂ N L)
      (mobileDegreeAtLeastTwoEnvelope
        κ₀ cLeft cRight N L)
      (hQ₂Nonneg N L)
      (hmobileNonneg N L)
      (htwo N hNtwo M L hNM hMκ hrun)
      hleft hright
  have hwidthNat :
      M - N ≤ κ₀ * N :=
    (Nat.sub_le M N).trans hMκ
  have hwidthReal :
      (((M - N : ℕ) : ℝ)) ≤
        (κ₀ : ℝ) * (N : ℝ) := by
    exact_mod_cast hwidthNat
  have hwidthMobile :
      (((M - N : ℕ) : ℝ) *
          mobileDegreeAtLeastTwoEnvelope
            κ₀ cLeft cRight N L) ≤
        ((κ₀ : ℝ) * (N : ℝ) *
          mobileDegreeAtLeastTwoEnvelope
            κ₀ cLeft cRight N L) :=
    mul_le_mul_of_nonneg_right
      hwidthReal (hmobileNonneg N L)
  have hmaximum :
      max (Q₂ N L)
          (((M - N : ℕ) : ℝ) *
            mobileDegreeAtLeastTwoEnvelope
              κ₀ cLeft cRight N L) ≤
        max (Q₂ N L)
          ((κ₀ : ℝ) * (N : ℝ) *
            mobileDegreeAtLeastTwoEnvelope
              κ₀ cLeft cRight N L) :=
    max_le_max le_rfl hwidthMobile
  calc
    ((boundedComponentHosts
        N M A L 10).card : ℝ) ≤
        ((((10 + 1) * (L + 1) ^ 10) ^ 2 : ℕ) : ℝ) *
          max (Q₂ N L)
            (((M - N : ℕ) : ℝ) *
              mobileDegreeAtLeastTwoEnvelope
                κ₀ cLeft cRight N L) :=
      hsource
    _ ≤
        ((((10 + 1) * (L + 1) ^ 10) ^ 2 : ℕ) : ℝ) *
          max (Q₂ N L)
            ((κ₀ : ℝ) * (N : ℝ) *
              mobileDegreeAtLeastTwoEnvelope
                κ₀ cLeft cRight N L) :=
      mul_le_mul_of_nonneg_left hmaximum (by positivity)
    _ = hostEnvelope N L := by
      dsimp only [hostEnvelope,
        moderateNonterminalHostEnvelope,
        componentShapeEnvelope]
      norm_num only [
        Nat.cast_pow, Nat.cast_mul,
        Nat.cast_add, Nat.cast_one]

end

end BoundedRatioNonterminalMobileAssembly
end PaperC
