import PaperC.Asymptotics.BoundedRatioManyDefectsFixedFibers
import PaperC.Asymptotics.BoundedRatioTerminalSummation
import PaperC.Asymptotics.LemmaFifteenThree

set_option maxHeartbeats 3600000

/-!
# Uniform summation of the degree-two fixed fibres

`BoundedRatioManyDefectsFixedFibers` reduces every degree-two
fixed-base/fixed-shape fibre to a sum over squarefree smooth coefficients.
There are two summands:

* for normalized coefficient one, the exact signed-divisor count
  `2 * τ(|Δ²|)`;
* otherwise, one generalized-Pell box.

This file performs that remaining sum.  The divisor term is bounded by
`8 (L+1)²`, the number of smooth coefficients by the elementary Chebyshev
envelope, and all Pell boxes by a common box at the bounded-ratio cutoff
`(κ₀+1)N`.  Their product is uniformly `N^o(1)`, which is stronger than the
`N^(1/2+o(1))` fixed-fibre input required by the global many-defects
assembly.  No Diophantine hypothesis beyond the already registered
generalized-Pell statement is introduced.
-/

namespace PaperC
namespace BoundedRatioManyDefectsDegreeTwoSum

open scoped BigOperators
open BoundedRatioComponentHosts
open BoundedRatioDistinctKernelTwoDefects
open BoundedRatioManyDefectsFixedFibers
open BoundedRatioManyDefectsFibers
open ComponentNormalization
open CriticalRunWindow
open PellInput
open PropositionSixteenOne
open SquarefreeSmoothCount

noncomputable section

/-! ## The exceptional signed-divisor summand -/

/-- A shape-independent real envelope for the signed divisors of `Δ²`. -/
noncomputable def degreeTwoSignedDivisorEnvelope
    (_N L : ℕ) : ℝ :=
  8 * (((L + 1 : ℕ) : ℝ) ^ 2)

/-- The elementary signed-divisor envelope is pointwise at least one. -/
theorem degreeTwoSignedDivisorEnvelope_one_le
    (N L : ℕ) :
    1 ≤ degreeTwoSignedDivisorEnvelope N L := by
  have hheight :
      (1 : ℝ) ≤ (((L + 1 : ℕ) : ℝ)) := by
    exact_mod_cast (Nat.succ_pos L)
  have hsquare :
      (1 : ℝ) ≤ (((L + 1 : ℕ) : ℝ) ^ 2) := by
    nlinarith [sq_nonneg ((((L + 1 : ℕ) : ℝ)) - 1)]
  unfold degreeTwoSignedDivisorEnvelope
  nlinarith

private theorem offsetShiftOfCard_natAbs_le
    {L r : ℕ} (offsets : Finset (Fin (L + 1)))
    (hcard : offsets.card = r) (i : Fin r) :
    (offsetShiftOfCard offsets hcard i).natAbs ≤ L + 1 := by
  have hbound :=
    AlignedRungeBridge.abs_channelVertexOffset_le
      ((offsetEnumeration offsets
        (Fin.cast hcard.symm i)).1)
  rw [Int.abs_eq_natAbs] at hbound
  exact_mod_cast hbound

/--
The exact exceptional term `2 * τ(|Δ²|)` is at most `8(L+1)²`.
-/
theorem signedDivisorCount_cast_le_envelope
    {N L : ℕ}
    (offsets : Finset (Fin (L + 1)))
    (hdegree : offsets.card = 2) :
    (((Int.divisorsAntidiag
      ((offsetShiftOfCard offsets hdegree 0 -
        offsetShiftOfCard offsets hdegree 1) ^ 2)).card : ℕ) : ℝ) ≤
      degreeTwoSignedDivisorEnvelope N L := by
  let Δ :=
    offsetShiftOfCard offsets hdegree 0 -
      offsetShiftOfCard offsets hdegree 1
  have hzero :=
    offsetShiftOfCard_natAbs_le offsets hdegree (0 : Fin 2)
  have hone :=
    offsetShiftOfCard_natAbs_le offsets hdegree (1 : Fin 2)
  have hdelta :
      Δ.natAbs ≤ 2 * (L + 1) := by
    calc
      Δ.natAbs ≤
          (offsetShiftOfCard offsets hdegree 0).natAbs +
            (offsetShiftOfCard offsets hdegree 1).natAbs :=
        Int.natAbs_sub_le _ _
      _ ≤ 2 * (L + 1) := by omega
  have hsquare :
      (Δ ^ 2).natAbs ≤ 4 * (L + 1) ^ 2 := by
    rw [Int.natAbs_pow]
    calc
      Δ.natAbs ^ 2 ≤ (2 * (L + 1)) ^ 2 :=
        Nat.pow_le_pow_left hdelta 2
      _ = 4 * (L + 1) ^ 2 := by ring
  have hdivisors :
      ((Δ ^ 2).natAbs.divisors.card : ℕ) ≤
        (Δ ^ 2).natAbs :=
    Nat.card_divisors_le_self _
  have hcast : (((Δ ^ 2).natAbs : ℕ) : ℤ) = Δ ^ 2 := by
    rw [Int.natCast_natAbs, abs_of_nonneg (sq_nonneg Δ)]
  have hnat :
      (Int.divisorsAntidiag (Δ ^ 2)).card ≤
        8 * (L + 1) ^ 2 := by
    calc
      (Int.divisorsAntidiag (Δ ^ 2)).card =
          (Int.divisorsAntidiag
            (((Δ ^ 2).natAbs : ℕ) : ℤ)).card := by rw [hcast]
      _ = 2 * (Δ ^ 2).natAbs.divisors.card :=
        card_int_divisorsAntidiag_natCast_eq_two_mul_divisors _
      _ ≤ 2 * (Δ ^ 2).natAbs :=
        Nat.mul_le_mul_left 2 hdivisors
      _ ≤ 2 * (4 * (L + 1) ^ 2) :=
        Nat.mul_le_mul_left 2 hsquare
      _ = 8 * (L + 1) ^ 2 := by ring
  have hnat' :
      (Int.divisorsAntidiag
        ((offsetShiftOfCard offsets hdegree 0 -
          offsetShiftOfCard offsets hdegree 1) ^ 2)).card ≤
        8 * (L + 1) ^ 2 := by
    simpa only [Δ] using hnat
  unfold degreeTwoSignedDivisorEnvelope
  exact_mod_cast hnat'

/-- The exceptional divisor envelope is uniformly subpolynomial. -/
theorem degreeTwoSignedDivisorEnvelope_uniformSubpolynomial
    {C : ℝ} (hC : 0 ≤ C) :
    UniformSubpolynomialOn
      (CriticalRunWindow.InRunLengthWindow C)
      degreeTwoSignedDivisorEnvelope := by
  have hheight :=
    CriticalRationalMassEnvelopes.runLengthAddOne_uniformSubpolynomial
      hC
  have hsquare :=
    ExpSqrtLog.uniformSubpolynomialOn_mul hheight hheight
  change
    UniformSubpolynomialOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun _N L => 8 * (((L + 1 : ℕ) : ℝ) ^ 2))
  simpa only [pow_two] using
    ExpSqrtLog.uniformSubpolynomialOn_const_mul 8 hsquare

/-! ## Common real envelope for the full coefficient sum -/

/--
The common degree-two residual.  The leading factor two absorbs the
natural ceiling in the Pell count.
-/
noncomputable def degreeTwoFixedFiberResidual
    (κ₀ : ℕ) (c : ℝ) (N L : ℕ) : ℝ :=
  2 *
    smoothKernelChebyshevEnvelope (L + 1) *
    degreeTwoSignedDivisorEnvelope N L *
    PellInput.expLogLogBound c
      (BoundedRatioTerminalClosure.terminalLabelCutoff κ₀ N)

/-- Every factor in the explicit degree-two residual is `N^o(1)`. -/
theorem degreeTwoFixedFiberResidual_uniformSubpolynomial
    {C c : ℝ} (hC : 0 ≤ C) (hc : 0 ≤ c) (κ₀ : ℕ) :
    UniformSubpolynomialOn
      (CriticalRunWindow.InRunLengthWindow C)
      (degreeTwoFixedFiberResidual κ₀ c) := by
  have hsmooth :=
    smoothKernelChebyshevEnvelope_uniformSubpolynomial hC
  have hdivisor :=
    degreeTwoSignedDivisorEnvelope_uniformSubpolynomial hC
  have hpell :=
    BoundedRatioTerminalSummation.expLogLogBound_terminalLabelCutoff_uniformSubpolynomial
      (C := C) hc κ₀
  have hproduct :=
    ExpSqrtLog.uniformSubpolynomialOn_mul
      (ExpSqrtLog.uniformSubpolynomialOn_mul
        hsmooth hdivisor)
      hpell
  have hscaled :=
    ExpSqrtLog.uniformSubpolynomialOn_const_mul 2 hproduct
  convert hscaled using 1
  funext N L
  unfold degreeTwoFixedFiberResidual
  ring

/--
In particular the degree-two residual satisfies the weaker
`N^(1/2+o(1))` interface consumed by the global fixed-fibre assembly.
-/
theorem degreeTwoFixedFiberResidual_uniformHalfPower
    {C c : ℝ} (hC : 0 ≤ C) (hc : 0 ≤ c) (κ₀ : ℕ) :
    UniformHalfPowerSubpolynomialOn
      (CriticalRunWindow.InRunLengthWindow C)
      (degreeTwoFixedFiberResidual κ₀ c) := by
  have hsub :=
    degreeTwoFixedFiberResidual_uniformSubpolynomial hC hc κ₀
  apply UniformHalfPower.of_sqrt_mul_subpolynomial hsub
  refine ⟨1, ?_⟩
  intro N hN L _hrun
  have hsqrt : 1 ≤ Real.sqrt (N : ℝ) := by
    apply Real.one_le_sqrt.mpr
    exact_mod_cast hN
  have hresidual :
      0 ≤ degreeTwoFixedFiberResidual κ₀ c N L := by
    unfold degreeTwoFixedFiberResidual
      degreeTwoSignedDivisorEnvelope
      smoothKernelChebyshevEnvelope
      PellInput.expLogLogBound
    positivity
  rw [abs_of_nonneg hresidual]
  calc
    degreeTwoFixedFiberResidual κ₀ c N L =
        1 * degreeTwoFixedFiberResidual κ₀ c N L := by ring
    _ ≤
        Real.sqrt N *
          degreeTwoFixedFiberResidual κ₀ c N L :=
      mul_le_mul_of_nonneg_right hsqrt hresidual

private theorem cutoff_le_terminalLabelCutoff
    {κ₀ N M L : ℕ}
    (hMκ : M ≤ κ₀ * N) (hL : L ≤ N) :
    boundedRatioCutoff M L ≤
      BoundedRatioTerminalClosure.terminalLabelCutoff κ₀ N := by
  unfold boundedRatioCutoff
    BoundedRatioTerminalClosure.terminalLabelCutoff
  calc
    M + L ≤ κ₀ * N + N := Nat.add_le_add hMκ hL
    _ = (κ₀ + 1) * N := by
      rw [Nat.add_mul, one_mul]

private theorem expLogLogBound_one_le_of_large
    {c : ℝ} (hc : 0 ≤ c) {X : ℕ}
    (hX : Real.exp (Real.exp 1) < (X : ℝ)) :
    1 ≤ PellInput.expLogLogBound c X := by
  have hXpos : 0 < (X : ℝ) :=
    (Real.exp_pos _).trans hX
  have hlogX :
      Real.exp 1 < Real.log (X : ℝ) := by
    have hmono :=
      Real.log_lt_log (Real.exp_pos (Real.exp 1)) hX
    simpa only [Real.log_exp] using hmono
  have hlogXpos : 0 < Real.log (X : ℝ) :=
    (Real.exp_pos 1).trans hlogX
  have hloglogX :
      1 < Real.log (Real.log (X : ℝ)) := by
    have hmono :=
      Real.log_lt_log (Real.exp_pos 1) hlogX
    simpa only [Real.log_exp] using hmono
  have hratio :
      0 ≤ Real.log (X : ℝ) /
        Real.log (Real.log (X : ℝ)) :=
    div_nonneg hlogXpos.le (zero_lt_one.trans hloglogX).le
  unfold PellInput.expLogLogBound
  rw [Real.one_le_exp_iff]
  have := mul_nonneg hc hratio
  simpa only [mul_div_assoc] using this

/--
Beyond the elementary logarithmic threshold the residual is at least one.
This lower bound lets later assemblies replace finite maxima or sums by
products of subpolynomial envelopes.
-/
theorem degreeTwoFixedFiberResidual_one_le_of_large
    {c : ℝ} (hc : 0 ≤ c) (κ₀ N L : ℕ)
    (hlarge :
      Real.exp (Real.exp 1) <
        (BoundedRatioTerminalClosure.terminalLabelCutoff κ₀ N : ℝ)) :
    1 ≤ degreeTwoFixedFiberResidual κ₀ c N L := by
  have hsmooth :
      1 ≤ smoothKernelChebyshevEnvelope (L + 1) := by
    unfold smoothKernelChebyshevEnvelope
    rw [Real.one_le_exp_iff]
    have hlogTwo : 0 ≤ Real.log (2 : ℝ) :=
      (Real.log_pos (by norm_num)).le
    have hratio :
        0 ≤ (((L + 1 : ℕ) : ℝ) /
          (Nat.log 2 (L + 1) : ℝ)) := by
      positivity
    positivity
  have hdivisor :
      1 ≤ degreeTwoSignedDivisorEnvelope N L := by
    exact degreeTwoSignedDivisorEnvelope_one_le N L
  have hpell :
      1 ≤ PellInput.expLogLogBound c
        (BoundedRatioTerminalClosure.terminalLabelCutoff κ₀ N) :=
    expLogLogBound_one_le_of_large hc hlarge
  have hproduct :
      1 ≤
        smoothKernelChebyshevEnvelope (L + 1) *
          degreeTwoSignedDivisorEnvelope N L *
          PellInput.expLogLogBound c
            (BoundedRatioTerminalClosure.terminalLabelCutoff κ₀ N) :=
    one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hsmooth hdivisor)
      hpell
  unfold degreeTwoFixedFiberResidual
  nlinarith

/-- The preceding lower bound holds uniformly for all sufficiently large `N`. -/
theorem degreeTwoFixedFiberResidual_eventually_one_le
    {c : ℝ} (hc : 0 ≤ c) (κ₀ : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L,
      1 ≤ degreeTwoFixedFiberResidual κ₀ c N L := by
  obtain ⟨N₀, hN₀⟩ :=
    exists_nat_gt (Real.exp (Real.exp 1))
  refine ⟨N₀, ?_⟩
  intro N hN L
  apply degreeTwoFixedFiberResidual_one_le_of_large hc
  exact hN₀.trans_le
    (by
      exact_mod_cast
        ((show N ≤
            BoundedRatioTerminalClosure.terminalLabelCutoff κ₀ N by
          unfold BoundedRatioTerminalClosure.terminalLabelCutoff
          exact Nat.le_mul_of_pos_left N (by omega))).trans'
            hN)

private theorem expLogLogBound_mono_on_large
    {c : ℝ} (hc : 0 ≤ c)
    {X₀ X Y : ℕ}
    (hmono :
      ∀ X Y : ℕ, X₀ ≤ X → X ≤ Y →
        Real.log (X : ℝ) / Real.log (Real.log (X : ℝ)) ≤
          Real.log (Y : ℝ) / Real.log (Real.log (Y : ℝ)))
    (hX₀ : X₀ ≤ X) (hXY : X ≤ Y) :
    PellInput.expLogLogBound c X ≤
      PellInput.expLogLogBound c Y := by
  unfold PellInput.expLogLogBound
  apply Real.exp_le_exp.mpr
  have hscaled :=
    mul_le_mul_of_nonneg_left (hmono X Y hX₀ hXY) hc
  simpa only [mul_div_assoc] using hscaled

private theorem natCeil_expLogLogBound_cast_le_twice
    {c : ℝ} (hc : 0 ≤ c) {X : ℕ}
    (hX : Real.exp (Real.exp 1) < (X : ℝ)) :
    ((⌈PellInput.expLogLogBound c X⌉₊ : ℕ) : ℝ) ≤
      2 * PellInput.expLogLogBound c X := by
  have hone :=
    expLogLogBound_one_le_of_large hc hX
  calc
    ((⌈PellInput.expLogLogBound c X⌉₊ : ℕ) : ℝ) ≤
        PellInput.expLogLogBound c X + 1 :=
      (Nat.ceil_lt_add_one
        (show 0 ≤ PellInput.expLogLogBound c X by
          unfold PellInput.expLogLogBound
          positivity)).le
    _ ≤
        PellInput.expLogLogBound c X +
          PellInput.expLogLogBound c X :=
      add_le_add_right hone _
    _ = 2 * PellInput.expLogLogBound c X := by ring

/-! ## Finite domination, uniformly in the fixed base and shape -/

/--
Generalized Pell bounds every left-oriented degree-two fixed fibre by the
common real residual.  The threshold is independent of `M`, `L`, the fixed
base and the fixed shape.
-/
theorem generalizedPell_implies_card_left_degreeTwoFiber_le_residual
    (hPell : PellInput.GeneralizedPellPolynomialBoxStatement)
    (κ₀ K : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧
      ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ M A L base,
        2 * N ≤ M →
        M ≤ κ₀ * N →
        L ≤ N →
        4 ≤ L + 1 →
        ∀ (shape :
          Finset (Fin (L + 1)) × Finset (Fin (L + 1))),
        (hdegree : shape.2.card = 2) →
        ((leftBaseShapeFiber
          N M A L K base shape).card : ℝ) ≤
            degreeTwoFixedFiberResidual κ₀ c N L := by
  let E : ℕ := max 4 (2 * K)
  have hEPos : 0 < E := by
    dsimp only [E]
    omega
  have hEFour : 4 ≤ E := by
    dsimp only [E]
    omega
  have hEK : 2 * K ≤ E := by
    dsimp only [E]
    omega
  obtain ⟨c, hc, Xpell, hpell⟩ :=
    card_leftBaseShapeFiber_degree_two_polynomial_of_generalizedPell
      hPell hEPos hEFour hEK
  obtain ⟨Xratio, hratio⟩ :=
    LemmaFifteenThree.log_div_loglog_monotone_eventually
  obtain ⟨Xlog, hXlog⟩ :=
    exists_nat_gt (Real.exp (Real.exp 1))
  refine ⟨c, hc, max Xpell (max Xratio Xlog), ?_⟩
  intro N hN M A L base hNM hMκ hL hB shape hdegree
  have hNtwo : 2 ≤ N := by omega
  have hNpell : Xpell ≤ N :=
    (le_max_left _ _).trans hN
  have htail : max Xratio Xlog ≤ N :=
    (le_max_right _ _).trans hN
  have hNratio : Xratio ≤ N :=
    (le_max_left _ _).trans htail
  have hNlog : Xlog ≤ N :=
    (le_max_right _ _).trans htail
  have hNcutoff :
      N ≤ boundedRatioCutoff M L := by
    unfold boundedRatioCutoff
    omega
  have hfinite :=
    hpell N M A L base shape hNtwo hdegree
      (hNpell.trans hNcutoff)
  have hcutoffTerminal :=
    cutoff_le_terminalLabelCutoff hMκ hL
  have hpellMono :=
    expLogLogBound_mono_on_large hc hratio
      (hNratio.trans hNcutoff) hcutoffTerminal
  have hlarge :
      Real.exp (Real.exp 1) <
        (boundedRatioCutoff M L : ℝ) :=
    hXlog.trans_le
      (by exact_mod_cast (hNlog.trans hNcutoff))
  have hceil :=
    natCeil_expLogLogBound_cast_le_twice hc hlarge
  have hceilCommon :
      ((⌈PellInput.expLogLogBound c
        (boundedRatioCutoff M L)⌉₊ : ℕ) : ℝ) ≤
        2 * PellInput.expLogLogBound c
          (BoundedRatioTerminalClosure.terminalLabelCutoff κ₀ N) :=
    hceil.trans (mul_le_mul_of_nonneg_left hpellMono (by norm_num))
  have hsmooth :=
    card_squarefreeSmoothUpTo_le_smoothKernelChebyshevEnvelope
      (X := boundedRatioCutoff M L ^ K) hB
  let S :=
    squarefreeSmoothUpTo
      (L + 1) (boundedRatioCutoff M L ^ K)
  let D : ℝ := degreeTwoSignedDivisorEnvelope N L
  let P : ℝ :=
    PellInput.expLogLogBound c
      (BoundedRatioTerminalClosure.terminalLabelCutoff κ₀ N)
  have hDone : 0 ≤ D := by
    dsimp only [D, degreeTwoSignedDivisorEnvelope]
    positivity
  have hPone : 1 ≤ P := by
    dsimp only [P]
    exact
      (expLogLogBound_one_le_of_large hc hlarge).trans
        hpellMono
  have hterm :
      ∀ d ∈ S,
        (((if leftNormalizedCoefficient shape base d = 1 then
              (Int.divisorsAntidiag
                ((offsetShiftOfCard shape.2 hdegree 0 -
                  offsetShiftOfCard shape.2 hdegree 1) ^ 2)).card
            else
              ⌈PellInput.expLogLogBound c
                (boundedRatioCutoff M L)⌉₊) : ℕ) : ℝ) ≤
          2 * D * P := by
    intro d hd
    by_cases heq : leftNormalizedCoefficient shape base d = 1
    · simp only [heq, if_pos]
      have hdivisor :=
        signedDivisorCount_cast_le_envelope
          (N := N) shape.2 hdegree
      dsimp only [D]
      calc
        (((Int.divisorsAntidiag
          ((offsetShiftOfCard shape.2 hdegree 0 -
            offsetShiftOfCard shape.2 hdegree 1) ^ 2)).card : ℕ) : ℝ) ≤
            D := hdivisor
        _ ≤ 2 * D * P := by nlinarith
    · simp only [heq, if_neg]
      dsimp only [P]
      calc
        ((⌈PellInput.expLogLogBound c
          (boundedRatioCutoff M L)⌉₊ : ℕ) : ℝ) ≤
            2 * P := hceilCommon
        _ ≤ 2 * D * P := by
          have hDoneOne : 1 ≤ D := by
            dsimp only [D]
            exact degreeTwoSignedDivisorEnvelope_one_le N L
          nlinarith
  have hfiniteCast :
      ((leftBaseShapeFiber
        N M A L K base shape).card : ℝ) ≤
        ∑ d ∈ S,
          (((if leftNormalizedCoefficient shape base d = 1 then
                (Int.divisorsAntidiag
                  ((offsetShiftOfCard shape.2 hdegree 0 -
                    offsetShiftOfCard shape.2 hdegree 1) ^ 2)).card
              else
                ⌈PellInput.expLogLogBound c
                  (boundedRatioCutoff M L)⌉₊) : ℕ) : ℝ) := by
    exact_mod_cast hfinite
  calc
    ((leftBaseShapeFiber
        N M A L K base shape).card : ℝ) ≤
        ∑ d ∈ S,
          (((if leftNormalizedCoefficient shape base d = 1 then
                (Int.divisorsAntidiag
                  ((offsetShiftOfCard shape.2 hdegree 0 -
                    offsetShiftOfCard shape.2 hdegree 1) ^ 2)).card
              else
                ⌈PellInput.expLogLogBound c
                  (boundedRatioCutoff M L)⌉₊) : ℕ) : ℝ) :=
      hfiniteCast
    _ ≤ ∑ _d ∈ S, 2 * D * P :=
      Finset.sum_le_sum fun d hd => hterm d hd
    _ = (S.card : ℝ) * (2 * D * P) := by
      simp
    _ ≤
        smoothKernelChebyshevEnvelope (L + 1) *
          (2 * D * P) := by
      apply mul_le_mul_of_nonneg_right
      · simpa only [S] using hsmooth
      · positivity
    _ = degreeTwoFixedFiberResidual κ₀ c N L := by
      unfold degreeTwoFixedFiberResidual
      dsimp only [D, P]
      ring

/-- Symmetric right-oriented finite domination. -/
theorem generalizedPell_implies_card_right_degreeTwoFiber_le_residual
    (hPell : PellInput.GeneralizedPellPolynomialBoxStatement)
    (κ₀ K : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧
      ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ M A L base,
        2 * N ≤ M →
        M ≤ κ₀ * N →
        L ≤ N →
        4 ≤ L + 1 →
        ∀ (shape :
          Finset (Fin (L + 1)) × Finset (Fin (L + 1))),
        (hdegree : shape.1.card = 2) →
        ((rightBaseShapeFiber
          N M A L K base shape).card : ℝ) ≤
            degreeTwoFixedFiberResidual κ₀ c N L := by
  let E : ℕ := max 4 (2 * K)
  have hEPos : 0 < E := by
    dsimp only [E]
    omega
  have hEFour : 4 ≤ E := by
    dsimp only [E]
    omega
  have hEK : 2 * K ≤ E := by
    dsimp only [E]
    omega
  obtain ⟨c, hc, Xpell, hpell⟩ :=
    card_rightBaseShapeFiber_degree_two_polynomial_of_generalizedPell
      hPell hEPos hEFour hEK
  obtain ⟨Xratio, hratio⟩ :=
    LemmaFifteenThree.log_div_loglog_monotone_eventually
  obtain ⟨Xlog, hXlog⟩ :=
    exists_nat_gt (Real.exp (Real.exp 1))
  refine ⟨c, hc, max Xpell (max Xratio Xlog), ?_⟩
  intro N hN M A L base hNM hMκ hL hB shape hdegree
  have hNtwo : 2 ≤ N := by omega
  have hNpell : Xpell ≤ N :=
    (le_max_left _ _).trans hN
  have htail : max Xratio Xlog ≤ N :=
    (le_max_right _ _).trans hN
  have hNratio : Xratio ≤ N :=
    (le_max_left _ _).trans htail
  have hNlog : Xlog ≤ N :=
    (le_max_right _ _).trans htail
  have hNcutoff :
      N ≤ boundedRatioCutoff M L := by
    unfold boundedRatioCutoff
    omega
  have hfinite :=
    hpell N M A L base shape hNtwo hdegree
      (hNpell.trans hNcutoff)
  have hcutoffTerminal :=
    cutoff_le_terminalLabelCutoff hMκ hL
  have hpellMono :=
    expLogLogBound_mono_on_large hc hratio
      (hNratio.trans hNcutoff) hcutoffTerminal
  have hlarge :
      Real.exp (Real.exp 1) <
        (boundedRatioCutoff M L : ℝ) :=
    hXlog.trans_le
      (by exact_mod_cast (hNlog.trans hNcutoff))
  have hceil :=
    natCeil_expLogLogBound_cast_le_twice hc hlarge
  have hceilCommon :
      ((⌈PellInput.expLogLogBound c
        (boundedRatioCutoff M L)⌉₊ : ℕ) : ℝ) ≤
        2 * PellInput.expLogLogBound c
          (BoundedRatioTerminalClosure.terminalLabelCutoff κ₀ N) :=
    hceil.trans (mul_le_mul_of_nonneg_left hpellMono (by norm_num))
  have hsmooth :=
    card_squarefreeSmoothUpTo_le_smoothKernelChebyshevEnvelope
      (X := boundedRatioCutoff M L ^ K) hB
  let S :=
    squarefreeSmoothUpTo
      (L + 1) (boundedRatioCutoff M L ^ K)
  let D : ℝ := degreeTwoSignedDivisorEnvelope N L
  let P : ℝ :=
    PellInput.expLogLogBound c
      (BoundedRatioTerminalClosure.terminalLabelCutoff κ₀ N)
  have hDone : 0 ≤ D := by
    dsimp only [D, degreeTwoSignedDivisorEnvelope]
    positivity
  have hPone : 1 ≤ P := by
    dsimp only [P]
    exact
      (expLogLogBound_one_le_of_large hc hlarge).trans
        hpellMono
  have hterm :
      ∀ d ∈ S,
        (((if rightNormalizedCoefficient shape base d = 1 then
              (Int.divisorsAntidiag
                ((offsetShiftOfCard shape.1 hdegree 0 -
                  offsetShiftOfCard shape.1 hdegree 1) ^ 2)).card
            else
              ⌈PellInput.expLogLogBound c
                (boundedRatioCutoff M L)⌉₊) : ℕ) : ℝ) ≤
          2 * D * P := by
    intro d hd
    by_cases heq : rightNormalizedCoefficient shape base d = 1
    · simp only [heq, if_pos]
      have hdivisor :=
        signedDivisorCount_cast_le_envelope
          (N := N) shape.1 hdegree
      dsimp only [D]
      calc
        (((Int.divisorsAntidiag
          ((offsetShiftOfCard shape.1 hdegree 0 -
            offsetShiftOfCard shape.1 hdegree 1) ^ 2)).card : ℕ) : ℝ) ≤
            D := hdivisor
        _ ≤ 2 * D * P := by nlinarith
    · simp only [heq, if_neg]
      dsimp only [P]
      calc
        ((⌈PellInput.expLogLogBound c
          (boundedRatioCutoff M L)⌉₊ : ℕ) : ℝ) ≤
            2 * P := hceilCommon
        _ ≤ 2 * D * P := by
          have hDoneOne : 1 ≤ D := by
            dsimp only [D]
            exact degreeTwoSignedDivisorEnvelope_one_le N L
          nlinarith
  have hfiniteCast :
      ((rightBaseShapeFiber
        N M A L K base shape).card : ℝ) ≤
        ∑ d ∈ S,
          (((if rightNormalizedCoefficient shape base d = 1 then
                (Int.divisorsAntidiag
                  ((offsetShiftOfCard shape.1 hdegree 0 -
                    offsetShiftOfCard shape.1 hdegree 1) ^ 2)).card
              else
                ⌈PellInput.expLogLogBound c
                  (boundedRatioCutoff M L)⌉₊) : ℕ) : ℝ) := by
    exact_mod_cast hfinite
  calc
    ((rightBaseShapeFiber
        N M A L K base shape).card : ℝ) ≤
        ∑ d ∈ S,
          (((if rightNormalizedCoefficient shape base d = 1 then
                (Int.divisorsAntidiag
                  ((offsetShiftOfCard shape.1 hdegree 0 -
                    offsetShiftOfCard shape.1 hdegree 1) ^ 2)).card
              else
                ⌈PellInput.expLogLogBound c
                  (boundedRatioCutoff M L)⌉₊) : ℕ) : ℝ) :=
      hfiniteCast
    _ ≤ ∑ _d ∈ S, 2 * D * P :=
      Finset.sum_le_sum fun d hd => hterm d hd
    _ = (S.card : ℝ) * (2 * D * P) := by
      simp
    _ ≤
        smoothKernelChebyshevEnvelope (L + 1) *
          (2 * D * P) := by
      apply mul_le_mul_of_nonneg_right
      · simpa only [S] using hsmooth
      · positivity
    _ = degreeTwoFixedFiberResidual κ₀ c N L := by
      unfold degreeTwoFixedFiberResidual
      dsimp only [D, P]
      ring

end

end BoundedRatioManyDefectsDegreeTwoSum
end PaperC
