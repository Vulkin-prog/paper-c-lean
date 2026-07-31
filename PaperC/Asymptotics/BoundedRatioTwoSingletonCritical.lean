import PaperC.Asymptotics.BoundedRatioTwoSingletonHosts
import PaperC.Asymptotics.BoundedRatioNonterminalCardinality
import PaperC.Analysis.CriticalWindowScale

set_option maxHeartbeats 3600000

/-!
# Critical-window completion of the two-singleton host count

This module turns the finite `(e,c,u,v)` parametrization of
`BoundedRatioTwoSingletonHosts` into the two asymptotic interfaces used by
the nonterminal sector.

* A fixed two-singleton shape has an endpoint-independent
  `N^(1+o(1))` envelope.
* The complete size-two component population satisfies the source bound
  `N exp(Cterm sqrt(B) / log(B))`, with `B = L+1`.

No arithmetic input is added.  The only asymptotic ingredients are the
critical-window comparison `B = O(log N)` and the elementary facts
`log B = o(B^(1/4))` and `B^(1/4) = o(sqrt B)`.
-/

namespace PaperC
namespace BoundedRatioTwoSingletonCritical

open BoundedRatioComponentHosts
open BoundedRatioNonterminalCardinality
open BoundedRatioTwoSingletonHosts
open Filter
open PrimeReciprocalSqrtSum
open PropositionSixteenOne

noncomputable section

/-! ## Explicit exponent and its coarse square-root bound -/

/-- The prime-sensitive exponent in the finite two-singleton estimate. -/
noncomputable def twoSingletonPrimeExponent (B : ℕ) : ℝ :=
  2 *
    (2 * Real.sqrt (rootCutoff B) +
      56 * Real.sqrt (2 * B) /
        ((Nat.log 2 B / 2 : ℕ) : ℝ))

/-- The source scale `sqrt(B) / log(B)`. -/
noncomputable def twoSingletonCriticalRatio (B : ℕ) : ℝ :=
  Real.sqrt (B : ℝ) / Real.log (B : ℝ)

/--
Before exploiting the denominator, the explicit Euler exponent is at most
`228 sqrt(B)`.
-/
theorem twoSingletonPrimeExponent_le_sqrt
    {B : ℕ} (hB : 16 ≤ B) :
    twoSingletonPrimeExponent B ≤
      228 * Real.sqrt (B : ℝ) := by
  have hrootFour :
      4 ≤ rootCutoff B :=
    four_le_rootCutoff hB
  have hrootSq :
      rootCutoff B ^ 2 ≤ B :=
    rootCutoff_sq_le (by omega)
  have hrootLe :
      rootCutoff B ≤ B := by
    calc
      rootCutoff B ≤ rootCutoff B ^ 2 := by
        rw [pow_two]
        exact Nat.le_mul_of_pos_right _ (by omega)
      _ ≤ B := hrootSq
  have hsqrtRoot :
      Real.sqrt (rootCutoff B : ℝ) ≤
        Real.sqrt (B : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast hrootLe)
  have hlogFour :
      4 ≤ Nat.log 2 B := by
    apply Nat.le_log_of_pow_le (by norm_num)
    norm_num
    exact hB
  have hqPosNat :
      0 < Nat.log 2 B / 2 := by
    omega
  have hqOne :
      (1 : ℝ) ≤ ((Nat.log 2 B / 2 : ℕ) : ℝ) := by
    exact_mod_cast hqPosNat
  have hsqrtTwo :
      Real.sqrt (2 : ℝ) ≤ 2 := by
    rw [Real.sqrt_le_iff]
    constructor
    · norm_num
    · norm_num
  have hsqrtTwoB :
      Real.sqrt (2 * (B : ℝ)) ≤
        2 * Real.sqrt (B : ℝ) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    exact mul_le_mul_of_nonneg_right
      hsqrtTwo (Real.sqrt_nonneg _)
  have hdiv :
      Real.sqrt (2 * (B : ℝ)) /
          ((Nat.log 2 B / 2 : ℕ) : ℝ) ≤
        2 * Real.sqrt (B : ℝ) := by
    calc
      Real.sqrt (2 * (B : ℝ)) /
            ((Nat.log 2 B / 2 : ℕ) : ℝ) ≤
          Real.sqrt (2 * (B : ℝ)) / 1 := by
        exact div_le_div_of_nonneg_left
          (Real.sqrt_nonneg _) (by norm_num) hqOne
      _ = Real.sqrt (2 * (B : ℝ)) := by ring
      _ ≤ 2 * Real.sqrt (B : ℝ) := hsqrtTwoB
  have hscaledDiv :
      56 * Real.sqrt (2 * (B : ℝ)) /
          ((Nat.log 2 B / 2 : ℕ) : ℝ) ≤
        56 * (2 * Real.sqrt (B : ℝ)) := by
    calc
      56 * Real.sqrt (2 * (B : ℝ)) /
            ((Nat.log 2 B / 2 : ℕ) : ℝ) =
          56 *
            (Real.sqrt (2 * (B : ℝ)) /
              ((Nat.log 2 B / 2 : ℕ) : ℝ)) := by ring
      _ ≤ 56 * (2 * Real.sqrt (B : ℝ)) :=
        mul_le_mul_of_nonneg_left hdiv (by norm_num)
  unfold twoSingletonPrimeExponent
  calc
    2 *
          (2 * Real.sqrt (rootCutoff B) +
            56 * Real.sqrt (2 * (B : ℝ)) /
              ((Nat.log 2 B / 2 : ℕ) : ℝ)) ≤
        2 *
          (2 * Real.sqrt (B : ℝ) +
            56 * (2 * Real.sqrt (B : ℝ))) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add
          (mul_le_mul_of_nonneg_left hsqrtRoot (by norm_num))
          hscaledDiv)
        (by norm_num)
    _ = 228 * Real.sqrt (B : ℝ) := by ring

/-! ## A linear envelope for one fixed two-singleton shape -/

/-- Fixed coefficient used in the endpoint-independent harmonic bound. -/
noncomputable def twoSingletonHarmonicCoefficient (κ₀ : ℕ) : ℝ :=
  3 + Real.log ((κ₀ + 1 : ℕ) : ℝ)

/--
Endpoint-independent envelope for one fixed two-singleton shape.

The factor `228` is the preceding coarse Euler exponent.  It is intentionally
weaker than the final `sqrt(B)/log(B)` estimate, but already has the exact
`N^(1+o(1))` rate required by the moderate-host assembly.
-/
noncomputable def twoSingletonShapeFiberEnvelope
    (κ₀ N L : ℕ) : ℝ :=
  (N : ℝ) *
    (((κ₀ + 1 : ℕ) : ℝ) *
      twoSingletonHarmonicCoefficient κ₀ *
      ((L + 1 : ℕ) : ℝ) *
      Real.exp (228 * Real.sqrt ((L + 1 : ℕ) : ℝ)))

theorem twoSingletonHarmonicCoefficient_nonneg
    (κ₀ : ℕ) :
    0 ≤ twoSingletonHarmonicCoefficient κ₀ := by
  unfold twoSingletonHarmonicCoefficient
  have hlog :
      0 ≤ Real.log ((κ₀ + 1 : ℕ) : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (Nat.succ_pos κ₀)
  linarith

/-- Pointwise nonnegativity of the fixed-shape envelope. -/
theorem twoSingletonShapeFiberEnvelope_nonneg
    (κ₀ N L : ℕ) :
    0 ≤ twoSingletonShapeFiberEnvelope κ₀ N L := by
  unfold twoSingletonShapeFiberEnvelope
  exact mul_nonneg (Nat.cast_nonneg N)
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg (Nat.cast_nonneg _)
          (twoSingletonHarmonicCoefficient_nonneg κ₀))
        (Nat.cast_nonneg _))
      (Real.exp_nonneg _))

/--
The exponential `exp(228 sqrt(L+1))` is uniformly subpolynomial in a
critical run-length window.
-/
theorem twoSingletonSqrtEnvelope_uniformSubpolynomial
    {C : ℝ} (hC : 0 ≤ C) :
    UniformSubpolynomialOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun _N L =>
        Real.exp
          (228 * Real.sqrt ((L + 1 : ℕ) : ℝ))) := by
  obtain ⟨Nwindow, hwindow⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  let D : ℝ :=
    228 * Real.sqrt CriticalRunWindow.upperConstant
  have hD : 0 ≤ D := by
    dsimp only [D]
    positivity
  have hstandard :
      UniformSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C)
        (fun N _L =>
          Real.exp (D * Real.sqrt (Real.log N))) :=
    ExpSqrtLog.uniformSubpolynomialOn
      (CriticalRunWindow.InRunLengthWindow C) D hD
  apply UniformSubpolynomial.mono hstandard
  refine ⟨max Nwindow 1, ?_⟩
  intro N hN L hrun
  have hNwindow :
      Nwindow ≤ N :=
    (le_max_left _ _).trans hN
  have hNone :
      1 ≤ N :=
    (le_max_right _ _).trans hN
  have hcritical :
      CriticalWindowParameters.InCriticalWindow
        CriticalRunWindow.lowerConstant
        CriticalRunWindow.upperConstant N (L + 1) :=
    (hwindow N hNwindow L hrun).1
  have hlogN :
      0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hNone)
  have hupperNonneg :
      0 ≤ CriticalRunWindow.upperConstant :=
    (CriticalRunWindow.lowerConstant_pos.le.trans
      CriticalRunWindow.lowerConstant_lt_upperConstant.le)
  have hsqrt :
      Real.sqrt ((L + 1 : ℕ) : ℝ) ≤
        Real.sqrt CriticalRunWindow.upperConstant *
          Real.sqrt (Real.log N) := by
    calc
      Real.sqrt ((L + 1 : ℕ) : ℝ) ≤
          Real.sqrt
            (CriticalRunWindow.upperConstant *
              Real.log N) :=
        Real.sqrt_le_sqrt hcritical.2.2.2
      _ =
          Real.sqrt CriticalRunWindow.upperConstant *
            Real.sqrt (Real.log N) :=
        Real.sqrt_mul hupperNonneg _
  have hexp :
      Real.exp
          (228 * Real.sqrt ((L + 1 : ℕ) : ℝ)) ≤
        Real.exp (D * Real.sqrt (Real.log N)) := by
    apply Real.exp_le_exp.mpr
    dsimp only [D]
    nlinarith
  simp only [abs_of_pos (Real.exp_pos _)]
  exact hexp

/-- The fixed-shape envelope has rate `N^(1+o(1))`. -/
theorem twoSingletonShapeFiberEnvelope_uniformLinear
    {C : ℝ} (hC : 0 ≤ C) (κ₀ : ℕ) :
    UniformLinearSubpolynomialOn
      (CriticalRunWindow.InRunLengthWindow C)
      (twoSingletonShapeFiberEnvelope κ₀) := by
  have hheight :=
    CriticalRationalMassEnvelopes.runLengthAddOne_uniformSubpolynomial
      hC
  have hexponential :=
    twoSingletonSqrtEnvelope_uniformSubpolynomial hC
  let residual : ℕ → ℕ → ℝ :=
    fun _N L =>
      (((κ₀ + 1 : ℕ) : ℝ) *
        twoSingletonHarmonicCoefficient κ₀) *
        (((L + 1 : ℕ) : ℝ) *
          Real.exp
            (228 * Real.sqrt ((L + 1 : ℕ) : ℝ)))
  have hheightExp :
      UniformSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C)
        (fun N L =>
          (((L + 1 : ℕ) : ℝ) *
            Real.exp
              (228 * Real.sqrt ((L + 1 : ℕ) : ℝ)))) :=
    ExpSqrtLog.uniformSubpolynomialOn_mul
      hheight hexponential
  have hresidual :
      UniformSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C)
        residual := by
    simpa only [residual] using
      ExpSqrtLog.uniformSubpolynomialOn_const_mul
        ((((κ₀ + 1 : ℕ) : ℝ) *
          twoSingletonHarmonicCoefficient κ₀))
        hheightExp
  apply UniformLinear.of_linear_mul_subpolynomial hresidual
  refine ⟨0, ?_⟩
  intro N _hN L _hrun
  have henvelope :
      0 ≤ twoSingletonShapeFiberEnvelope κ₀ N L :=
    twoSingletonShapeFiberEnvelope_nonneg κ₀ N L
  have hresidualNonneg :
      0 ≤ residual N L := by
    dsimp only [residual]
    exact mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _)
        (twoSingletonHarmonicCoefficient_nonneg κ₀))
      (mul_nonneg (Nat.cast_nonneg _) (Real.exp_nonneg _))
  rw [abs_of_nonneg henvelope,
    abs_of_nonneg hresidualNonneg]
  unfold twoSingletonShapeFiberEnvelope
  dsimp only [residual]
  ring_nf
  exact le_rfl

/-! ## Bounded-ratio logarithmic bookkeeping -/

/--
In the critical window, the natural logarithm of `N` is at most twice the
height `B = L+1`.  The deliberately round constant avoids carrying
`log 2` through the finite estimates.
-/
theorem real_log_le_two_mul_height
    {N B : ℕ}
    (hcritical :
      CriticalWindowParameters.InCriticalWindow
        CriticalRunWindow.lowerConstant
        CriticalRunWindow.upperConstant N B) :
    Real.log (N : ℝ) ≤ 2 * (B : ℝ) := by
  have hlogTwoPos :
      0 < Real.log (2 : ℝ) :=
    Real.log_pos (by norm_num)
  have hlogTwoLeOne :
      Real.log (2 : ℝ) ≤ 1 :=
    Real.log_two_lt_d9.le.trans (by norm_num)
  have hlower := hcritical.2.2.1
  unfold CriticalRunWindow.lowerConstant at hlower
  have hscaled :
      Real.log (N : ℝ) ≤
        (B : ℝ) * (2 * Real.log 2) := by
    apply (div_le_iff₀ (by positivity :
      0 < (2 : ℝ) * Real.log 2)).mp
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using hlower
  calc
    Real.log (N : ℝ) ≤
        (B : ℝ) * (2 * Real.log 2) := hscaled
    _ ≤ (B : ℝ) * (2 * 1) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hlogTwoLeOne (by norm_num))
        (Nat.cast_nonneg B)
    _ = 2 * (B : ℝ) := by ring

/--
The cutoff and its harmonic logarithm lose only one linear factor in the
critical height, uniformly over `M ≤ κ₀N`.
-/
theorem boundedRatioCutoff_and_log_le
    {κ₀ N M L : ℕ}
    (hN : 1 ≤ N)
    (hNM : 2 * N ≤ M)
    (hMκ : M ≤ κ₀ * N)
    (hL : L ≤ N)
    (hcritical :
      CriticalWindowParameters.InCriticalWindow
        CriticalRunWindow.lowerConstant
        CriticalRunWindow.upperConstant N (L + 1)) :
    boundedRatioCutoff M L ≤ (κ₀ + 1) * N ∧
      1 + Real.log (boundedRatioCutoff M L : ℝ) ≤
        twoSingletonHarmonicCoefficient κ₀ *
          ((L + 1 : ℕ) : ℝ) := by
  have hcutoff :
      boundedRatioCutoff M L ≤ (κ₀ + 1) * N := by
    unfold boundedRatioCutoff
    calc
      M + L ≤ κ₀ * N + N :=
        Nat.add_le_add hMκ hL
      _ = (κ₀ + 1) * N := by ring
  have hNpos : 0 < N := by omega
  have hcutoffPos :
      0 < boundedRatioCutoff M L := by
    unfold boundedRatioCutoff
    omega
  have hupperPos :
      0 < (κ₀ + 1) * N :=
    Nat.mul_pos (Nat.succ_pos κ₀) hNpos
  have hlogCutoff :
      Real.log (boundedRatioCutoff M L : ℝ) ≤
        Real.log (((κ₀ + 1) * N : ℕ) : ℝ) :=
    Real.log_le_log
      (by exact_mod_cast hcutoffPos)
      (by exact_mod_cast hcutoff)
  have hlogProduct :
      Real.log (((κ₀ + 1) * N : ℕ) : ℝ) =
        Real.log ((κ₀ + 1 : ℕ) : ℝ) +
          Real.log (N : ℝ) := by
    have hkRealPos :
        (0 : ℝ) < ((κ₀ + 1 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.succ_pos κ₀)
    have hNRealPos :
        (0 : ℝ) < (N : ℝ) := by
      exact_mod_cast hNpos
    rw [Nat.cast_mul,
      Real.log_mul hkRealPos.ne' hNRealPos.ne']
  have hlogN :
      Real.log (N : ℝ) ≤
        2 * ((L + 1 : ℕ) : ℝ) :=
    real_log_le_two_mul_height hcritical
  have hlogCoeff :
      0 ≤ 1 + Real.log ((κ₀ + 1 : ℕ) : ℝ) := by
    have :
        0 ≤ Real.log ((κ₀ + 1 : ℕ) : ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast (Nat.succ_pos κ₀)
    linarith
  have hheightOne :
      (1 : ℝ) ≤ ((L + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.succ_pos L)
  have hcoeffHeight :
      1 + Real.log ((κ₀ + 1 : ℕ) : ℝ) ≤
        (1 + Real.log ((κ₀ + 1 : ℕ) : ℝ)) *
          ((L + 1 : ℕ) : ℝ) := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hheightOne hlogCoeff
  refine ⟨hcutoff, ?_⟩
  calc
    1 + Real.log (boundedRatioCutoff M L : ℝ) ≤
        (1 + Real.log ((κ₀ + 1 : ℕ) : ℝ)) +
          2 * ((L + 1 : ℕ) : ℝ) := by
      linarith
    _ ≤
        (1 + Real.log ((κ₀ + 1 : ℕ) : ℝ)) *
            ((L + 1 : ℕ) : ℝ) +
          2 * ((L + 1 : ℕ) : ℝ) :=
      by linarith
    _ =
        twoSingletonHarmonicCoefficient κ₀ *
          ((L + 1 : ℕ) : ℝ) := by
      unfold twoSingletonHarmonicCoefficient
      ring

/-! ## Eventual domination of every fixed two-singleton shape -/

/--
Every admissible two-singleton shape is eventually bounded by the common
endpoint-independent envelope.  This is the precise `Q₂` input required by
the moderate-host assembly.
-/
theorem card_twoSingletonShapeFiber_cast_le_envelope_eventually
    {C : ℝ} (hC : 0 ≤ C) (κ₀ A : ℕ) :
    ∃ N₂ : ℕ, ∀ N ≥ N₂, ∀ M L,
      2 * N ≤ M →
      M ≤ κ₀ * N →
      CriticalRunWindow.InRunLengthWindow C N L →
      ∀ shape ∈ boundedOffsetShapes L 10,
        shape.1.card + shape.2.card = 2 →
        ((boundedComponentHostsOfShape
          N M A L 10 shape).card : ℝ) ≤
          twoSingletonShapeFiberEnvelope κ₀ N L := by
  obtain ⟨Nwindow, hwindow⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  obtain ⟨Nadm, hadm⟩ :=
    CriticalWeightedDefect.admissible_eventually
      CriticalRunWindow.lowerConstant_pos
      CriticalRunWindow.lowerConstant_lt_upperConstant
  obtain ⟨Nsixteen, hsixteen⟩ :=
    DependencyEdgesCritical.runLengthAddOne_tends_to_infinity
      hC 16
  refine
    ⟨max Nwindow (max Nadm (max Nsixteen 2)), ?_⟩
  intro N hN M L hNM hMκ hrun shape hshape htotal
  have hNwindow :
      Nwindow ≤ N :=
    (le_max_left _ _).trans hN
  have htail :
      max Nadm (max Nsixteen 2) ≤ N :=
    (le_max_right _ _).trans hN
  have hNadm :
      Nadm ≤ N :=
    (le_max_left _ _).trans htail
  have htail' :
      max Nsixteen 2 ≤ N :=
    (le_max_right _ _).trans htail
  have hNsixteen :
      Nsixteen ≤ N :=
    (le_max_left _ _).trans htail'
  have hNtwo :
      2 ≤ N :=
    (le_max_right _ _).trans htail'
  have hcritical :
      CriticalWindowParameters.InCriticalWindow
        CriticalRunWindow.lowerConstant
        CriticalRunWindow.upperConstant N (L + 1) :=
    (hwindow N hNwindow L hrun).1
  have hAdm :=
    hadm N hNadm (L + 1) hcritical
  have htwoHeight :
      2 * (L + 1) ≤ N :=
    CriticalWindowParameters.two_mul_H_le_N_of_criticalWindow
      hAdm.1 hAdm.2.2.2.1
  have hL :
      L ≤ N := by omega
  have hB :
      16 ≤ L + 1 :=
    hsixteen N hNsixteen L hrun
  obtain ⟨hcutoff, hlog⟩ :=
    boundedRatioCutoff_and_log_le
      (show 1 ≤ N by omega) hNM hMκ hL hcritical
  have hcutoffReal :
      (boundedRatioCutoff M L : ℝ) ≤
        ((κ₀ + 1 : ℕ) : ℝ) * (N : ℝ) := by
    exact_mod_cast hcutoff
  have hcutoffPosNat :
      0 < boundedRatioCutoff M L := by
    unfold boundedRatioCutoff
    omega
  have hlogNonneg :
      0 ≤ 1 + Real.log (boundedRatioCutoff M L : ℝ) := by
    have hcutoffOne :
        (1 : ℝ) ≤ (boundedRatioCutoff M L : ℝ) := by
      exact_mod_cast hcutoffPosNat
    have := Real.log_nonneg hcutoffOne
    linarith
  have hprime :
      (twoSingletonParameterCount M L 10 : ℝ) ≤
        (boundedRatioCutoff M L : ℝ) *
          (1 + Real.log (boundedRatioCutoff M L : ℝ)) *
            Real.exp (twoSingletonPrimeExponent (L + 1)) := by
    simpa only [twoSingletonPrimeExponent, Nat.cast_mul,
      Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] using
      (twoSingletonParameterCount_cast_le_primeSensitive
        (M := M) (L := L) (K := 10) hB)
  have hexponent :
      Real.exp (twoSingletonPrimeExponent (L + 1)) ≤
        Real.exp
          (228 * Real.sqrt ((L + 1 : ℕ) : ℝ)) :=
    Real.exp_le_exp.mpr
      (twoSingletonPrimeExponent_le_sqrt hB)
  have hfinite :
      ((boundedComponentHostsOfShape
        N M A L 10 shape).card : ℝ) ≤
        (twoSingletonParameterCount M L 10 : ℝ) := by
    exact_mod_cast
      card_twoSingletonShapeFiber_le_parameterCount
        hNtwo hshape htotal
  calc
    ((boundedComponentHostsOfShape
        N M A L 10 shape).card : ℝ) ≤
        (twoSingletonParameterCount M L 10 : ℝ) :=
      hfinite
    _ ≤
        (boundedRatioCutoff M L : ℝ) *
          (1 + Real.log (boundedRatioCutoff M L : ℝ)) *
            Real.exp (twoSingletonPrimeExponent (L + 1)) :=
      hprime
    _ ≤
        (((κ₀ + 1 : ℕ) : ℝ) * (N : ℝ)) *
          (twoSingletonHarmonicCoefficient κ₀ *
            ((L + 1 : ℕ) : ℝ)) *
          Real.exp
            (228 * Real.sqrt ((L + 1 : ℕ) : ℝ)) := by
      exact mul_le_mul
        (mul_le_mul hcutoffReal hlog
          hlogNonneg
          (mul_nonneg (Nat.cast_nonneg _)
            (Nat.cast_nonneg _)))
        hexponent (Real.exp_nonneg _)
        (mul_nonneg
          (mul_nonneg (Nat.cast_nonneg _)
            (Nat.cast_nonneg _))
          (mul_nonneg
            (twoSingletonHarmonicCoefficient_nonneg κ₀)
            (Nat.cast_nonneg _)))
    _ = twoSingletonShapeFiberEnvelope κ₀ N L := by
      unfold twoSingletonShapeFiberEnvelope
      ring

/--
Packaged `Q₂` witness: nonnegative, uniformly `N^(1+o(1))`, and uniformly
dominant over every fixed two-singleton shape.
-/
theorem exists_twoSingletonShapeFiberEnvelope
    {C : ℝ} (hC : 0 ≤ C) (κ₀ A : ℕ) :
    ∃ Q₂ : ℕ → ℕ → ℝ,
      UniformLinearSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C) Q₂ ∧
      (∀ N L, 0 ≤ Q₂ N L) ∧
      ∃ N₂ : ℕ, ∀ N ≥ N₂, ∀ M L,
        2 * N ≤ M →
        M ≤ κ₀ * N →
        CriticalRunWindow.InRunLengthWindow C N L →
        ∀ shape ∈ boundedOffsetShapes L 10,
          shape.1.card + shape.2.card = 2 →
          ((boundedComponentHostsOfShape
            N M A L 10 shape).card : ℝ) ≤
            Q₂ N L := by
  refine
    ⟨twoSingletonShapeFiberEnvelope κ₀,
      twoSingletonShapeFiberEnvelope_uniformLinear hC κ₀,
      twoSingletonShapeFiberEnvelope_nonneg κ₀,
      ?_⟩
  exact
    card_twoSingletonShapeFiber_cast_le_envelope_eventually
      hC κ₀ A

/-! ## The source `sqrt(B) / log(B)` exponent -/

/--
Eventually `log B` is bounded by the fourth root of `B`.  Keeping this
small analytic fact separate makes every subsequent numerical absorption
transparent.
-/
theorem eventually_log_le_fourthRoot :
    ∃ B₀ : ℕ, ∀ B ≥ B₀,
      16 ≤ B ∧
      Real.log (B : ℝ) ≤
        Real.sqrt (Real.sqrt (B : ℝ)) := by
  have hquarter :
      0 < (1 / 4 : ℝ) := by norm_num
  have hraw :
      ∀ᶠ B : ℕ in Filter.atTop,
        ‖Real.log (B : ℝ)‖ ≤
          (1 : ℝ) * ‖(B : ℝ) ^ (1 / 4 : ℝ)‖ :=
    tendsto_natCast_atTop_atTop.eventually
      ((isLittleO_log_rpow_atTop hquarter).bound zero_lt_one)
  obtain ⟨B₀, hsharp⟩ :=
    Filter.eventually_atTop.mp
      (hraw.and (Filter.eventually_ge_atTop 16))
  refine ⟨B₀, ?_⟩
  intro B hB
  have hlarge := hsharp B hB
  have hBlog :
      0 < Real.log (B : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < B by omega))
  have hBnonneg :
      0 ≤ (B : ℝ) := by positivity
  have hfourth :
      (B : ℝ) ^ (1 / 4 : ℝ) =
        Real.sqrt (Real.sqrt (B : ℝ)) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
      ← Real.rpow_mul hBnonneg]
    congr 1
    ring
  refine ⟨hlarge.2, ?_⟩
  have h := hlarge.1
  rw [Real.norm_eq_abs, abs_of_pos hBlog,
    Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hBnonneg _),
    one_mul, hfourth] at h
  exact h

/--
The complete prime-sensitive exponent is eventually bounded by
`676 sqrt(B)/log(B)`.  The same threshold also records the two elementary
absorptions used below: `log B ≤ sqrt(B)/log B` and
`1 ≤ sqrt(B)/log B`.
-/
theorem twoSingletonPrimeExponent_le_criticalRatio_eventually :
    ∃ B₀ : ℕ, ∀ B ≥ B₀,
      16 ≤ B ∧
      twoSingletonPrimeExponent B ≤
        676 * twoSingletonCriticalRatio B ∧
      Real.log (B : ℝ) ≤ twoSingletonCriticalRatio B ∧
      1 ≤ twoSingletonCriticalRatio B := by
  obtain ⟨B₀, hB₀⟩ := eventually_log_le_fourthRoot
  refine ⟨B₀, ?_⟩
  intro B hB₀B
  obtain ⟨hB, hlogFourth⟩ := hB₀ B hB₀B
  have hBrealNonneg :
      0 ≤ (B : ℝ) := by positivity
  have hBlog :
      0 < Real.log (B : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < B by omega))
  have hsqrtBNonneg :
      0 ≤ Real.sqrt (B : ℝ) :=
    Real.sqrt_nonneg _
  have hfourthNonneg :
      0 ≤ Real.sqrt (Real.sqrt (B : ℝ)) :=
    Real.sqrt_nonneg _
  have hfourthSq :
      Real.sqrt (Real.sqrt (B : ℝ)) *
          Real.sqrt (Real.sqrt (B : ℝ)) =
        Real.sqrt (B : ℝ) :=
    Real.mul_self_sqrt hsqrtBNonneg
  have hlogSq :
      Real.log (B : ℝ) * Real.log (B : ℝ) ≤
        Real.sqrt (B : ℝ) := by
    calc
      Real.log (B : ℝ) * Real.log (B : ℝ) ≤
          Real.sqrt (Real.sqrt (B : ℝ)) *
            Real.sqrt (Real.sqrt (B : ℝ)) :=
        mul_self_le_mul_self hBlog.le hlogFourth
      _ = Real.sqrt (B : ℝ) := hfourthSq
  have hlogRatio :
      Real.log (B : ℝ) ≤
        twoSingletonCriticalRatio B := by
    unfold twoSingletonCriticalRatio
    exact (le_div_iff₀ hBlog).2 hlogSq
  have hlogEight :
      1 < Real.log (8 : ℝ) := by
    have htwo := Real.log_two_gt_d9
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num,
      Real.log_pow] 
    norm_num
    linarith
  have hlogEightLe :
      Real.log (8 : ℝ) ≤ Real.log (B : ℝ) := by
    apply Real.log_le_log (by norm_num)
    exact_mod_cast (show 8 ≤ B by omega)
  have honeRatio :
      1 ≤ twoSingletonCriticalRatio B :=
    (hlogEight.trans_le hlogEightLe).le.trans hlogRatio
  have hrootSq :
      rootCutoff B ^ 2 ≤ B :=
    rootCutoff_sq_le (by omega)
  have hrootToSqrt :
      (rootCutoff B : ℝ) ≤
        Real.sqrt (B : ℝ) := by
    have hcast :
        ((rootCutoff B : ℝ) ^ 2) ≤ (B : ℝ) := by
      exact_mod_cast hrootSq
    have hsqrt := Real.sqrt_le_sqrt hcast
    simpa only [Real.sqrt_sq (Nat.cast_nonneg _)] using hsqrt
  have hsqrtRoot :
      Real.sqrt (rootCutoff B : ℝ) ≤
        Real.sqrt (Real.sqrt (B : ℝ)) :=
    Real.sqrt_le_sqrt hrootToSqrt
  have hfourthRatio :
      Real.sqrt (Real.sqrt (B : ℝ)) ≤
        twoSingletonCriticalRatio B := by
    unfold twoSingletonCriticalRatio
    apply (le_div_iff₀ hBlog).2
    calc
      Real.sqrt (Real.sqrt (B : ℝ)) *
            Real.log (B : ℝ) ≤
          Real.sqrt (Real.sqrt (B : ℝ)) *
            Real.sqrt (Real.sqrt (B : ℝ)) :=
        mul_le_mul_of_nonneg_left hlogFourth hfourthNonneg
      _ = Real.sqrt (B : ℝ) := hfourthSq
  have hrootRatio :
      Real.sqrt (rootCutoff B : ℝ) ≤
        twoSingletonCriticalRatio B :=
    hsqrtRoot.trans hfourthRatio
  have hlogFour :
      4 ≤ Nat.log 2 B := by
    apply Nat.le_log_of_pow_le (by norm_num)
    norm_num
    exact hB
  have hqPosNat :
      0 < Nat.log 2 B / 2 := by omega
  have hqPos :
      (0 : ℝ) <
        ((Nat.log 2 B / 2 : ℕ) : ℝ) := by
    exact_mod_cast hqPosNat
  have hrealLogLeNat :
      Real.log (B : ℝ) ≤ (Nat.log 2 B : ℝ) :=
    CriticalWindowScale.real_log_le_nat_log_two
      (show 8 ≤ B by omega)
  have hnatLogLeThreeHalf :
      Nat.log 2 B ≤ 3 * (Nat.log 2 B / 2) := by
    omega
  have hrealLogLeThreeHalf :
      Real.log (B : ℝ) ≤
        3 * ((Nat.log 2 B / 2 : ℕ) : ℝ) := by
    calc
      Real.log (B : ℝ) ≤ (Nat.log 2 B : ℝ) :=
        hrealLogLeNat
      _ ≤ (3 * (Nat.log 2 B / 2) : ℕ) := by
        exact_mod_cast hnatLogLeThreeHalf
      _ = 3 * ((Nat.log 2 B / 2 : ℕ) : ℝ) := by
        push_cast
        ring
  have hsqrtTwo :
      Real.sqrt (2 : ℝ) ≤ 2 := by
    rw [Real.sqrt_le_iff]
    constructor <;> norm_num
  have hsqrtTwoB :
      Real.sqrt (2 * (B : ℝ)) ≤
        2 * Real.sqrt (B : ℝ) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    exact mul_le_mul_of_nonneg_right
      hsqrtTwo hsqrtBNonneg
  have hsecond :
      Real.sqrt (2 * (B : ℝ)) /
          ((Nat.log 2 B / 2 : ℕ) : ℝ) ≤
        6 * twoSingletonCriticalRatio B := by
    calc
      Real.sqrt (2 * (B : ℝ)) /
            ((Nat.log 2 B / 2 : ℕ) : ℝ) =
          3 * Real.sqrt (2 * (B : ℝ)) /
            (3 * ((Nat.log 2 B / 2 : ℕ) : ℝ)) := by
        field_simp
      _ ≤
          3 * Real.sqrt (2 * (B : ℝ)) /
            Real.log (B : ℝ) := by
        apply div_le_div_of_nonneg_left
        · positivity
        · exact hBlog
        · exact hrealLogLeThreeHalf
      _ ≤
          (6 * Real.sqrt (B : ℝ)) /
            Real.log (B : ℝ) := by
        apply div_le_div_of_nonneg_right
        · nlinarith
        · exact hBlog.le
      _ = 6 * twoSingletonCriticalRatio B := by
        unfold twoSingletonCriticalRatio
        ring
  refine ⟨hB, ?_, hlogRatio, honeRatio⟩
  unfold twoSingletonPrimeExponent
  calc
    2 *
          (2 * Real.sqrt (rootCutoff B) +
            56 * Real.sqrt (2 * (B : ℝ)) /
              ((Nat.log 2 B / 2 : ℕ) : ℝ)) ≤
        2 *
          (2 * twoSingletonCriticalRatio B +
            56 * (6 * twoSingletonCriticalRatio B)) := by
      apply mul_le_mul_of_nonneg_left
      · exact add_le_add
          (mul_le_mul_of_nonneg_left hrootRatio (by norm_num))
          (by
            calc
              56 * Real.sqrt (2 * (B : ℝ)) /
                    ((Nat.log 2 B / 2 : ℕ) : ℝ) =
                  56 *
                    (Real.sqrt (2 * (B : ℝ)) /
                      ((Nat.log 2 B / 2 : ℕ) : ℝ)) := by ring
              _ ≤ 56 *
                    (6 * twoSingletonCriticalRatio B) :=
                mul_le_mul_of_nonneg_left hsecond (by norm_num))
      · norm_num
    _ = 676 * twoSingletonCriticalRatio B := by ring

/-! ## Absorbing the polynomial prefactor -/

/-- The fixed bounded-ratio coefficient left before the five powers of `B`. -/
noncomputable def twoSingletonPolynomialCoefficient (κ₀ : ℕ) : ℝ :=
  9 * ((κ₀ + 1 : ℕ) : ℝ) *
    twoSingletonHarmonicCoefficient κ₀

/--
An explicit terminal constant for the complete size-two population.

The summands are respectively the bounded-ratio coefficient, five powers
of `B`, and the explicit Euler exponent `676`.
-/
noncomputable def twoSingletonTerminalConstant (κ₀ : ℕ) : ℝ :=
  twoSingletonPolynomialCoefficient κ₀ + 681

theorem twoSingletonPolynomialCoefficient_nonneg
    (κ₀ : ℕ) :
    0 ≤ twoSingletonPolynomialCoefficient κ₀ := by
  unfold twoSingletonPolynomialCoefficient
  exact mul_nonneg
    (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
    (twoSingletonHarmonicCoefficient_nonneg κ₀)

theorem twoSingletonTerminalConstant_nonneg
    (κ₀ : ℕ) :
    0 ≤ twoSingletonTerminalConstant κ₀ := by
  unfold twoSingletonTerminalConstant
  have := twoSingletonPolynomialCoefficient_nonneg κ₀
  linarith

/--
The polynomial prefactor and prime-sensitive Euler loss fit inside the
explicit terminal exponential once the critical-ratio comparisons hold.
-/
theorem twoSingletonPolynomialEuler_le_terminalExp
    (κ₀ : ℕ) {B : ℕ}
    (hB : 16 ≤ B)
    (hexponent :
      twoSingletonPrimeExponent B ≤
        676 * twoSingletonCriticalRatio B)
    (hlog :
      Real.log (B : ℝ) ≤ twoSingletonCriticalRatio B)
    (hratioOne :
      1 ≤ twoSingletonCriticalRatio B) :
    twoSingletonPolynomialCoefficient κ₀ *
          (B : ℝ) ^ 5 *
          Real.exp (twoSingletonPrimeExponent B) ≤
      Real.exp
        (twoSingletonTerminalConstant κ₀ *
          twoSingletonCriticalRatio B) := by
  let P : ℝ := twoSingletonPolynomialCoefficient κ₀
  let R : ℝ := twoSingletonCriticalRatio B
  have hP :
      0 ≤ P := by
    simpa only [P] using
      twoSingletonPolynomialCoefficient_nonneg κ₀
  have hR :
      0 ≤ R :=
    zero_le_one.trans (by simpa only [R] using hratioOne)
  have hPmul :
      P ≤ P * R := by
    dsimp only [R]
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left
        hratioOne hP
  have hPexp :
      P ≤ Real.exp (P * R) := by
    calc
      P ≤ P + 1 := by linarith
      _ ≤ Real.exp P := Real.add_one_le_exp P
      _ ≤ Real.exp (P * R) :=
        Real.exp_le_exp.mpr hPmul
  have hBrealPos :
      0 < (B : ℝ) := by
    exact_mod_cast (show 0 < B by omega)
  have hBexp :
      (B : ℝ) ≤ Real.exp R := by
    calc
      (B : ℝ) = Real.exp (Real.log (B : ℝ)) :=
        (Real.exp_log hBrealPos).symm
      _ ≤ Real.exp R :=
        Real.exp_le_exp.mpr (by simpa only [R] using hlog)
  have hBpow :
      (B : ℝ) ^ 5 ≤ Real.exp (5 * R) := by
    calc
      (B : ℝ) ^ 5 ≤ (Real.exp R) ^ 5 :=
        pow_le_pow_left₀ (Nat.cast_nonneg B) hBexp 5
      _ = Real.exp (5 * R) := by
        rw [← Real.exp_nat_mul]
        norm_num
  have hEuler :
      Real.exp (twoSingletonPrimeExponent B) ≤
        Real.exp (676 * R) :=
    Real.exp_le_exp.mpr
      (by simpa only [R] using hexponent)
  have hfirstProduct :
      P * (B : ℝ) ^ 5 ≤
        Real.exp (P * R) * Real.exp (5 * R) :=
    mul_le_mul hPexp hBpow (pow_nonneg (Nat.cast_nonneg B) _)
      (Real.exp_nonneg _)
  change
    P * (B : ℝ) ^ 5 *
          Real.exp (twoSingletonPrimeExponent B) ≤
      Real.exp
        ((P + 681) * R)
  calc
    P * (B : ℝ) ^ 5 *
          Real.exp (twoSingletonPrimeExponent B) ≤
        (Real.exp (P * R) * Real.exp (5 * R)) *
          Real.exp (676 * R) :=
      mul_le_mul hfirstProduct hEuler
        (Real.exp_nonneg _)
        (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
    _ =
        Real.exp
          ((P + 681) * R) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

/-! ## Complete size-two host population -/

/--
The complete population of component hosts of size two is eventually
bounded by the source-shaped envelope

`N exp(Cterm sqrt(L+1) / log(L+1))`,

with the explicit nonnegative constant
`Cterm = twoSingletonTerminalConstant κ₀`.
-/
theorem card_boundedComponentHosts_two_cast_le_sizeTwoEnvelope_eventually
    {C : ℝ} (hC : 0 ≤ C) (κ₀ A : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ M L,
      2 * N ≤ M →
      M ≤ κ₀ * N →
      CriticalRunWindow.InRunLengthWindow C N L →
      ((boundedComponentHosts N M A L 2).card : ℝ) ≤
        sizeTwoComponentHostEnvelope
          (twoSingletonTerminalConstant κ₀) N L := by
  obtain ⟨B₀, hsharp⟩ :=
    twoSingletonPrimeExponent_le_criticalRatio_eventually
  obtain ⟨Nwindow, hwindow⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  obtain ⟨Nadm, hadm⟩ :=
    CriticalWeightedDefect.admissible_eventually
      CriticalRunWindow.lowerConstant_pos
      CriticalRunWindow.lowerConstant_lt_upperConstant
  obtain ⟨Nlarge, hlarge⟩ :=
    DependencyEdgesCritical.runLengthAddOne_tends_to_infinity
      hC B₀
  refine
    ⟨max Nwindow (max Nadm (max Nlarge 2)), ?_⟩
  intro N hN M L hNM hMκ hrun
  have hNwindow :
      Nwindow ≤ N :=
    (le_max_left _ _).trans hN
  have htail :
      max Nadm (max Nlarge 2) ≤ N :=
    (le_max_right _ _).trans hN
  have hNadm :
      Nadm ≤ N :=
    (le_max_left _ _).trans htail
  have htail' :
      max Nlarge 2 ≤ N :=
    (le_max_right _ _).trans htail
  have hNlarge :
      Nlarge ≤ N :=
    (le_max_left _ _).trans htail'
  have hNtwo :
      2 ≤ N :=
    (le_max_right _ _).trans htail'
  have hcritical :
      CriticalWindowParameters.InCriticalWindow
        CriticalRunWindow.lowerConstant
        CriticalRunWindow.upperConstant N (L + 1) :=
    (hwindow N hNwindow L hrun).1
  have hAdm :=
    hadm N hNadm (L + 1) hcritical
  have htwoHeight :
      2 * (L + 1) ≤ N :=
    CriticalWindowParameters.two_mul_H_le_N_of_criticalWindow
      hAdm.1 hAdm.2.2.2.1
  have hL :
      L ≤ N := by omega
  have hBlarge :
      B₀ ≤ L + 1 :=
    hlarge N hNlarge L hrun
  obtain ⟨hB, hexponent, hlogRatio, hratioOne⟩ :=
    hsharp (L + 1) hBlarge
  obtain ⟨hcutoff, hlog⟩ :=
    boundedRatioCutoff_and_log_le
      (show 1 ≤ N by omega) hNM hMκ hL hcritical
  have hcutoffReal :
      (boundedRatioCutoff M L : ℝ) ≤
        ((κ₀ + 1 : ℕ) : ℝ) * (N : ℝ) := by
    exact_mod_cast hcutoff
  have hcutoffPosNat :
      0 < boundedRatioCutoff M L := by
    unfold boundedRatioCutoff
    omega
  have hlogNonneg :
      0 ≤ 1 + Real.log (boundedRatioCutoff M L : ℝ) := by
    have hcutoffOne :
        (1 : ℝ) ≤ (boundedRatioCutoff M L : ℝ) := by
      exact_mod_cast hcutoffPosNat
    have := Real.log_nonneg hcutoffOne
    linarith
  have hcutoffUpperNonneg :
      0 ≤ ((κ₀ + 1 : ℕ) : ℝ) * (N : ℝ) :=
    mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hinner :
      (boundedRatioCutoff M L : ℝ) *
            (1 + Real.log (boundedRatioCutoff M L : ℝ)) *
            Real.exp (twoSingletonPrimeExponent (L + 1)) ≤
        (((κ₀ + 1 : ℕ) : ℝ) * (N : ℝ)) *
            (twoSingletonHarmonicCoefficient κ₀ *
              ((L + 1 : ℕ) : ℝ)) *
            Real.exp (twoSingletonPrimeExponent (L + 1)) := by
    apply mul_le_mul_of_nonneg_right
    · exact mul_le_mul hcutoffReal hlog
        hlogNonneg hcutoffUpperNonneg
    · exact Real.exp_nonneg _
  have hfinite :
      ((boundedComponentHosts N M A L 2).card : ℝ) ≤
        (((3 * (L + 1) ^ 2) ^ 2 : ℕ) : ℝ) *
          ((boundedRatioCutoff M L : ℝ) *
            (1 + Real.log (boundedRatioCutoff M L : ℝ)) *
            Real.exp (twoSingletonPrimeExponent (L + 1))) := by
    simpa only [twoSingletonPrimeExponent, Nat.cast_mul,
      Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] using
      (card_boundedComponentHosts_two_cast_le_primeSensitive
        (N := N) (M := M) (A := A) (L := L) hNtwo hB)
  have hshapeCast :
      (((3 * (L + 1) ^ 2) ^ 2 : ℕ) : ℝ) =
        9 * ((L + 1 : ℕ) : ℝ) ^ 4 := by
    norm_num only [Nat.cast_pow, Nat.cast_mul,
      Nat.cast_ofNat]
    ring
  have hpolynomial :
      ((boundedComponentHosts N M A L 2).card : ℝ) ≤
        (N : ℝ) *
          (twoSingletonPolynomialCoefficient κ₀ *
            ((L + 1 : ℕ) : ℝ) ^ 5 *
            Real.exp (twoSingletonPrimeExponent (L + 1))) := by
    calc
      ((boundedComponentHosts N M A L 2).card : ℝ) ≤
          (((3 * (L + 1) ^ 2) ^ 2 : ℕ) : ℝ) *
            ((boundedRatioCutoff M L : ℝ) *
              (1 + Real.log (boundedRatioCutoff M L : ℝ)) *
              Real.exp (twoSingletonPrimeExponent (L + 1))) :=
        hfinite
      _ =
          (9 * ((L + 1 : ℕ) : ℝ) ^ 4) *
            ((boundedRatioCutoff M L : ℝ) *
              (1 + Real.log (boundedRatioCutoff M L : ℝ)) *
              Real.exp (twoSingletonPrimeExponent (L + 1))) := by
        rw [hshapeCast]
      _ ≤
          (9 * ((L + 1 : ℕ) : ℝ) ^ 4) *
            ((((κ₀ + 1 : ℕ) : ℝ) * (N : ℝ)) *
              (twoSingletonHarmonicCoefficient κ₀ *
                ((L + 1 : ℕ) : ℝ)) *
              Real.exp (twoSingletonPrimeExponent (L + 1))) :=
        mul_le_mul_of_nonneg_left hinner (by positivity)
      _ =
          (N : ℝ) *
            (twoSingletonPolynomialCoefficient κ₀ *
              ((L + 1 : ℕ) : ℝ) ^ 5 *
              Real.exp (twoSingletonPrimeExponent (L + 1))) := by
        unfold twoSingletonPolynomialCoefficient
        ring
  have habsorb :=
    twoSingletonPolynomialEuler_le_terminalExp
      κ₀ hB hexponent hlogRatio hratioOne
  calc
    ((boundedComponentHosts N M A L 2).card : ℝ) ≤
        (N : ℝ) *
          (twoSingletonPolynomialCoefficient κ₀ *
            ((L + 1 : ℕ) : ℝ) ^ 5 *
            Real.exp (twoSingletonPrimeExponent (L + 1))) :=
      hpolynomial
    _ ≤
        (N : ℝ) *
          Real.exp
            (twoSingletonTerminalConstant κ₀ *
              twoSingletonCriticalRatio (L + 1)) :=
      mul_le_mul_of_nonneg_left habsorb (Nat.cast_nonneg N)
    _ =
        sizeTwoComponentHostEnvelope
          (twoSingletonTerminalConstant κ₀) N L := by
      unfold sizeTwoComponentHostEnvelope
        twoSingletonCriticalRatio
      ring

/--
Existential form matching the statement used by the downstream terminal
assembly.
-/
theorem exists_sizeTwoComponentHostEnvelope
    {C : ℝ} (hC : 0 ≤ C) (κ₀ A : ℕ) :
    ∃ Cterm : ℝ, 0 ≤ Cterm ∧
      ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ M L,
        2 * N ≤ M →
        M ≤ κ₀ * N →
        CriticalRunWindow.InRunLengthWindow C N L →
        ((boundedComponentHosts N M A L 2).card : ℝ) ≤
          sizeTwoComponentHostEnvelope Cterm N L := by
  exact
    ⟨twoSingletonTerminalConstant κ₀,
      twoSingletonTerminalConstant_nonneg κ₀,
      card_boundedComponentHosts_two_cast_le_sizeTwoEnvelope_eventually
        hC κ₀ A⟩

end

end BoundedRatioTwoSingletonCritical
end PaperC
