import PaperC.Asymptotics.SteinChenCritical
import PaperC.Asymptotics.ExactLengthBadStartMassCritical
import PaperC.Asymptotics.DyadicKappaQuantitative
import PaperC.Asymptotics.NonterminalSectorSaving
import PaperC.Probability.MarkedSteinChenSplitBound

set_option maxHeartbeats 1800000

/-!
# Critical-window reduction for the truncated marked Stein--Chen terms

This file transports the already certified §13 first-term estimate through
the fixed shift `Q = L + E + 1`.  It proves unconditionally that the marked
first term is `o_{C,E}(1)`.

It also packages the exact final reduction for the retained marked count:
once the explicit finite relation envelope from
`MarkedSteinChenTerms` is shown to be `o_{C,E}(1)`, the averaged marked
total variation is `o_{C,E}(1)`.  This reduction introduces no proposition
or bridge; its premise is the concrete little-oh statement about the
already defined finite envelope.
-/

namespace PaperC
namespace MarkedSteinChenCritical

open ExactLengthBadStartMassCritical
open MarkedConditionalDependencyGraph
open MarkedSteinChenSplitBound
open MarkedSteinChenTerms

noncomputable section

/-- Real first Stein--Chen term of the retained marked family. -/
def markedBOneReal (E N L : ℕ) : ℝ :=
  ((markedBOneFinite N L E : ℚ) : ℝ)

/-- Real common-relation envelope for the marked second term. -/
def markedBTwoRelationEnvelopeReal (E N L : ℕ) : ℝ :=
  ((markedBTwoRelationEnvelope N L E : ℚ) : ℝ)

/-- Real sharper local/separated envelope for the marked second term. -/
def markedBTwoSplitEnvelopeReal (E N L : ℕ) : ℝ :=
  ((markedBTwoSplitEnvelope N L E : ℚ) : ℝ)

/-- Real form of the explicit numerator of the sharper marked bound. -/
def markedBTwoSplitNumeratorReal (E N L : ℕ) : ℝ :=
  (markedBTwoSplitNumerator N L E : ℝ)

/-- The explicit local contribution before the fixed mark multiplicity. -/
def markedLocalSplitNumeratorReal (E N L : ℕ) : ℝ :=
  (2 : ℝ) ^ (E + 1) *
    (2 * (N : ℝ) * ((markedCommonRowCount L E + 1 : ℕ) : ℝ))

/-- Total variation of the averaged retained marked count. -/
def retainedMarkedTotalVariation
    (E N L : ℕ) : ℝ :=
  SectionThirteenFiniteBound.natTotalVariation
    (averagedConditionalMarkedLaw N L E)
    (commonMarkedPoissonLaw N L E)

theorem markedBOneReal_nonneg (E N L : ℕ) :
    0 ≤ markedBOneReal E N L := by
  unfold markedBOneReal markedBOneFinite
  apply Rat.cast_nonneg.mpr
  exact Finset.sum_nonneg fun _ _ ↦
    Finset.sum_nonneg fun _ _ ↦ by positivity

theorem markedBTwoRelationEnvelopeReal_nonneg (E N L : ℕ) :
    0 ≤ markedBTwoRelationEnvelopeReal E N L := by
  classical
  unfold markedBTwoRelationEnvelopeReal markedBTwoRelationEnvelope
  apply Rat.cast_nonneg.mpr
  exact Finset.sum_nonneg fun _ _ ↦
    Finset.sum_nonneg fun _ _ ↦ by
      split_ifs <;> positivity

theorem markedBTwoSplitEnvelopeReal_nonneg (E N L : ℕ) :
    0 ≤ markedBTwoSplitEnvelopeReal E N L := by
  classical
  unfold markedBTwoSplitEnvelopeReal markedBTwoSplitEnvelope
  apply Rat.cast_nonneg.mpr
  exact Finset.sum_nonneg fun _ _ ↦
    Finset.sum_nonneg fun _ _ ↦ by
      split_ifs <;> positivity

theorem markedBTwoSplitNumeratorReal_nonneg (E N L : ℕ) :
    0 ≤ markedBTwoSplitNumeratorReal E N L := by
  unfold markedBTwoSplitNumeratorReal
  positivity

theorem markedLocalSplitNumeratorReal_nonneg (E N L : ℕ) :
    0 ≤ markedLocalSplitNumeratorReal E N L := by
  unfold markedLocalSplitNumeratorReal
  positivity

/--
The common-length first term pulled back along `Q=L+E+1` is uniformly
little-oh of one.
-/
theorem commonSteinBOne_shift_uniformLittleOOne
    {C : ℝ} (hC : 0 ≤ C) (E : ℕ) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun N L ↦
        SteinChenCritical.steinBOneReal
          N (markedCommonRowCount L E))
      (fun _ _ ↦ 1) := by
  have hshiftNonneg : 0 ≤ C + (E + 1 : ℕ) := by positivity
  have hcore :=
    SteinChenCritical.steinBOne_uniformLittleOOne hshiftNonneg
  intro ε hε
  obtain ⟨Ncore, hNcore⟩ := hcore ε hε
  refine ⟨Ncore, ?_⟩
  intro N hN L hrun
  exact hNcore N hN (markedCommonRowCount L E)
    (commonExactRowCount_in_runLengthWindow hrun)

/--
Marked first term:

`b₁^(E) = o_{C,E}(1)`.
-/
theorem markedBOneReal_uniformLittleOOne
    {C : ℝ} (hC : 0 ≤ C) (E : ℕ) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (markedBOneReal E)
      (fun _ _ ↦ 1) := by
  let A : ℝ := (E + 1 : ℝ) ^ 2 * (2 : ℝ) ^ (2 * E)
  have hApos : 0 < A := by
    dsimp only [A]
    positivity
  have hcommon := commonSteinBOne_shift_uniformLittleOOne hC E
  intro ε hε
  obtain ⟨Ncore, hNcore⟩ :=
    hcommon (ε / A) (div_pos hε hApos)
  refine ⟨Ncore, ?_⟩
  intro N hN L hrun
  have hbound :=
    hNcore N hN L hrun
  have hfiniteQ :=
    markedBOneFinite_le_commonSteinBOne N L E
  have hfinite :
      markedBOneReal E N L ≤
        A *
          SteinChenCritical.steinBOneReal
            N (markedCommonRowCount L E) := by
    unfold markedBOneReal A SteinChenCritical.steinBOneReal
    exact_mod_cast hfiniteQ
  have hcommonNonneg :
      0 ≤
        SteinChenCritical.steinBOneReal
          N (markedCommonRowCount L E) := by
    unfold SteinChenCritical.steinBOneReal
    apply Rat.cast_nonneg.mpr
    unfold SteinChenTerms.steinBOne
    exact Finset.sum_nonneg fun _ _ ↦ by
      unfold SteinChenTerms.conditionalMarginal
      positivity
  simp only [abs_one, mul_one,
    abs_of_nonneg (markedBOneReal_nonneg E N L)] at hbound ⊢
  rw [abs_of_nonneg hcommonNonneg] at hbound
  calc
    markedBOneReal E N L ≤
        A *
          SteinChenCritical.steinBOneReal
            N (markedCommonRowCount L E) :=
      hfinite
    _ ≤ A * (ε / A) :=
      mul_le_mul_of_nonneg_left hbound hApos.le
    _ = ε := by
      field_simp [ne_of_gt hApos]

/-! ## The sharper marked second term -/

/--
Pull a quadratic little-oh estimate back through the fixed common-row
shift `Q = L + E + 1`.
-/
private theorem commonShift_uniformLittleOQuadratic
    {C : ℝ} (E : ℕ) {f : ℕ → ℕ → ℝ}
    (hf :
      UniformLittleOOn
        (CriticalRunWindow.InRunLengthWindow (C + (E + 1 : ℕ)))
        f (fun N _ ↦ (N : ℝ) ^ 2)) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun N L ↦ f N (markedCommonRowCount L E))
      (fun N _ ↦ (N : ℝ) ^ 2) := by
  intro ε hε
  obtain ⟨Nf, hNf⟩ := hf ε hε
  refine ⟨Nf, ?_⟩
  intro N hN L hrun
  exact hNf N hN (markedCommonRowCount L E)
    (commonExactRowCount_in_runLengthWindow hrun)

/--
The explicit local numerator `2^(E+1) · 2N(Q+1)` is uniformly
little-oh of `N²` for every fixed mark cutoff.
-/
theorem markedLocalSplitNumeratorReal_uniformLittleOQuadratic
    {C : ℝ} (hC : 0 ≤ C) (E : ℕ) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (markedLocalSplitNumeratorReal E)
      (fun N _ ↦ (N : ℝ) ^ 2) := by
  have hshiftNonneg : 0 ≤ C + (E + 1 : ℕ) := by positivity
  have hlengthShift :=
    CriticalRationalMassEnvelopes.runLengthAddOne_uniformSubpolynomial
      hshiftNonneg
  have hlength :
      UniformSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C)
        (fun _ L ↦
          (((markedCommonRowCount L E + 1 : ℕ) : ℝ))) := by
    intro k hk
    obtain ⟨Nlength, hNlength⟩ := hlengthShift k hk
    refine ⟨Nlength, ?_⟩
    intro N hN L hrun
    exact hNlength N hN (markedCommonRowCount L E)
      (commonExactRowCount_in_runLengthWindow hrun)
  have hfactor :
      UniformSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C)
        (fun _ L ↦
          ((2 : ℝ) ^ (E + 1) * 2) *
            (((markedCommonRowCount L E + 1 : ℕ) : ℝ))) :=
    ExpSqrtLog.uniformSubpolynomialOn_const_mul
      ((2 : ℝ) ^ (E + 1) * 2) hlength
  have hlinear :
      UniformLinearSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C)
        (markedLocalSplitNumeratorReal E) := by
    apply UniformLinear.of_linear_mul_subpolynomial hfactor
    refine ⟨0, ?_⟩
    intro N _hN L _hrun
    rw [abs_of_nonneg (markedLocalSplitNumeratorReal_nonneg E N L)]
    rw [abs_of_nonneg (by positivity :
      0 ≤
        ((2 : ℝ) ^ (E + 1) * 2) *
          (((markedCommonRowCount L E + 1 : ℕ) : ℝ)))]
    unfold markedLocalSplitNumeratorReal
    ring_nf
    exact le_rfl
  exact
    SectionTwelveMoments.uniformLittleOQuadratic_of_uniformLinear hlinear

/-- Multiplication by a fixed nonnegative constant preserves uniform
little-oh at an arbitrary scale. -/
private theorem uniformLittleOOn_const_mul
    {admissible : ℕ → ℕ → Prop}
    {f scale : ℕ → ℕ → ℝ}
    (A : ℝ) (hA : 0 ≤ A)
    (hf : UniformLittleOOn admissible f scale) :
    UniformLittleOOn admissible
      (fun N L ↦ A * f N L) scale := by
  by_cases hAzero : A = 0
  · subst A
    simpa using uniformLittleOOn_zero admissible scale
  · have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hAzero)
    intro ε hε
    obtain ⟨Nf, hNf⟩ := hf (ε / A) (div_pos hε hApos)
    refine ⟨Nf, ?_⟩
    intro N hN L hrun
    have hbound := hNf N hN L hrun
    rw [abs_mul, abs_of_nonneg hA]
    calc
      A * |f N L| ≤ A * ((ε / A) * |scale N L|) :=
        mul_le_mul_of_nonneg_left hbound hA
      _ = ε * |scale N L| := by
        field_simp [ne_of_gt hApos]

/--
The complete §13 second-term numerator, pulled back to the common marked
row count, is uniformly little-oh of `N²`.  Its sole arithmetic input is
the canonical dyadic mother-mass theorem.
-/
theorem commonSteinBTwoNumerator_shift_uniformLittleOQuadratic
    {C : ℝ} (hC : 0 ≤ C) (E : ℕ)
    (hES :
      EvertseSilvermanInput.EvertseSilvermanAbscissaStatement)
    (hPell :
      PellInput.GeneralizedPellPolynomialBoxStatement) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun N L ↦
        SteinChenCritical.steinBTwoNumerator
          N (markedCommonRowCount L E))
      (fun N _ ↦ (N : ℝ) ^ 2) := by
  have hshiftNonneg : 0 ≤ C + (E + 1 : ℕ) := by positivity
  have hhomBig :
      UniformBigOOn
        (CriticalRunWindow.InRunLengthWindow (C + (E + 1 : ℕ)))
        (PropositionElevenTwo.homogeneousMass 3)
        SectionThirteenRate.quadraticDivLogLogSquaredScale := by
    obtain ⟨Q₂, hQ₂Rate, hQ₂Nonneg, hQ₂Dom⟩ :=
      BoundedRatioTwoSingletonCritical.exists_twoSingletonShapeFiberEnvelope
        hshiftNonneg 2 3
    obtain ⟨Cterm, hCterm, hhostsTwo⟩ :=
      BoundedRatioTwoSingletonCritical.exists_sizeTwoComponentHostEnvelope
        hshiftNonneg 2 3
    obtain ⟨hostEnvelope, hhostRate, hhostNonneg, hhostsTen⟩ :=
      BoundedRatioNonterminalMobileAssembly.evertseSilverman_generalizedPell_imply_exists_moderateNonterminalHostEnvelope
        hshiftNonneg 2 3 hES hPell Q₂ hQ₂Rate hQ₂Nonneg hQ₂Dom
    have hlogTwo : 0 < Real.log 2 :=
      Real.log_pos (by norm_num)
    let K : ℝ := (2 * Cterm + 1) / Real.log 2
    have hK : 0 ≤ K := by
      dsimp only [K]
      exact div_nonneg (by linarith) hlogTwo.le
    have hthreshold : 2 * Cterm < K * Real.log 2 := by
      dsimp only [K]
      rw [div_mul_cancel₀ _ hlogTwo.ne']
      linarith
    have hR2κ :=
      DyadicKappaQuantitative.R2κ_dyadic_uniformBigO
        hshiftNonneg hCterm hK hthreshold hES hPell hostEnvelope
          hhostRate hhostNonneg hhostsTen hhostsTwo
    have heq :
        PropositionElevenTwo.homogeneousMass 3 =
          fun N L ↦ PropositionSixteenOne.R2κ N (2 * N) L := by
      funext N L
      exact
        DyadicKappaTransport.homogeneousMass_eq_R2κ_two_mul
          3 N L
    rw [heq]
    exact hR2κ
  have hhomLittle :=
    NonterminalSectorSaving.uniformBigOOn_trans_uniformLittleOOn
      hhomBig
      (NonterminalSectorSaving.quadraticDivLogLogSquaredScale_uniformLittleO_quadratic
        (CriticalRunWindow.InRunLengthWindow (C + (E + 1 : ℕ))))
  have hcore :=
    SteinChenCritical.steinBTwoNumerator_uniformLittleOQuadratic
      (A := 3) hshiftNonneg hhomLittle
  exact commonShift_uniformLittleOQuadratic E hcore

/--
The explicit split numerator is dominated by the fixed mark multiplicity
times the local numerator plus the complete §13 numerator at the common
row count.
-/
theorem markedBTwoSplitNumeratorReal_le_common
    (E N L : ℕ) :
    markedBTwoSplitNumeratorReal E N L ≤
      (((E + 1 : ℕ) : ℝ) ^ 2) *
        (markedLocalSplitNumeratorReal E N L +
          SteinChenCritical.steinBTwoNumerator
            N (markedCommonRowCount L E)) := by
  unfold markedBTwoSplitNumeratorReal markedBTwoSplitNumerator
    markedLocalSplitNumeratorReal SteinChenCritical.steinBTwoNumerator
  push_cast
  simp only [markedPrimeCutoff,
    ExactLengthBadStartMass.exactLengthBaseCutoff,
    markedCommonRowCount]
  have hpairs :
      0 ≤
        ((SectionTwelveMoments.touchingOffDiagPairs
          N (ExactLengthBadStartMass.commonExactRowCount L E)).card : ℝ) := by
    positivity
  have htouch :
      0 ≤
        (TouchingMass.touchingMass
          N (ExactLengthBadStartMass.commonExactRowCount L E) : ℝ) := by
    positivity
  nlinarith

/--
The explicit split numerator is uniformly `o_{C,E}(N²)`, with the
homogeneous mother mass supplied by the bounded-ratio `κ` proof.
-/
theorem markedBTwoSplitNumeratorReal_uniformLittleOQuadratic
    {C : ℝ} (hC : 0 ≤ C) (E : ℕ)
    (hES :
      EvertseSilvermanInput.EvertseSilvermanAbscissaStatement)
    (hPell :
      PellInput.GeneralizedPellPolynomialBoxStatement) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (markedBTwoSplitNumeratorReal E)
      (fun N _ ↦ (N : ℝ) ^ 2) := by
  have hlocal :=
    markedLocalSplitNumeratorReal_uniformLittleOQuadratic hC E
  have hcommon :=
    commonSteinBTwoNumerator_shift_uniformLittleOQuadratic
      hC E hES hPell
  have hsum :=
    PropositionElevenTwo.uniformLittleOOn_add hlocal hcommon
  let A : ℝ := (((E + 1 : ℕ) : ℝ) ^ 2)
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  have hscaled :=
    uniformLittleOOn_const_mul A hA hsum
  intro ε hε
  obtain ⟨Nscaled, hNscaled⟩ := hscaled ε hε
  refine ⟨Nscaled, ?_⟩
  intro N hN L hrun
  have hbound := hNscaled N hN L hrun
  have hdom := markedBTwoSplitNumeratorReal_le_common E N L
  have hcommonNonneg :
      0 ≤
        SteinChenCritical.steinBTwoNumerator
          N (markedCommonRowCount L E) := by
    unfold SteinChenCritical.steinBTwoNumerator
    positivity
  have hscaledNonneg :
      0 ≤
        A *
          (markedLocalSplitNumeratorReal E N L +
            SteinChenCritical.steinBTwoNumerator
              N (markedCommonRowCount L E)) := by
    exact mul_nonneg hA
      (add_nonneg
        (markedLocalSplitNumeratorReal_nonneg E N L)
        hcommonNonneg)
  simp only [abs_of_nonneg
      (markedBTwoSplitNumeratorReal_nonneg E N L),
    abs_of_nonneg hscaledNonneg,
    abs_of_nonneg (sq_nonneg (N : ℝ))] at hbound ⊢
  exact hdom.trans hbound

/--
A nonnegative quadratic little-oh numerator remains `o(1)` after division
by the marked denominator `2^(2(L+1))`.
-/
private theorem normalizedMarkedQuadratic_uniformLittleOOne
    {C : ℝ}
    {f : ℕ → ℕ → ℝ}
    (hC : 0 ≤ C)
    (hf :
      UniformLittleOOn
        (CriticalRunWindow.InRunLengthWindow C)
        f (fun N _ ↦ (N : ℝ) ^ 2))
    (hfNonneg : ∀ N L, 0 ≤ f N L) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun N L ↦ f N L / (2 : ℝ) ^ (2 * (L + 1)))
      (fun _ _ ↦ 1) := by
  obtain ⟨Nwindow, hwindow⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  let B := CriticalRunWindow.balanceConstant C
  have hBpos : 0 < B := by
    unfold B CriticalRunWindow.balanceConstant
    positivity
  intro ε hε
  let δ : ℝ := ε / B ^ 2
  have hδ : 0 < δ := by
    dsimp only [δ]
    positivity
  obtain ⟨Nf, hNf⟩ := hf δ hδ
  refine ⟨max Nwindow Nf, ?_⟩
  intro N hN L hrun
  have hw :=
    hwindow N ((le_max_left _ _).trans hN) L hrun
  have hbound :=
    hNf N ((le_max_right _ _).trans hN) L hrun
  have hfLe :
      f N L ≤ δ * (N : ℝ) ^ 2 := by
    simpa only [abs_of_nonneg (hfNonneg N L),
      abs_of_nonneg (sq_nonneg (N : ℝ))] using hbound
  have hratioBaseNonneg :
      0 ≤ (N : ℝ) / (2 : ℝ) ^ L := by positivity
  have hratioNonneg :
      0 ≤ (N : ℝ) / (2 : ℝ) ^ (L + 1) := by positivity
  have hbalanceBase :
      (N : ℝ) / (2 : ℝ) ^ L ≤ B := by
    simpa only [B] using hw.2.2
  have hbalance :
      (N : ℝ) / (2 : ℝ) ^ (L + 1) ≤ B := by
    rw [pow_succ]
    calc
      (N : ℝ) / ((2 : ℝ) ^ L * 2) =
          ((N : ℝ) / (2 : ℝ) ^ L) / 2 := by ring
      _ ≤ (N : ℝ) / (2 : ℝ) ^ L := by
        nlinarith
      _ ≤ B := hbalanceBase
  have hbalanceSq :
      ((N : ℝ) / (2 : ℝ) ^ (L + 1)) ^ 2 ≤ B ^ 2 :=
    pow_le_pow_left₀ hratioNonneg hbalance 2
  simp only [abs_div, abs_of_nonneg (hfNonneg N L),
    abs_of_pos (pow_pos (by norm_num : (0 : ℝ) < 2) (2 * (L + 1))),
    abs_one, mul_one]
  calc
    f N L / (2 : ℝ) ^ (2 * (L + 1)) ≤
        (δ * (N : ℝ) ^ 2) / (2 : ℝ) ^ (2 * (L + 1)) :=
      div_le_div_of_nonneg_right hfLe (by positivity)
    _ = δ * ((N : ℝ) / (2 : ℝ) ^ (L + 1)) ^ 2 := by
      rw [show 2 * (L + 1) = (L + 1) * 2 by omega, pow_mul]
      ring
    _ ≤ δ * B ^ 2 :=
      mul_le_mul_of_nonneg_left hbalanceSq hδ.le
    _ = ε := by
      dsimp only [δ]
      field_simp [ne_of_gt hBpos]

/--
The sharper marked relation envelope satisfies

`b₂^(E) = o_{C,E}(1)`.

The separated mass is supplied by the canonical bounded-ratio mother-mass
proof.
-/
theorem markedBTwoSplitEnvelopeReal_uniformLittleOOne
    {C : ℝ} (hC : 0 ≤ C) (E : ℕ)
    (hES :
      EvertseSilvermanInput.EvertseSilvermanAbscissaStatement)
    (hPell :
      PellInput.GeneralizedPellPolynomialBoxStatement) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (markedBTwoSplitEnvelopeReal E)
      (fun _ _ ↦ 1) := by
  have hnormalized :=
    normalizedMarkedQuadratic_uniformLittleOOne hC
      (markedBTwoSplitNumeratorReal_uniformLittleOQuadratic
        hC E hES hPell)
      (markedBTwoSplitNumeratorReal_nonneg E)
  obtain ⟨Nwindow, hwindow⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  intro ε hε
  obtain ⟨Nnorm, hNnorm⟩ := hnormalized ε hε
  refine ⟨max 2 (max Nwindow Nnorm), ?_⟩
  intro N hN L hrun
  have hNtwo : 2 ≤ N :=
    (le_max_left 2 (max Nwindow Nnorm)).trans hN
  have htail : max Nwindow Nnorm ≤ N :=
    (le_max_right 2 (max Nwindow Nnorm)).trans hN
  have hw :=
    hwindow N ((le_max_left Nwindow Nnorm).trans htail) L hrun
  have hLpos : 1 ≤ L := Nat.succ_le_iff.mpr hw.2.1
  have hfiniteQ :=
    markedBTwoSplitEnvelope_le_explicit
      (N := N) (L := L) (E := E) hNtwo hLpos
  have hfinite := (Rat.cast_le (K := ℝ)).2 hfiniteQ
  push_cast at hfinite
  have hbound :=
    hNnorm N ((le_max_right Nwindow Nnorm).trans htail) L hrun
  have hquotNonneg :
      0 ≤
        markedBTwoSplitNumeratorReal E N L /
          (2 : ℝ) ^ (2 * (L + 1)) := by
    exact div_nonneg
      (markedBTwoSplitNumeratorReal_nonneg E N L) (by positivity)
  simp only [abs_one, mul_one,
    abs_of_nonneg (markedBTwoSplitEnvelopeReal_nonneg E N L)] at hbound ⊢
  rw [abs_of_nonneg hquotNonneg] at hbound
  apply hfinite.trans
  simpa only [markedBTwoSplitEnvelopeReal,
    markedBTwoSplitNumeratorReal] using hbound

/--
Source-shaped wrapper using the internally discharged quadratic-order
conductor comparison and the Nicolas--Robin divisor estimate.
-/
theorem markedBTwoSplitEnvelopeReal_uniformLittleOOne_canonical
    {C : ℝ} (hC : 0 ≤ C) (E : ℕ)
    (hES :
      EvertseSilvermanInput.EvertseSilvermanAbscissaStatement)
    (hDivisor :
      PellInput.NicolasRobinDivisorLogBoundStatement) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (markedBTwoSplitEnvelopeReal E)
      (fun _ _ ↦ 1) :=
  markedBTwoSplitEnvelopeReal_uniformLittleOOne
    hC E hES
      (PellInput.generalizedPellPolynomialBox_of_divisorLogBound hDivisor)

/--
Final finite-to-asymptotic reduction for the retained marked count.

The premise is exactly the remaining concrete estimate on
`markedBTwoRelationEnvelopeReal`; no abstract hypothesis is registered.
-/
theorem retainedMarkedTotalVariation_uniformLittleOOne_of_bTwoEnvelope
    (hAGG :
      ArratiaGoldsteinGordonInput.ArratiaGoldsteinGordonStatement)
    {C : ℝ} (hC : 0 ≤ C) (E : ℕ)
    (hBTwo :
      UniformLittleOOn
        (CriticalRunWindow.InRunLengthWindow C)
        (markedBTwoRelationEnvelopeReal E)
        (fun _ _ ↦ 1)) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (retainedMarkedTotalVariation E)
      (fun _ _ ↦ 1) := by
  have hBOne := markedBOneReal_uniformLittleOOne hC E
  obtain ⟨Nwindow, hwindow⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  intro ε hε
  obtain ⟨N1, hN1⟩ := hBOne (ε / 4) (by positivity)
  obtain ⟨N2, hN2⟩ := hBTwo (ε / 4) (by positivity)
  refine ⟨max 2 (max Nwindow (max N1 N2)), ?_⟩
  intro N hN L hrun
  have hNtwo : 2 ≤ N :=
    (le_max_left 2 (max Nwindow (max N1 N2))).trans hN
  have htail : max Nwindow (max N1 N2) ≤ N :=
    (le_max_right 2 (max Nwindow (max N1 N2))).trans hN
  have hLpos :
      1 ≤ L := by
    have hw := hwindow N
      ((le_max_left Nwindow (max N1 N2)).trans htail) L hrun
    exact Nat.succ_le_iff.mpr hw.2.1
  have hb1 := hN1 N
    ((le_max_left N1 N2).trans
      ((le_max_right Nwindow (max N1 N2)).trans htail)) L hrun
  have hb2 := hN2 N
    ((le_max_right N1 N2).trans
      ((le_max_right Nwindow (max N1 N2)).trans htail)) L hrun
  have htvNonneg :
      0 ≤ retainedMarkedTotalVariation E N L := by
    unfold retainedMarkedTotalVariation
    exact SectionThirteenFiniteBound.natTotalVariation_nonneg _ _
  have hbasic :=
    averagedConditionalMarked_natTotalVariation_le
      (E := E) hAGG hNtwo hLpos
  have hb1' :
      markedBOneReal E N L ≤ ε / 4 := by
    simpa only [abs_one, mul_one,
      abs_of_nonneg (markedBOneReal_nonneg E N L)] using hb1
  have hb2' :
      markedBTwoRelationEnvelopeReal E N L ≤ ε / 4 := by
    simpa only [abs_one, mul_one,
      abs_of_nonneg
        (markedBTwoRelationEnvelopeReal_nonneg E N L)] using hb2
  have hb2Finite :=
    markedBTwoAverage_le_relationEnvelope (N := N) (E := E) hLpos
  have hb2Cast :
      ((markedBTwoAverage N L E : ℚ) : ℝ) ≤
        markedBTwoRelationEnvelopeReal E N L :=
    Rat.cast_le.mpr hb2Finite
  simp only [abs_one, mul_one, abs_of_nonneg htvNonneg]
  unfold retainedMarkedTotalVariation
  calc
    SectionThirteenFiniteBound.natTotalVariation
        (averagedConditionalMarkedLaw N L E)
        (commonMarkedPoissonLaw N L E) ≤
      2 *
        (markedBOneReal E N L +
          ((markedBTwoAverage N L E : ℚ) : ℝ)) := by
      simpa only [markedBOneReal] using hbasic
    _ ≤ 2 * (ε / 4 + ε / 4) := by
      apply mul_le_mul_of_nonneg_left
      · exact add_le_add hb1' (hb2Cast.trans hb2')
      · norm_num
    _ = ε := by ring

/--
Final finite-to-asymptotic reduction through the sharper local/separated
second-term envelope.
-/
theorem retainedMarkedTotalVariation_uniformLittleOOne_of_bTwoSplitEnvelope
    (hAGG :
      ArratiaGoldsteinGordonInput.ArratiaGoldsteinGordonStatement)
    {C : ℝ} (hC : 0 ≤ C) (E : ℕ)
    (hBTwo :
      UniformLittleOOn
        (CriticalRunWindow.InRunLengthWindow C)
        (markedBTwoSplitEnvelopeReal E)
        (fun _ _ ↦ 1)) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (retainedMarkedTotalVariation E)
      (fun _ _ ↦ 1) := by
  have hBOne := markedBOneReal_uniformLittleOOne hC E
  obtain ⟨Nwindow, hwindow⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  intro ε hε
  obtain ⟨N1, hN1⟩ := hBOne (ε / 4) (by positivity)
  obtain ⟨N2, hN2⟩ := hBTwo (ε / 4) (by positivity)
  refine ⟨max 2 (max Nwindow (max N1 N2)), ?_⟩
  intro N hN L hrun
  have hNtwo : 2 ≤ N :=
    (le_max_left 2 (max Nwindow (max N1 N2))).trans hN
  have htail : max Nwindow (max N1 N2) ≤ N :=
    (le_max_right 2 (max Nwindow (max N1 N2))).trans hN
  have hLpos :
      1 ≤ L := by
    have hw := hwindow N
      ((le_max_left Nwindow (max N1 N2)).trans htail) L hrun
    exact Nat.succ_le_iff.mpr hw.2.1
  have hb1 := hN1 N
    ((le_max_left N1 N2).trans
      ((le_max_right Nwindow (max N1 N2)).trans htail)) L hrun
  have hb2 := hN2 N
    ((le_max_right N1 N2).trans
      ((le_max_right Nwindow (max N1 N2)).trans htail)) L hrun
  have htvNonneg :
      0 ≤ retainedMarkedTotalVariation E N L := by
    unfold retainedMarkedTotalVariation
    exact SectionThirteenFiniteBound.natTotalVariation_nonneg _ _
  have hbasic :=
    averagedConditionalMarked_natTotalVariation_le
      (E := E) hAGG hNtwo hLpos
  have hb1' :
      markedBOneReal E N L ≤ ε / 4 := by
    simpa only [abs_one, mul_one,
      abs_of_nonneg (markedBOneReal_nonneg E N L)] using hb1
  have hb2' :
      markedBTwoSplitEnvelopeReal E N L ≤ ε / 4 := by
    simpa only [abs_one, mul_one,
      abs_of_nonneg
        (markedBTwoSplitEnvelopeReal_nonneg E N L)] using hb2
  have hb2Finite :=
    markedBTwoAverage_le_splitEnvelope (N := N) (E := E) hLpos
  have hb2Cast :
      ((markedBTwoAverage N L E : ℚ) : ℝ) ≤
        markedBTwoSplitEnvelopeReal E N L :=
    Rat.cast_le.mpr hb2Finite
  simp only [abs_one, mul_one, abs_of_nonneg htvNonneg]
  unfold retainedMarkedTotalVariation
  calc
    SectionThirteenFiniteBound.natTotalVariation
        (averagedConditionalMarkedLaw N L E)
        (commonMarkedPoissonLaw N L E) ≤
      2 *
        (markedBOneReal E N L +
          ((markedBTwoAverage N L E : ℚ) : ℝ)) := by
      simpa only [markedBOneReal] using hbasic
    _ ≤ 2 * (ε / 4 + ε / 4) := by
      apply mul_le_mul_of_nonneg_left
      · exact add_le_add hb1' (hb2Cast.trans hb2')
      · norm_num
    _ = ε := by ring

/--
Canonical retained marked Stein--Chen convergence, conditional only on
the three source-level literature inputs AGG, Evertse--Silverman, and
Nicolas--Robin.  The conductor comparison is discharged internally.
-/
theorem retainedMarkedTotalVariation_uniformLittleOOne_canonical
    (hAGG :
      ArratiaGoldsteinGordonInput.ArratiaGoldsteinGordonStatement)
    {C : ℝ} (hC : 0 ≤ C) (E : ℕ)
    (hES :
      EvertseSilvermanInput.EvertseSilvermanAbscissaStatement)
    (hDivisor :
      PellInput.NicolasRobinDivisorLogBoundStatement) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (retainedMarkedTotalVariation E)
      (fun _ _ ↦ 1) :=
  retainedMarkedTotalVariation_uniformLittleOOne_of_bTwoSplitEnvelope
    hAGG hC E
      (markedBTwoSplitEnvelopeReal_uniformLittleOOne_canonical
        hC E hES hDivisor)

end

end MarkedSteinChenCritical
end PaperC
