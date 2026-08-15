import PaperC.Asymptotics.DyadicKappaQuantitative
import PaperC.Asymptotics.SectionThirteenRate
import PaperC.Probability.InfiniteStartProbabilityTransfer

set_option maxHeartbeats 2400000

/-!
# Corollary 13.10: the complete explicit total-variation rate

This module upgrades the qualitative Section 13 assembly to the manuscript's
explicit rate

`1 / (log log N)^2`.

All arithmetic dependence is factored through one quantitative
homogeneous-mass estimate.  The canonical endpoint obtains that estimate
from the bounded-ratio `κ` proof.  The dependency-edge rate below is derived
from the elementary harmonic estimate in `SectionThirteenRate`; no PNT,
Mertens theorem, primitive assumption, or additional bridge is introduced.
-/

namespace PaperC
namespace CorollaryThirteenTen

open BadStartCount
open LargePrimeDependencyGraph
open InfiniteStartProbabilityTransfer
open SectionThirteenCouplings
open SectionThirteenCritical
open SectionThirteenFiniteBound
open SectionThirteenRate
open SteinChenCritical
open TerminalPrimeCutoff

noncomputable section

/-! ## Lower-order terms in the dependency-edge estimate -/

/-- The square of the critical run length remains uniformly
subpolynomial. -/
theorem runLengthAddOneSquared_uniformSubpolynomial
    {C : ℝ} (hC : 0 ≤ C) :
    UniformSubpolynomialOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun _ L ↦ ((L + 1 : ℕ) : ℝ) ^ 2) := by
  have hB :=
    CriticalRationalMassEnvelopes.runLengthAddOne_uniformSubpolynomial hC
  simpa only [pow_two] using
    ExpSqrtLog.uniformSubpolynomialOn_mul hB hB

/-- The harmonic `N (L+1)^2 (1+log(3N))` contribution has a fixed power
saving relative to `N²`, hence the required logarithmic rate. -/
theorem dependencyEdgeHarmonicTerm_uniformBigO
    {C : ℝ} (hC : 0 ≤ C) :
    UniformBigOOn
      (CriticalRunWindow.InRunLengthWindow C)
      dependencyEdgeHarmonicTerm
      quadraticDivLogLogSquaredScale := by
  let admissible := CriticalRunWindow.InRunLengthWindow C
  have hBsq :
      UniformSubpolynomialOn admissible
        (fun _ L ↦ ((L + 1 : ℕ) : ℝ) ^ 2) :=
    runLengthAddOneSquared_uniformSubpolynomial hC
  have hlog :
      UniformSubpolynomialOn admissible
        (fun N _ ↦ 1 + Real.log (3 * (N : ℝ))) :=
    one_add_log_three_mul_uniformSubpolynomial admissible
  have hs :
      UniformSubpolynomialOn admissible
        (fun N L ↦
          2 * (((L + 1 : ℕ) : ℝ) ^ 2 *
            (1 + Real.log (3 * (N : ℝ))))) :=
    ExpSqrtLog.uniformSubpolynomialOn_const_mul 2
      (ExpSqrtLog.uniformSubpolynomialOn_mul hBsq hlog)
  have hrat :
      UniformRationalPowerSubpolynomialOn 1 1 admissible
        (fun N L ↦
          (2 * (((L + 1 : ℕ) : ℝ) ^ 2 *
            (1 + Real.log (3 * (N : ℝ))))) * (N : ℝ)) :=
    UniformRationalPower.mul_subpolynomial (by omega)
      (natCast_uniformRationalPowerOne admissible) hs
  have hbig :=
    rationalPower_uniformBigO_natPowerDivLogLogSquared
      (p := 1) (q := 1) (r := 2) (by omega) hrat
  change UniformBigOOn admissible _
    quadraticDivLogLogSquaredScale at hbig
  change UniformBigOOn admissible _ _ at hbig ⊢
  convert hbig using 1
  · funext N L
    unfold dependencyEdgeHarmonicTerm
    norm_num only [Nat.cast_add, Nat.cast_one]
    ring

/-- The linear cardinal contribution in the edge estimate has the same
rate. -/
theorem dependencyEdgeLinearTerm_uniformBigO
    {C : ℝ} (hC : 0 ≤ C) :
    UniformBigOOn
      (CriticalRunWindow.InRunLengthWindow C)
      dependencyEdgeLinearTerm
      quadraticDivLogLogSquaredScale := by
  let admissible := CriticalRunWindow.InRunLengthWindow C
  have hBsq :
      UniformSubpolynomialOn admissible
        (fun _ L ↦ ((L + 1 : ℕ) : ℝ) ^ 2) :=
    runLengthAddOneSquared_uniformSubpolynomial hC
  have hs :
      UniformSubpolynomialOn admissible
        (fun _ L ↦ 3 * (((L + 1 : ℕ) : ℝ) ^ 2)) :=
    ExpSqrtLog.uniformSubpolynomialOn_const_mul 3 hBsq
  have hrat :
      UniformRationalPowerSubpolynomialOn 1 1 admissible
        (fun N L ↦
          (3 * (((L + 1 : ℕ) : ℝ) ^ 2)) * (N : ℝ)) :=
    UniformRationalPower.mul_subpolynomial (by omega)
      (natCast_uniformRationalPowerOne admissible) hs
  have hbig :=
    rationalPower_uniformBigO_natPowerDivLogLogSquared
      (p := 1) (q := 1) (r := 2) (by omega) hrat
  change UniformBigOOn admissible _
    quadraticDivLogLogSquaredScale at hbig
  change UniformBigOOn admissible _ _ at hbig ⊢
  convert hbig using 1
  · funext N L
    unfold dependencyEdgeLinearTerm
    norm_num only [Nat.cast_add, Nat.cast_one]
    ring

/-! ## The reciprocal-square edge term -/

/--
Pointwise quantitative estimate for the main reciprocal-square contribution.
The factor `3584 = 56 * 8²` records exactly the two elementary comparisons

* `Y log₂ Y ≥ (L+1)² log²(L+1)/2`;
* `log log N ≤ 8 log(L+1)`.
-/
theorem dependencyEdgeMainTerm_le
    {N L : ℕ}
    (hB : 8 ≤ L + 1)
    (hloglogPos : 0 < Real.log (Real.log N))
    (hloglog :
      Real.log (Real.log N) ≤
        8 * Real.log ((L + 1 : ℕ) : ℝ)) :
    dependencyEdgeMainTerm N L ≤
      3584 * quadraticDivLogLogSquaredScale N L := by
  let B : ℕ := L + 1
  let Y : ℕ := terminalPrimeCutoff B
  let ell : ℝ := (Nat.log 2 Y : ℝ)
  let logB : ℝ := Real.log (B : ℝ)
  let loglogN : ℝ := Real.log (Real.log N)
  have hB8 : 8 ≤ B := by simpa only [B] using hB
  have hBtwo : 2 ≤ B := by omega
  have hBY : B ≤ Y := by
    dsimp only [Y]
    exact le_terminalPrimeCutoff hBtwo
  have hYpos : 0 < (Y : ℝ) := by
    exact_mod_cast
      (lt_of_lt_of_le (by omega : 0 < B) hBY)
  have hlogBpos : 0 < logB := by
    dsimp only [logB]
    exact Real.log_pos (by
      exact_mod_cast (show 1 < B by omega))
  have hlogBhalf : (1 / 2 : ℝ) ≤ logB := by
    have hcastB : (2 : ℝ) ≤ (B : ℝ) := by
      exact_mod_cast hBtwo
    have hlogMono :
        Real.log (2 : ℝ) ≤ Real.log (B : ℝ) :=
      Real.log_le_log (by norm_num) hcastB
    have hhalfTwo : (1 / 2 : ℝ) < Real.log 2 := by
      nlinarith [Real.log_two_gt_d9]
    exact hhalfTwo.le.trans (by
      simpa only [logB] using hlogMono)
  have hBsq :
      (64 : ℝ) ≤ (B : ℝ) ^ 2 := by
    have hcastB : (8 : ℝ) ≤ (B : ℝ) := by
      exact_mod_cast hB8
    nlinarith
  have hscaleTwo :
      (2 : ℝ) ≤ terminalPrimeScale B := by
    unfold terminalPrimeScale
    calc
      (2 : ℝ) ≤ 64 * (1 / 2) := by norm_num
      _ ≤ (B : ℝ) ^ 2 * Real.log (B : ℝ) := by
        apply mul_le_mul hBsq
          (by simpa only [logB] using hlogBhalf)
        · norm_num
        · positivity
  have hfloor :=
    terminalPrimeScale_lt_cutoff_add_one B
  have hYlower :
      terminalPrimeScale B / 2 ≤ (Y : ℝ) := by
    dsimp only [Y] at hfloor ⊢
    nlinarith
  have hlogBLeEll : logB ≤ ell := by
    have hbinaryB :=
      CriticalWindowScale.real_log_le_nat_log_two hB8
    have hbinaryMono :
        Nat.log 2 B ≤ Nat.log 2 Y :=
      Nat.log_mono_right hBY
    have hfirst :
        logB ≤ (Nat.log 2 B : ℝ) := by
      simpa only [logB] using hbinaryB
    have hsecond :
        (Nat.log 2 B : ℝ) ≤ ell := by
      dsimp only [ell]
      exact_mod_cast hbinaryMono
    exact hfirst.trans hsecond
  have hellPos : 0 < ell :=
    hlogBpos.trans_le hlogBLeEll
  have hdenomLower :
      (B : ℝ) ^ 2 * logB ^ 2 / 2 ≤
        (Y : ℝ) * ell := by
    have hmul :=
      mul_le_mul hYlower hlogBLeEll hlogBpos.le hYpos.le
    calc
      (B : ℝ) ^ 2 * logB ^ 2 / 2 =
          (terminalPrimeScale B / 2) * logB := by
        unfold terminalPrimeScale
        dsimp only [logB]
        ring
      _ ≤ (Y : ℝ) * ell := hmul
  have hsmallDenomPos :
      0 < (B : ℝ) ^ 2 * logB ^ 2 / 2 := by
    positivity
  have hlogBSqPos : 0 < logB ^ 2 :=
    pow_pos hlogBpos 2
  have hloglogNPos : 0 < loglogN := by
    simpa only [loglogN] using hloglogPos
  have hloglogNSqPos : 0 < loglogN ^ 2 :=
    pow_pos hloglogNPos 2
  have hloglogLe :
      loglogN ≤ 8 * logB := by
    simpa only [loglogN, logB, B] using hloglog
  have hloglogSq :
      loglogN ^ 2 ≤ 64 * logB ^ 2 := by
    nlinarith [sq_nonneg (loglogN - 8 * logB)]
  have hmain :
      (B : ℝ) ^ 2 *
          (28 * (N : ℝ) ^ 2 /
            ((Y : ℝ) * ell)) ≤
        56 * (N : ℝ) ^ 2 / logB ^ 2 := by
    calc
      (B : ℝ) ^ 2 *
            (28 * (N : ℝ) ^ 2 /
              ((Y : ℝ) * ell)) =
          (28 * (N : ℝ) ^ 2 * (B : ℝ) ^ 2) /
            ((Y : ℝ) * ell) := by ring
      _ ≤
          (28 * (N : ℝ) ^ 2 * (B : ℝ) ^ 2) /
            ((B : ℝ) ^ 2 * logB ^ 2 / 2) := by
        apply div_le_div_of_nonneg_left
        · positivity
        · exact hsmallDenomPos
        · exact hdenomLower
      _ = 56 * (N : ℝ) ^ 2 / logB ^ 2 := by
        field_simp [ne_of_gt hlogBpos,
          show (B : ℝ) ≠ 0 by positivity]
        ring
  have hlast :
      56 * (N : ℝ) ^ 2 / logB ^ 2 ≤
        3584 * (N : ℝ) ^ 2 / loglogN ^ 2 := by
    apply
      (div_le_div_iff₀ hlogBSqPos hloglogNSqPos).2
    calc
      (56 * (N : ℝ) ^ 2) * loglogN ^ 2 ≤
          (56 * (N : ℝ) ^ 2) *
            (64 * logB ^ 2) :=
        mul_le_mul_of_nonneg_left hloglogSq (by positivity)
      _ =
          (3584 * (N : ℝ) ^ 2) * logB ^ 2 := by ring
  have hall :
      (B : ℝ) ^ 2 *
          (28 * (N : ℝ) ^ 2 / ((Y : ℝ) * ell)) ≤
        3584 *
          ((N : ℝ) ^ 2 /
            (Real.log (Real.log N)) ^ 2) :=
    hmain.trans (by
      simpa only [loglogN, mul_div_assoc] using hlast)
  simpa only [dependencyEdgeMainTerm,
    quadraticDivLogLogSquaredScale, B, Y, ell,
    Nat.cast_add, Nat.cast_one] using hall

/-- Uniform form of the preceding main-term estimate in the literal critical
window. -/
theorem dependencyEdgeMainTerm_uniformBigO
    {C : ℝ} (hC : 0 ≤ C) :
    UniformBigOOn
      (CriticalRunWindow.InRunLengthWindow C)
      dependencyEdgeMainTerm
      quadraticDivLogLogSquaredScale := by
  obtain ⟨Nwindow, hwindow⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  obtain ⟨Nadm, hadm⟩ :=
    CriticalWeightedDefect.admissible_eventually
      CriticalRunWindow.lowerConstant_pos
      CriticalRunWindow.lowerConstant_lt_upperConstant
  obtain ⟨Nheight, hheight⟩ :=
    DependencyEdgesCritical.runLengthAddOne_tends_to_infinity hC 8
  obtain ⟨Nlog, hlog⟩ :=
    CriticalWeightedDefect.eventually_loglog_le_eight_log_height
      CriticalRunWindow.lowerConstant_pos
  refine ⟨3584, by norm_num,
    max Nwindow (max Nadm (max Nheight Nlog)), ?_⟩
  intro N hN L hrun
  have htail :
      max Nadm (max Nheight Nlog) ≤ N :=
    (le_max_right Nwindow
      (max Nadm (max Nheight Nlog))).trans hN
  have hw :=
    hwindow N
      ((le_max_left Nwindow
        (max Nadm (max Nheight Nlog))).trans hN)
      L hrun
  have hAdm :=
    hadm N ((le_max_left Nadm (max Nheight Nlog)).trans htail)
      (L + 1) hw.1
  have hB :
      8 ≤ L + 1 :=
    hheight N
      ((le_max_left Nheight Nlog).trans
        ((le_max_right Nadm (max Nheight Nlog)).trans htail))
      L hrun
  have hlogs :=
    hlog N
      ((le_max_right Nheight Nlog).trans
        ((le_max_right Nadm (max Nheight Nlog)).trans htail))
      (L + 1) hAdm
  have hpoint :=
    dependencyEdgeMainTerm_le hB hlogs.1 hlogs.2
  have hmainNonneg :
      0 ≤ dependencyEdgeMainTerm N L := by
    unfold dependencyEdgeMainTerm
    positivity
  have hscaleNonneg :
      0 ≤ quadraticDivLogLogSquaredScale N L := by
    unfold quadraticDivLogLogSquaredScale
    positivity
  simpa only [abs_of_nonneg hmainNonneg,
    abs_of_nonneg hscaleNonneg] using hpoint

/--
Lemma 13.6 with the sharp rate needed by Corollary 13.10:

`E_Y = O_C(N²/(log log N)²)`

at `Y = floor((L+1)² log(L+1))`.
-/
theorem orderedDependencyEdges_terminalCutoff_uniformBigO
    {C : ℝ} (hC : 0 ≤ C) :
    UniformBigOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun N L ↦
        ((orderedDependencyEdges N L
          (terminalPrimeCutoff (L + 1))).card : ℝ))
      quadraticDivLogLogSquaredScale := by
  have hmain := dependencyEdgeMainTerm_uniformBigO hC
  have hharmonic := dependencyEdgeHarmonicTerm_uniformBigO hC
  have hlinear := dependencyEdgeLinearTerm_uniformBigO hC
  have hsum :=
    PropositionElevenThree.uniformBigOOn_add
      (PropositionElevenThree.uniformBigOOn_add hmain hharmonic)
      hlinear
  apply SectionThirteenRate.uniformBigOOn_mono hsum
  obtain ⟨Nwindow, hwindow⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  obtain ⟨Nadm, hadm⟩ :=
    CriticalWeightedDefect.admissible_eventually
      CriticalRunWindow.lowerConstant_pos
      CriticalRunWindow.lowerConstant_lt_upperConstant
  obtain ⟨Nheight, hheight⟩ :=
    DependencyEdgesCritical.runLengthAddOne_tends_to_infinity hC 8
  refine ⟨max Nwindow (max Nadm Nheight), ?_⟩
  intro N hN L hrun
  have htail :
      max Nadm Nheight ≤ N :=
    (le_max_right Nwindow (max Nadm Nheight)).trans hN
  have hw :=
    hwindow N
      ((le_max_left Nwindow (max Nadm Nheight)).trans hN)
      L hrun
  have hAdm :=
    hadm N ((le_max_left Nadm Nheight).trans htail)
      (L + 1) hw.1
  have hB :
      8 ≤ L + 1 :=
    hheight N ((le_max_right Nadm Nheight).trans htail) L hrun
  have htwoB :
      2 * (L + 1) ≤ N :=
    CriticalWindowParameters.two_mul_H_le_N_of_criticalWindow
      hAdm.1 hAdm.2.2.2.1
  have hNtwo : 2 ≤ N := hAdm.2.1
  have hLN : L ≤ N := by omega
  have hLY :
      L ≤ terminalPrimeCutoff (L + 1) := by
    exact (by omega : L ≤ L + 1).trans
      (le_terminalPrimeCutoff (by omega))
  have hY :
      4 ≤ terminalPrimeCutoff (L + 1) :=
    (by omega : 4 ≤ L + 1).trans
      (le_terminalPrimeCutoff (by omega))
  have hfinite :=
    card_orderedDependencyEdges_cast_le_harmonic
      (N := N) (L := L)
      (Y := terminalPrimeCutoff (L + 1))
      hNtwo hLN hLY hY
  have hedgeNonneg :
      0 ≤
        ((orderedDependencyEdges N L
          (terminalPrimeCutoff (L + 1))).card : ℝ) := by
    positivity
  rw [abs_of_nonneg hedgeNonneg]
  calc
    ((orderedDependencyEdges N L
        (terminalPrimeCutoff (L + 1))).card : ℝ) ≤
      (L + 1 : ℝ) ^ 2 *
        (28 * (N : ℝ) ^ 2 /
            ((terminalPrimeCutoff (L + 1) : ℝ) *
              (Nat.log 2 (terminalPrimeCutoff (L + 1)) : ℝ)) +
          2 * (N : ℝ) * (1 + Real.log (3 * N)) +
          3 * (N : ℝ)) := hfinite
    _ =
      (dependencyEdgeMainTerm N L +
        dependencyEdgeHarmonicTerm N L) +
          dependencyEdgeLinearTerm N L := by
      unfold dependencyEdgeMainTerm dependencyEdgeHarmonicTerm
        dependencyEdgeLinearTerm
      ring
    _ ≤
        |(dependencyEdgeMainTerm N L +
          dependencyEdgeHarmonicTerm N L) +
            dependencyEdgeLinearTerm N L| :=
      le_abs_self _

/-! ## Quantitative Stein--Chen numerators -/

/-- The linear population `N` has the required quadratic logarithmic
envelope. -/
theorem dyadicLength_uniformBigO
    {C : ℝ} :
    UniformBigOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun N _ ↦ (N : ℝ))
      quadraticDivLogLogSquaredScale := by
  have hrat :=
    SectionThirteenRate.natCast_uniformRationalPowerOne
      (CriticalRunWindow.InRunLengthWindow C)
  have hbig :=
    SectionThirteenRate.rationalPower_uniformBigO_natPowerDivLogLogSquared
      (p := 1) (q := 1) (r := 2) (by omega) hrat
  change UniformBigOOn
    (CriticalRunWindow.InRunLengthWindow C)
    (fun N _ ↦ (N : ℝ))
    quadraticDivLogLogSquaredScale at hbig
  exact hbig

/-- The complete ordered touching population has the same rate. -/
theorem touchingOffDiagPairs_uniformBigO
    {C : ℝ} :
    UniformBigOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun N L ↦
        ((SectionTwelveMoments.touchingOffDiagPairs N L).card : ℝ))
      quadraticDivLogLogSquaredScale := by
  have htwoN :=
    SectionThirteenRate.uniformBigOOn_const_mul 2
      (dyadicLength_uniformBigO (C := C))
  apply SectionThirteenRate.uniformBigOOn_mono htwoN
  refine ⟨0, ?_⟩
  intro N _hN L _hrun
  have hsubset :
      SectionTwelveMoments.touchingOffDiagPairs N L ⊆
        TouchingPairs.touchingPairs N L := by
    intro pair hpair
    have hp :=
      SectionTwelveMoments.mem_touchingOffDiagPairs.mp hpair
    exact TouchingPairs.mem_touchingPairs.mpr
      ⟨hp.1, hp.2.1, hp.2.2.2⟩
  have hcardNat :
      (SectionTwelveMoments.touchingOffDiagPairs N L).card ≤
        2 * N :=
    (Finset.card_le_card hsubset).trans
      (TouchingPairs.card_touchingPairs_le_two_mul N L)
  have hcard :
      ((SectionTwelveMoments.touchingOffDiagPairs N L).card : ℝ) ≤
        2 * (N : ℝ) := by
    exact_mod_cast hcardNat
  rw [abs_of_nonneg (by positivity),
    abs_of_nonneg (by positivity : 0 ≤ 2 * (N : ℝ))]
  exact hcard

/-- The touching defect mass is `N^(1+o(1))`, hence has the required
quadratic logarithmic envelope. -/
theorem touchingMass_uniformBigO
    {C : ℝ} (hC : 0 ≤ C) :
    UniformBigOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun N L ↦ (TouchingMass.touchingMass N L : ℝ))
      quadraticDivLogLogSquaredScale := by
  have hlinear :=
    CriticalTouchingPairs.touchingMass_uniformLinearSubpolynomial hC
  have hrat :
      UniformRationalPowerSubpolynomialOn 1 1
        (CriticalRunWindow.InRunLengthWindow C)
        (fun N L ↦ (TouchingMass.touchingMass N L : ℝ)) := by
    simpa only [UniformLinearSubpolynomialOn,
      UniformRationalPowerSubpolynomialOn,
      Nat.one_mul] using hlinear
  have hbig :=
    SectionThirteenRate.rationalPower_uniformBigO_natPowerDivLogLogSquared
      (p := 1) (q := 1) (r := 2) (by omega) hrat
  change UniformBigOOn
    (CriticalRunWindow.InRunLengthWindow C)
    (fun N L ↦ (TouchingMass.touchingMass N L : ℝ))
    quadraticDivLogLogSquaredScale at hbig
  exact hbig

/--
Exact transport of any quantitative homogeneous-mass estimate to the
separated defect numerator used by Stein--Chen.

This mass-level entry point is used by the canonical bounded-ratio proof.
-/
theorem separatedDefectMass_uniformBigO_of_homogeneousMass
    {C : ℝ} (A : ℕ)
    (hhom :
      UniformBigOOn
        (CriticalRunWindow.InRunLengthWindow C)
        (PropositionElevenTwo.homogeneousMass A)
        quadraticDivLogLogSquaredScale) :
    UniformBigOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun N L ↦
        (SectionTwelveMoments.jointDefectMass N L
          (SectionTwelveMoments.separatedOffDiagPairs N L) : ℝ))
      quadraticDivLogLogSquaredScale := by
  apply SectionThirteenRate.uniformBigOOn_mono hhom
  refine ⟨2, ?_⟩
  intro N hN L _hrun
  rw [
    SectionTwelveMoments.jointDefectMass_separated_cast_eq_homogeneousMass
      (A := A) hN]

/-- Quantitative numerator estimate for the first Stein--Chen term. -/
theorem steinBOneNumerator_uniformBigO
    {C : ℝ} (hC : 0 ≤ C) :
    UniformBigOOn
      (CriticalRunWindow.InRunLengthWindow C)
      SteinChenCritical.steinBOneNumerator
      quadraticDivLogLogSquaredScale := by
  have hsum :=
    PropositionElevenThree.uniformBigOOn_add
      (dyadicLength_uniformBigO (C := C))
      (orderedDependencyEdges_terminalCutoff_uniformBigO hC)
  change UniformBigOOn
    (CriticalRunWindow.InRunLengthWindow C)
    (fun N L ↦
      (N : ℝ) +
        ((orderedDependencyEdges N L
          (terminalPrimeCutoff (L + 1))).card : ℝ))
    quadraticDivLogLogSquaredScale
  exact hsum

/--
Quantitative numerator estimate for the averaged second Stein--Chen term,
given the separated mass at the required scale.
-/
theorem steinBTwoNumerator_uniformBigO_of_separatedDefectMass
    {C : ℝ} (hC : 0 ≤ C)
    (hseparated :
      UniformBigOOn
        (CriticalRunWindow.InRunLengthWindow C)
        (fun N L ↦
          (SectionTwelveMoments.jointDefectMass N L
            (SectionTwelveMoments.separatedOffDiagPairs N L) : ℝ))
        quadraticDivLogLogSquaredScale) :
    UniformBigOOn
      (CriticalRunWindow.InRunLengthWindow C)
      SteinChenCritical.steinBTwoNumerator
      quadraticDivLogLogSquaredScale := by
  have hpairs := touchingOffDiagPairs_uniformBigO (C := C)
  have hedge := orderedDependencyEdges_terminalCutoff_uniformBigO hC
  have htouch := touchingMass_uniformBigO hC
  have hfirst :=
    PropositionElevenThree.uniformBigOOn_add hpairs hedge
  have hsecond :=
    PropositionElevenThree.uniformBigOOn_add hfirst htouch
  have hall :=
    PropositionElevenThree.uniformBigOOn_add hsecond hseparated
  unfold SteinChenCritical.steinBTwoNumerator
  simpa only [add_assoc] using hall

/-! ## Quantitative Stein--Chen terms -/

/-- First Stein--Chen term at the explicit rate. -/
theorem steinBOne_uniformBigO_explicitRate
    {C : ℝ} (hC : 0 ≤ C) :
    UniformBigOOn
      (CriticalRunWindow.InRunLengthWindow C)
      SteinChenCritical.steinBOneReal
      inverseLogLogSquaredRate := by
  have hnormalized :=
    SectionThirteenRate.normalizedQuadraticLogLog_uniformBigO hC
      (steinBOneNumerator_uniformBigO hC)
      (fun N L ↦ by
        unfold SteinChenCritical.steinBOneNumerator
        positivity)
  apply SectionThirteenRate.uniformBigOOn_mono hnormalized
  refine ⟨0, ?_⟩
  intro N _hN L _hrun
  have hfiniteQ :=
    SteinChenTerms.steinBOne_le
      N L (terminalPrimeCutoff (L + 1))
  have hfinite := (Rat.cast_le (K := ℝ)).2 hfiniteQ
  push_cast at hfinite
  have htargetNonneg :
      0 ≤ SteinChenCritical.steinBOneReal N L := by
    unfold SteinChenCritical.steinBOneReal
    apply Rat.cast_nonneg.mpr
    unfold SteinChenTerms.steinBOne
    exact Finset.sum_nonneg fun _pair _ ↦ by
      unfold SteinChenTerms.conditionalMarginal
      positivity
  have hnumNonneg :
      0 ≤ SteinChenCritical.steinBOneNumerator N L := by
    unfold SteinChenCritical.steinBOneNumerator
    positivity
  rw [abs_of_nonneg htargetNonneg,
    abs_of_nonneg (div_nonneg hnumNonneg (by positivity))]
  apply hfinite.trans_eq
  unfold SteinChenCritical.steinBOneNumerator
  rfl

/--
Averaged second Stein--Chen term at the explicit rate, from a direct
quantitative numerator estimate.
-/
theorem steinBTwoAverage_uniformBigO_explicitRate_of_numerator
    {C : ℝ} (hC : 0 ≤ C)
    (hnumerator :
      UniformBigOOn
        (CriticalRunWindow.InRunLengthWindow C)
        SteinChenCritical.steinBTwoNumerator
        quadraticDivLogLogSquaredScale) :
    UniformBigOOn
      (CriticalRunWindow.InRunLengthWindow C)
      SteinChenCritical.steinBTwoAverageReal
      inverseLogLogSquaredRate := by
  have hnormalized :=
    SectionThirteenRate.normalizedQuadraticLogLog_uniformBigO hC
      hnumerator
      (fun N L ↦ by
        unfold SteinChenCritical.steinBTwoNumerator
        positivity)
  apply SectionThirteenRate.uniformBigOOn_mono hnormalized
  obtain ⟨Nwindow, hwindow⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  obtain ⟨Nadm, hadm⟩ :=
    CriticalWeightedDefect.admissible_eventually
      CriticalRunWindow.lowerConstant_pos
      CriticalRunWindow.lowerConstant_lt_upperConstant
  refine ⟨max Nwindow Nadm, ?_⟩
  intro N hN L hrun
  have hw :=
    hwindow N ((le_max_left _ _).trans hN) L hrun
  have hAdm :=
    hadm N ((le_max_right _ _).trans hN) (L + 1) hw.1
  have hfiniteQ :=
    SteinChenTerms.steinBTwoAverage_le
      (N := N) (L := L)
      (Y := terminalPrimeCutoff (L + 1))
      hAdm.2.1 hw.2.1
  have hfinite := (Rat.cast_le (K := ℝ)).2 hfiniteQ
  push_cast at hfinite
  have htargetNonneg :
      0 ≤ SteinChenCritical.steinBTwoAverageReal N L := by
    unfold SteinChenCritical.steinBTwoAverageReal
      SteinChenTerms.steinBTwoAverage
      SectionTwelveMoments.jointPairMass
    apply Rat.cast_nonneg.mpr
    exact Finset.sum_nonneg fun pair _ ↦
      SteinChenTerms.jointStartProbability_nonneg
        N L pair.1 pair.2
  have hnumNonneg :
      0 ≤ SteinChenCritical.steinBTwoNumerator N L := by
    unfold SteinChenCritical.steinBTwoNumerator
    positivity
  rw [abs_of_nonneg htargetNonneg,
    abs_of_nonneg (div_nonneg hnumNonneg (by positivity))]
  apply hfinite.trans_eq
  unfold SteinChenCritical.steinBTwoNumerator
  rfl

/--
The uniformly averaged conditional good-start law satisfies the explicit
AGG rate once the averaged second Stein--Chen term is controlled.
-/
theorem
    averagedConditionalGoodTotalVariation_uniformBigO_explicitRate_of_steinBTwo
    {C : ℝ} (hC : 0 ≤ C)
    (hAGG :
      ArratiaGoldsteinGordonInput.ArratiaGoldsteinGordonStatement)
    (hbTwo :
      UniformBigOOn
        (CriticalRunWindow.InRunLengthWindow C)
        SteinChenCritical.steinBTwoAverageReal
        inverseLogLogSquaredRate) :
    UniformBigOOn
      (CriticalRunWindow.InRunLengthWindow C)
      ConditionalAGGCritical.averagedConditionalGoodTotalVariation
      inverseLogLogSquaredRate := by
  have hbOne := steinBOne_uniformBigO_explicitRate hC
  have hsum :=
    PropositionElevenThree.uniformBigOOn_add hbOne hbTwo
  have htwo :=
    SectionThirteenRate.uniformBigOOn_const_mul 2 hsum
  apply SectionThirteenRate.uniformBigOOn_mono htwo
  obtain ⟨Nwindow, hwindow⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  refine ⟨max 2 Nwindow, ?_⟩
  intro N hN L hrun
  have hNtwo : 2 ≤ N :=
    (le_max_left 2 Nwindow).trans hN
  have hw :=
    hwindow N ((le_max_right 2 Nwindow).trans hN) L hrun
  have hLY :
      L + 1 ≤ terminalPrimeCutoff (L + 1) :=
    window_succ_le_terminalPrimeCutoff hw.2.1 le_rfl
  have hfinite :=
    ConditionalAGGAverage.averagedConditionalGood_natTotalVariation_le_steinTerms
      hAGG hNtwo hw.2.1 hLY
  have htargetNonneg :
      0 ≤
        ConditionalAGGCritical.averagedConditionalGoodTotalVariation N L :=
    ConditionalAGGCritical.averagedConditionalGoodTotalVariation_nonneg N L
  rw [abs_of_nonneg htargetNonneg]
  calc
    ConditionalAGGCritical.averagedConditionalGoodTotalVariation N L ≤
        2 *
          (SteinChenCritical.steinBOneReal N L +
            SteinChenCritical.steinBTwoAverageReal N L) := by
      simpa only [
        ConditionalAGGCritical.averagedConditionalGoodTotalVariation,
        SteinChenCritical.steinBOneReal,
        SteinChenCritical.steinBTwoAverageReal] using hfinite
    _ ≤
        |2 *
          (SteinChenCritical.steinBOneReal N L +
            SteinChenCritical.steinBTwoAverageReal N L)| :=
      le_abs_self _

/-! ## Final assembly -/

/--
Corollary 13.10 from a quantitative estimate for the averaged conditional
good-start law.  This is the arithmetic-agnostic final assembly used by the
canonical path.
-/
theorem corollary_thirteen_ten_uniformBigO_of_averagedConditional
    {C : ℝ} (hC : 0 ≤ C)
    (hagg :
      UniformBigOOn
        (CriticalRunWindow.InRunLengthWindow C)
        ConditionalAGGCritical.averagedConditionalGoodTotalVariation
        inverseLogLogSquaredRate) :
    UniformBigOOn
      (CriticalRunWindow.InRunLengthWindow C)
      SectionThirteenCritical.fullDyadicTargetPoissonTotalVariation
      inverseLogLogSquaredRate := by
  let terminalY : ℕ → ℕ :=
    fun L ↦ terminalPrimeCutoff (L + 1)
  have hbad :
      UniformBigOOn
        (CriticalRunWindow.InRunLengthWindow C)
        (fun N L ↦
          badStartProbabilityMassReal N L (terminalY L))
        inverseLogLogSquaredRate := by
    change UniformBigOOn
      (CriticalRunWindow.InRunLengthWindow C)
      BadStartMassCritical.terminalBadStartProbabilityMass
      inverseLogLogSquaredRate
    exact
      SectionThirteenRate.terminalBadStartProbabilityMass_uniformBigO_explicitRate
        hC
  have hcount :
      UniformBigOOn
        (CriticalRunWindow.InRunLengthWindow C)
        (fun N L ↦
          ((terminalBadStarts N L (terminalY L)).card : ℝ) /
            (2 : ℝ) ^ L)
        inverseLogLogSquaredRate := by
    simpa only [terminalY] using
      SectionThirteenRate.normalized_terminalBadStarts_uniformBigO_explicitRate
        hC
  have hsum :=
    PropositionElevenThree.uniformBigOOn_add
      (PropositionElevenThree.uniformBigOOn_add hbad hagg)
      hcount
  apply SectionThirteenRate.uniformBigOOn_mono hsum
  obtain ⟨Nwindow, hwindow⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  refine ⟨max 2 Nwindow, ?_⟩
  intro N hN L hrun
  have hNtwo : 2 ≤ N :=
    (le_max_left 2 Nwindow).trans hN
  have hw :=
    hwindow N ((le_max_right 2 Nwindow).trans hN) L hrun
  have hLY :
      L + 1 ≤ terminalY L := by
    dsimp only [terminalY]
    exact window_succ_le_terminalPrimeCutoff hw.2.1 le_rfl
  have hfinite :=
    natTotalVariation_fullDyadic_targetPoisson_le_components
      hNtwo hw.2.1 hLY
  rw [abs_of_nonneg
    (SectionThirteenCritical.fullDyadicTargetPoissonTotalVariation_nonneg
      N L)]
  calc
    SectionThirteenCritical.fullDyadicTargetPoissonTotalVariation N L ≤
        badStartProbabilityMassReal N L (terminalY L) +
          ConditionalAGGCritical.averagedConditionalGoodTotalVariation N L +
          ((terminalBadStarts N L (terminalY L)).card : ℝ) /
            (2 : ℝ) ^ L := by
      simpa only [
        SectionThirteenCritical.fullDyadicTargetPoissonTotalVariation,
        ConditionalAGGCritical.averagedConditionalGoodTotalVariation,
        terminalY] using hfinite
    _ ≤
        |(badStartProbabilityMassReal N L (terminalY L) +
          ConditionalAGGCritical.averagedConditionalGoodTotalVariation N L) +
            ((terminalBadStarts N L (terminalY L)).card : ℝ) /
              (2 : ℝ) ^ L| :=
      le_abs_self _

/--
Mass-level form of Corollary 13.10.  All arithmetic enters through the
single homogeneous-mass estimate supplied by the canonical `κ` proof.
-/
theorem corollary_thirteen_ten_uniformBigO_of_homogeneousMass
    {C : ℝ} (hC : 0 ≤ C)
    (hAGG :
      ArratiaGoldsteinGordonInput.ArratiaGoldsteinGordonStatement)
    (A : ℕ)
    (hhom :
      UniformBigOOn
        (CriticalRunWindow.InRunLengthWindow C)
        (PropositionElevenTwo.homogeneousMass A)
        quadraticDivLogLogSquaredScale) :
    UniformBigOOn
      (CriticalRunWindow.InRunLengthWindow C)
      SectionThirteenCritical.fullDyadicTargetPoissonTotalVariation
      inverseLogLogSquaredRate := by
  have hseparated :=
    separatedDefectMass_uniformBigO_of_homogeneousMass A hhom
  have hnumerator :=
    steinBTwoNumerator_uniformBigO_of_separatedDefectMass
      hC hseparated
  have hbTwo :=
    steinBTwoAverage_uniformBigO_explicitRate_of_numerator
      hC hnumerator
  have hconditional :=
    averagedConditionalGoodTotalVariation_uniformBigO_explicitRate_of_steinBTwo
      hC hAGG hbTwo
  exact
    corollary_thirteen_ten_uniformBigO_of_averagedConditional
      hC hconditional

/--
Canonical Corollary 13.10 with the generalized-Pell package discharged by the
internal quadratic-order conductor descent and the source-shaped
Nicolas--Robin logarithmic divisor inequality.
-/
theorem corollary_thirteen_ten_uniformBigO_canonical
    {C : ℝ} (hC : 0 ≤ C)
    (hAGG :
      ArratiaGoldsteinGordonInput.ArratiaGoldsteinGordonStatement)
    (hES :
      EvertseSilvermanInput.EvertseSilvermanAbscissaStatement)
    (hDivisor :
      PellInput.NicolasRobinDivisorLogBoundStatement) :
    UniformBigOOn
      (CriticalRunWindow.InRunLengthWindow C)
      SectionThirteenCritical.fullDyadicTargetPoissonTotalVariation
      inverseLogLogSquaredRate :=
  corollary_thirteen_ten_uniformBigO_of_homogeneousMass
    hC hAGG 3
      (DyadicKappaQuantitative.homogeneousMass_uniformBigO
        hC hES hDivisor)

/--
Canonical theorem-level form of Theorem 1.1 with only source-shaped external
literature inputs in its signature.
-/
theorem theorem_one_one_uniformBigO_canonical
    {C : ℝ} (hC : 0 ≤ C)
    (hAGG :
      ArratiaGoldsteinGordonInput.ArratiaGoldsteinGordonStatement)
    (hES :
      EvertseSilvermanInput.EvertseSilvermanAbscissaStatement)
    (hDivisor :
      PellInput.NicolasRobinDivisorLogBoundStatement) :
    UniformBigOOn
      (CriticalRunWindow.InRunLengthWindow C)
      SectionThirteenCritical.fullDyadicTargetPoissonTotalVariation
      inverseLogLogSquaredRate :=
  corollary_thirteen_ten_uniformBigO_canonical
    hC hAGG hES hDivisor

/--
Theorem 1.1 stated directly for the dyadic start-count random variable on the
infinite Rademacher product law.  Exact cylinder transfer identifies this law
with `fullDyadicStartLaw`, so the quantitative conclusion and its external
hypotheses are unchanged.
-/
theorem theorem_one_one_infinite_model
    {C : ℝ} (hC : 0 ≤ C)
    (hAGG :
      ArratiaGoldsteinGordonInput.ArratiaGoldsteinGordonStatement)
    (hES :
      EvertseSilvermanInput.EvertseSilvermanAbscissaStatement)
    (hDivisor :
      PellInput.NicolasRobinDivisorLogBoundStatement) :
    UniformBigOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun N L =>
        SectionThirteenFiniteBound.natTotalVariation
          (infiniteDyadicStartLaw N L)
          (targetPoissonLaw N L))
      inverseLogLogSquaredRate := by
  have hfinite :=
    theorem_one_one_uniformBigO_canonical
      hC hAGG hES hDivisor
  change
    UniformBigOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun N L =>
        SectionThirteenFiniteBound.natTotalVariation
          (fullDyadicStartLaw N L)
          (targetPoissonLaw N L))
      inverseLogLogSquaredRate at hfinite
  simpa only [infiniteDyadicStartCount_law_eq_fullDyadicStartLaw] using
    hfinite

end

end CorollaryThirteenTen
end PaperC
