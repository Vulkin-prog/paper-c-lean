import PaperC.Asymptotics.BoundedRatioRationalMass
import PaperC.Asymptotics.BoundedRatioShallowCoreSector
import PaperC.Asymptotics.BoundedRatioSmallHeightSector
import PaperC.Asymptotics.BoundedRatioSmallProductSector
import PaperC.Asymptotics.BoundedRatioTerminalSummation

set_option maxHeartbeats 3600000

/-!
# Elementary quantitative dyadic consequences of the bounded-ratio theory

The bounded-ratio estimates are stated with an endpoint `M` satisfying
`2N ≤ M ≤ κ₀N`.  This file records their specialization to the mother
dyadic block `M = 2N`.  In particular, all the elementary pieces of the
canonical Section 11 partition retain their source exponents after the
specialization.

The only arithmetic input below is generalized Pell, and it occurs solely
in the intrinsic terminal-sector estimate.
-/

namespace PaperC
namespace BoundedRatioElementaryQuantitative

open BoundedRatioCanonicalTerminalPopulation
open PropositionSixteenOne

noncomputable section

/-! ## The generic dyadic specialization -/

/--
A bounded-ratio rational-power estimate with `κ₀ = 2` specializes, without
loss, to the mother dyadic endpoint `M = 2N`.
-/
theorem uniformRationalPowerInBoundedRatioWindow_dyadic
    {p q : ℕ} {C : ℝ}
    {f : ℕ → ℕ → ℕ → ℝ}
    (hf :
      UniformRationalPowerInBoundedRatioWindow
        p q C 2 f) :
    UniformRationalPowerSubpolynomialOn
      p q
      (CriticalRunWindow.InRunLengthWindow C)
      (fun N L ↦ f N (2 * N) L) := by
  intro k hk
  obtain ⟨N₀, hN₀⟩ := hf k hk
  refine ⟨N₀, ?_⟩
  intro N hN L hrun
  exact hN₀ N hN (2 * N) L le_rfl le_rfl hrun

/-!
The finite domination lemmas for the second and third sectors need the
harmless eventual side conditions `2 ≤ N`, `L ≤ N`, and `8 ≤ L+1`.
They depend only on the critical window, so we package them once.
-/
private theorem eventually_dyadic_sector_side_conditions
    {C : ℝ} (hC : 0 ≤ C) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L,
      CriticalRunWindow.InRunLengthWindow C N L →
        2 ≤ N ∧ L ≤ N ∧ 8 ≤ L + 1 := by
  obtain ⟨Nwindow, hwindow⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  have hupperNonneg :
      0 ≤ CriticalRunWindow.upperConstant :=
    (CriticalRunWindow.lowerConstant_pos.trans
      CriticalRunWindow.lowerConstant_lt_upperConstant).le
  obtain ⟨Nlength, hlength⟩ :=
    ExpSqrtLog.linear_log_add_one_pow_le_nat_eventually
      CriticalRunWindow.upperConstant hupperNonneg 1 (by omega)
  obtain ⟨Nadm, hNadm⟩ :=
    CriticalWeightedDefect.admissible_eventually
      CriticalRunWindow.lowerConstant_pos
      CriticalRunWindow.lowerConstant_lt_upperConstant
  obtain ⟨Nheight, hNheight⟩ :=
    CriticalWeightedDefect.height_tends_to_infinity
      (c₂ := CriticalRunWindow.upperConstant)
      CriticalRunWindow.lowerConstant_pos 8
  refine
    ⟨max 2
      (max Nwindow (max Nlength (max Nadm Nheight))), ?_⟩
  intro N hN L hrun
  have hNtwo : 2 ≤ N :=
    (le_max_left 2
      (max Nwindow (max Nlength (max Nadm Nheight)))).trans hN
  have htail :
      max Nwindow (max Nlength (max Nadm Nheight)) ≤ N :=
    (le_max_right 2
      (max Nwindow (max Nlength (max Nadm Nheight)))).trans hN
  have hNwindow : Nwindow ≤ N :=
    (le_max_left Nwindow
      (max Nlength (max Nadm Nheight))).trans htail
  have htail₂ :
      max Nlength (max Nadm Nheight) ≤ N :=
    (le_max_right Nwindow
      (max Nlength (max Nadm Nheight))).trans htail
  have hNlength : Nlength ≤ N :=
    (le_max_left Nlength (max Nadm Nheight)).trans htail₂
  have htail₃ : max Nadm Nheight ≤ N :=
    (le_max_right Nlength (max Nadm Nheight)).trans htail₂
  have hNadmN : Nadm ≤ N :=
    (le_max_left Nadm Nheight).trans htail₃
  have hNheightN : Nheight ≤ N :=
    (le_max_right Nadm Nheight).trans htail₃
  have hfirst := hwindow N hNwindow L hrun
  have hLplusTwoReal :
      (((L + 1) + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by
    simpa using
      hlength N hNlength (L + 1) hfirst.1.2.2.2
  have hLplusTwo : (L + 1) + 1 ≤ N := by
    exact_mod_cast hLplusTwoReal
  have hadmissible :
      CriticalWeightedDefect.Admissible
        CriticalRunWindow.lowerConstant
        CriticalRunWindow.upperConstant N (L + 1) :=
    hNadm N hNadmN (L + 1) hfirst.1
  have hB : 8 ≤ L + 1 :=
    hNheight N hNheightN (L + 1) hadmissible
  exact ⟨hNtwo, by omega, hB⟩

/-! ## Systematic mother mass -/

/-- The bounded-ratio systematic mass has its source `3/2` exponent. -/
theorem systematicMass_uniformThreeHalvesInBoundedRatioWindow
    {C : ℝ} (hC : 0 ≤ C) :
    UniformRationalPowerInBoundedRatioWindow
      3 2 C 2 (systematicMass 3) := by
  apply
    BoundedRatioSectorClosure.uniformRationalPowerInBoundedRatioWindow_of_nonnegative_envelope
      (p := 3) (q := 2)
      (envelope := fun N L ↦
        ((BoundedRatioRationalMass.boundedRationalMassSup
          2 3 N L : ℕ) : ℝ))
  · simpa only [UniformThreeHalvesSubpolynomialOn,
      UniformRationalPowerSubpolynomialOn] using
      BoundedRatioRationalMass.boundedRationalMassSup_uniformThreeHalves
        hC 2 3 (by norm_num)
  · intro N M L
    unfold systematicMass
    split_ifs <;> positivity
  · intro N L
    positivity
  · refine ⟨2, ?_⟩
    intro N hN M L hNM hMκ _hrun
    rw [systematicMass_eq_boundedRationalMass hN]
    exact_mod_cast
      BoundedRatioRationalMass.boundedRationalMass_le_sup
        (κ₀ := 2) (A := 3) (L := L) hNM hMκ

/--
The systematic contribution on `[N,2N)` is
`N^(3/2+o_C(1))`.
-/
theorem systematicMass_dyadic_uniformThreeHalves
    {C : ℝ} (hC : 0 ≤ C) :
    UniformRationalPowerSubpolynomialOn
      3 2
      (CriticalRunWindow.InRunLengthWindow C)
      (fun N L ↦ systematicMass 3 N (2 * N) L) :=
  uniformRationalPowerInBoundedRatioWindow_dyadic
    (systematicMass_uniformThreeHalvesInBoundedRatioWindow hC)

/-! ## The first three residual sectors -/

/--
The literal small-prime-product sector on `[N,2N)` keeps the exponent
`7/4`, for the canonical intrinsic terminal classifier.
-/
theorem smallPrimeProduct_dyadic_uniformSevenFourths
    {C : ℝ} (hC : 0 ≤ C) (K : ℝ) :
    UniformRationalPowerSubpolynomialOn
      7 4
      (CriticalRunWindow.InRunLengthWindow C)
      (fun N L ↦
        sectorResidualMass 3
          (boundedIntrinsicTerminalPredicate 3 K)
          .smallPrimeProduct N (2 * N) L) := by
  apply uniformRationalPowerInBoundedRatioWindow_dyadic
  simpa only [
    BoundedRatioSmallProductSector.UniformSevenFourthsInBoundedRatioWindow,
    UniformRationalPowerInBoundedRatioWindow] using
    BoundedRatioSmallProductSector.smallProductSectorLinearMass_uniformSevenFourths
      hC 2 3 (by norm_num)
      (boundedIntrinsicTerminalPredicate 3 K)

/--
The literal small-canonical-height sector has exponent `7/4` uniformly in
the bounded endpoint.
-/
theorem smallCanonicalHeight_uniformSevenFourthsInBoundedRatioWindow
    {C : ℝ} (hC : 0 ≤ C) (κ₀ A : ℕ) (hA : 1 ≤ A)
    (terminal : TerminalPredicateFamily) :
    UniformRationalPowerInBoundedRatioWindow
      7 4 C κ₀
      (sectorResidualMass A terminal .smallCanonicalHeight) := by
  apply
    BoundedRatioSectorClosure.uniformRationalPowerInBoundedRatioWindow_of_nonnegative_envelope
      (BoundedRatioSmallHeightSector.boundedSmallHeightLinearEnvelope_uniformSevenFourths
        hC κ₀ A)
  · intro N M L
    unfold sectorResidualMass
    split_ifs <;> positivity
  · exact
      BoundedRatioSmallHeightSector.boundedSmallHeightLinearEnvelope_nonneg
        C κ₀ A
  · obtain ⟨Nside, hside⟩ :=
      eventually_dyadic_sector_side_conditions hC
    refine ⟨Nside, ?_⟩
    intro N hN M L hNM hMκ hrun
    obtain ⟨hNtwo, hL, hB⟩ :=
      hside N hN L hrun
    have hbase : N ≤ M := by omega
    have hfinite :=
      BoundedRatioSmallHeightSector.sectorResidualMassNat_cast_le_linearEnvelope
        hNtwo hbase hMκ hL hB hA terminal hrun
    simpa only [sectorResidualMass, dif_pos hNtwo] using hfinite

/--
The small-canonical-height sector on `[N,2N)` keeps the exponent `7/4`
for the canonical intrinsic classifier.
-/
theorem smallCanonicalHeight_dyadic_uniformSevenFourths
    {C : ℝ} (hC : 0 ≤ C) (K : ℝ) :
    UniformRationalPowerSubpolynomialOn
      7 4
      (CriticalRunWindow.InRunLengthWindow C)
      (fun N L ↦
        sectorResidualMass 3
          (boundedIntrinsicTerminalPredicate 3 K)
          .smallCanonicalHeight N (2 * N) L) :=
  uniformRationalPowerInBoundedRatioWindow_dyadic
    (smallCanonicalHeight_uniformSevenFourthsInBoundedRatioWindow
      hC 2 3 (by norm_num)
      (boundedIntrinsicTerminalPredicate 3 K))

/--
The literal shallow-core sector has exponent `31/16` uniformly in the
bounded endpoint.
-/
theorem shallowCore_uniformThirtyOneSixteenthsInBoundedRatioWindow
    {C : ℝ} (hC : 0 ≤ C) (κ₀ A : ℕ)
    (terminal : TerminalPredicateFamily) :
    UniformRationalPowerInBoundedRatioWindow
      31 16 C κ₀
      (sectorResidualMass A terminal .shallowCore) := by
  apply
    BoundedRatioSectorClosure.uniformRationalPowerInBoundedRatioWindow_of_nonnegative_envelope
      (BoundedRatioShallowCoreSector.boundedRatioShallowCoreLinearEnvelope_uniformThirtyOneSixteenths
        hC κ₀ A)
  · intro N M L
    unfold sectorResidualMass
    split_ifs <;> positivity
  · intro N L
    unfold
      BoundedRatioShallowCoreSector.boundedRatioShallowCoreLinearEnvelope
    positivity
  · obtain ⟨Nside, hside⟩ :=
      eventually_dyadic_sector_side_conditions hC
    refine ⟨Nside, ?_⟩
    intro N hN M L hNM hMκ hrun
    obtain ⟨hNtwo, hL, _hB⟩ :=
      hside N hN L hrun
    have hbase : N ≤ M := by omega
    exact
      BoundedRatioShallowCoreSector.sectorResidualMass_le_linearEnvelope
        hNtwo terminal hbase hMκ hL

/--
The shallow-core sector on `[N,2N)` keeps the exponent `31/16` for the
canonical intrinsic classifier.
-/
theorem shallowCore_dyadic_uniformThirtyOneSixteenths
    {C : ℝ} (hC : 0 ≤ C) (K : ℝ) :
    UniformRationalPowerSubpolynomialOn
      31 16
      (CriticalRunWindow.InRunLengthWindow C)
      (fun N L ↦
        sectorResidualMass 3
          (boundedIntrinsicTerminalPredicate 3 K)
          .shallowCore N (2 * N) L) :=
  uniformRationalPowerInBoundedRatioWindow_dyadic
    (shallowCore_uniformThirtyOneSixteenthsInBoundedRatioWindow
      hC 2 3 (boundedIntrinsicTerminalPredicate 3 K))

/-! ## The aligned sector -/

/--
The aligned deep-core sector on `[N,2N)` is eventually zero.  Consequently
it is big-oh with respect to every comparison scale.
-/
theorem alignedDeepCore_dyadic_uniformBigO_of_scale
    {C : ℝ} (hC : 0 ≤ C) (K : ℝ)
    (g : ℕ → ℕ → ℝ) :
    UniformBigOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun N L ↦
        sectorResidualMass 3
          (boundedIntrinsicTerminalPredicate 3 K)
          .alignedDeepCore N (2 * N) L)
      g := by
  obtain ⟨Nempty, hNemptyTwo, hNempty⟩ :=
    alignedDeepCoreSector_eventually_empty
      hC 3 (boundedIntrinsicTerminalPredicate 3 K)
  refine ⟨0, le_rfl, Nempty, ?_⟩
  intro N hN L hrun
  have hNtwo : 2 ≤ N :=
    hNemptyTwo.trans hN
  have hempty :=
    hNempty N hN (2 * N) L hrun hNtwo
  have hmass :
      sectorResidualMass 3
          (boundedIntrinsicTerminalPredicate 3 K)
          .alignedDeepCore N (2 * N) L = 0 := by
    simp only [sectorResidualMass, dif_pos hNtwo,
      sectorResidualMassNat, hempty, Finset.sum_empty,
      Nat.cast_zero]
  simp only [hmass, abs_zero, zero_mul, le_refl]

/--
Quantitative form used in the total mother-mass assembly: the aligned
sector is big-oh of `N²/(log log N)²` (indeed it is eventually zero).
-/
theorem alignedDeepCore_dyadic_uniformBigO
    {C : ℝ} (hC : 0 ≤ C) (K : ℝ) :
    UniformBigOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun N L ↦
        sectorResidualMass 3
          (boundedIntrinsicTerminalPredicate 3 K)
          .alignedDeepCore N (2 * N) L)
      (fun N _L ↦
        (N : ℝ) ^ 2 /
          (Real.log (Real.log N)) ^ 2) :=
  alignedDeepCore_dyadic_uniformBigO_of_scale hC K _

/-- Strongest zero-scale form of the preceding eventual vanishing. -/
theorem alignedDeepCore_dyadic_uniformBigO_zero
    {C : ℝ} (hC : 0 ≤ C) (K : ℝ) :
    UniformBigOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun N L ↦
        sectorResidualMass 3
          (boundedIntrinsicTerminalPredicate 3 K)
          .alignedDeepCore N (2 * N) L)
      (fun _N _L ↦ 0) :=
  alignedDeepCore_dyadic_uniformBigO_of_scale hC K _

/-! ## The intrinsic terminal sector -/

/--
Under generalized Pell, the canonical intrinsic terminal sector on
`[N,2N)` has exponent `7/4`.
-/
theorem terminal_dyadic_uniformSevenFourths
    {C : ℝ} (hC : 0 ≤ C) (K : ℝ) (hK : 0 ≤ K)
    (hPell :
      PellInput.GeneralizedPellPolynomialBoxStatement) :
    UniformRationalPowerSubpolynomialOn
      7 4
      (CriticalRunWindow.InRunLengthWindow C)
      (fun N L ↦
        sectorResidualMass 3
          (boundedIntrinsicTerminalPredicate 3 K)
          .terminal N (2 * N) L) := by
  apply uniformRationalPowerInBoundedRatioWindow_dyadic
  simpa only [
    BoundedRatioSmallProductSector.UniformSevenFourthsInBoundedRatioWindow,
    UniformRationalPowerInBoundedRatioWindow] using
    BoundedRatioTerminalSummation.generalizedPell_implies_intrinsicTerminalSector_uniformSevenFourths
      hC 2 3 K (by norm_num) (by norm_num) hK hPell

end

end BoundedRatioElementaryQuantitative
end PaperC
