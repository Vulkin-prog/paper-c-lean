import PaperC.Asymptotics.PropositionElevenTwo

set_option maxHeartbeats 1800000

/-!
# Corollary 11.3: a quantitative homogeneous-mass envelope

The qualitative Proposition 11.2 already disintegrates the homogeneous
mass into the systematic term and the seven literal sectors of Lemma 11.1.
This module keeps that exact disintegration and upgrades every sector with a
genuine power saving to the slower exponential scale occurring in
Corollary 11.3.

Only sector six needs a new input.  Its interface is deliberately narrower
than the whole corollary: it mentions just the concrete nonterminal sector
mass.  Thus the proof does not hide the already formalized power-saving
sectors behind an aggregate hypothesis.
-/

namespace PaperC
namespace PropositionElevenThree

open CanonicalSectionElevenPartition
open PropositionElevenTwo
open RationalMassFinite
open ResidualMasses
open SectionElevenPartition

noncomputable section

/--
The rate in Corollary 11.3:

`N² exp (-c sqrt (log N) / log log N)`.

The expression is defined for every natural `N`; all uses below are beyond
an explicit threshold where both logarithms are positive.
-/
noncomputable def quantitativeHomogeneousScale
    (c : ℝ) (N _L : ℕ) : ℝ :=
  (N : ℝ) ^ 2 *
    Real.exp
      (-c * Real.sqrt (Real.log N) /
        Real.log (Real.log N))

/--
Every fixed rational power strictly below two is bounded by the
Corollary 11.3 scale.  This is the reusable analytic comparison needed for
the systematic term and sectors one, two, three, five and seven.
-/
theorem rationalPower_uniformBigO_quantitativeHomogeneousScale
    {p q : ℕ} (hpq : p < 2 * q)
    {admissible : ℕ → ℕ → Prop}
    {f : ℕ → ℕ → ℝ}
    (hf :
      UniformRationalPowerSubpolynomialOn
        p q admissible f)
    {c : ℝ} (hc : 0 ≤ c) :
    UniformBigOOn admissible f
      (quantitativeHomogeneousScale c) := by
  have hq : 0 < q := by
    by_contra hq0
    have : q = 0 := Nat.eq_zero_of_not_pos hq0
    simp [this] at hpq
  have htwo : 0 < (2 : ℕ) := by omega
  obtain ⟨Nf, hNf⟩ := hf 2 htwo
  let a : ℝ := (q * 2 : ℕ) * c
  have ha : 0 ≤ a := by
    dsimp only [a]
    positivity
  obtain ⟨Nexp, hNexp⟩ :=
    ExpSqrtLog.pow_le_nat_eventually a ha 1 (by omega)
  obtain ⟨Nlog, hNlog⟩ :=
    exists_nat_gt (Real.exp (Real.exp 1))
  refine ⟨1, by norm_num, max Nf (max Nexp Nlog), ?_⟩
  intro N hN L hNL
  have hNfN : Nf ≤ N :=
    (le_max_left Nf (max Nexp Nlog)).trans hN
  have hNtail : max Nexp Nlog ≤ N :=
    (le_max_right Nf (max Nexp Nlog)).trans hN
  have hNexpN : Nexp ≤ N :=
    (le_max_left Nexp Nlog).trans hNtail
  have hNlogN : Nlog ≤ N :=
    (le_max_right Nexp Nlog).trans hNtail
  have hthreshold :
      Real.exp (Real.exp 1) < (N : ℝ) :=
    hNlog.trans_le (by exact_mod_cast hNlogN)
  have hlogN :
      Real.exp 1 < Real.log N := by
    have hlogs :=
      Real.log_lt_log (Real.exp_pos (Real.exp 1)) hthreshold
    simpa only [Real.log_exp] using hlogs
  have hloglogN :
      1 < Real.log (Real.log N) := by
    have hlogs :=
      Real.log_lt_log (Real.exp_pos 1) hlogN
    simpa only [Real.log_exp] using hlogs
  have hlogNpos : 0 < Real.log N :=
    (Real.exp_pos 1).trans hlogN
  have hloglogNpos : 0 < Real.log (Real.log N) :=
    zero_lt_one.trans hloglogN
  have hsqrtDivLe :
      Real.sqrt (Real.log N) /
          Real.log (Real.log N) ≤
        Real.sqrt (Real.log N) := by
    have hdenom : 1 ≤ Real.log (Real.log N) := hloglogN.le
    exact (div_le_iff₀ hloglogNpos).2 (by
      nlinarith [Real.sqrt_nonneg (Real.log N)])
  let s : ℝ :=
    c * Real.sqrt (Real.log N) /
      Real.log (Real.log N)
  have hs : 0 ≤ s := by
    dsimp only [s]
    positivity
  have hexpCompare :
      Real.exp ((q * 2 : ℕ) * s) ≤ (N : ℝ) := by
    have hsExponent :
        (q * 2 : ℕ) * s ≤
          a * Real.sqrt (Real.log N) := by
      dsimp only [s, a]
      calc
        ((q * 2 : ℕ) : ℝ) *
              (c * Real.sqrt (Real.log N) /
                Real.log (Real.log N)) =
            (((q * 2 : ℕ) : ℝ) * c) *
              (Real.sqrt (Real.log N) /
                Real.log (Real.log N)) := by ring
        _ ≤
            (((q * 2 : ℕ) : ℝ) * c) *
              Real.sqrt (Real.log N) :=
          mul_le_mul_of_nonneg_left hsqrtDivLe (by positivity)
    calc
      Real.exp ((q * 2 : ℕ) * s) ≤
          Real.exp (a * Real.sqrt (Real.log N)) :=
        Real.exp_le_exp.mpr hsExponent
      _ ≤ (N : ℝ) := by
        simpa only [pow_one] using hNexp N hNexpN
  have hNpos : (0 : ℝ) < (N : ℝ) :=
    (Real.exp_pos _).trans hthreshold
  have hNnonneg : (0 : ℝ) ≤ (N : ℝ) := hNpos.le
  have hNone : (1 : ℝ) ≤ (N : ℝ) :=
    ((Real.log_pos_iff (Nat.cast_nonneg N)).mp hlogNpos).le
  have hgap :
      p * 2 + 2 ≤ 2 * (q * 2) := by
    omega
  have hpowerMono :
      (N : ℝ) ^ (p * 2 + 2) ≤
        (N : ℝ) ^ (2 * (q * 2)) :=
    pow_le_pow_right₀ hNone hgap
  have hfPower :=
    hNf N hNfN L hNL
  have htargetPower :
      |f N L| ^ (q * 2) ≤
        (quantitativeHomogeneousScale c N L) ^ (q * 2) := by
    have hscaled :
        |f N L| ^ (q * 2) *
            Real.exp ((q * 2 : ℕ) * s) ≤
          (N : ℝ) ^ (2 * (q * 2)) := by
      calc
        |f N L| ^ (q * 2) *
              Real.exp ((q * 2 : ℕ) * s) ≤
            (N : ℝ) ^ (p * 2 + 1) * (N : ℝ) :=
          mul_le_mul hfPower hexpCompare
            (Real.exp_nonneg _) (by positivity)
        _ = (N : ℝ) ^ (p * 2 + 2) := by
          rw [← pow_succ]
        _ ≤ (N : ℝ) ^ (2 * (q * 2)) := hpowerMono
    have hdiv :=
      (le_div_iff₀ (Real.exp_pos ((q * 2 : ℕ) * s))).2 hscaled
    calc
      |f N L| ^ (q * 2) ≤
          (N : ℝ) ^ (2 * (q * 2)) /
            Real.exp ((q * 2 : ℕ) * s) := hdiv
      _ =
          (quantitativeHomogeneousScale c N L) ^ (q * 2) := by
        unfold quantitativeHomogeneousScale
        dsimp only [s]
        rw [mul_pow, ← pow_mul, div_eq_mul_inv,
          show
            -c * Real.sqrt (Real.log N) /
                Real.log (Real.log N) =
              -(c * Real.sqrt (Real.log N) /
                Real.log (Real.log N)) by ring,
          Real.exp_neg, inv_pow, Real.exp_nat_mul]
  have hroot :
      |f N L| ≤ quantitativeHomogeneousScale c N L := by
    apply
      (pow_le_pow_iff_left₀
        (abs_nonneg (f N L))
        (mul_nonneg (sq_nonneg (N : ℝ))
          (Real.exp_nonneg _))
        (Nat.ne_of_gt (Nat.mul_pos hq htwo))).mp
    exact htargetPower
  have hscaleNonneg :
      0 ≤ quantitativeHomogeneousScale c N L := by
    unfold quantitativeHomogeneousScale
    positivity
  simpa only [one_mul, abs_of_nonneg hscaleNonneg] using hroot

/-!
The only new arithmetic interface.  It is exactly sector (6), not the whole
homogeneous sum.
-/

/- AUDIT_BRIDGE
{
  "id": "PCv07c-C11.3-nonterminal-sector-rate",
  "kind": "internal",
  "status": "open",
  "lean_name": "PaperC.PropositionElevenThree.NonterminalSectorQuantitativeStatement",
  "citation": {
    "authors": ["Brice Pouly"],
    "title": "Loi de Poisson critique dans un bloc dyadique — Débuts de longues plages constantes d’une fonction aléatoire complètement multiplicative de Rademacher étendue",
    "version": "7c, juillet 2026",
    "target_pdf_sha256": "23a5db3c8d024cab3fb8ca9f8f1443f40cf9502b1fb6682a331f5948f57a3336",
    "locator": "Corollaire 11.3, démonstration, p. 37"
  },
  "source_statement": {
    "verbatim": "Le secteur (6) économise exp((C_term − K log 2)√B/log B) par la proposition 9.11, et K log 2 > 2C_term rend l’exposant inférieur à −C_term√B/log B.",
    "source_url": "paper_C_complete_v07c.pdf#page=37",
    "verification": "manual_primary_source_check_required"
  },
  "manuscript_locator": {
    "result": "Corollaire 11.3",
    "equation": "quantitative saving in sector (6)",
    "pages": "37"
  },
  "formalization_relation": "legacy generic sixth-sector API, retained for independent callers: the canonical dyadic mother-mass and Theorem 1.1 routes bypass it via the proved bounded-ratio kappa decomposition, so this open bridge is nonblocking for every canonical theorem-level endpoint"
}
AUDIT_BRIDGE -/
def NonterminalSectorQuantitativeStatement
    (C : ℝ) (A : ℕ) (c : ℝ)
    (smallRowRank : SmallRowRankFamily)
    (rankBudget : RankBudgetFamily) : Prop :=
  UniformBigOOn
    (CriticalRunWindow.InRunLengthWindow C)
    (sectorResidualMass A smallRowRank rankBudget
      .nonterminal)
    (quantitativeHomogeneousScale c)

/-! ## Big-O assembly calculus -/

/-- Pointwise addition preserves a common uniform big-O scale. -/
theorem uniformBigOOn_add
    {admissible : ℕ → ℕ → Prop}
    {f g scale : ℕ → ℕ → ℝ}
    (hf : UniformBigOOn admissible f scale)
    (hg : UniformBigOOn admissible g scale) :
    UniformBigOOn admissible
      (fun N L ↦ f N L + g N L) scale := by
  obtain ⟨Kf, hKf, Nf, hf⟩ := hf
  obtain ⟨Kg, hKg, Ng, hg⟩ := hg
  refine ⟨Kf + Kg, add_nonneg hKf hKg, max Nf Ng, ?_⟩
  intro N hN L hNL
  have hfN := hf N ((le_max_left _ _).trans hN) L hNL
  have hgN := hg N ((le_max_right _ _).trans hN) L hNL
  calc
    |f N L + g N L| ≤ |f N L| + |g N L| := abs_add _ _
    _ ≤ Kf * |scale N L| + Kg * |scale N L| :=
      add_le_add hfN hgN
    _ = (Kf + Kg) * |scale N L| := by ring

/-- A finite sum of functions satisfying one uniform big-O estimate has the
same scale. -/
theorem uniformBigOOn_finset_sum
    {ι : Type*}
    {admissible : ℕ → ℕ → Prop}
    {F : ι → ℕ → ℕ → ℝ}
    {scale : ℕ → ℕ → ℝ}
    (s : Finset ι)
    (hF : ∀ i ∈ s, UniformBigOOn admissible (F i) scale) :
    UniformBigOOn admissible
      (fun N L ↦ ∑ i ∈ s, F i N L) scale := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨0, le_rfl, 0, ?_⟩
      intro N _ L _hNL
      simp
  | @insert i s hi ih =>
      have heq :
          (fun N L ↦ ∑ j ∈ insert i s, F j N L) =
            fun N L ↦ F i N L + ∑ j ∈ s, F j N L := by
        funext N L
        rw [Finset.sum_insert hi]
      rw [heq]
      exact uniformBigOOn_add
        (hF i (Finset.mem_insert_self i s))
        (ih fun j hj ↦ hF j (Finset.mem_insert_of_mem hj))

/-- Fintype form used by the seven-sector decomposition. -/
theorem uniformBigOOn_fintype_sum
    {ι : Type*} [Fintype ι]
    {admissible : ℕ → ℕ → Prop}
    {F : ι → ℕ → ℕ → ℝ}
    {scale : ℕ → ℕ → ℝ}
    (hF : ∀ i, UniformBigOOn admissible (F i) scale) :
    UniformBigOOn admissible
      (fun N L ↦ ∑ i, F i N L) scale := by
  have h :=
    uniformBigOOn_finset_sum (Finset.univ : Finset ι)
      (fun i _hi ↦ hF i)
  simpa using h

/-! ## The six already power-saving contributions -/

/-- Proposition 5.4's systematic mass is already far below the quantitative
Corollary 11.3 scale. -/
theorem systematicMass_uniformBigO_quantitative
    {C : ℝ} (hC : 0 ≤ C) (A : ℕ) (hA : 1 ≤ A)
    {c : ℝ} (hc : 0 ≤ c) :
    UniformBigOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (systematicMass A)
      (quantitativeHomogeneousScale c) := by
  have hfourThird :
      UniformRationalPowerSubpolynomialOn 4 3
        (CriticalRunWindow.InRunLengthWindow C)
        (systematicMass A) := by
    apply UniformRationalPower.mono
      (CriticalRationalMass.rationalMass_two_uniformFourThird
        hC A hA)
    refine ⟨2, ?_⟩
    intro N hN L _hrun
    have hleft : 0 ≤ systematicMass A N L := by
      simp [systematicMass, hN]
    have hright : 0 ≤ (rationalMass N A L 2 : ℝ) := by
      positivity
    rw [abs_of_nonneg hleft, abs_of_nonneg hright,
      systematicMass_eq_rationalMass hN]
  exact
    rationalPower_uniformBigO_quantitativeHomogeneousScale
      (p := 4) (q := 3) (by omega) hfourThird hc

/-- Sector one has the `N^(7/4+o(1))` saving of Proposition 7.3. -/
theorem smallPrimeProductSector_uniformBigO_quantitative
    {C : ℝ} (hC : 0 ≤ C) (A : ℕ)
    (smallRowRank : SmallRowRankFamily)
    (rankBudget : RankBudgetFamily)
    {c : ℝ} (hc : 0 ≤ c) :
    UniformBigOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (sectorResidualMass A smallRowRank rankBudget
        .smallPrimeProduct)
      (quantitativeHomogeneousScale c) := by
  have hrate :=
    PropositionSevenThreeCritical.smallProductLinearResidualMass_uniformSevenFourths
      hC A
  have hquant :=
    rationalPower_uniformBigO_quantitativeHomogeneousScale
      (p := 7) (q := 4) (by omega) hrate hc
  have heq :
      sectorResidualMass A smallRowRank rankBudget
          .smallPrimeProduct =
        PropositionSevenThreeCritical.smallProductLinearResidualMassTotal
          A := by
    funext N L
    exact sectorResidualMass_smallPrimeProduct_eq
      A smallRowRank rankBudget N L
  rw [heq]
  exact hquant

/-- Sector two has the `N^(19/12+o(1))` saving of Proposition 7.4. -/
theorem smallCanonicalHeightSector_uniformBigO_quantitative
    {C : ℝ} (hC : 0 ≤ C) (A : ℕ) (hA : 1 ≤ A)
    (smallRowRank : SmallRowRankFamily)
    (rankBudget : RankBudgetFamily)
    {c : ℝ} (hc : 0 ≤ c) :
    UniformBigOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (sectorResidualMass A smallRowRank rankBudget
        .smallCanonicalHeight)
      (quantitativeHomogeneousScale c) := by
  have hrate :=
    PropositionSevenFourCritical.smallHeightLargeProductLinearResidualMass_uniformNineteenTwelfths
      hC A hA
  have hquant :=
    rationalPower_uniformBigO_quantitativeHomogeneousScale
      (p := 19) (q := 12) (by omega) hrate hc
  have heq :
      sectorResidualMass A smallRowRank rankBudget
          .smallCanonicalHeight =
        PropositionSevenFourCritical.smallHeightLargeProductLinearResidualMassTotal
          A := by
    funext N L
    exact sectorResidualMass_smallCanonicalHeight_eq
      A smallRowRank rankBudget N L
  rw [heq]
  exact hquant

/-- Sector three has the weakest power saving, `N^(31/16+o(1))`, which is
still stronger than the exponential saving displayed in Corollary 11.3. -/
theorem shallowCoreSector_uniformBigO_quantitative
    {C : ℝ} (hC : 0 ≤ C) (A : ℕ)
    (smallRowRank : SmallRowRankFamily)
    (rankBudget : RankBudgetFamily)
    {c : ℝ} (hc : 0 ≤ c) :
    UniformBigOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (sectorResidualMass A smallRowRank rankBudget
        .shallowCore)
      (quantitativeHomogeneousScale c) := by
  have hrate :=
    PropositionSevenFiveCritical.shallowCoreLinearResidualMass_uniformThirtyOneSixteenths
      hC A
  have hquant :=
    rationalPower_uniformBigO_quantitativeHomogeneousScale
      (p := 31) (q := 16) (by omega) hrate hc
  have heq :
      sectorResidualMass A smallRowRank rankBudget .shallowCore =
        PropositionSevenFiveCritical.shallowCoreLinearResidualMassTotal
          A := by
    funext N L
    exact sectorResidualMass_shallowCore_eq
      A smallRowRank rankBudget N L
  rw [heq]
  exact hquant

/-- Sector four is eventually empty, hence has zero quantitative mass. -/
theorem alignedDeepCoreSector_uniformBigO_quantitative
    {C : ℝ} (hC : 0 ≤ C) (A : ℕ)
    (smallRowRank : SmallRowRankFamily)
    (rankBudget : RankBudgetFamily)
    (c : ℝ) :
    UniformBigOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (sectorResidualMass A smallRowRank rankBudget
        .alignedDeepCore)
      (quantitativeHomogeneousScale c) := by
  obtain ⟨Nempty, hNemptyTwo, hNempty⟩ :=
    alignedDeepCoreSector_eventually_empty
      hC A smallRowRank rankBudget
  refine ⟨0, le_rfl, Nempty, ?_⟩
  intro N hN L hrun
  have hNtwo : 2 ≤ N := hNemptyTwo.trans hN
  have hempty := hNempty N hN L hrun hNtwo
  have hmass :
      sectorResidualMass A smallRowRank rankBudget
          .alignedDeepCore N L = 0 := by
    simp only [sectorResidualMass, dif_pos hNtwo,
      sectorResidualMassNat, hempty, linearResidualMass,
      Finset.sum_empty, Nat.cast_zero]
  simp [hmass]

/-- Sector five inherits the `N^(3/2+o(1))` estimate conditional only on
the already registered Proposition 9.9 host-count interface. -/
theorem manyDefectsSector_uniformBigO_quantitative
    {C : ℝ} (hC : 0 ≤ C) (A : ℕ)
    (smallRowRank : SmallRowRankFamily)
    (rankBudget : RankBudgetFamily)
    (hhosts : PropositionNineNine.HostCountStatement C A)
    {c : ℝ} (hc : 0 ≤ c) :
    UniformBigOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (sectorResidualMass A smallRowRank rankBudget
        .manyDefects)
      (quantitativeHomogeneousScale c) := by
  have hthreeHalves :
      UniformRationalPowerSubpolynomialOn 3 2
        (CriticalRunWindow.InRunLengthWindow C)
        (sectorResidualMass A smallRowRank rankBudget
          .manyDefects) := by
    apply UniformRationalPower.mono
      (PropositionNineNine.proposition_nine_nine_uniformThreeHalves
        hC A hhosts)
    refine ⟨2, ?_⟩
    intro N hN L _hrun
    have hleft :
        0 ≤ sectorResidualMass A smallRowRank rankBudget
          .manyDefects N L := by
      simp [sectorResidualMass, hN]
    have hright : 0 ≤ PropositionNineNine.linearMass A N L := by
      simp [PropositionNineNine.linearMass, hN]
    rw [abs_of_nonneg hleft, abs_of_nonneg hright]
    exact sectorResidualMass_manyDefects_le
      hN smallRowRank rankBudget
  exact
    rationalPower_uniformBigO_quantitativeHomogeneousScale
      (p := 3) (q := 2) (by omega) hthreeHalves hc

/-- Sector seven inherits the `N^(7/4+o(1))` terminal estimate already
registered for Theorem 10.1. -/
theorem terminalSector_uniformBigO_quantitative
    {C : ℝ} {A : ℕ}
    {smallRowRank : SmallRowRankFamily}
    {rankBudget : RankBudgetFamily}
    (hterminal :
      TerminalSectorMassStatement
        C A smallRowRank rankBudget)
    {c : ℝ} (hc : 0 ≤ c) :
    UniformBigOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (sectorResidualMass A smallRowRank rankBudget
        .terminal)
      (quantitativeHomogeneousScale c) :=
  rationalPower_uniformBigO_quantitativeHomogeneousScale
    (p := 7) (q := 4) (by omega) hterminal hc

/-! ## Complete Corollary 11.3 -/

/-- Every residual sector has the quantitative rate once the sole new
sixth-sector interface is supplied. -/
theorem everySector_uniformBigO_quantitative
    {C : ℝ} (hC : 0 ≤ C) (A : ℕ) (hA : 1 ≤ A)
    (smallRowRank : SmallRowRankFamily)
    (rankBudget : RankBudgetFamily)
    (hhosts : PropositionNineNine.HostCountStatement C A)
    {c : ℝ} (hc : 0 ≤ c)
    (hnonterminal :
      NonterminalSectorQuantitativeStatement
        C A c smallRowRank rankBudget)
    (hterminal :
      TerminalSectorMassStatement
        C A smallRowRank rankBudget) :
    ∀ sector : ResidualSector,
      UniformBigOOn
        (CriticalRunWindow.InRunLengthWindow C)
        (sectorResidualMass A smallRowRank rankBudget sector)
        (quantitativeHomogeneousScale c) := by
  intro sector
  cases sector with
  | smallPrimeProduct =>
      exact smallPrimeProductSector_uniformBigO_quantitative
        hC A smallRowRank rankBudget hc
  | smallCanonicalHeight =>
      exact smallCanonicalHeightSector_uniformBigO_quantitative
        hC A hA smallRowRank rankBudget hc
  | shallowCore =>
      exact shallowCoreSector_uniformBigO_quantitative
        hC A smallRowRank rankBudget hc
  | alignedDeepCore =>
      exact alignedDeepCoreSector_uniformBigO_quantitative
        hC A smallRowRank rankBudget c
  | manyDefects =>
      exact manyDefectsSector_uniformBigO_quantitative
        hC A smallRowRank rankBudget hhosts hc
  | nonterminal =>
      exact hnonterminal
  | terminal =>
      exact terminalSector_uniformBigO_quantitative
        hterminal hc

/--
Corollary 11.3 in fully quantified conditional form.

The conclusion is the literal homogeneous mass `R₂(N,L)`.  The only new
premise beyond Proposition 11.2 is the narrow quantitative sixth-sector
interface above.
-/
theorem corollary_eleven_three_uniformBigO
    {C : ℝ} (hC : 0 ≤ C) (A : ℕ) (hA : 1 ≤ A)
    (smallRowRank : SmallRowRankFamily)
    (rankBudget : RankBudgetFamily)
    (hhosts : PropositionNineNine.HostCountStatement C A)
    {c : ℝ} (hc : 0 < c)
    (hnonterminal :
      NonterminalSectorQuantitativeStatement
        C A c smallRowRank rankBudget)
    (hterminal :
      TerminalSectorMassStatement
        C A smallRowRank rankBudget) :
    UniformBigOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (homogeneousMass A)
      (quantitativeHomogeneousScale c) := by
  have hsystematic :=
    systematicMass_uniformBigO_quantitative
      hC A hA hc.le
  have hsectors :
      UniformBigOOn
        (CriticalRunWindow.InRunLengthWindow C)
        (fun N L ↦
          ∑ sector : ResidualSector,
            sectorResidualMass A smallRowRank rankBudget
              sector N L)
        (quantitativeHomogeneousScale c) :=
    uniformBigOOn_fintype_sum
      (everySector_uniformBigO_quantitative
        hC A hA smallRowRank rankBudget
        hhosts hc.le hnonterminal hterminal)
  have htotal := uniformBigOOn_add hsystematic hsectors
  have heq :
      homogeneousMass A =
        fun N L ↦ systematicMass A N L +
          ∑ sector : ResidualSector,
            sectorResidualMass A smallRowRank rankBudget
              sector N L := by
    funext N L
    rw [homogeneousMass_eq_systematic_add_residual,
      residualMass_eq_sum_sectorResidualMass]
  rw [heq]
  exact htotal

end

end PropositionElevenThree
end PaperC
