import PaperC.Probability.SteinChenTerms

/-!
# Stein--Chen terms in the critical run-length window

This file closes the asymptotic part of Lemma 13.8 from the finite majorants
in `SteinChenTerms`.

* The first term is unconditional: its numerator is `N + E_Y`, where
  `E_Y = o_C(N²)` at the literal terminal cutoff.
* The averaged second term has numerator
  `T_N + E_Y + touchingMass + separatedDefectMass`.
  The first three summands are unconditional.  The last is transported from
  the public conclusion of Proposition 11.2 through the exact public
  identification in `SectionTwelveMoments`.

Division by `2^(2L)` turns every `o_C(N²)` numerator into `o_C(1)` because
`N / 2^L` is uniformly bounded in the literal critical window.
-/

namespace PaperC
namespace SteinChenCritical

open TerminalPrimeCutoff

noncomputable section

/-- Real first Stein--Chen term at the literal terminal cutoff. -/
noncomputable def steinBOneReal
    (N L : ℕ) : ℝ :=
  ((SteinChenTerms.steinBOne N L
    (terminalPrimeCutoff (L + 1)) : ℚ) : ℝ)

/-- Real averaged second Stein--Chen term at the literal terminal cutoff. -/
noncomputable def steinBTwoAverageReal
    (N L : ℕ) : ℝ :=
  ((SteinChenTerms.steinBTwoAverage N L
    (terminalPrimeCutoff (L + 1)) : ℚ) : ℝ)

/-- Numerator in the public finite estimate for the first term. -/
noncomputable def steinBOneNumerator
    (N L : ℕ) : ℝ :=
  (N : ℝ) +
    ((LargePrimeDependencyGraph.orderedDependencyEdges N L
      (terminalPrimeCutoff (L + 1))).card : ℝ)

/-- Numerator in the public finite estimate for the averaged second term. -/
noncomputable def steinBTwoNumerator
    (N L : ℕ) : ℝ :=
  ((SectionTwelveMoments.touchingOffDiagPairs N L).card : ℝ) +
    ((LargePrimeDependencyGraph.orderedDependencyEdges N L
      (terminalPrimeCutoff (L + 1))).card : ℝ) +
    (TouchingMass.touchingMass N L : ℝ) +
    (SectionTwelveMoments.jointDefectMass N L
      (SectionTwelveMoments.separatedOffDiagPairs N L) : ℝ)

/-- The linear population `N` is uniformly little-oh of `N²`. -/
theorem dyadicLength_uniformLittleOQuadratic
    (admissible : ℕ → ℕ → Prop) :
    UniformLittleOOn admissible
      (fun N _ => (N : ℝ))
      (fun N _ => (N : ℝ) ^ 2) := by
  have hlinear :
      UniformLinearSubpolynomialOn admissible
        (fun N _ => (N : ℝ)) := by
    have hone :=
      ExpSqrtLog.uniformSubpolynomialOn_const admissible 1
    apply UniformLinear.of_linear_mul_subpolynomial hone
    refine ⟨0, ?_⟩
    intro N _ L _hNL
    simp only [abs_of_nonneg
      (by positivity : (0 : ℝ) ≤ (N : ℝ)), abs_one, mul_one]
    exact le_rfl
  exact
    SectionTwelveMoments.uniformLittleOQuadratic_of_uniformLinear hlinear

/--
The complete ordered touching population is `O(N)`, hence uniformly
`o_C(N²)`.
-/
theorem touchingOffDiagPairs_uniformLittleOQuadratic
    {C : ℝ} :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun N L =>
        ((SectionTwelveMoments.touchingOffDiagPairs N L).card : ℝ))
      (fun N _ => (N : ℝ) ^ 2) := by
  have hlinear :
      UniformLinearSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C)
        (fun N L =>
          ((SectionTwelveMoments.touchingOffDiagPairs N L).card : ℝ)) := by
    have htwo :=
      ExpSqrtLog.uniformSubpolynomialOn_const
        (CriticalRunWindow.InRunLengthWindow C) 2
    apply UniformLinear.of_linear_mul_subpolynomial htwo
    refine ⟨0, ?_⟩
    intro N _ L _hrun
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
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    calc
      ((SectionTwelveMoments.touchingOffDiagPairs N L).card : ℝ) ≤
          2 * (N : ℝ) := hcard
      _ = (N : ℝ) * 2 := by ring
  exact
    SectionTwelveMoments.uniformLittleOQuadratic_of_uniformLinear hlinear

/--
Transport of the public Proposition 11.2 conclusion to the exact separated
defect mass used in `SteinChenTerms`.
-/
theorem separatedDefectMass_uniformLittleOQuadratic
    {C : ℝ} {A : ℕ}
    (h11 :
      UniformLittleOOn
        (CriticalRunWindow.InRunLengthWindow C)
        (PropositionElevenTwo.homogeneousMass A)
        (fun N _ => (N : ℝ) ^ 2)) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun N L =>
        (SectionTwelveMoments.jointDefectMass N L
          (SectionTwelveMoments.separatedOffDiagPairs N L) : ℝ))
      (fun N _ => (N : ℝ) ^ 2) := by
  intro ε hε
  obtain ⟨N11, hN11⟩ := h11 ε hε
  refine ⟨max 2 N11, ?_⟩
  intro N hN L hrun
  change
    |(SectionTwelveMoments.jointDefectMass N L
        (SectionTwelveMoments.separatedOffDiagPairs N L) : ℝ)| ≤
      ε * |(N : ℝ) ^ 2|
  rw [
    SectionTwelveMoments.jointDefectMass_separated_cast_eq_homogeneousMass
      (A := A) ((le_max_left _ _).trans hN)]
  exact hN11 N ((le_max_right _ _).trans hN) L hrun

/--
Any nonnegative `o_C(N²)` numerator becomes `o_C(1)` after division by
`2^(2L)`.
-/
private theorem normalizedQuadratic_uniformLittleOOne
    {C : ℝ}
    {f : ℕ → ℕ → ℝ}
    (hC : 0 ≤ C)
    (hf :
      UniformLittleOOn
        (CriticalRunWindow.InRunLengthWindow C)
        f (fun N _ => (N : ℝ) ^ 2))
    (hfNonneg : ∀ N L, 0 ≤ f N L) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun N L => f N L / (2 : ℝ) ^ (2 * L))
      (fun _ _ => 1) := by
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
  have hratioNonneg :
      0 ≤ (N : ℝ) / (2 : ℝ) ^ L := by positivity
  have hbalance :
      (N : ℝ) / (2 : ℝ) ^ L ≤ B := by
    simpa only [B] using hw.2.2
  have hbalanceSq :
      ((N : ℝ) / (2 : ℝ) ^ L) ^ 2 ≤ B ^ 2 :=
    pow_le_pow_left₀ hratioNonneg hbalance 2
  simp only [abs_div, abs_of_nonneg (hfNonneg N L),
    abs_of_pos (pow_pos (by norm_num : (0 : ℝ) < 2) (2 * L)),
    abs_one, mul_one]
  calc
    f N L / (2 : ℝ) ^ (2 * L) ≤
        (δ * (N : ℝ) ^ 2) / (2 : ℝ) ^ (2 * L) :=
      div_le_div_of_nonneg_right hfLe (by positivity)
    _ = δ * ((N : ℝ) / (2 : ℝ) ^ L) ^ 2 := by
      rw [show 2 * L = L * 2 by omega, pow_mul]
      ring
    _ ≤ δ * B ^ 2 :=
      mul_le_mul_of_nonneg_left hbalanceSq hδ.le
    _ = ε := by
      dsimp only [δ]
      field_simp [ne_of_gt hBpos]

/--
The finite first-term numerator is uniformly `o_C(N²)`.
-/
theorem steinBOneNumerator_uniformLittleOQuadratic
    {C : ℝ} (hC : 0 ≤ C) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      steinBOneNumerator
      (fun N _ => (N : ℝ) ^ 2) := by
  have hN :=
    dyadicLength_uniformLittleOQuadratic
      (CriticalRunWindow.InRunLengthWindow C)
  have hedge :=
    DependencyEdgesCritical.orderedDependencyEdges_terminalCutoff_uniformLittleOQuadratic
      hC
  have hsum :=
    PropositionElevenTwo.uniformLittleOOn_add hN hedge
  simpa only [steinBOneNumerator] using hsum

/--
First part of Lemma 13.8:
`b₁ = o_C(1)` at the literal terminal cutoff.
-/
theorem steinBOne_uniformLittleOOne
    {C : ℝ} (hC : 0 ≤ C) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      steinBOneReal
      (fun _ _ => 1) := by
  have hnormalized :=
    normalizedQuadratic_uniformLittleOOne
      hC
      (steinBOneNumerator_uniformLittleOQuadratic hC)
      (fun N L => by
        unfold steinBOneNumerator
        positivity)
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := hnormalized ε hε
  refine ⟨N₀, ?_⟩
  intro N hN L hrun
  have hfiniteQ :=
    SteinChenTerms.steinBOne_le
      N L (terminalPrimeCutoff (L + 1))
  have hfinite := (Rat.cast_le (K := ℝ)).2 hfiniteQ
  push_cast at hfinite
  have htargetNonneg : 0 ≤ steinBOneReal N L := by
    unfold steinBOneReal
    apply Rat.cast_nonneg.mpr
    unfold SteinChenTerms.steinBOne
    exact Finset.sum_nonneg fun _pair _ ↦ by
      unfold SteinChenTerms.conditionalMarginal
      positivity
  have hnumNonneg : 0 ≤ steinBOneNumerator N L := by
    unfold steinBOneNumerator
    positivity
  have hbound := hN₀ N hN L hrun
  simp only [abs_of_nonneg htargetNonneg, abs_one, mul_one] at hbound ⊢
  rw [abs_of_nonneg (div_nonneg hnumNonneg
    (by positivity : 0 ≤ (2 : ℝ) ^ (2 * L)))] at hbound
  apply hfinite.trans
  simpa only [steinBOneNumerator] using hbound

/--
The complete finite numerator for the averaged second term is
`o_C(N²)`, assuming exactly the public Proposition 11.2 conclusion.
-/
theorem steinBTwoNumerator_uniformLittleOQuadratic
    {C : ℝ} (hC : 0 ≤ C) {A : ℕ}
    (h11 :
      UniformLittleOOn
        (CriticalRunWindow.InRunLengthWindow C)
        (PropositionElevenTwo.homogeneousMass A)
        (fun N _ => (N : ℝ) ^ 2)) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      steinBTwoNumerator
      (fun N _ => (N : ℝ) ^ 2) := by
  have hpairs :=
    touchingOffDiagPairs_uniformLittleOQuadratic (C := C)
  have hedge :=
    DependencyEdgesCritical.orderedDependencyEdges_terminalCutoff_uniformLittleOQuadratic
      hC
  have htouch :=
    SectionTwelveMoments.touchingMass_uniformLittleOQuadratic hC
  have hseparated :=
    separatedDefectMass_uniformLittleOQuadratic h11
  have hfirst :=
    PropositionElevenTwo.uniformLittleOOn_add hpairs hedge
  have hsecond :=
    PropositionElevenTwo.uniformLittleOOn_add hfirst htouch
  have hall :=
    PropositionElevenTwo.uniformLittleOOn_add hsecond hseparated
  unfold steinBTwoNumerator
  simpa only [add_assoc] using hall

/--
Averaged second Stein--Chen term from the public conclusion of
Proposition 11.2.
-/
theorem steinBTwoAverage_uniformLittleOOne_of_propositionElevenTwo
    {C : ℝ} (hC : 0 ≤ C) {A : ℕ}
    (h11 :
      UniformLittleOOn
        (CriticalRunWindow.InRunLengthWindow C)
        (PropositionElevenTwo.homogeneousMass A)
        (fun N _ => (N : ℝ) ^ 2)) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      steinBTwoAverageReal
      (fun _ _ => 1) := by
  have hnormalized :=
    normalizedQuadratic_uniformLittleOOne
      hC
      (steinBTwoNumerator_uniformLittleOQuadratic hC h11)
      (fun N L => by
        unfold steinBTwoNumerator
        positivity)
  obtain ⟨Nwindow, hwindow⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  intro ε hε
  obtain ⟨Nnorm, hnorm⟩ := hnormalized ε hε
  refine ⟨max Nwindow Nnorm, ?_⟩
  intro N hN L hrun
  have hw :=
    hwindow N ((le_max_left _ _).trans hN) L hrun
  have hNtwo : 2 ≤ N := by
    have hcritical := hw.1
    have hheightPos :
        (0 : ℝ) < ((L + 1 : ℕ) : ℝ) := by positivity
    have hlogNpos : 0 < Real.log (N : ℝ) := by
      have hc₂ :
          0 < CriticalRunWindow.upperConstant :=
        CriticalRunWindow.lowerConstant_pos.trans
          CriticalRunWindow.lowerConstant_lt_upperConstant
      have hprodPos :
          0 <
            CriticalRunWindow.upperConstant * Real.log (N : ℝ) :=
        hheightPos.trans_le hcritical.2.2.2
      by_contra h
      have hnonpos : Real.log (N : ℝ) ≤ 0 := le_of_not_gt h
      exact (not_lt_of_ge
        (mul_nonpos_of_nonneg_of_nonpos hc₂.le hnonpos)) hprodPos
    have hNone : (1 : ℝ) < (N : ℝ) :=
      (Real.log_pos_iff (Nat.cast_nonneg N)).mp hlogNpos
    exact_mod_cast hNone
  have hfiniteQ :=
    SteinChenTerms.steinBTwoAverage_le
      (N := N) (L := L)
      (Y := terminalPrimeCutoff (L + 1))
      hNtwo hw.2.1
  have hfinite := (Rat.cast_le (K := ℝ)).2 hfiniteQ
  push_cast at hfinite
  have htargetNonneg : 0 ≤ steinBTwoAverageReal N L := by
    unfold steinBTwoAverageReal SteinChenTerms.steinBTwoAverage
      SectionTwelveMoments.jointPairMass
    apply Rat.cast_nonneg.mpr
    exact Finset.sum_nonneg fun pair _ =>
      SteinChenTerms.jointStartProbability_nonneg
        N L pair.1 pair.2
  have hnumNonneg : 0 ≤ steinBTwoNumerator N L := by
    unfold steinBTwoNumerator
    positivity
  have hbound :=
    hnorm N ((le_max_right _ _).trans hN) L hrun
  simp only [abs_of_nonneg htargetNonneg, abs_one, mul_one] at hbound ⊢
  rw [abs_of_nonneg (div_nonneg hnumNonneg
    (by positivity : 0 ≤ (2 : ℝ) ^ (2 * L)))] at hbound
  apply hfinite.trans
  simpa only [steinBTwoNumerator] using hbound

/--
Second part of Lemma 13.8, with exactly the named public hypotheses of
Proposition 11.2.
-/
theorem steinBTwoAverage_uniformLittleOOne
    {C : ℝ} (hC : 0 ≤ C) (A : ℕ) (hA : 1 ≤ A)
    (smallRowRank : PropositionElevenTwo.SmallRowRankFamily)
    (rankBudget : PropositionElevenTwo.RankBudgetFamily)
    (hhosts : PropositionNineNine.HostCountStatement C A)
    (hnonterminal :
      PropositionElevenTwo.NonterminalSectorMassStatement
        C A smallRowRank rankBudget)
    (hterminal :
      PropositionElevenTwo.TerminalSectorMassStatement
        C A smallRowRank rankBudget) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      steinBTwoAverageReal
      (fun _ _ => 1) := by
  apply
    steinBTwoAverage_uniformLittleOOne_of_propositionElevenTwo
      hC
  exact
    PropositionElevenTwo.proposition_eleven_two_uniformLittleOQuadratic
      hC A hA smallRowRank rankBudget
      hhosts hnonterminal hterminal

end

end SteinChenCritical
end PaperC
