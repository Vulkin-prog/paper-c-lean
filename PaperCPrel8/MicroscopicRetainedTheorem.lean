import PaperCPrel8.MicroscopicRetainedRates
import PaperCPrel8.MicroscopicFootprintLedger

/-! # Uniform retained-field theorem under the literal paper information budget

Every retained coordinate is a true exact signed run indicator. The prime
cutoff, excess cutoff, good set and cylinder are explicitly constructed.
This theorem does not yet restore discarded sites or unbounded excess marks.
-/
namespace PaperC.Prel8.MicroscopicRetainedTheorem
open PaperC.Prel8.MicroscopicActualGeometry PaperC.Prel8.MicroscopicPaperBudget
open PaperC.Prel8.MicroscopicProfileBudget PaperC.Prel8.MicroscopicRetainedRates
open PaperC.Prel8.MicroscopicGoodField PaperC.Prel8.ActualSignedPalm
open PaperC.Prel8.MicroscopicInfiniteField PaperC.Prel8.MicroscopicRelationExcess
open PaperC.Prel8.MicroscopicFootprintLedger PaperC.Prel8.MicroscopicFiniteLedger
open PaperC.ConditionalStartProbability PaperC.ArratiaGoldsteinGordonInput
open PaperC.V282.DirectionalSteinInput PaperC.V282.FiniteFieldTotalVariation
open PaperC.V282.FiniteFieldPoissonCoupling PaperC.V282.AllStartSoftPoisson
open PaperC.V282.SaddleParameters PaperC.V282.SaddleScales PaperC.V282.PrimeEulerPNT
open scoped NNReal
noncomputable section

abbrev actualSites (M L : ℕ) (I : ℝ) :=
  goodSites M (M-L) L (paperExcess M L I) (primeCutoff M)

def retainedDistance (M L : ℕ) (I : ℝ)
    (A : SmallSample (sourceCylinder M L I) (primeCutoff M) → Prop) : ℝ :=
  massTotalVariation (conditionalLaw (sourceCylinder M L I) (primeCutoff M) L
    (paperExcess M L I) (actualSites M L I) A) (poissonFieldMass (rate L))

/-- Uniform comparison on the entire retained finite marked lattice with the paper's budget. -/
theorem retained_comparison_eventually (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax c c' epsilon : ℝ) (hbetaMin : 0 < betaMin)
    (hband : betaMin < betaMax) (hc' : 0 < c') (hcc : c' < c) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ, ∀ I : ℝ,
      betaMin*Real.log M ≤ (L+1:ℝ) → (L+1:ℝ) ≤ betaMax*Real.log M →
      0 ≤ I → 1 ≤ siteRate M L →
      I+Real.log (siteRate M L) ≤ saddleCutoff 1 (Real.log M)-c*saddleNu 1 (Real.log M) →
      ∀ A : SmallSample (sourceCylinder M L I) (primeCutoff M) → Prop,
      ∀ _hA : 0 < eventProbability (FinitePMF.uniform (SampleSpace (sourceCylinder M L I)))
        (fun ω => A (restrictSmall (sourceCylinder M L I) (primeCutoff M) ω)),
      I = -Real.log (eventProbability (FinitePMF.uniform (SampleSpace (sourceCylinder M L I)))
        (fun ω => A (restrictSmall (sourceCylinder M L I) (primeCutoff M) ω))) →
      DirectionalSolutionBounds (rate L : Index (actualSites M L I) (paperExcess M L I) → ℝ≥0) →
      retainedDistance M L I A ≤ 2*Real.exp (-c'*saddleNu 1 (Real.log M))+
        2*(M:ℝ)^(-(1/(3:ℝ))+epsilon) := by
  have hbeta : 0 < betaMax := hbetaMin.trans hband
  obtain ⟨Mg,hg⟩ := actual_geometry_eventually betaMin betaMax c hbetaMin hband (by linarith)
  obtain ⟨Mb,hb⟩ := paper_to_ambient_budget_eventually betaMax c c' hbeta hcc
  obtain ⟨Me,he⟩ := actual_edgeCount_bound hPNT (betaMax+1) c' (by linarith) hc'
  obtain ⟨Ml,hl⟩ := local_budget_rate (betaMax+1) 11 epsilon (by linarith) (by norm_num) hepsilon
  obtain ⟨Mr,hr⟩ := conditional_actual_profile_bound betaMin betaMax epsilon hbetaMin hband hepsilon
  refine ⟨max 1 (max Mg (max Mb (max Me (max Ml Mr)))), ?_⟩
  intro M hM L I hlo hhi hI hrate hbudget A hA hinfo hsolution
  have g := hg M (by omega) L I hlo hhi hI hrate hbudget
  have geom := actual_goodGeometry g
  obtain ⟨_,hambient⟩ := hb M (by omega) L I hhi hrate hbudget
  let Q := L+paperExcess M L I+1
  have hQ : (Q:ℝ) ≤ (betaMax+1)*Real.log M := by
    have := g.shifted_upper
    dsimp only [Q]
    push_cast
    linarith
  have hedge := he M (by omega) (sourceCylinder M L I) (M-L) L (paperExcess M L I)
    g.population g.support_short (by simpa only [Q,Nat.cast_add,Nat.cast_one] using hQ) (actualSites M L I) (goodSites_subset _ _ _ _ _) geom
  have hlocal := hl M (by omega) Q hQ I (fullRate M L) hI g.ambient_rate g.ambient_budget
  have hrel := hr M (by omega) (M-L) L (primeCutoff M) (sourceCylinder M L I) I
    hlo hhi hI g.ambient_rate g.ambient_budget g.interior_end g.profile_cylinder
  have hgraph := graph_budget_absorption hI (show 0 < (fullRate M L:ℝ) by have := g.ambient_rate; linarith) hambient (eta := c')
  have hgm : ((actualSites M L I).card:ℝ) ≤ M := by
    have hc : (actualSites M L I).card ≤ M-L := by
      have hh := Finset.card_le_card (goodSites_subset M (M-L) L (paperExcess M L I) (primeCutoff M))
      simpa only [Nat.card_Icc,Nat.add_sub_cancel] using hh
    exact_mod_cast hc.trans (Nat.sub_le M L)
  have hm : (0:ℝ) < M := by exact_mod_cast (show 0<M by omega)
  rw [fullRate_coe] at hlocal hgraph
  have hQcast : (Q:ℝ)+1=(L:ℝ)+(paperExcess M L I:ℝ)+2 := by
    dsimp only [Q]
    push_cast
    ring
  have hnum := retained_ledger_bound
    (p := 1/(2:ℝ)^L) (m := M) (n := ((M-L:ℕ):ℝ)) (g := (actualSites M L I).card)
    (b := edgeCount geom) (r := (M:ℝ)^(-(1/(3:ℝ))+epsilon))
    (I := I) (V := saddleCutoff 1 (Real.log M)) (nu := saddleNu 1 (Real.log M)) (c := c') (Q := Q)
    (by positivity) (by positivity) (by exact_mod_cast Nat.sub_le M L) (by positivity) hgm hI
    (by rw [hQcast]; exact hedge)
    (by convert hlocal using 1; ring) hm
    (by simpa only [show 2*c'-c'=c' by ring,div_eq_mul_inv,one_mul] using hgraph)
  have hcomp := infinite_relation_comparison geom g.strong_prime A hA hsolution
  have hinv : Real.exp I =
      (eventProbability (FinitePMF.uniform (SampleSpace (sourceCylinder M L I)))
        (fun ω => A (restrictSmall (sourceCylinder M L I) (primeCutoff M) ω)))⁻¹ := by
    conv_lhs => rw [hinfo]
    rw [Real.exp_neg,Real.exp_log hA]
  change retainedDistance M L I A ≤ _ at hcomp
  calc
    _ ≤ _ := hcomp
    _ = (1/(2:ℝ)^L)^2 * (((actualSites M L I).card:ℝ)+edgeCount geom+
        4*((actualSites M L I).card:ℝ)*(2*(Q:ℝ)+1)+Real.exp I*edgeCount geom) +
        Real.exp I*((1/(2:ℝ)^L)^2*separatedExcess (sourceCylinder M L I) L
          (paperExcess M L I) (actualSites M L I)) := by
      rw [hinv]
      dsimp only [Q]
      push_cast
      ring
    _ ≤ _ := by linarith only [hnum,hrel]

end
end PaperC.Prel8.MicroscopicRetainedTheorem
