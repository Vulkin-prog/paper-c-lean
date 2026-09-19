import PaperCPrel8.MicroscopicPairLedger
import PaperCV282.ExactMarkedInfinite

/-! # Exact passage of the microscopic marked field to the infinite source

All small-prime events are represented when the cylinder covers the cutoff.
The conditional masses below are actual source probabilities, not formal kernels.
-/
namespace PaperC.Prel8.MicroscopicInfiniteField
open PaperC.Prel8.ActualSignedPalm PaperC.Prel8.MicroscopicFiniteLedger
open PaperC.Prel8.MicroscopicPairLedger PaperC.Prel8.FiniteConditioning
open MeasureTheory PaperC.InfiniteRademacher PaperC.InfiniteCylinderTransfer
open PaperC.InfiniteExactLengthProbabilityTransfer PaperC.ConditionalStartProbability
open PaperC.V282.ExactMarkedModel PaperC.V282.ExactMarkedInfinite
open PaperC.V282.InfiniteFieldTransfer PaperC.ConditionalAGGAverage
open PaperC.SectionThirteenCouplings PaperC.ArratiaGoldsteinGordonInput
open PaperC.V282.DirectionalSteinInput
open PaperC.V282.FiniteFieldTotalVariation PaperC.V282.FiniteFieldPoissonCoupling
open scoped NNReal
noncomputable section
local instance : MeasurableSpace F₂ := ⊤
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- Uniform finite events are exactly the masses of their infinite cylinder preimages. -/
theorem cylinder_probability (C : ℕ) (P : SampleSpace C → Prop) :
    (infiniteRademacherMeasure {ω | P (restrictToFinite C ω)}).toReal =
      eventProbability (FinitePMF.uniform (SampleSpace C)) P := by
  have he : {ω | P (restrictToFinite C ω)} = restrictToFinite C ⁻¹' {σ | P σ} := rfl
  rw [he, ← Measure.map_apply (measurable_restrictToFinite C)
    (Set.toFinite _ |>.measurableSet), map_infiniteRademacherMeasure_restrictToFinite,
    finiteRademacherMeasure_event_eq_uniformEventProbability]
  rw [ENNReal.toReal_ofReal]
  · exact (eventProbability_fullUniformPMF_eq P |>.trans
      (congrArg (fun x : ℚ => (x : ℝ)) (finiteUniformProbability_eq_uniformEventProbability P))).symm
  · apply Rat.cast_nonneg.mpr
    unfold PaperC.uniformEventProbability
    positivity

/-- The literal field of exact signed runs, indexed by retained left boundaries. -/
def infiniteField (L E : ℕ) (G : Finset ℕ) (ω : InfiniteSample) (i : Index G E) : ℕ :=
  signedMarkValue (infiniteValueBit ω) (i.1.val+1) L i.2.1.val i.2.2

/-- Every retained source coordinate agrees with its finite prime restriction. -/
theorem field_restrict {C Y L E : ℕ} {G : Finset ℕ}
    (h : GoodGeometry C Y L E G) (ω : InfiniteSample) :
    field C L E G (restrictToFinite C ω) = infiniteField L E G ω := by
  funext i
  have hc : i.1.val+1+(L+i.2.1.val) ≤ C := by
    have := h.cylinder_le i.1.val i.1.property
    have := i.2.1.isLt
    omega
  simp only [field, infiniteField, signedMarkValue, signedExactMark_restrictToFinite_iff hc]

/-- Actual infinite-source conditional masses for any event in the represented small trace. -/
def conditionalLaw (C Y L E : ℕ) (G : Finset ℕ) (A : SmallSample C Y → Prop)
    (z : Index G E → ℕ) : ℝ :=
  (infiniteRademacherMeasure {ω | A (restrictSmall C Y (restrictToFinite C ω)) ∧
    infiniteField L E G ω = z}).toReal /
  (infiniteRademacherMeasure {ω | A (restrictSmall C Y (restrictToFinite C ω))}).toReal

/-- Equality of the entire conditional field law, rather than only its marginals. -/
theorem conditionalLaw_eq_finite {C Y L E : ℕ} {G : Finset ℕ}
    (h : GoodGeometry C Y L E G) (A : SmallSample C Y → Prop)
    (hA : 0 < eventProbability (FinitePMF.uniform (SampleSpace C))
      (fun ω => A (restrictSmall C Y ω))) :
    conditionalLaw C Y L E G A = finiteFieldLaw (sourceLaw A hA) (field C L E G) := by
  funext z
  rw [finiteFieldLaw_eq_eventProbability]
  change _ = eventProbability (conditional _ _ hA) _
  rw [probability_conditional]
  unfold conditionalLaw
  simp_rw [← field_restrict h]
  rw [cylinder_probability C (fun σ => A (restrictSmall C Y σ) ∧ field C L E G σ = z),
    cylinder_probability C (fun σ => A (restrictSmall C Y σ))]

/-- The infinite conditional law is normalized by its actual positive event probability. -/
theorem conditionalLaw_hasSum {C Y L E : ℕ} {G : Finset ℕ}
    (h : GoodGeometry C Y L E G) (A : SmallSample C Y → Prop)
    (hA : 0 < eventProbability (FinitePMF.uniform (SampleSpace C))
      (fun ω => A (restrictSmall C Y ω))) :
    HasSum (conditionalLaw C Y L E G A) 1 := by
  rw [conditionalLaw_eq_finite h A hA]
  exact hasSum_finiteFieldLaw _ _

/-- Source-facing infinite-field comparison with the proved finite arithmetic ledger. -/
theorem infinite_arithmetic_comparison {C Y L E : ℕ} {G : Finset ℕ}
    (h : GoodGeometry C Y L E G) (hY : 2*(L+E+2) ≤ Y)
    (A : SmallSample C Y → Prop)
    (hA : 0 < eventProbability (FinitePMF.uniform (SampleSpace C))
      (fun ω => A (restrictSmall C Y ω)))
    (hsolution : DirectionalSolutionBounds (rate L : Index G E → ℝ≥0)) :
    massTotalVariation (conditionalLaw C Y L E G A) (poissonFieldMass (rate L)) ≤
      (1/(2:ℝ)^L)^2 * ((G.card : ℝ) + edgeCount h + weightedEdges h
        (eventProbability (FinitePMF.uniform (SampleSpace C)) (fun ω => A (restrictSmall C Y ω)))) := by
  rw [conditionalLaw_eq_finite h A hA]
  exact finite_arithmetic_comparison h hY A hA hsolution

end
end PaperC.Prel8.MicroscopicInfiniteField
