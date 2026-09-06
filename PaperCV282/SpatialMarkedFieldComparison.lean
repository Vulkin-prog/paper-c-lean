import PaperCV282.SpatialMarkedSource
import PaperCV282.SpatialMarkedTargetProjection
import PaperCV282.SpatialMarkedTargetTail
import PaperCV282.CountableLawTransfer
import PaperCV282.ExactMarkedRates
import PaperCV282.ExactMarkedSourceTail

/-!
# Comparison of the actual spatial field with all excesses and both signs

Both laws live on the same countable, finitely supported lattice. The proof
removes the actual source and target tails after the finite marked comparison.
-/
namespace PaperC.V282.SpatialMarkedFieldComparison

open MeasureTheory InfiniteMassCoupling CountableLawTransfer FiniteFieldTotalVariation
open SpatialMarkedTypes SpatialMarkedSource SpatialMarkedTarget SpatialMarkedTargetProjection
open SpatialMarkedTargetTail ExactMarkedInfinite ExactMarkedModel ExactMarkedFieldBounds
open ExactMarkedRates ExactMarkedSourceTail InfiniteRademacher ConditionalStartProbability
open InfiniteExactLengthProbabilityTransfer FiniteFieldPoissonCoupling
open PrimeEulerPNT ProcessAGGInput AllStartSoftPoisson
open MarkedDetruncation

noncomputable section

local instance instProbabilityInfiniteRademacher : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

def spatialTargetLaw (N L : ℕ) : SpatialMarkedConfig N → ℝ :=
  observableLaw (spatialTargetMeasure N L) id

theorem spatialTargetLaw_eq_singleton (N L : ℕ) (config : SpatialMarkedConfig N) :
    spatialTargetLaw N L config=(spatialTargetMeasure N L).real {config} := rfl

theorem hasSum_spatialTargetLaw (N L : ℕ) : HasSum (spatialTargetLaw N L) 1 :=
  hasSum_observableLaw _ measurable_id

theorem spatialTargetLaw_nonneg (N L : ℕ) (config : SpatialMarkedConfig N) :
    0 ≤ spatialTargetLaw N L config := observableLaw_nonneg _ _ _

def spatialSignedDistance (N L : ℕ) : ℝ :=
  massTotalVariation (spatialSourceLaw N L) (spatialTargetLaw N L)

theorem spatialSignedDistance_nonneg (N L : ℕ) : 0 ≤ spatialSignedDistance N L :=
  massTotalVariation_nonneg _ _

theorem spatialSignedDistance_le_one (N L : ℕ) : spatialSignedDistance N L ≤ 1 :=
  massTotalVariation_le_one (hasSum_spatialSourceLaw N L) (hasSum_spatialTargetLaw N L)
    (spatialSourceLaw_nonneg N L) (spatialTargetLaw_nonneg N L)

/-- All finite source coordinates are measurable on the original infinite product space. -/
theorem measurable_infiniteSignedField_full (N L E : ℕ) :
    Measurable (infiniteSignedField N L E (dyadicBlock N)) := by
  have h : (projectConfiguration N E) ∘ (spatialMarkedSource N L) =
      infiniteSignedField N L E (dyadicBlock N) := funext (project_spatialMarkedSource N L E)
  rw [← h]
  exact (measurable_of_countable _).comp (measurable_spatialMarkedSource N L)

/-- A single tail event controls the whole discarded signed source configuration. -/
theorem source_embedding_disagreement_le (N L E : ℕ) :
    infiniteRademacherMeasure.real {ω | spatialMarkedSource N L ω ≠
      embedConfiguration N E (infiniteSignedField N L E (dyadicBlock N) ω)} ≤
        infiniteMarkTailProbability N L E := by
  change _ ≤ infiniteRademacherMeasure.real (infiniteMarkTailEvent N L E)
  rw [← spatialSourceTail_eq_markTail]
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro ω hω
  by_contra hn
  apply hω
  rw [← project_spatialMarkedSource,embed_project_configuration]
  exact spatialMarkedSource_eq_truncate_off_tail N L E ω hn

theorem target_embedding_disagreement_le (N L E : ℕ) :
    (spatialTargetMeasure N L).real {config | config ≠
      embedConfiguration N E (projectConfiguration N E config)} ≤
        (fullRate N L : ℝ)/(2 : ℝ)^(E+1) := by
  apply (measureReal_mono (μ := spatialTargetMeasure N L) (s₂ := spatialTargetTail N E) ?_).trans
    (spatial_target_tail_probability_le N L E)
  intro config hconfig
  by_contra hn
  apply hconfig
  rw [embed_project_configuration]
  exact (spatial_truncation_eq_outside_tail N E config hn).symm

/-- All sites, all excesses, and both signs are compared on one common countable lattice. -/
theorem spatial_signed_tv_le_finite_and_tails (N L E : ℕ) :
    spatialSignedDistance N L ≤ infiniteMarkTailProbability N L E+
      exactSignedDistance N L E (dyadicBlock N)+(fullRate N L : ℝ)/(2 : ℝ)^(E+1) := by
  have htarget : observableLaw (spatialTargetMeasure N L) (projectConfiguration N E) =
      poissonFieldMass (ExactMarkedFieldTransfer.allSignedRates N L E (dyadicBlock N)) :=
    funext (spatial_project_mass_eq N L E)
  have hfinite : massTotalVariation
      (observableLaw infiniteRademacherMeasure (infiniteSignedField N L E (dyadicBlock N)))
      (observableLaw (spatialTargetMeasure N L) (projectConfiguration N E)) =
      exactSignedDistance N L E (dyadicBlock N) := by
    rw [htarget]
    rfl
  exact truncation_tv_le_of_bounds infiniteRademacherMeasure (spatialTargetMeasure N L)
    (measurable_spatialMarkedSource N L) measurable_id (measurable_infiniteSignedField_full N L E)
    (measurable_of_countable (projectConfiguration N E)) (embedConfiguration N E)
    (source_embedding_disagreement_le N L E) hfinite.le (target_embedding_disagreement_le N L E)

/-- A full-band quantitative estimate with a free, growing excess cutoff. -/
theorem spatial_signed_full_band (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax epsilon eta : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hepsilon : 0 < epsilon) (heta : 0 < eta) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L E : ℕ,
      betaMin*Real.log N ≤ (L+1 : ℝ) → (L+E+2 : ℝ) ≤ betaMax*Real.log N →
      spatialSignedDistance N L ≤ 32*exactMarkedRate N L epsilon eta+
        ((fullRate N L : ℝ)/(2 : ℝ)^(E+1))*(2+(N : ℝ)^(-(1/(2 : ℝ))+epsilon)) := by
  obtain ⟨Nf,hf⟩ := theorem_five_six_signed_full_band hAGG hPNT betaMin betaMax epsilon eta
    hbetaMin hbeta hepsilon heta
  obtain ⟨Nt,ht⟩ := source_mark_tail_le_eventually betaMin betaMax epsilon
    hbetaMin hbeta hepsilon
  refine ⟨max Nf Nt,?_⟩
  intro N hN L E hlo hhi
  have hlo' : betaMin*Real.log N ≤ (L+E+2 : ℝ) := by
    have he : (0 : ℝ) ≤ E := by positivity
    linarith
  have hfin := (hf N (by omega) L E hlo hhi).2.2
  have htail := ht N (by omega) L E hlo' hhi
  have hdist := spatial_signed_tv_le_finite_and_tails N L E
  linarith

end
end PaperC.V282.SpatialMarkedFieldComparison
