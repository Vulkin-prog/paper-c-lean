import PaperCPrel8.EmpiricalScaleBounds
import PaperCPrel8.MicroscopicReadouts
import PaperCV282.ExactMarkedSignProjection

/-! # The empirical windows of the actual arithmetic start field

Fin(M-L) coordinate i is exactly the integer start i+2. Thus window u is
the sum of J_{j+1,L}, j=u+1,...,u+h, appearing in 7.8a. Summing all exact
marks agrees almost surely with this actual start field, by run finiteness.
-/
namespace PaperC.Prel8.EmpiricalStartField
open MeasureTheory ProbabilityTheory Filter Topology
open PaperC.InfiniteRademacher
open PaperC.Prel8.MicroscopicSiteRestoration PaperC.Prel8.MicroscopicValueProfile
open PaperC.Prel8.EmpiricalWindowVariance PaperC.Prel8.EmpiricalWindowLaw
open PaperC.V282.BulkMarkedTypes PaperC.V282.BulkMarkedSource PaperC.V282.BulkMarkedTarget
open PaperC.V282.BulkMarkedComparison PaperC.V282.BulkMarkedAggregation
open PaperC.V282.PoissonFieldMeasure PaperC.V282.ExactMarkedSignProjection
open PaperC.V282.SharpConditioning PaperC.V282.FiniteFieldTotalVariation
open PaperC.V282.ConditionedCountableLaw
open scoped NNReal
noncomputable section
local instance : MeasurableSpace PaperC.F₂ := ⊤
local instance : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

/-- Exact integer endpoints of the interior-start set. -/
theorem mem_interior_iff (M L x : ℕ) :
    x ∈ interiorStarts M L ↔ 2 ≤ x ∧ x ≤ M-L+1 := by
  simp only [interiorStarts, retainedStarts, Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro ⟨j,hj,rfl⟩
    omega
  · intro hx
    exact ⟨x-1,by omega,by omega⟩

/-- The reindexing retains the original integer positions. -/
def interiorEquiv (M L : ℕ) : Fin (M-L) ≃ interiorStarts M L where
  toFun i := ⟨i.val+2,(mem_interior_iff M L _).mpr (by omega)⟩
  invFun x := ⟨x.val-2,by have hx := (mem_interior_iff M L x.val).mp x.property; omega⟩
  left_inv i := by ext; simp
  right_inv x := by
    ext
    have hx := (mem_interior_iff M L x.val).mp x.property
    dsimp
    omega

/-- Actual arithmetic starts indexed in their original order. -/
def actualStarts (M L : ℕ) (ω : InfiniteSample) (i : Fin (M-L)) : ℕ :=
  startField (interiorStarts M L) L ω (interiorEquiv M L i)

/-- Sum all signs and all excesses, and keep the exact site order. -/
def readStarts (M L : ℕ) (c : SpatialMarkedConfig (interiorStarts M L)) (i : Fin (M-L)) : ℕ :=
  siteCounts (interiorStarts M L) c (interiorEquiv M L i)

theorem measurable_actualStarts (M L : ℕ) : Measurable (actualStarts M L) := by
  apply Measurable.of_eval
  intro i
  exact (measurable_pi_apply _).comp (measurable_startField _ _)

/-- The full marked target becomes the actual independent site-Poisson law. -/
theorem readStarts_hasLaw (M L : ℕ) :
    HasLaw (readStarts M L) (fieldMeasure (fun _ : Fin (M-L) => (1:ℝ≥0)/2^L))
      (spatialTargetMeasure (interiorStarts M L) L) := by
  have hr := hasLaw_reindexedPoisson (startFieldRates (interiorStarts M L) L)
    (interiorEquiv M L).symm
  have hc := hr.fun_comp (hasLaw_siteCounts (interiorStarts M L) L)
  exact hc

/-- Run finiteness justifies replacing the marked projection by actual starts. -/
theorem ae_readStarts_eq_actual (M L : ℕ) :
    (fun ω => readStarts M L (spatialMarkedSource (interiorStarts M L) L ω))
      =ᵐ[infiniteRademacherMeasure] actualStarts M L := by
  filter_upwards [ae_siteCounts_source_eq (interiorStarts M L) L
    (fun x hx => ((mem_interior_iff M L x).mp hx).1)] with ω hω
  exact congrArg (fun v : interiorStarts M L → ℕ => fun i => v (interiorEquiv M L i)) hω

/-- Actual ordered starts inherit the full microscopic comparison with constant one. -/
theorem actual_start_distance_le (M L : ℕ) :
    measureTotalVariation (infiniteRademacherMeasure.map (actualStarts M L))
      (fieldMeasure (fun _ : Fin (M-L) => (1:ℝ≥0)/2^L)) ≤
    massTotalVariation (conditionalObservableLaw infiniteRademacherMeasure Set.univ
      (spatialMarkedSource (interiorStarts M L) L)) (spatialTargetLaw (interiorStarts M L) L) := by
  have ht := PaperC.Prel8.MicroscopicReadouts.measurable_readout_le M L Set.univ
    (by simp : 0 < infiniteRademacherMeasure.real Set.univ)
    (readStarts M L) (measurable_of_countable _)
  rw [cond_univ, (readStarts_hasLaw M L).map_eq] at ht
  simp only [Function.comp_def] at ht
  rw [Measure.map_congr (ae_readStarts_eq_actual M L)] at ht
  exact ht

/-- The paper's empirical deviation event has one full-field error plus the overlap bound. -/
theorem actual_frequency_tail_le (M L N h r : ℕ) (hN : 0 < N) (hh : 0 < h)
    (hfit : N+h ≤ (M-L)+1) {eta : ℝ} (heta : 0 < eta) :
    infiniteRademacherMeasure.real {ω |
      eta < |frequency N h r (actualStarts M L ω)-
        (poissonMeasure (h*((1:ℝ≥0)/2^L))).real {r}|} ≤
    massTotalVariation (conditionalObservableLaw infiniteRademacherMeasure Set.univ
      (spatialMarkedSource (interiorStarts M L) L)) (spatialTargetLaw (interiorStarts M L) L) +
      (2*(h:ℝ)-1)/(4*N*eta^2) :=
  source_frequency_tail_le infiniteRademacherMeasure (actualStarts M L)
    (measurable_actualStarts M L) _ hN hh hfit _ (actual_start_distance_le M L) r heta

/-- Almost-sure Poisson convergence for the genuine arithmetic window frequencies,
under explicit summable full-field errors, overlap ratios and limiting means.
The literal 7.8a length/window sequence still needs those numerical checks. -/
theorem ae_actual_empirical_poisson
    (sizes length N h : ℕ → ℕ) (delta : ℕ → ℝ) (tau : ℝ≥0)
    (hN : ∀ k, 0 < N k) (hh : ∀ᶠ k in atTop, 0 < h k)
    (hfit : ∀ᶠ k in atTop, N k+h k ≤ (sizes k-length k)+1)
    (hfield : ∀ᶠ k in atTop,
      massTotalVariation (conditionalObservableLaw infiniteRademacherMeasure Set.univ
        (spatialMarkedSource (interiorStarts (sizes k) (length k)) (length k)))
        (spatialTargetLaw (interiorStarts (sizes k) (length k)) (length k)) ≤ delta k)
    (hd : Summable delta) (hratio : Summable (fun k => (h k:ℝ)/(N k)))
    (hmean : Tendsto (fun k => (h k:ℝ)*((1:ℝ)/2^(length k))) atTop (𝓝 (tau:ℝ))) :
    ∀ᵐ ω ∂infiniteRademacherMeasure, Tendsto (fun k => massTotalVariation
      (fun r => frequency (N k) (h k) r (actualStarts (sizes k) (length k) ω))
      (fun r => (poissonMeasure tau).real {r})) atTop (𝓝 0) := by
  apply PaperC.Prel8.EmpiricalWindowConvergence.ae_empirical_variation_convergence
    infiniteRademacherMeasure (fun k => sizes k-length k) N h
    (fun k => actualStarts (sizes k) (length k))
    (fun k => measurable_actualStarts _ _) (fun k => (1:ℝ≥0)/2^(length k)) delta hN hh hfit
    ?_ hd hratio _ ?_ (fun _ => measureReal_nonneg) ?_
  · filter_upwards [hfield] with k hk
    exact (actual_start_distance_le (sizes k) (length k)).trans hk
  · simpa only [poissonMeasure_real_singleton] using hasSum_one_poissonMeasure tau
  · intro r
    apply PaperC.Prel8.EmpiricalScaleBounds.poisson_mass_tendsto _ tau _ r
    simpa using hmean

end
end PaperC.Prel8.EmpiricalStartField
