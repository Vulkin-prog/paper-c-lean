import PaperCV282.MaximalCouplingMeasure
import PaperCV282.QuenchedScalarBand
import PaperCV282.QuenchedSpatialClosure

/-! # A maximal coupling for each scale and each observed prime environment

These are ordinary couplings of individual conditional laws. No compatible
choice across scales, or additional arithmetic independence, is asserted.
-/
namespace PaperC.V282.QuenchedMaximalCouplings

open MeasureTheory ProbabilityTheory Filter Topology InfiniteRademacher InfiniteCylinderTransfer
open InfiniteConditionalWords ConditionalStartProbability FinitePrimeEnvironment
open ConditionedCountableLaw InfiniteMassCoupling MaximalCouplingMeasure
open QuenchedScalarBand QuenchedSpatialClosure HardPoissonRates AllStartSoftPoisson
open GeometricSaddleSummability ScalarSteinInput PrimeEulerPNT SaddleParameters SaddleScales
open SectionThirteenFiniteBound InfiniteMaskedScalarTransfer

noncomputable section

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤
local instance instProbabilityInfiniteRademacher : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

/-- Exact maximal coupling of the actual conditional source and target, in every environment. -/
theorem environment_maximal_coupling {α : Type*} [Countable α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (C Y : ℕ)
    (f : InfiniteSample → α) (hf : Measurable f) (q : α → ℝ)
    (hq : HasSum q 1) (hq0 : ∀ x,0≤q x) (omega : InfiniteSample) :
    ∃ mu : Measure (α × α), IsProbabilityMeasure mu ∧
      observableLaw mu Prod.fst=conditionalObservableLaw infiniteRademacherMeasure
        (infiniteSmallPrimeAtom C Y (smallPrimeRestriction C Y omega)) f ∧
      observableLaw mu Prod.snd=q ∧
      mu.real {z | z.1≠z.2}=environmentDistance C Y f q omega := by
  have hp : 0 < infiniteRademacherMeasure.real
      (infiniteSmallPrimeAtom C Y (smallPrimeRestriction C Y omega)) := by
    rw [PrimeFieldEventConditioning.real_atom_mass]
    positivity
  exact exists_maximal_coupling _ q (hasSum_conditionalObservableLaw _ _ hp hf) hq
    (conditionalObservableLaw_nonneg _ _ _) hq0

/-- Every pointwise environment estimate is realized by an ordinary coupling. -/
theorem environment_coupling_le {α : Type*} [Countable α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (C Y : ℕ)
    (f : InfiniteSample → α) (hf : Measurable f) (q : α → ℝ)
    (hq : HasSum q 1) (hq0 : ∀ x,0≤q x) (omega : InfiniteSample) {r : ℝ}
    (hr : environmentDistance C Y f q omega≤r) :
    ∃ mu : Measure (α × α), IsProbabilityMeasure mu ∧
      observableLaw mu Prod.fst=conditionalObservableLaw infiniteRademacherMeasure
        (infiniteSmallPrimeAtom C Y (smallPrimeRestriction C Y omega)) f ∧
      observableLaw mu Prod.snd=q ∧ mu.real {z | z.1≠z.2}≤r := by
  obtain ⟨mu,hp,hf',hq',hd⟩ := environment_maximal_coupling C Y f hf q hq hq0 omega
  exact ⟨mu,hp,hf',hq',hd.le.trans hr⟩

/-- The simultaneous scalar conclusion has a coupling for every admissible length and scale. -/
theorem corollary_six_four_scalar_couplings (hStein : ScalarSteinFactorsStatement)
    (hPNT : PrimeNumberTheoremRemainder) (sizes : ℕ → ℕ) (hg : GeometricLowerGrowth sizes)
    (lo hi c beta : ℝ) (hlo : 0<lo) (hhi : lo<hi) (hb : 0<beta) (hbc : beta<c) :
    ∀ᵐ omega ∂infiniteRademacherMeasure, ∀ᶠ k in atTop, ∀ L : ℕ,
      lo*Real.log (sizes k)≤(L+1 : ℝ) → (L+1 : ℝ)≤hi*Real.log (sizes k) →
      max 0 (Real.log (fullRate (sizes k) L))≤
        saddleCutoff 1 (Real.log (sizes k))-c*saddleNu 1 (Real.log (sizes k)) →
      ∃ mu : Measure (ℕ × ℕ), IsProbabilityMeasure mu ∧
        observableLaw mu Prod.fst=conditionalObservableLaw infiniteRademacherMeasure
          (infiniteSmallPrimeAtom (hardCutoff (sizes k)) (hardCutoff (sizes k))
            (smallPrimeRestriction (hardCutoff (sizes k)) (hardCutoff (sizes k)) omega))
          (infiniteMaskedCount L (dyadicBlock (sizes k))) ∧
        observableLaw mu Prod.snd=poissonMass (fullRate (sizes k) L) ∧
        mu.real {z | z.1≠z.2}≤Real.exp (-beta*saddleNu 1 (Real.log (sizes k))) := by
  filter_upwards [corollary_six_four_uniform_scalar hStein hPNT sizes hg lo hi c beta hlo hhi hb hbc]
    with omega hw
  filter_upwards [hw] with k hk
  intro L hL hL' hbu
  have hf : Measurable (infiniteMaskedCount L (dyadicBlock (sizes k))) := by
    apply measurable_to_countable'
    intro n
    exact measurableSet_infiniteMaskedCount_event _ (Finset.Subset.refl _) n
  exact environment_coupling_le _ _ _ hf _ (hasSum_poissonMass _) (poissonMass_nonneg _) omega
    (hk L hL hL' hbu)

end
end PaperC.V282.QuenchedMaximalCouplings
