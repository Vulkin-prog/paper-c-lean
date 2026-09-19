import PaperCV282.PrefixScalarBounds
import PaperCV282.SaddlePoissonScales
import PaperC.Probability.PoissonVoidApproximation

/-! # An independent scalar hit bound for the shifted microscopic tail

This module imports only the pre-existing scalar theory. In particular it does
not use the new microscopic Palm comparison that will later consume this bound.
-/
namespace PaperC.Prel8.IndependentScalarTail
open MeasureTheory Set PaperC.InfiniteRademacher
open PaperC.V282.InfiniteMaskedScalarTransfer PaperC.V282.FiniteStartMaskSource
open PaperC.V282.PrefixScalarBounds PaperC.V282.SaddlePoissonScales
open PaperC.V282.HardPoissonRates PaperC.V282.AllStartSoftPoisson
open PaperC.V282.ScalarSteinInput PaperC.V282.PrimeEulerPNT
open PaperC.V282.LaishramUniformInput PaperC.V282.PostQuadraticLiterature
open PaperC.ArratiaGoldsteinGordonInput PaperC.SectionThirteenFiniteBound
open PaperC.PoissonVoidApproximation
open scoped NNReal
noncomputable section
local instance : MeasurableSpace PaperC.F₂ := ⊤
local instance : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- Existence of a genuine start in an arbitrary finite mask. -/
def hitEvent (K : ℕ) (mask : Finset ℕ) : Set InfiniteSample :=
  {ω | infiniteMaskedCount K mask ω ≠ 0}

/-- The count's nonzero event is the union of the actual start events. -/
theorem hitEvent_iff (K : ℕ) (mask : Finset ℕ) (ω : InfiniteSample) :
    ω ∈ hitEvent K mask ↔ ∃ x ∈ mask, PaperC.StartEvent (infiniteValueBit ω) x K := by
  simp [hitEvent, infiniteMaskedCount]

/-- No measurability assumption on an unspecified observable is needed. -/
theorem measurableSet_hitEvent (K : ℕ) (mask : Finset ℕ) : MeasurableSet (hitEvent K mask) :=
  (measurableSet_count_event mask (C := mask.sup id+K)
    (fun _x hx => Nat.add_le_add_right (Finset.le_sup (f := id) hx) K) 0).compl

/-- Non-vacancy is exactly one minus the actual scalar mass at zero. -/
theorem hit_probability_eq (K : ℕ) (mask : Finset ℕ) :
    infiniteRademacherMeasure.real (hitEvent K mask) = 1-infiniteMaskedLaw K mask 0 := by
  have hm := measurableSet_count_event mask (C := mask.sup id+K)
    (fun _x hx => Nat.add_le_add_right (Finset.le_sup (f := id) hx) K) 0
  change infiniteRademacherMeasure.real ({ω | infiniteMaskedCount K mask ω=0}ᶜ) = _
  rw [measureReal_compl hm, probReal_univ]
  rfl

/-- Testing vacancy in the established scalar law gives an independent hit estimate. -/
theorem hit_probability_le (K : ℕ) (mask : Finset ℕ) (r : ℝ≥0) :
    infiniteRademacherMeasure.real (hitEvent K mask) ≤ (r:ℝ) +
      2*natTotalVariation (infiniteMaskedLaw K mask) (poissonMass r) := by
  have h := abs_mass_zero_sub_le_two_mul_natTotalVariation
    (summable_infiniteMaskedLaw K mask) (hasSum_poissonMass r).summable
    (infiniteMaskedLaw_nonneg K mask) (poissonMass_nonneg r)
  have hz : poissonMass r 0 = Real.exp (-(r:ℝ)) := by
    rw [poissonMass_formula]; simp
  rw [hz] at h
  rw [hit_probability_eq]
  linarith [neg_abs_le (infiniteMaskedLaw K mask 0-Real.exp (-(r:ℝ))),
    Real.add_one_le_exp (-(r:ℝ))]

/-- The old scalar hard rate is at most twice the intensity, uniformly before the length. -/
theorem hardRate_le_twice_intensity :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ K : ℕ, hardRate M K (1/12) 1 ≤ 2*(fullRate M K:ℝ) := by
  obtain ⟨Mzero,hz⟩ := saddle_exponential_le_eventually 1 1 1 1 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨max Mzero 1, ?_⟩
  intro M hM K
  have he := hz M (by omega)
  have hp : (M:ℝ)^(-(1/3:ℝ)+1/12) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast (show 1≤M by omega)) (by norm_num)
  unfold hardRate
  simp only [one_mul, neg_mul] at he ⊢
  nlinarith [(fullRate M K).coe_nonneg]

/-- F.1's shifted scalar tail, valid for every length in a fixed logarithmic band. -/
theorem prefix_hit_bound_eventually
    (hStein : ScalarSteinFactorsStatement) (hLS : UniformPrimeDivisorStatement)
    (hShorey : ShoreySquareProductStatement) (hPNT : PrimeNumberTheoremRemainder)
    (hNR : PaperC.PellInput.NicolasRobinDivisorLogBoundStatement)
    (betaMin betaMax : ℝ) (hbetaMin : 0<betaMin) (hbeta : betaMin<betaMax) :
    ∃ Mzero : ℕ, ∀ M≥Mzero, ∀ K : ℕ,
      betaMin*Real.log M≤(K+1:ℝ) → (K+1:ℝ)≤betaMax*Real.log M →
      infiniteRademacherMeasure.real (hitEvent K (Finset.Ico 2 M)) ≤
        173*(M:ℝ)/(2:ℝ)^K +
          4*Real.exp (-(betaMin*Real.log 2/8)*(Real.log M/Real.log (Real.log M))) := by
  obtain ⟨Mp,hp⟩ := global_source_hard_rate_eventually hStein hLS hShorey hPNT hNR
    betaMin betaMax (1/12) 1 hbetaMin hbeta (by norm_num) (by norm_num)
  obtain ⟨Mr,hr⟩ := hardRate_le_twice_intensity
  refine ⟨max Mp Mr, ?_⟩
  intro M hM K hlo hhi
  have hh := hit_probability_le K (Finset.Ico 2 M) (fullRate M K)
  have hv := hp M (by omega) K hlo hhi
  have hb := hr M (by omega) K
  rw [fullRate_coe] at hh hb
  calc
    _ ≤ 173*((M:ℝ)/(2:ℝ)^K) + 4*Real.exp (-(betaMin*Real.log 2/8)*(Real.log M/Real.log (Real.log M))) := by linarith
    _ = _ := by ring

/-- Restricting the queried start set can only improve the independent scalar tail. -/
theorem hit_probability_mono (K : ℕ) {s t : Finset ℕ} (hst : s ⊆ t) :
    infiniteRademacherMeasure.real (hitEvent K s) ≤ infiniteRademacherMeasure.real (hitEvent K t) := by
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  intro ω hω
  obtain ⟨x,hx,hs⟩ := (hitEvent_iff K s ω).mp hω
  exact (hitEvent_iff K t ω).mpr ⟨x,hst hx,hs⟩

end
end PaperC.Prel8.IndependentScalarTail
