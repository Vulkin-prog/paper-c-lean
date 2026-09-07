import PaperCV282.MeanScalarBudget
import PaperCV282.QuenchedFiniteFamilies
import PaperCV282.GeometricScaleInstances

/-! # Almost-sure scalar approximation simultaneously on a complete fixed logarithmic band -/
namespace PaperC.V282.QuenchedScalarBand

open MeasureTheory Filter Topology InfiniteRademacher InfiniteCylinderTransfer
open FinitePrimeEnvironment MeanScalarBudget QuenchedFiniteFamilies GeometricSaddleSummability
open GeometricScaleInstances AllStartSoftPoisson HardPoissonRates SaddleParameters SaddleScales
open InfiniteMaskedScalarTransfer ScalarSteinInput PrimeEulerPNT

noncomputable section

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤
local instance instProbabilityInfiniteRademacher : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

def scalarEnvironmentDistance (N L : ℕ) : InfiniteSample → ℝ :=
  environmentDistance (hardCutoff N) (hardCutoff N)
    (infiniteMaskedCount L (dyadicBlock N)) (poissonMass (fullRate N L))

/-- All and only the lengths in the fixed band with the common information margin. -/
def admissibleLengths (N : ℕ) (lo hi c : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range (⌊hi*Real.log N⌋₊+1)).filter fun L =>
    lo*Real.log N≤(L+1 : ℝ) ∧ (L+1 : ℝ)≤hi*Real.log N ∧
    max 0 (Real.log (fullRate N L))≤saddleCutoff 1 (Real.log N)-c*saddleNu 1 (Real.log N)

theorem mem_admissibleLengths (N L : ℕ) (lo hi c : ℝ) :
    L∈admissibleLengths N lo hi c ↔
      lo*Real.log N≤(L+1 : ℝ) ∧ (L+1 : ℝ)≤hi*Real.log N ∧
      max 0 (Real.log (fullRate N L))≤saddleCutoff 1 (Real.log N)-c*saddleNu 1 (Real.log N) := by
  classical
  simp only [admissibleLengths,Finset.mem_filter,Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_,h⟩
    have hh : (L : ℝ)≤hi*Real.log N := by linarith [h.2.1]
    exact Nat.lt_succ_of_le (Nat.le_floor hh)

theorem card_admissibleLengths (N : ℕ) (lo hi c : ℝ) (hhi : 0≤hi)
    (hlog : 1≤Real.log N) :
    ((admissibleLengths N lo hi c).card : ℝ)≤(hi+1)*Real.log N := by
  classical
  have hc : (admissibleLengths N lo hi c).card≤⌊hi*Real.log N⌋₊+1 := by
    exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)
  have hf := Nat.floor_le (mul_nonneg hhi (by linarith : 0≤Real.log N))
  have hc' : ((admissibleLengths N lo hi c).card : ℝ)≤(⌊hi*Real.log N⌋₊ : ℝ)+1 := by
    exact_mod_cast hc
  nlinarith

/-- One almost-sure event controls every admissible length, with no independence assumption. -/
theorem corollary_six_four_uniform_scalar (hStein : ScalarSteinFactorsStatement)
    (hPNT : PrimeNumberTheoremRemainder) (sizes : ℕ → ℕ) (hg : GeometricLowerGrowth sizes)
    (lo hi c beta : ℝ) (hlo : 0<lo) (hhi : lo<hi) (hb : 0<beta) (hbc : beta<c) :
    ∀ᵐ omega ∂infiniteRademacherMeasure, ∀ᶠ k in atTop, ∀ L : ℕ,
      lo*Real.log (sizes k)≤(L+1 : ℝ) → (L+1 : ℝ)≤hi*Real.log (sizes k) →
      max 0 (Real.log (fullRate (sizes k) L))≤
        saddleCutoff 1 (Real.log (sizes k))-c*saddleNu 1 (Real.log (sizes k)) →
      scalarEnvironmentDistance (sizes k) L omega≤
        Real.exp (-beta*saddleNu 1 (Real.log (sizes k))) := by
  obtain ⟨Nzero,hzero⟩ := mean_scalar_hard_rate hStein hPNT lo hi c ((c+beta)/2)
    hlo hhi (by linarith) (by linarith)
  have hcard : ∀ᶠ k in atTop,
      ((admissibleLengths (sizes k) lo hi c).card : ℝ)≤(hi+1)*Real.log (sizes k) := by
    filter_upwards [(log_sizes_tendsto_atTop hg).eventually (eventually_ge_atTop (1 : ℝ))] with k hk
    exact card_admissibleLengths _ _ _ _ (hlo.trans hhi).le hk
  have hm : ∀ᶠ k in atTop, ∀ L∈admissibleLengths (sizes k) lo hi c,
      (∫ omega, scalarEnvironmentDistance (sizes k) L omega ∂infiniteRademacherMeasure)≤
        40*Real.exp (-((c+beta)/2)*saddleNu 1 (Real.log (sizes k)))+(sizes k : ℝ)^(-(1 : ℝ)) := by
    filter_upwards [(sizes_tendsto_atTop hg).eventually (eventually_ge_atTop Nzero)] with k hk
    intro L hL
    have hh := (mem_admissibleLengths _ _ _ _ _).mp hL
    have h := hzero (sizes k) hk L hh.1 hh.2.1 hh.2.2
    simpa only [scalarEnvironmentDistance,integral_environmentDistance] using
      h.trans (le_add_of_nonneg_right (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  have h := ae_eventually_uniform_saddle_bound infiniteRademacherMeasure
    (fun k => admissibleLengths (sizes k) lo hi c) (fun k L => scalarEnvironmentDistance (sizes k) L)
    (fun _ _ => integrable_environmentDistance _ _ _ _)
    (fun _ _ => environmentDistance_nonneg _ _ _ _) sizes hg
    (hi+1) 1 ((c+beta)/2) beta 1 40 (by norm_num) (by linarith) (by norm_num) (by norm_num) hcard hm
  filter_upwards [h] with omega hw
  filter_upwards [hw] with k hk
  intro L hL hL' hbu
  exact hk L ((mem_admissibleLengths _ _ _ _ _).mpr ⟨hL,hL',hbu⟩)

end
end PaperC.V282.QuenchedScalarBand
