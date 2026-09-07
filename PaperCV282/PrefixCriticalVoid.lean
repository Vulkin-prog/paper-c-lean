import PaperCV282.PrefixScalarConvergence

/-! # The literal critical-window longest-run void law

The source is the same finite-prefix longest constant stretch. Both smallness
and convergence are deduced from the proved comparison of its actual count law.
-/
namespace PaperC.V282.PrefixCriticalVoid

open Filter Topology MeasureTheory InfiniteRademacher CorollaryPrefixLaw CriticalRunWindow
open ScalarSteinInput AllStartSoftPoisson PrefixContainedBounds PrefixScalarConvergence
open PrimeEulerPNT LaishramUniformInput PostQuadraticLiterature

noncomputable section
local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

/-- Uniform critical-window approximation of the actual longest-run void, before L is chosen. -/
theorem critical_prefix_void_le_eventually
    (hStein : ScalarSteinFactorsStatement) (hLS : UniformPrimeDivisorStatement)
    (hShorey : ShoreySquareProductStatement) (hPNT : PrimeNumberTheoremRemainder)
    (hNR : PellInput.NicolasRobinDivisorLogBoundStatement)
    (C delta : ℝ) (hC : 0≤C) (hdelta : 0<delta) :
    ∃ Mzero : ℕ, ∀ M≥Mzero, ∀ L : ℕ, InRunLengthWindow C M L →
      |infiniteRademacherMeasure.real {omega | infinitePrefixLongestConstantStretch M omega<L}-
        Real.exp (-((M : ℝ)/(2 : ℝ)^L))|≤delta := by
  obtain ⟨Nt,ht⟩ := critical_prefix_tv_le_eventually hStein hLS hShorey hPNT hNR
    C (delta/2) hC (by positivity)
  obtain ⟨Nb,hb⟩ := firstMomentWindow_eventually hC
  obtain ⟨Nc,hc⟩ := logarithmic_containment_eventually lowerConstant upperConstant
    lowerConstant_pos (lowerConstant_pos.trans lowerConstant_lt_upperConstant).le
  refine ⟨max Nt (max Nb Nc),?_⟩
  intro M hM L hw
  have hband := (hb M (by omega) L hw).1
  have hLM := (hc M (by omega) L (by exact_mod_cast hband.2.2.1)
    (by exact_mod_cast hband.2.2.2)).2
  have hv := prefix_void_error_le_twice_tv hLM
  have ht' := ht M (by omega) L hw
  linarith

/-- The critical-window void law uses the genuine longest run in the infinite source. -/
theorem theorem_seven_four_critical_void
    (hStein : ScalarSteinFactorsStatement) (hLS : UniformPrimeDivisorStatement)
    (hShorey : ShoreySquareProductStatement) (hPNT : PrimeNumberTheoremRemainder)
    (hNR : PellInput.NicolasRobinDivisorLogBoundStatement)
    (C : ℝ) (hC : 0≤C) (L : ℕ → ℕ)
    (hwindow : ∀ᶠ M in atTop, InRunLengthWindow C M (L M)) :
    Tendsto (fun M : ℕ =>
      |infiniteRademacherMeasure.real {omega | infinitePrefixLongestConstantStretch M omega<L M}-
        Real.exp (-((M : ℝ)/(2 : ℝ)^(L M)))|) atTop (𝓝 0) := by
  obtain ⟨Nb,hb⟩ := firstMomentWindow_eventually hC
  apply bounded_prefix_void_tendsto_zero hStein hLS hShorey hPNT hNR
    lowerConstant upperConstant (balanceConstant C) lowerConstant_pos lowerConstant_lt_upperConstant L
  · filter_upwards [hwindow,eventually_ge_atTop Nb] with M hw hM
    have hband := (hb M hM (L M) hw).1
    exact ⟨by exact_mod_cast hband.2.2.1,by exact_mod_cast hband.2.2.2⟩
  · filter_upwards [hwindow,eventually_ge_atTop Nb] with M hw hM
    simpa only [fullRate_coe] using (hb M hM (L M) hw).2.2


end
end PaperC.V282.PrefixCriticalVoid
