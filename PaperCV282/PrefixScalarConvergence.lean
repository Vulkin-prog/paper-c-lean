import PaperCV282.PrefixVoidBounds
import PaperCV282.SaddleRateConvergence
import PaperC.Probability.CriticalRunWindow

/-! # The true prefix law in bounded-intensity and critical windows

All probability estimates come from the established finite-prefix comparison.
The smallness threshold is uniform before the run length is chosen.
-/
namespace PaperC.V282.PrefixScalarConvergence

open Filter Topology MeasureTheory CorollaryPrefixLaw CriticalRunWindow InfiniteRademacher
open PrefixVoidBounds PoissonVoidApproximation
open ArratiaGoldsteinGordonInput SectionThirteenFiniteBound ScalarSteinInput
open PrefixContainedBounds AllStartSoftPoisson HardPoissonRates SaddleRateConvergence
open PrimeEulerPNT LaishramUniformInput PostQuadraticLiterature

noncomputable section

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

/-- The microscopic remainder vanishes on every fixed positive ambient scale. -/
theorem deep_remainder_tendsto_zero (c : ℝ) (hc : 0<c) :
    Tendsto (fun M : ℕ => Real.exp (-c*(Real.log M/Real.log (Real.log M))))
      atTop (𝓝 0) := by
  have hlog : Tendsto (fun M : ℕ => Real.log M) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hi := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hlog
  have hp : ∀ᶠ M : ℕ in atTop, 0<Real.log (Real.log M)/Real.log M := by
    filter_upwards [hlog.eventually (eventually_ge_atTop (2 : ℝ))] with M hM
    exact div_pos (Real.log_pos (by linarith)) (by linarith)
  have hs := tendsto_inv_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.mpr ⟨hi,hp⟩)
  have hs' : Tendsto (fun M : ℕ => Real.log M/Real.log (Real.log M)) atTop atTop := by
    simpa only [Function.comp_def,id_eq,one_div,inv_div] using hs
  exact Real.tendsto_exp_atBot.comp (hs'.const_mul_atTop_of_neg (by linarith))

/-- The right-end overflow cost vanishes uniformly for bounded intensity. -/
theorem overflow_le_half_power_eventually (betaMax : ℝ) (hbetaMax : 0≤betaMax) :
    ∃ Mzero : ℕ, ∀ M≥Mzero, ∀ L : ℕ,
      (L+1 : ℝ)≤betaMax*Real.log M →
      (L : ℝ)/(2 : ℝ)^L ≤ (fullRate M L : ℝ)*(M : ℝ)^(-(1/2 : ℝ)) := by
  obtain ⟨Np,hp⟩ := LogarithmicWordPowers.polynomial_factor_le_rpow_eventually
    betaMax hbetaMax 1 1 (1/2) (by norm_num)
  refine ⟨max Np 1,?_⟩
  intro M hM L hL
  have hMp : (0 : ℝ)<M := by exact_mod_cast (show 0<M by omega)
  have hlen : (L : ℝ)≤(M : ℝ)^(1/2 : ℝ) := by
    have h := hp M (by omega) L (by simpa using hL)
    simp only [pow_one,one_mul,abs_of_nonneg (by positivity : (0 : ℝ)≤L+1)] at h
    linarith
  have hid : (M : ℝ)^(1/2 : ℝ) = (M : ℝ)*(M : ℝ)^(-(1/2 : ℝ)) := by
    convert Real.rpow_add hMp 1 (-(1/2 : ℝ)) using 1 <;> norm_num
  calc
    (L : ℝ)/(2 : ℝ)^L ≤ (M : ℝ)^(1/2 : ℝ)/(2 : ℝ)^L :=
      div_le_div_of_nonneg_right hlen (by positivity)
    _ = (fullRate M L : ℝ)*(M : ℝ)^(-(1/2 : ℝ)) := by rw [hid,fullRate_coe]; ring

/-- True contained-prefix TV is uniformly small in any fixed band at bounded intensity. -/
theorem contained_prefix_tv_le_eventually
    (hStein : ScalarSteinFactorsStatement) (hLS : UniformPrimeDivisorStatement)
    (hShorey : ShoreySquareProductStatement) (hPNT : PrimeNumberTheoremRemainder)
    (hNR : PellInput.NicolasRobinDivisorLogBoundStatement)
    (betaMin betaMax K delta : ℝ) (hbetaMin : 0<betaMin)
    (hbeta : betaMin<betaMax) (hdelta : 0<delta) :
    ∃ Mzero : ℕ, ∀ M≥Mzero, ∀ L : ℕ,
      betaMin*Real.log M≤(L+1 : ℝ) → (L+1 : ℝ)≤betaMax*Real.log M →
      (fullRate M L : ℝ)≤K →
      natTotalVariation (infinitePrefixStartLaw M L) (poissonMass (fullRate M L))≤delta := by
  obtain ⟨Nt,ht⟩ := theorem_seven_four_contained_prefix hStein hLS hShorey hPNT hNR
    betaMin betaMax (1/12) 1 hbetaMin hbeta (by norm_num) (by norm_num)
  obtain ⟨Na,ha⟩ := MesoscopicPrefixMass.border_mass_ambient_scale_eventually
    betaMin betaMax hbetaMin hbeta hPNT
  obtain ⟨No,ho⟩ := overflow_le_half_power_eventually betaMax (hbetaMin.trans hbeta).le
  obtain ⟨Nh,hh⟩ := hard_rate_le_eventually K 1 (1/12) (delta/129) (by norm_num) (by positivity)
  have hc : 0<betaMin*Real.log 2/8 := by positivity
  obtain ⟨Nd,hd⟩ := eventually_atTop.1 ((deep_remainder_tendsto_zero _ hc).eventually
    (gt_mem_nhds (by positivity : (0 : ℝ)<delta/15)))
  have hp : Tendsto (fun M : ℕ => K*(M : ℝ)^(-(1/2 : ℝ))) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ)<1/2)).comp
      tendsto_natCast_atTop_atTop).const_mul K
  obtain ⟨Np,hp⟩ := eventually_atTop.1 (hp.eventually
    (gt_mem_nhds (by positivity : (0 : ℝ)<delta/3)))
  refine ⟨max Nt (max Na (max No (max Nh (max Nd Np)))),?_⟩
  intro M hM L hlo hhi hK
  have htv := ht M (by omega) L hlo hhi
  have halpha := ha M (by omega) L (by simpa using hlo) (by simpa using hhi)
  have hover := (ho M (by omega) L hhi).trans
    (mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg (Nat.cast_nonneg M) _))
  have hhard : hardRate M L (1/12) 1≤delta/129 := by
    simpa only [hardRate] using hh M (by omega) (fullRate M L : ℝ) (by positivity) hK
  have hmin := min_le_right (1 : ℝ) (hardRate M L (1/12) 1)
  have hdeep := hd M (by omega)
  have hpoly := hp M (by omega)
  linarith

/-- The comparison holds along every bounded-intensity sequence in the full band. -/
theorem contained_prefix_tv_tendsto_zero
    (hStein : ScalarSteinFactorsStatement) (hLS : UniformPrimeDivisorStatement)
    (hShorey : ShoreySquareProductStatement) (hPNT : PrimeNumberTheoremRemainder)
    (hNR : PellInput.NicolasRobinDivisorLogBoundStatement)
    (betaMin betaMax K : ℝ) (hbetaMin : 0<betaMin) (hbeta : betaMin<betaMax)
    (L : ℕ → ℕ)
    (hband : ∀ᶠ M : ℕ in atTop, betaMin*Real.log M≤(L M+1 : ℝ) ∧
      (L M+1 : ℝ)≤betaMax*Real.log M)
    (hK : ∀ᶠ M in atTop, (fullRate M (L M) : ℝ)≤K) :
    Tendsto (fun M => natTotalVariation (infinitePrefixStartLaw M (L M))
      (poissonMass (fullRate M (L M)))) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall (fun M => ha.trans_le (FiniteFieldTotalVariation.massTotalVariation_nonneg _ _))
  · intro b hb
    obtain ⟨N,hN⟩ := contained_prefix_tv_le_eventually hStein hLS hShorey hPNT hNR
      betaMin betaMax K (b/2) hbetaMin hbeta (by positivity)
    filter_upwards [hband,hK,eventually_ge_atTop N] with M hband hK hM
    exact (hN M hM (L M) hband.1 hband.2 hK).trans_lt (by linarith)

/-- The literal critical window is covered uniformly before L. -/
theorem critical_prefix_tv_le_eventually
    (hStein : ScalarSteinFactorsStatement) (hLS : UniformPrimeDivisorStatement)
    (hShorey : ShoreySquareProductStatement) (hPNT : PrimeNumberTheoremRemainder)
    (hNR : PellInput.NicolasRobinDivisorLogBoundStatement)
    (C delta : ℝ) (hC : 0≤C) (hdelta : 0<delta) :
    ∃ Mzero : ℕ, ∀ M≥Mzero, ∀ L : ℕ, InRunLengthWindow C M L →
      natTotalVariation (infinitePrefixStartLaw M L) (poissonMass (fullRate M L))≤delta := by
  obtain ⟨Nb,hb⟩ := firstMomentWindow_eventually hC
  obtain ⟨Nt,ht⟩ := contained_prefix_tv_le_eventually hStein hLS hShorey hPNT hNR
    lowerConstant upperConstant (balanceConstant C) delta lowerConstant_pos
    lowerConstant_lt_upperConstant hdelta
  refine ⟨max Nb Nt,?_⟩
  intro M hM L hw
  obtain ⟨hband,_,hrate⟩ := hb M (by omega) L hw
  apply ht M (by omega) L
  · exact_mod_cast hband.2.2.1
  · exact_mod_cast hband.2.2.2
  · simpa only [fullRate_coe] using hrate

/-- Theorem 7.4's critical-window conclusion concerns the actual infinite prefix count. -/
theorem theorem_seven_four_critical
    (hStein : ScalarSteinFactorsStatement) (hLS : UniformPrimeDivisorStatement)
    (hShorey : ShoreySquareProductStatement) (hPNT : PrimeNumberTheoremRemainder)
    (hNR : PellInput.NicolasRobinDivisorLogBoundStatement)
    (C : ℝ) (hC : 0≤C) (L : ℕ → ℕ)
    (hwindow : ∀ᶠ M in atTop, InRunLengthWindow C M (L M)) :
    Tendsto (fun M => natTotalVariation (infinitePrefixStartLaw M (L M))
      (poissonMass (fullRate M (L M)))) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall (fun M => ha.trans_le (FiniteFieldTotalVariation.massTotalVariation_nonneg _ _))
  · intro b hb
    obtain ⟨N,hN⟩ := critical_prefix_tv_le_eventually hStein hLS hShorey hPNT hNR
      C (b/2) hC (by positivity)
    filter_upwards [hwindow,eventually_ge_atTop N] with M hw hM
    exact (hN M hM (L M) hw).trans_lt (by linarith)

/-- The true longest-run void error is controlled by the comparison of the contained count. -/
theorem prefix_void_error_le_twice_tv {M L : ℕ} (hLM : L≤M) :
    |infiniteRademacherMeasure.real {omega | infinitePrefixLongestConstantStretch M omega<L}-
      Real.exp (-((M : ℝ)/(2 : ℝ)^L))| ≤
      2*natTotalVariation (infinitePrefixStartLaw M L) (poissonMass (fullRate M L)) := by
  have h := abs_mass_zero_sub_le_two_mul_natTotalVariation
    (p := infinitePrefixStartLaw M L) (q := poissonMass (fullRate M L))
    (by rw [infinitePrefixStartCount_law_eq_prefixStartLaw]; exact summable_finiteNatLaw _ _)
    (hasSum_poissonMass _).summable (fun _ => ENNReal.toReal_nonneg) (poissonMass_nonneg _)
  rw [prefix_mass_zero_eq_void hLM,poisson_mass_zero] at h
  exact h

/-- The actual void approximation tends to zero throughout every bounded-intensity band. -/
theorem bounded_prefix_void_tendsto_zero
    (hStein : ScalarSteinFactorsStatement) (hLS : UniformPrimeDivisorStatement)
    (hShorey : ShoreySquareProductStatement) (hPNT : PrimeNumberTheoremRemainder)
    (hNR : PellInput.NicolasRobinDivisorLogBoundStatement)
    (betaMin betaMax K : ℝ) (hbetaMin : 0<betaMin) (hbeta : betaMin<betaMax)
    (L : ℕ → ℕ)
    (hband : ∀ᶠ M : ℕ in atTop, betaMin*Real.log M≤(L M+1 : ℝ) ∧
      (L M+1 : ℝ)≤betaMax*Real.log M)
    (hK : ∀ᶠ M in atTop, (fullRate M (L M) : ℝ)≤K) :
    Tendsto (fun M : ℕ =>
      |infiniteRademacherMeasure.real {omega | infinitePrefixLongestConstantStretch M omega<L M}-
        Real.exp (-((M : ℝ)/(2 : ℝ)^(L M)))|) atTop (𝓝 0) := by
  have ht := contained_prefix_tv_tendsto_zero hStein hLS hShorey hPNT hNR
    betaMin betaMax K hbetaMin hbeta L hband hK
  obtain ⟨Nc,hc⟩ := logarithmic_containment_eventually betaMin betaMax hbetaMin (hbetaMin.trans hbeta).le
  apply squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) _ (by simpa using ht.const_mul 2)
  filter_upwards [hband,eventually_ge_atTop Nc] with M hband hM
  exact prefix_void_error_le_twice_tv (hc M hM (L M) hband.1 hband.2).2


end
end PaperC.V282.PrefixScalarConvergence
