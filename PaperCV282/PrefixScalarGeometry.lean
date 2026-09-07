import PaperCV282.PrefixScalarCouplings
import PaperCV282.MacroscopicRetentionBounds
import PaperCV282.AllStartSoftPoisson

/-! # Exact geometry and Poisson recentering of the retained prefix -/
namespace PaperC.V282.PrefixScalarGeometry

open Affine ArratiaGoldsteinGordonInput SectionThirteenFiniteBound SectionThirteenCouplings ScalarSteinInput
open FiniteStartMaskAverages MacroscopicGeometry MacroscopicRetentionBounds
open MesoscopicPrefixMass MaskedScalarCoupling AllStartSoftPoisson

noncomputable section

theorem macro_subset_global {M : ℕ} {delta : ℝ} (hM : 2≤M) (hd : 0<delta) :
    macroscopicStarts M delta⊆Finset.Ico 2 M := by
  intro x hx
  obtain ⟨hl,hu⟩ := (mem_macroscopicStarts _ _ _).mp hx
  exact Finset.mem_Ico.mpr ⟨(two_le_macroscopic_lowerEndpoint hM hd).trans hl,hu⟩

theorem macro_subset_closed (M : ℕ) (delta : ℝ) :
    macroscopicStarts M delta⊆Finset.Icc ⌈(M : ℝ)^delta⌉₊ M := by
  intro x hx
  obtain ⟨hl,hu⟩ := (mem_macroscopicStarts _ _ _).mp hx
  exact Finset.mem_Icc.mpr ⟨hl,hu.le⟩

theorem removed_global_subset_realPrefix (M : ℕ) (delta : ℝ) :
    Finset.Ico 2 M\macroscopicStarts M delta⊆realPrefix M delta := by
  intro x hx
  obtain ⟨hglobal,hnot⟩ := Finset.mem_sdiff.mp hx
  obtain ⟨hx,hm⟩ := Finset.mem_Ico.mp hglobal
  apply mem_realPrefix.mpr
  refine ⟨hx,?_⟩
  by_contra hp
  exact hnot ((mem_macroscopicStarts_iff_real M delta x).mpr ⟨by linarith,hm⟩)

theorem abs_macroRate_sub_fullRate {M L : ℕ} {delta : ℝ}
    (hM : 1≤M) (hd : 0≤delta) (hdOne : delta≤1) :
    |(maskRate L (macroscopicStarts M delta) : ℝ)-(fullRate M L : ℝ)| ≤
      2*(M : ℝ)^delta/(2 : ℝ)^L := by
  have hMr : (1 : ℝ)≤M := by exact_mod_cast hM
  have hp : (M : ℝ)^delta≤M := by simpa using Real.rpow_le_rpow_of_exponent_le hMr hdOne
  have hceil : ⌈(M : ℝ)^delta⌉₊≤M := Nat.ceil_le.mpr hp
  have hpow : (1 : ℝ)≤(M : ℝ)^delta := Real.one_le_rpow hMr hd
  have hc := Nat.ceil_lt_add_one (Real.rpow_nonneg (by positivity : (0 : ℝ)≤M) delta)
  change |((macroscopicStarts M delta).card : ℝ)/2^L-(M : ℝ)/2^L|≤_
  rw [macroscopicStarts,Nat.card_Ico,Nat.cast_sub hceil]
  have he : ((M : ℝ)-(⌈(M : ℝ)^delta⌉₊ : ℝ))/2^L-(M : ℝ)/2^L =
      -((⌈(M : ℝ)^delta⌉₊ : ℝ)/(2 : ℝ)^L) := by ring
  rw [he,abs_neg,abs_of_nonneg (by positivity)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  linarith

theorem macro_full_poisson_tv_le {M L : ℕ} {delta : ℝ}
    (hM : 1≤M) (hd : 0≤delta) (hdOne : delta≤1) :
    natTotalVariation (poissonMass (maskRate L (macroscopicStarts M delta))) (poissonMass (fullRate M L)) ≤
      2*(M : ℝ)^delta/(2 : ℝ)^L := by
  rw [poissonMass_eq_poissonPMFReal,poissonMass_eq_poissonPMFReal]
  exact (natTotalVariation_poisson_le_abs_rate_sub _ _).trans (abs_macroRate_sub_fullRate hM hd hdOne)

/-- Restoring the square-root prefix is smaller than the displayed relation remainder. -/
theorem squareRoot_restoration_le {M L : ℕ} (hM : 1≤M) {epsilon : ℝ} (heps : 0≤epsilon) :
    (M : ℝ)^(1/2 : ℝ)/(2 : ℝ)^L ≤
      (fullRate M L : ℝ)*(M : ℝ)^(-(1/3 : ℝ)+epsilon) := by
  rw [prefix_bulk_term_eq M L (1/2) (by omega)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hM) (by linarith)

end
end PaperC.V282.PrefixScalarGeometry
