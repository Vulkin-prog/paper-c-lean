import PaperCV282.AffineCrossoverBudget
import PaperCV282.MacroTransportInformation
import PaperCV282.MesoscopicPrefixMass

/-! # Prime and mesoscopic margins dominate hard conditioning uniformly in the length -/
namespace PaperC.V282.AffineCrossoverErrorsScales

open Filter Topology SaddleParameters SaddleScales AffineCrossoverBudget
open MacroTransportInformation MesoscopicPrefixMass PrimeEulerPNT

noncomputable section

/-- Any fixed positive prime-scale exponent dominates an ambient deep exponential. -/
theorem prime_margin_ambient_eventually
    (hPNT : PrimeNumberTheoremRemainder) (betaMin betaMax t : ℝ)
    (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax) (ht : 0 < t) :
    ∃ Mzero : ℕ, ∀ M≥Mzero, ∀ L : ℕ,
      betaMin*Real.log M≤(L+1 : ℝ) → (L+1 : ℝ)≤betaMax*Real.log M →
      (2 : ℝ)^(-t*Nat.primeCounting L) ≤
        Real.exp (-(t*betaMin*Real.log 2/8)*(Real.log M/Real.log (Real.log M))) := by
  obtain ⟨Mzero,hzero⟩ := border_mass_ambient_scale_eventually betaMin betaMax hbetaMin hbeta hPNT
  refine ⟨Mzero,?_⟩
  intro M hM L hlo hhi
  have hlog := Real.log_le_log (by positivity : 0<((2 : ℝ)⁻¹)^Nat.primeCounting L)
    (hzero M hM L (by simpa using hlo) (by simpa using hhi))
  rw [Real.log_pow,Real.log_inv,Real.log_exp] at hlog
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ)<2)]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left hlog ht.le
  nlinarith only [hh]

/-- Multiplying a prime-margin error by exp(I) leaves half of its ambient exponent. -/
theorem information_weighted_prime_margin_eventually
    (hPNT : PrimeNumberTheoremRemainder) (betaMin betaMax t : ℝ)
    (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax) (ht : 0 < t) :
    ∃ Mzero : ℕ, ∀ M≥Mzero, ∀ L : ℕ,
      betaMin*Real.log M≤(L+1 : ℝ) → (L+1 : ℝ)≤betaMax*Real.log M →
      ∀ I : ℝ, I≤saddleCutoff 1 (Real.log M) →
      Real.exp I * (2 : ℝ)^(-t*Nat.primeCounting L) ≤
        Real.exp (-(t*betaMin*Real.log 2/16)*(Real.log M/Real.log (Real.log M))) := by
  obtain ⟨Np,hp⟩ := prime_margin_ambient_eventually hPNT betaMin betaMax t hbetaMin hbeta ht
  have hlogTwo : 0<Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  obtain ⟨Ni,hi⟩ := information_weighted_deep_eventually 1 1 (t*betaMin*Real.log 2/8)
    (by norm_num) (by positivity)
  refine ⟨max Np Ni,?_⟩
  intro M hM L hlo hhi I hI
  apply (mul_le_mul_of_nonneg_left (hp M (by omega) L hlo hhi) (Real.exp_nonneg I)).trans
  simpa only [one_mul,show t*betaMin*Real.log 2/8/2=t*betaMin*Real.log 2/16 by ring] using
    hi M (by omega) I (by simpa only [one_mul] using hI)

/-- A full unit of the L/log L exponent absorbs exp(I), uniformly in the logarithmic band. -/
theorem information_le_length_scale_eventually (betaMin betaMax : ℝ)
    (hbetaMin : 0<betaMin) (hbeta : betaMin<betaMax) :
    ∃ Mzero : ℕ, ∀ M≥Mzero, ∀ L : ℕ,
      betaMin*Real.log M≤(L+1 : ℝ) → (L+1 : ℝ)≤betaMax*Real.log M →
      ∀ I : ℝ, I≤saddleCutoff 1 (Real.log M) → I≤(L : ℝ)/Real.log L := by
  obtain ⟨Ns,hs⟩ := IntermediateDefectScales.logarithmic_scales_eventually
    betaMin betaMax hbetaMin hbeta
  obtain ⟨Nv,hv⟩ := saddle_le_deep_scale_eventually 1 1 (betaMin/4) (by norm_num) (by positivity)
  refine ⟨max Ns Nv,?_⟩
  intro M hM L hlo hhi I hI
  have hv' : saddleCutoff 1 (Real.log M)≤(betaMin/4)*(Real.log M/Real.log (Real.log M)) := by
    simpa only [one_mul] using hv M (by omega)
  exact hI.trans (hv'.trans (hs M (by omega) L (by simpa using hlo) (by simpa using hhi)).1)

/-- The positive ambient deep coefficient has a vanishing exponential. -/
theorem prime_margin_error_tendsto_zero (betaMin t : ℝ) (hbetaMin : 0<betaMin) (ht : 0<t) :
    Tendsto (fun M : ℕ => Real.exp (-(t*betaMin*Real.log 2/16)*
      (Real.log M/Real.log (Real.log M)))) atTop (𝓝 0) := by
  have hlogTwo : 0<Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  exact PrefixScalarConvergence.deep_remainder_tendsto_zero _ (by positivity)

end
end PaperC.V282.AffineCrossoverErrorsScales
