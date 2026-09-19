import PaperCPrel8.TypicalDictionaryFinite
import PaperCV282.DyadicFullValueProfile
import PaperCV282.SaddleArithmeticBounds
import PaperCV282.HardPoissonRates
import PaperCV282.DictionaryFieldInfinite

/-! # Uniform arithmetic normalization with no upper restriction on dictionary growth -/
namespace PaperC.Prel8.TypicalDictionaryRates
open Filter Topology
open PaperC.SectionTwelveMoments PaperC.V282.ProfileMonomials
open PaperC.V282.DyadicFullValueProfile PaperC.V282.LogarithmicWordPowers
open PaperC.V282.RelationProfileRestriction PaperC.V282.TwoWindowParity
open PaperC.V282.MaskedArithmeticGeometry PaperC.V282.MaskedPairGeometry
open PaperC.V282.TouchingPairGeometry PaperC.V282.FullBandArithmetic
open PaperC.V282.SaddleParameters PaperC.V282.SaddleScales PaperC.V282.SaddleArithmeticBounds
open PaperC.V282.HardPoissonRates PaperC.V282.SaddleCutoffAdmissibility
open PaperC.V282.PrimeEulerPNT PaperC.V282.ProcessAGGInput PaperC.V282.RandomDictionary
open PaperC.Prel8.TypicalDictionaryFinite PaperC.Prel8.TypicalDictionaryTransfer
noncomputable section

/-- Exact normalization retains the useful factor 1/m in the first profile term. -/
theorem selected_profile_identity {N Q m : ℝ} (hN : 0 < N) (hQ : 0 < Q) (hm : 0 < m) :
    (m/Q)*(1/Q)*coarseProfile N Q =
      N^(-(1/(3:ℝ)))*((N*(m/Q))^2/m+N*(m/Q)) := by
  have hfirst : N^(5/(3:ℝ))=N^(-(1/(3:ℝ)))*N^2 := by
    rw [← Real.rpow_natCast,← Real.rpow_add hN]; congr 1; norm_num
  have hsecond : N^(2/(3:ℝ))=N^(-(1/(3:ℝ)))*N := by
    conv_rhs => rhs; rw [← Real.rpow_one N]
    rw [← Real.rpow_add hN]; congr 1; norm_num
  unfold coarseProfile
  rw [hfirst,hsecond]
  field_simp

/-- The actual uncapped full-value relation cost is uniform in every sampled size m. -/
theorem selected_profile_le_eventually (betaMin betaMax epsilon : ℝ)
    (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax) (hepsilon : 0 < epsilon) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      betaMin*Real.log N ≤ (L+1:ℝ) → (L+1:ℝ) ≤ betaMax*Real.log N →
      ∀ mask : Finset ℕ, mask ⊆ dyadicBlock N → ∀ m : ℕ, 1 ≤ m →
      ((m:ℝ)/(2:ℝ)^(L+1))*((1:ℝ)/(2:ℝ)^(L+1))*
        (valueWeightMass (dyadicCutoff N L) L (separatedPairs mask L):ℝ) ≤
      (N:ℝ)^(-(1/(3:ℝ))+epsilon)*
        (((N:ℝ)*((m:ℝ)/(2:ℝ)^(L+1)))^2/m+(N:ℝ)*((m:ℝ)/(2:ℝ)^(L+1))) := by
  obtain ⟨Nz,hz⟩ := valueWeightMass_mask_le_coarse_eventually betaMin betaMax epsilon hbetaMin hbeta hepsilon
  refine ⟨max Nz 1,?_⟩
  intro N hN L hlo hhi mask hmask m hm
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hmR : (0:ℝ)<m := by exact_mod_cast (show 0<m by omega)
  have hs : separatedPairs mask L ⊆ separatedOffDiagPairs N L := by
    rw [← separatedPairs_block_eq]
    intro xy hxy
    obtain ⟨hx,hy,hd⟩ := (mem_separatedPairs _ _ _ _).mp hxy
    exact (mem_separatedPairs _ _ _ _).mpr ⟨hmask hx,hmask hy,hd⟩
  have h := hz N (by omega) L hlo hhi _ hs
  calc
    _ ≤ ((m:ℝ)/(2:ℝ)^(L+1))*((1:ℝ)/(2:ℝ)^(L+1))*
        ((N:ℝ)^epsilon*coarseProfile N ((2:ℝ)^(L+1))) := by gcongr
    _ = (N:ℝ)^epsilon*(((m:ℝ)/(2:ℝ)^(L+1))*((1:ℝ)/(2:ℝ)^(L+1))*
        coarseProfile N ((2:ℝ)^(L+1))) := by ring
    _ = _ := by
      rw [selected_profile_identity hn (by positivity) hmR,← mul_assoc,← Real.rpow_add hn]
      congr 2
      ring

/-- All three arithmetic costs at the actual hard cutoff, before imposing an intensity cap. -/
theorem typical_rate_eventually (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax epsilon eta : ℝ) (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax)
    (hepsilon : 0 < epsilon) (heta : 0 < eta) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L m : ℕ,
      betaMin*Real.log N ≤ (L+1:ℝ) → (L+1:ℝ) ≤ betaMax*Real.log N →
      1 ≤ m → m ≤ 2^(L+1) → ∀ mask : Finset ℕ, mask ⊆ dyadicBlock N →
      dictionaryAverage (L+1) m (maskedDistance N L (hardCutoff N) mask) ≤
      (2*((N:ℝ)*((m:ℝ)/(2:ℝ)^(L+1)))+6*((N:ℝ)*((m:ℝ)/(2:ℝ)^(L+1)))^2)*
        Real.exp (-saddleCutoff 1 (Real.log N)+eta*saddleNu 1 (Real.log N))+
      8*((m:ℝ)/(2:ℝ)^(L+1))^2*(N:ℝ)*(L+1:ℝ)+
      2*(N:ℝ)^(-(1/(3:ℝ))+epsilon)*
        (((N:ℝ)*((m:ℝ)/(2:ℝ)^(L+1)))^2/m+(N:ℝ)*((m:ℝ)/(2:ℝ)^(L+1))) := by
  have hb : 0 < betaMax := hbetaMin.trans hbeta
  obtain ⟨Np,hp⟩ := selected_profile_le_eventually betaMin betaMax epsilon hbetaMin hbeta hepsilon
  obtain ⟨Nd,hd⟩ := normalized_fullBadMask_saddle_cost_le_eventually hPNT 1 betaMax eta (by norm_num) hb heta
  obtain ⟨Ne,he⟩ := normalized_degree_and_edges_saddle_le_eventually 1 betaMax eta (by norm_num) hb heta
  obtain ⟨Na,ha⟩ := saddleCutoff_nat_admissible_eventually 1 (2*betaMax) (by norm_num) (by positivity)
  refine ⟨max Np (max Nd (max Ne (max Na 2))),?_⟩
  intro N hN L m hlo hhi hm hmb mask hmask
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hlog : 0 ≤ Real.log (N:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1≤N by omega))
  have hwide : ((L+1)+1:ℝ) ≤ (2*betaMax)*Real.log N := by nlinarith [hhi]
  have hY := (ha N (by omega) (L+1) (by simpa only [Nat.cast_add,Nat.cast_one] using hwide)).2.2.1
  have h := finite_typical_bound hAGG mask hmask (by omega) hY hm hmb
  have hd' := hd N (by omega) L hhi mask
  simp only [div_one] at hd'
  have he' := (he N (by omega) L hhi mask hmask).2
  have hp' := hp N (by omega) L hlo hhi mask hmask m hm
  have hd'' := (div_le_iff₀ hn).mp hd'
  have he'' := (div_le_iff₀ (sq_pos_of_pos hn)).mp he'
  have hdm := mul_le_mul_of_nonneg_left hd'' (show 0 ≤ (m:ℝ)/(2:ℝ)^(L+1) by positivity)
  have hem := mul_le_mul_of_nonneg_left he'' (sq_nonneg ((m:ℝ)/(2:ℝ)^(L+1)))
  unfold hardCutoff
  nlinarith

end
end PaperC.Prel8.TypicalDictionaryRates
