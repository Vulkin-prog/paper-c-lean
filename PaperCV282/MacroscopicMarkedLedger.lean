import PaperCV282.MacroscopicArithmeticBounds
import PaperCV282.MacroscopicCutoffBounds
import PaperCV282.BulkMarkedFieldBounds
import PaperCV282.ExactMarkedArithmeticRates

/-! # Actual marked arithmetic at a common macroscopic hard cutoff -/
namespace PaperC.V282.MacroscopicMarkedLedger

open MacroscopicMaskGeometry HostRankMass BulkMarkedFieldBounds ExactMarkedArithmeticRates
open MaskedArithmeticGeometry MaskedPairGeometry SectionTwelveMoments TwoWindowParity
open HardPoissonRates SaddleParameters SaddleScales PrimeEulerPNT AllStartSoftPoisson

noncomputable section

/-- The complete-vertex deletion first moment keeps only one intensity factor. -/
theorem defect_cost_le_eventually
    (betaMin betaMax delta epsilon : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hdelta : 0 < delta) (hepsilon : 0 < epsilon) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      betaMin * Real.log N ≤ (L + 1 : ℝ) → (L + 1 : ℝ) ≤ betaMax * Real.log N →
      ∀ mask : Finset ℕ, mask ⊆ Finset.Icc ⌈(N : ℝ) ^ delta⌉₊ N → ∀ a : ℝ, 0 ≤ a →
        a * (fullDefectMass L mask : ℝ) ≤
          (N : ℝ) ^ (-(1 / (3 : ℝ)) + epsilon) * ((N : ℝ) * a) := by
  obtain ⟨Nzero,hzero⟩ := MacroscopicArithmeticBounds.fullDefectMass_div_block_le_eventually
    betaMin betaMax delta epsilon hbetaMin hbeta hdelta hepsilon
  refine ⟨max Nzero 1, ?_⟩
  intro N hN L hlo hhi mask hmask a ha
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hone : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hpow : (N : ℝ) ^ (-(1 / (2 : ℝ)) + epsilon) ≤
      (N : ℝ) ^ (-(1 / (3 : ℝ)) + epsilon) :=
    Real.rpow_le_rpow_of_exponent_le hone (by linarith)
  have hh := (hzero N (by omega) L hlo hhi mask hmask).trans hpow
  have hh' := (div_le_iff₀ hn).mp hh
  calc
    _ ≤ a * ((N : ℝ) ^ (-(1 / (3 : ℝ)) + epsilon) * N) :=
      mul_le_mul_of_nonneg_left hh' ha
    _ = _ := by ring


/-- The true hard-cutoff bad-site and graph costs keep lambda and lambda squared separately. -/
theorem cutoff_costs_le_eventually
    (hPNT : PrimeNumberTheoremRemainder) (betaMax eta : ℝ)
    (hbeta : 0 < betaMax) (heta : 0 < eta) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      (L + 1 : ℝ) ≤ betaMax * Real.log N →
      ∀ mask : Finset ℕ, mask ⊆ Finset.Icc 2 N → ∀ a : ℝ, 0 ≤ a →
      a * ((badMask L (hardCutoff N) mask).card : ℝ) ≤
        ((N : ℝ) * a) * Real.exp (-saddleCutoff 1 (Real.log N) + eta * saddleNu 1 (Real.log N)) ∧
      a ^ 2 * ((maskedSupportEdges L (hardCutoff N) mask).card : ℝ) ≤
        ((N : ℝ) * a) ^ 2 * Real.exp (-saddleCutoff 1 (Real.log N) + eta * saddleNu 1 (Real.log N)) := by
  obtain ⟨Nd,hd⟩ := MacroscopicCutoffBounds.normalized_badMask_saddle_le_eventually hPNT 1 betaMax eta
    (by norm_num) hbeta heta
  obtain ⟨Ne,he⟩ := MacroscopicCutoffBounds.normalized_degree_and_edges_saddle_le_eventually 1 betaMax eta
    (by norm_num) hbeta heta
  refine ⟨max Nd (max Ne 1), ?_⟩
  intro N hN L hL mask hmask a ha
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hdn := hd N (by omega) L hL mask hmask
  simp only [div_one] at hdn
  have hd' := (div_le_iff₀ hn).mp hdn
  have he' := (div_le_iff₀ (sq_pos_of_pos hn)).mp (he N (by omega) L hL mask hmask).2
  change a * ((badMask L ⌊Real.exp (saddleCutoff 1 (Real.log N))⌋₊ mask).card : ℝ) ≤ _ ∧ _
  constructor
  · calc
      _ ≤ a * (Real.exp (-saddleCutoff 1 (Real.log N) + eta * saddleNu 1 (Real.log N)) * N) :=
        mul_le_mul_of_nonneg_left hd' ha
      _ = _ := by ring
  · change a ^ 2 * ((maskedSupportEdges L ⌊Real.exp (saddleCutoff 1 (Real.log N))⌋₊ mask).card : ℝ) ≤ _
    calc
      _ ≤ a ^ 2 * (Real.exp (-saddleCutoff 1 (Real.log N) + eta * saddleNu 1 (Real.log N)) * (N : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left he' (sq_nonneg a)
      _ = _ := by ring

/-- The full marked ledger, with the literal base and maximal supports, throughout the whole band. -/
theorem marked_ledger_hard_rate_eventually
    (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax delta epsilon eta : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hdelta : 0 < delta) (hepsilon : 0 < epsilon) (heta : 0 < eta) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L E : ℕ,
      betaMin*Real.log N ≤ (L+1 : ℝ) → (L+E+2 : ℝ) ≤ betaMax*Real.log N →
      ∀ C : ℕ, N + L ≤ C → ∀ mask : Finset ℕ, mask ⊆ Finset.Icc ⌈(N : ℝ) ^ delta⌉₊ N →
      exactMarkedLedger C mask L E (hardCutoff N) mask ≤
        32*(fullRate N L : ℝ)*(1+(fullRate N L : ℝ))*
          (Real.exp (-saddleCutoff 1 (Real.log N)+eta*saddleNu 1 (Real.log N))+
            (N : ℝ)^(-(1/(3 : ℝ))+epsilon)) := by
  have hbetaMax : 0 < betaMax := hbetaMin.trans hbeta
  obtain ⟨Nm,hm⟩ := defect_cost_le_eventually betaMin betaMax delta epsilon hbetaMin hbeta hdelta hepsilon
  obtain ⟨Nc,hc⟩ := cutoff_costs_le_eventually hPNT betaMax eta hbetaMax heta
  obtain ⟨Na,ha⟩ := marked_diagonal_cost_le_eventually betaMax epsilon hbetaMax.le hepsilon
  obtain ⟨Nr,hr⟩ := MacroscopicArithmeticBounds.normalized_relation_mass_le_eventually betaMin betaMax delta epsilon hbetaMin hbeta hdelta hepsilon
  refine ⟨max 2 (max Nm (max Nc (max Na Nr))),?_⟩
  intro N hN L E hlo hhi C hC mask hmask
  have hbounded : mask ⊆ Finset.Icc 2 N := fun x hx => MacroscopicArithmeticBounds.closed_macroscopic_subset_Icc (M := N) (by omega) hdelta (hmask hx)
  have hlhi : (L+1 : ℝ)≤betaMax*Real.log N := by
    have hE : (0 : ℝ)≤E := by positivity
    linarith
  have hqhi : ((L+E+1 : ℕ)+1 : ℝ)≤betaMax*Real.log N := by
    push_cast
    linarith
  have hdef := hm N (by omega) L hlo hlhi mask hmask
    (1/(2 : ℝ)^L) (by positivity)
  obtain ⟨hbad,hedges⟩ := hc N (by omega) (L+E+1) hqhi mask hbounded
    (1/(2 : ℝ)^L) (by positivity)
  have hdiag := ha N (by omega) L (L+E+1) hqhi
  have hrelation := hr N (by omega) L hlo hlhi C hC mask hmask (separatedPairs mask L) (Finset.Subset.refl _)
  have hlam : (N : ℝ)*(1/(2 : ℝ)^L)=(fullRate N L : ℝ) := by simp only [fullRate_coe];ring
  rw [hlam] at hdef hbad hedges
  have hm' : (1/(2 : ℝ)^L)*(fullDefectMass L mask : ℝ) ≤
      (fullRate N L : ℝ)*(N : ℝ)^(-(1/(3 : ℝ))+epsilon) := by simpa only [mul_comm] using hdef
  have ha' : (1/(2 : ℝ)^L)^2*((mask.card : ℝ)*(L+E+2)) ≤
      (fullRate N L : ℝ)^2*(N : ℝ)^(-(1/(3 : ℝ))+epsilon) := by
    have hcard : (mask.card : ℝ) ≤ N := by exact_mod_cast card_mask_le hbounded
    calc
      _ ≤ (1/(2 : ℝ)^L)^2*((N : ℝ)*(L+E+2)) := by gcongr
      _ ≤ _ := by convert hdiag using 1 <;> push_cast <;> ring
  have ht' : (1/(2 : ℝ)^L)^2*(relationWeightMass C L (separatedPairs mask L) : ℝ) ≤
      (N : ℝ)^(-(1/(3 : ℝ))+epsilon)*((fullRate N L : ℝ)^2+2*(fullRate N L : ℝ)) := by
    convert hrelation using 1
    rw [Nat.mul_comm 2 L,pow_mul]
    ring
  unfold exactMarkedLedger
  convert ledger_numeric_bound (by positivity : (0 : ℝ)≤(fullRate N L : ℝ))
    (Real.exp_nonneg _) (Real.rpow_nonneg (by positivity) _) hm' hbad ha' hedges ht' using 1
  ring


/-- The actual averaged source and target tail cost, with every excess above E. -/
theorem complete_tail_cost_le_eventually
    (betaMin betaMax delta : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hdelta : 0 < delta) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L E : ℕ,
      betaMin * Real.log N ≤ (L + 1 : ℝ) →
      (L + E + 2 : ℝ) ≤ betaMax * Real.log N →
      ∀ mask : Finset ℕ, mask ⊆ Finset.Icc ⌈(N : ℝ) ^ delta⌉₊ N →
      ((fullDefectMass (L + E + 1) mask : ℝ) + 2 * mask.card) / (2 : ℝ) ^ (L + E + 1) ≤
        3 * (fullRate N L : ℝ) / (2 : ℝ) ^ (E + 1) := by
  obtain ⟨Nm, hm⟩ := MacroscopicArithmeticBounds.fullDefectMass_le_half_power_eventually
    betaMin betaMax delta (1 / 4) hbetaMin hbeta hdelta (by norm_num)
  refine ⟨max Nm 2, ?_⟩
  intro N hN L E hlo hhi mask hmask
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hlQ : betaMin * Real.log N ≤ ((L + E + 1 : ℕ) + 1 : ℝ) := by
    push_cast
    have he : (0 : ℝ) ≤ E := by positivity
    linarith
  have huQ : ((L + E + 1 : ℕ) + 1 : ℝ) ≤ betaMax * Real.log N := by push_cast; linarith
  have hmass := hm N (by omega) (L + E + 1) hlQ huQ mask hmask
  have hmassN : (fullDefectMass (L + E + 1) mask : ℝ) ≤ N := by
    apply hmass.trans
    calc
      _ ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn (by norm_num)
      _ = _ := Real.rpow_one _
  have hbounded : mask ⊆ Finset.Icc 2 N := fun x hx =>
    MacroscopicArithmeticBounds.closed_macroscopic_subset_Icc (by omega) hdelta (hmask hx)
  have hcard : (mask.card : ℝ) ≤ N := by exact_mod_cast card_mask_le hbounded
  calc
    _ ≤ (3 * N : ℝ) / (2 : ℝ) ^ (L + E + 1) :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    _ = _ := by
      rw [fullRate_coe, show L + E + 1 = L + (E + 1) by omega, pow_add]
      ring

end
end PaperC.V282.MacroscopicMarkedLedger
