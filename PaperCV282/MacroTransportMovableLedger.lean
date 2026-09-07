import PaperCV282.MacroscopicMarkedLedger
import PaperCV282.ExactMarkedMovableRates

/-! # Macroscopic marked arithmetic at the true movable saddle, with separate intensities -/
namespace PaperC.V282.MacroTransportMovableLedger

open MacroscopicMaskGeometry HostRankMass BulkMarkedFieldBounds ExactMarkedArithmeticRates
open MaskedArithmeticGeometry MaskedPairGeometry SectionTwelveMoments TwoWindowParity
open HardPoissonRates SaddleParameters SaddleScales PrimeEulerPNT AllStartSoftPoisson
open MacroscopicMarkedLedger ExactMarkedMovableRates

noncomputable section

theorem movable_cutoff_costs_le_eventually
    (hPNT : PrimeNumberTheoremRemainder) (betaMax eta : ℝ)
    (hbeta : 0 < betaMax) (heta : 0 < eta) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      (L + 1 : ℝ) ≤ betaMax * Real.log N →
      ∀ mask : Finset ℕ, mask ⊆ Finset.Icc 2 N → ∀ a : ℝ, 0 ≤ a →
      a * ((badMask L ⌊Real.exp (saddleCutoff 2 (Real.log N))⌋₊ mask).card : ℝ) ≤
        ((N : ℝ) * a) * Real.exp (-saddleCutoff 2 (Real.log N)/2 + eta * saddleNu 2 (Real.log N)) ∧
      a ^ 2 * ((maskedSupportEdges L ⌊Real.exp (saddleCutoff 2 (Real.log N))⌋₊ mask).card : ℝ) ≤
        ((N : ℝ) * a) ^ 2 * Real.exp (-saddleCutoff 2 (Real.log N) + eta * saddleNu 2 (Real.log N)) := by
  obtain ⟨Nd,hd⟩ := MacroscopicCutoffBounds.normalized_badMask_saddle_le_eventually hPNT 2 betaMax eta
    (by norm_num) hbeta heta
  obtain ⟨Ne,he⟩ := MacroscopicCutoffBounds.normalized_degree_and_edges_saddle_le_eventually 2 betaMax eta
    (by norm_num) hbeta heta
  refine ⟨max Nd (max Ne 1), ?_⟩
  intro N hN L hL mask hmask a ha
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hdn := hd N (by omega) L hL mask hmask
  have hd' := (div_le_iff₀ hn).mp hdn
  have he' := (div_le_iff₀ (sq_pos_of_pos hn)).mp (he N (by omega) L hL mask hmask).2
  change a * ((badMask L ⌊Real.exp (saddleCutoff 2 (Real.log N))⌋₊ mask).card : ℝ) ≤ _ ∧ _
  constructor
  · calc
      _ ≤ a * (Real.exp (-saddleCutoff 2 (Real.log N)/2 + eta * saddleNu 2 (Real.log N)) * N) :=
        mul_le_mul_of_nonneg_left hd' ha
      _ = _ := by ring
  · calc
      _ ≤ a ^ 2 * (Real.exp (-saddleCutoff 2 (Real.log N) + eta * saddleNu 2 (Real.log N)) * (N : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left he' (sq_nonneg a)
      _ = _ := by ring

theorem marked_ledger_movable_rate_eventually
    (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax delta epsilon eta : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hdelta : 0 < delta) (hepsilon : 0 < epsilon) (heta : 0 < eta) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L E : ℕ,
      betaMin*Real.log N ≤ (L+1 : ℝ) → (L+E+2 : ℝ) ≤ betaMax*Real.log N →
      ∀ C : ℕ, N + L ≤ C → ∀ mask : Finset ℕ, mask ⊆ Finset.Icc ⌈(N : ℝ) ^ delta⌉₊ N →
      exactMarkedLedger C mask L E ⌊Real.exp (saddleCutoff 2 (Real.log N))⌋₊ mask ≤
        movableMarkedRate N L epsilon eta := by
  have hbetaMax : 0 < betaMax := hbetaMin.trans hbeta
  obtain ⟨Nm,hm⟩ := defect_cost_le_eventually betaMin betaMax delta epsilon hbetaMin hbeta hdelta hepsilon
  obtain ⟨Nc,hc⟩ := movable_cutoff_costs_le_eventually hPNT betaMax eta hbetaMax heta
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
  unfold movableMarkedRate
  convert separated_ledger_numeric_bound (by positivity : (0 : ℝ)≤(fullRate N L : ℝ))
    (Real.exp_nonneg _) (Real.exp_nonneg _) (Real.rpow_nonneg (by positivity) _) hm' hbad ha' hedges ht' using 1
  ring



end
end PaperC.V282.MacroTransportMovableLedger
