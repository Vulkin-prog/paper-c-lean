import PaperCV282.ExactMarkedArithmeticRates
import PaperCV282.ExactMarkedFieldBounds
import PaperCV282.BadStartRankinFreeCutoff
import PaperCV282.CutoffGraphFreeCutoff
import PaperCV282.FreeCutoffAdmissibility
import PaperCV282.SaddleArithmeticBounds

/-!
# Labelled exact-mark costs at a genuine movable cutoff

Deletion is linear in the base intensity; support edges are quadratic.
Both support lengths are retained. These are process bounds, without the
scalar soft Stein factor or any directional multivariate Stein premise.
-/
namespace PaperC.V282.ExactMarkedMovableRates

open ExactMarkedLedger ExactMarkedArithmeticRates DictionaryArithmeticRates FullBandArithmetic
open MaskedArithmeticGeometry MaskedPairGeometry SectionTwelveMoments TwoWindowParity
open SaddleParameters SaddleScales PrimeEulerPNT AllStartSoftPoisson
open BadStartRankinFreeCutoff CutoffGraphFreeCutoff FreeCutoffAdmissibility
open SaddleArithmeticBounds SaddleCutoffAdmissibility ExactMarkedFieldBounds ProcessAGGInput
open InfiniteConditionalWords InfiniteCylinderTransfer Filter Topology

noncomputable section

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

/-- Separate the genuinely different linear-deletion and quadratic-edge exponentials. -/
def freeMarkedRate (N L : ℕ) (w epsilon eta : ℝ) : ℝ :=
  32*((fullRate N L : ℝ)*Real.exp (-saddleCost (Real.log N/w)+eta*(Real.log N/w))+
    (fullRate N L : ℝ)^2*Real.exp (-w+eta*(Real.log N/w))+
    (fullRate N L : ℝ)*(1+(fullRate N L : ℝ))*(N : ℝ)^(-(1/(3 : ℝ))+epsilon))

def movableMarkedRate (N L : ℕ) (epsilon eta : ℝ) : ℝ :=
  32*((fullRate N L : ℝ)*Real.exp (-saddleCutoff 2 (Real.log N)/2+eta*saddleNu 2 (Real.log N))+
    (fullRate N L : ℝ)^2*Real.exp (-saddleCutoff 2 (Real.log N)+eta*saddleNu 2 (Real.log N))+
    (fullRate N L : ℝ)*(1+(fullRate N L : ℝ))*(N : ℝ)^(-(1/(3 : ℝ))+epsilon))

theorem separated_ledger_numeric_bound {p lambda Hbad Hedge R M D A G T : ℝ}
    (hlambda : 0≤lambda) (hbad : 0≤Hbad) (hedge : 0≤Hedge) (hR : 0≤R)
    (hm : p*M≤lambda*R) (hd : p*D≤lambda*Hbad)
    (ha : p^2*A≤lambda^2*R) (hg : p^2*G≤lambda^2*Hedge)
    (ht : p^2*T≤R*(lambda^2+2*lambda)) :
    p*(M+2*D)+p^2*(20*A+4*G+2*T) ≤
      32*(lambda*Hbad+lambda^2*Hedge+lambda*(1+lambda)*R) := by
  have hsum := add_le_add (add_le_add hm (mul_le_mul_of_nonneg_left hd (by norm_num : (0 : ℝ)≤2)))
    (add_le_add (add_le_add (mul_le_mul_of_nonneg_left ha (by norm_num : (0 : ℝ)≤20))
      (mul_le_mul_of_nonneg_left hg (by norm_num : (0 : ℝ)≤4)))
      (mul_le_mul_of_nonneg_left ht (by norm_num : (0 : ℝ)≤2)))
  have hpad : 0≤30*lambda*Hbad+28*lambda^2*Hedge+(27*lambda+10*lambda^2)*R := by positivity
  nlinarith only [hsum,hpad]

/-- Arithmetic composition for any cutoff, using the actual normalized deletion and edge counts. -/
theorem marked_ledger_of_cutoff_bounds_eventually
    (betaMin betaMax epsilon : ℝ) (hbetaMin : 0<betaMin)
    (hbeta : betaMin<betaMax) (hepsilon : 0<epsilon) :
    ∃ Nzero : ℕ, ∀ N≥Nzero, ∀ L E Y : ℕ,
      betaMin*Real.log N≤(L+1 : ℝ) → (L+E+2 : ℝ)≤betaMax*Real.log N →
      ∀ Hbad Hedge : ℝ, 0≤Hbad → 0≤Hedge →
      ((fullBadMask N (L+E+1) Y (dyadicBlock N)).card : ℝ)/N≤Hbad →
      ((maskedSupportEdges (L+E+1) Y (dyadicBlock N)).card : ℝ)/(N : ℝ)^2≤Hedge →
      exactMarkedLedger N L E Y (dyadicBlock N) ≤
        32*((fullRate N L : ℝ)*Hbad+(fullRate N L : ℝ)^2*Hedge+
          (fullRate N L : ℝ)*(1+(fullRate N L : ℝ))*(N : ℝ)^(-(1/(3 : ℝ))+epsilon)) := by
  have hbetaMax : 0<betaMax := hbetaMin.trans hbeta
  obtain ⟨Nm,hm⟩ := dictionary_defect_cost_le_eventually betaMin betaMax epsilon hbetaMin hbeta hepsilon
  obtain ⟨Na,ha⟩ := marked_diagonal_cost_le_eventually betaMax epsilon hbetaMax.le hepsilon
  obtain ⟨Nr,hr⟩ := normalized_relation_mass_le_eventually betaMin betaMax epsilon hbetaMin hbeta hepsilon
  refine ⟨max 1 (max Nm (max Na Nr)),?_⟩
  intro N hN L E Y hlo hhi Hbad Hedge hbad hedge hD hG
  have hn : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hlhi : (L+1 : ℝ)≤betaMax*Real.log N := by
    have hE : (0 : ℝ)≤E := by positivity
    linarith
  have hqhi : ((L+E+1 : ℕ)+1 : ℝ)≤betaMax*Real.log N := by push_cast;linarith
  have hdef := hm N (by omega) L hlo hlhi (dyadicBlock N) (Finset.Subset.refl _)
    (1/(2 : ℝ)^L) (by positivity)
  have hdiag := ha N (by omega) L (L+E+1) hqhi
  have hrelation := hr N (by omega) L hlo hlhi
  have hlam : (N : ℝ)*(1/(2 : ℝ)^L)=(fullRate N L : ℝ) := by simp only [fullRate_coe];ring
  rw [hlam] at hdef
  have hm' : (1/(2 : ℝ)^L)*(fullDefectMass L (dyadicBlock N) : ℝ)≤
      (fullRate N L : ℝ)*(N : ℝ)^(-(1/(3 : ℝ))+epsilon) := by simpa only [mul_comm] using hdef
  have hd' : (1/(2 : ℝ)^L)*((fullBadMask N (L+E+1) Y (dyadicBlock N)).card : ℝ)≤
      (fullRate N L : ℝ)*Hbad := by
    convert mul_le_mul_of_nonneg_left hD (show 0≤(fullRate N L : ℝ) by positivity) using 1
    · rfl
    · rw [fullRate_coe]
      field_simp [ne_of_gt hn]
  have hg' : (1/(2 : ℝ)^L)^2*((maskedSupportEdges (L+E+1) Y (dyadicBlock N)).card : ℝ)≤
      (fullRate N L : ℝ)^2*Hedge := by
    convert mul_le_mul_of_nonneg_left hG (sq_nonneg (fullRate N L : ℝ)) using 1
    · rfl
    · rw [fullRate_coe]
      field_simp [ne_of_gt hn]
  have ha' : (1/(2 : ℝ)^L)^2*((N : ℝ)*(L+E+2))≤
      (fullRate N L : ℝ)^2*(N : ℝ)^(-(1/(3 : ℝ))+epsilon) := by
    convert hdiag using 1 <;> push_cast <;> ring
  have ht' : (1/(2 : ℝ)^L)^2*(jointDefectMass N L (separatedPairs (dyadicBlock N) L) : ℝ)≤
      (N : ℝ)^(-(1/(3 : ℝ))+epsilon)*((fullRate N L : ℝ)^2+2*(fullRate N L : ℝ)) := by
    convert hrelation using 1
    rw [Nat.mul_comm 2 L,pow_mul]
    ring
  unfold exactMarkedLedger
  convert separated_ledger_numeric_bound (by positivity : (0 : ℝ)≤(fullRate N L : ℝ))
    hbad hedge (Real.rpow_nonneg hn.le _) hm' hd' ha' hg' ht' using 1
  ring

/-- A threshold before the freely moving real cutoff and both natural support lengths. -/
theorem exact_marked_free_rate_eventually (hPNT : PrimeNumberTheoremRemainder)
    (c C betaMin betaMax epsilon eta : ℝ) (hc : 0<c) (hC : 0<C)
    (hbetaMin : 0<betaMin) (hbeta : betaMin<betaMax) (hepsilon : 0<epsilon) (heta : 0<eta) :
    ∃ Nzero : ℕ, ∀ N≥Nzero, ∀ w : ℝ,
      c*Real.sqrt (Real.log N*Real.log (Real.log N))≤w →
      w≤C*Real.sqrt (Real.log N*Real.log (Real.log N)) →
      ∀ L E : ℕ, betaMin*Real.log N≤(L+1 : ℝ) → (L+E+2 : ℝ)≤betaMax*Real.log N →
      exactMarkedLedger N L E ⌊Real.exp w⌋₊ (dyadicBlock N)≤freeMarkedRate N L w epsilon eta := by
  have hbetaMax := hbetaMin.trans hbeta
  obtain ⟨Nb,hb⟩ := marked_ledger_of_cutoff_bounds_eventually betaMin betaMax epsilon hbetaMin hbeta hepsilon
  obtain ⟨Nd,hd⟩ := normalized_fullBadMask_free_cutoff_le_eventually hPNT c C betaMax eta hc hC hbetaMax heta
  obtain ⟨Ng,hg⟩ := normalized_degree_and_edges_free_cutoff_le_eventually c C betaMax eta hc hC hbetaMax heta
  refine ⟨max Nb (max Nd Ng),?_⟩
  intro N hN w hwlo hwhi L E hlo hhi
  have hqhi : ((L+E+1 : ℕ)+1 : ℝ)≤betaMax*Real.log N := by push_cast;linarith
  exact hb N (by omega) L E _ hlo hhi _ _ (Real.exp_nonneg _) (Real.exp_nonneg _)
    (hd N (by omega) w hwlo hwhi (L+E+1) hqhi (dyadicBlock N))
    (hg N (by omega) w hwlo hwhi (L+E+1) hqhi _ (Finset.Subset.refl _)).2

/-- Specialization to the actual movable saddle V=2D(H/V), keeping the linear and quadratic terms. -/
theorem exact_marked_movable_rate_eventually (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax epsilon eta : ℝ) (hbetaMin : 0<betaMin)
    (hbeta : betaMin<betaMax) (hepsilon : 0<epsilon) (heta : 0<eta) :
    ∃ Nzero : ℕ, ∀ N≥Nzero, ∀ L E : ℕ,
      betaMin*Real.log N≤(L+1 : ℝ) → (L+E+2 : ℝ)≤betaMax*Real.log N →
      exactMarkedLedger N L E ⌊Real.exp (saddleCutoff 2 (Real.log N))⌋₊ (dyadicBlock N)≤
        movableMarkedRate N L epsilon eta := by
  have hbetaMax := hbetaMin.trans hbeta
  obtain ⟨Nb,hb⟩ := marked_ledger_of_cutoff_bounds_eventually betaMin betaMax epsilon hbetaMin hbeta hepsilon
  obtain ⟨Nd,hd⟩ := normalized_fullBadMask_saddle_cost_le_eventually hPNT 2 betaMax eta (by norm_num) hbetaMax heta
  obtain ⟨Ng,hg⟩ := normalized_degree_and_edges_saddle_le_eventually 2 betaMax eta (by norm_num) hbetaMax heta
  refine ⟨max Nb (max Nd Ng),?_⟩
  intro N hN L E hlo hhi
  have hqhi : ((L+E+1 : ℕ)+1 : ℝ)≤betaMax*Real.log N := by push_cast;linarith
  exact hb N (by omega) L E _ hlo hhi _ _ (Real.exp_nonneg _) (Real.exp_nonneg _)
    (hd N (by omega) (L+E+1) hqhi (dyadicBlock N))
    (hg N (by omega) (L+E+1) hqhi _ (Finset.Subset.refl _)).2


/-- The actual finite signed field, at every free cutoff, with full F_Y explicitly identified. -/
theorem signed_free_field_rate_eventually
    (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (c C betaMin betaMax epsilon eta : ℝ) (hc : 0<c) (hC : 0<C)
    (hbetaMin : 0<betaMin) (hbeta : betaMin<betaMax) (hepsilon : 0<epsilon) (heta : 0<eta) :
    ∃ Nzero : ℕ, ∀ N≥Nzero, ∀ w : ℝ,
      c*Real.sqrt (Real.log N*Real.log (Real.log N))≤w →
      w≤C*Real.sqrt (Real.log N*Real.log (Real.log N)) →
      ∀ L E : ℕ, betaMin*Real.log N≤(L+1 : ℝ) → (L+E+2 : ℝ)≤betaMax*Real.log N →
      smallPrimeSigmaAlgebra (max ⌊Real.exp w⌋₊ (dyadicCutoff N (L+E+1))) ⌊Real.exp w⌋₊ =
        MeasurableSpace.comap (restrictToFinite ⌊Real.exp w⌋₊) inferInstance ∧
      exactSignedConditionalDistance (max ⌊Real.exp w⌋₊ (dyadicCutoff N (L+E+1))) N L E ⌊Real.exp w⌋₊
        (dyadicBlock N)≤freeMarkedRate N L w epsilon eta ∧
      exactSignedDistance N L E (dyadicBlock N)≤freeMarkedRate N L w epsilon eta := by
  have hbetaMax := hbetaMin.trans hbeta
  obtain ⟨Nr,hr⟩ := exact_marked_free_rate_eventually hPNT c C betaMin betaMax epsilon eta
    hc hC hbetaMin hbeta hepsilon heta
  obtain ⟨Na,ha⟩ := free_cutoff_admissible_eventually c C (2*betaMax) hc hC (by positivity)
  obtain ⟨Nl,hl⟩ := TouchingPairMass.length_pos_eventually betaMin hbetaMin
  refine ⟨max 2 (max Nr (max Na Nl)),?_⟩
  intro N hN w hwlo hwhi L E hlo hhi
  have hL : 1≤L := hl N (by omega) L hlo
  have hhi' : ((L+E+2 : ℕ)+1 : ℝ)≤(2*betaMax)*Real.log N := by
    push_cast
    have he : (0 : ℝ)≤E := by positivity
    have hll : (0 : ℝ)≤L := by positivity
    nlinarith
  have hY : 2*(L+E+2)≤⌊Real.exp w⌋₊ :=
    (ha N (by omega) w hwlo hwhi (L+E+2) hhi').2.1
  obtain ⟨hFY,hcond,huncond⟩ := signed_field_fullFY_bound hAGG (by omega : 2≤N) hL hY
    (dyadicBlock N) (Finset.Subset.refl _)
  have hrate := hr N (by omega) w hwlo hwhi L E hlo hhi
  exact ⟨hFY,hcond.trans hrate,huncond.trans hrate⟩

/-- The finite labelled precursor of (5.20), at the actual movable saddle a=2.
This is a process estimate with linear and quadratic intensities, not a scalar soft bound. -/
theorem signed_movable_field_rate_eventually
    (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax epsilon eta : ℝ) (hbetaMin : 0<betaMin)
    (hbeta : betaMin<betaMax) (hepsilon : 0<epsilon) (heta : 0<eta) :
    ∃ Nzero : ℕ, ∀ N≥Nzero, ∀ L E : ℕ,
      betaMin*Real.log N≤(L+1 : ℝ) → (L+E+2 : ℝ)≤betaMax*Real.log N →
      smallPrimeSigmaAlgebra
        (max ⌊Real.exp (saddleCutoff 2 (Real.log N))⌋₊ (dyadicCutoff N (L+E+1)))
        ⌊Real.exp (saddleCutoff 2 (Real.log N))⌋₊ =
        MeasurableSpace.comap (restrictToFinite ⌊Real.exp (saddleCutoff 2 (Real.log N))⌋₊) inferInstance ∧
      exactSignedConditionalDistance
        (max ⌊Real.exp (saddleCutoff 2 (Real.log N))⌋₊ (dyadicCutoff N (L+E+1))) N L E
        ⌊Real.exp (saddleCutoff 2 (Real.log N))⌋₊ (dyadicBlock N)≤movableMarkedRate N L epsilon eta ∧
      exactSignedDistance N L E (dyadicBlock N)≤movableMarkedRate N L epsilon eta := by
  have hbetaMax := hbetaMin.trans hbeta
  obtain ⟨Nr,hr⟩ := exact_marked_movable_rate_eventually hPNT betaMin betaMax epsilon eta
    hbetaMin hbeta hepsilon heta
  obtain ⟨Na,ha⟩ := saddleCutoff_nat_admissible_eventually 2 (2*betaMax) (by norm_num) (by positivity)
  obtain ⟨Nl,hl⟩ := TouchingPairMass.length_pos_eventually betaMin hbetaMin
  refine ⟨max 2 (max Nr (max Na Nl)),?_⟩
  intro N hN L E hlo hhi
  have hL : 1≤L := hl N (by omega) L hlo
  have hhi' : ((L+E+2 : ℕ)+1 : ℝ)≤(2*betaMax)*Real.log N := by
    push_cast
    have he : (0 : ℝ)≤E := by positivity
    have hll : (0 : ℝ)≤L := by positivity
    nlinarith
  have hY : 2*(L+E+2)≤⌊Real.exp (saddleCutoff 2 (Real.log N))⌋₊ :=
    (ha N (by omega) (L+E+2) hhi').2.2.1
  obtain ⟨hFY,hcond,huncond⟩ := signed_field_fullFY_bound hAGG (by omega : 2≤N) hL hY
    (dyadicBlock N) (Finset.Subset.refl _)
  have hrate := hr N (by omega) L E hlo hhi
  exact ⟨hFY,hcond.trans hrate,huncond.trans hrate⟩

end
end PaperC.V282.ExactMarkedMovableRates
