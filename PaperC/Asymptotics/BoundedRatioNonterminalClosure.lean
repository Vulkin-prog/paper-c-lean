import PaperC.Asymptotics.CriticalChannelPowers
import PaperC.Asymptotics.PropositionSixteenOneCore
import PaperC.Combinatorics.BoundedRatioCanonicalTerminalPopulation

set_option maxHeartbeats 1800000

/-!
# Closure of the bounded-ratio nonterminal sector

The intrinsic sixth fibre comes with the exact pointwise rank saving

`weight(pair) * 2^(R_K(B)+1) ≤ 4 * 2^B`.

This file sums that inequality, divides by the positive extracted power,
and transports the resulting finite envelope to the critical window.  The
only remaining input is a cardinality statement: after division by the
extracted rank factor, the effective number of intrinsic nonterminal pairs
must be `o(N)`, uniformly in the bounded-ratio endpoint.

No Diophantine input is used in this transfer.  In particular,
Evertse--Silverman and generalized Pell are not part of the residual
Lemma 17.28 obligation isolated below.
-/

namespace PaperC
namespace BoundedRatioNonterminalClosure

open BoundedRatioCanonicalTerminalPopulation
open PropositionSixteenOne

noncomputable section

/-! ## Exact finite summation of the pointwise saving -/

/-- The intrinsic nonterminal mass is the public sixth-sector mass. -/
theorem boundedIntrinsicNonterminalResidualMass_eq_sectorResidualMassNat
    {N M A L : ℕ} (hN : 2 ≤ N) (K : ℝ) :
    boundedIntrinsicNonterminalResidualMass N M A L hN K =
      sectorResidualMassNat
        (M := M) (L := L) A hN
        (boundedIntrinsicTerminalPredicate A K) .nonterminal := by
  unfold boundedIntrinsicNonterminalResidualMass sectorResidualMassNat
  rw [boundedRatioSectorPairs_nonterminal_eq_intrinsicNonterminalPairs]

/--
Finite summed form of the rank saving.  This is the exact arithmetic
content needed before division by `2^(R_K(B)+1)`.
-/
theorem boundedIntrinsicNonterminalResidualMass_mul_two_pow_budget_succ_le
    {N M A L : ℕ} (hN : 2 ≤ N) (K : ℝ) :
    boundedIntrinsicNonterminalResidualMass N M A L hN K *
        2 ^ (terminalRankBudget K L + 1) ≤
      (boundedIntrinsicNonterminalPairs N M A L hN K).card *
        (4 * 2 ^ (L + 1)) := by
  unfold boundedIntrinsicNonterminalResidualMass
  rw [Finset.sum_mul]
  calc
    (∑ pair ∈ boundedIntrinsicNonterminalPairs N M A L hN K,
        residualWeight A hN pair *
          2 ^ (terminalRankBudget K L + 1)) ≤
        ∑ _pair ∈ boundedIntrinsicNonterminalPairs N M A L hN K,
          4 * 2 ^ (L + 1) := by
      exact Finset.sum_le_sum fun pair hpair ↦
        residualWeight_mul_two_pow_budget_succ_le hpair
    _ =
        (boundedIntrinsicNonterminalPairs N M A L hN K).card *
          (4 * 2 ^ (L + 1)) := by
      simp

/-! ## Proof-independent cardinal and mass envelopes -/

/-- Cardinality of the intrinsic sixth fibre, set to zero below `N=2`. -/
noncomputable def intrinsicNonterminalCardinality
    (A : ℕ) (K : ℝ) (N M L : ℕ) : ℕ :=
  if hN : 2 ≤ N then
    (boundedIntrinsicNonterminalPairs N M A L hN K).card
  else 0

/--
Effective cardinality after extracting the full pointwise rank factor.
-/
noncomputable def intrinsicNonterminalEffectiveCardinality
    (A : ℕ) (K : ℝ) (N M L : ℕ) : ℝ :=
  (intrinsicNonterminalCardinality A K N M L : ℝ) /
    ((2 ^ (terminalRankBudget K L + 1) : ℕ) : ℝ)

/--
The exact real envelope obtained by summing the pointwise estimate.
-/
noncomputable def intrinsicNonterminalMassEnvelope
    (A : ℕ) (K : ℝ) (N M L : ℕ) : ℝ :=
  intrinsicNonterminalEffectiveCardinality A K N M L *
    ((4 * 2 ^ (L + 1) : ℕ) : ℝ)

/--
Critical normalization of the effective cardinality.  Saying that this
three-variable function is `o(N²)` is exactly saying that the effective
cardinality is `o(N)`.
-/
noncomputable def intrinsicNonterminalNormalizedCardinality
    (A : ℕ) (K : ℝ) (N M L : ℕ) : ℝ :=
  (N : ℝ) * intrinsicNonterminalEffectiveCardinality A K N M L

theorem intrinsicNonterminalEffectiveCardinality_nonneg
    (A : ℕ) (K : ℝ) (N M L : ℕ) :
    0 ≤ intrinsicNonterminalEffectiveCardinality A K N M L := by
  unfold intrinsicNonterminalEffectiveCardinality
  positivity

theorem intrinsicNonterminalMassEnvelope_nonneg
    (A : ℕ) (K : ℝ) (N M L : ℕ) :
    0 ≤ intrinsicNonterminalMassEnvelope A K N M L := by
  unfold intrinsicNonterminalMassEnvelope
  exact mul_nonneg
    (intrinsicNonterminalEffectiveCardinality_nonneg A K N M L)
    (by positivity)

theorem intrinsicNonterminalNormalizedCardinality_nonneg
    (A : ℕ) (K : ℝ) (N M L : ℕ) :
    0 ≤ intrinsicNonterminalNormalizedCardinality A K N M L := by
  unfold intrinsicNonterminalNormalizedCardinality
  exact mul_nonneg (by positivity)
    (intrinsicNonterminalEffectiveCardinality_nonneg A K N M L)

/-- The public sixth-sector mass is pointwise bounded by the exact envelope. -/
theorem intrinsicNonterminalSectorResidualMass_le_massEnvelope
    (A : ℕ) (K : ℝ) (N M L : ℕ) :
    sectorResidualMass A
        (boundedIntrinsicTerminalPredicate A K)
        .nonterminal N M L ≤
      intrinsicNonterminalMassEnvelope A K N M L := by
  by_cases hN : 2 ≤ N
  · have hfinite :=
      boundedIntrinsicNonterminalResidualMass_mul_two_pow_budget_succ_le
        (M := M) (A := A) (L := L) hN K
    have hcast :
        (boundedIntrinsicNonterminalResidualMass
            N M A L hN K : ℝ) *
              ((2 ^ (terminalRankBudget K L + 1) : ℕ) : ℝ) ≤
          ((boundedIntrinsicNonterminalPairs
              N M A L hN K).card : ℝ) *
            ((4 * 2 ^ (L + 1) : ℕ) : ℝ) := by
      exact_mod_cast hfinite
    have hdenominator :
        0 < ((2 ^ (terminalRankBudget K L + 1) : ℕ) : ℝ) := by
      positivity
    rw [sectorResidualMass, dif_pos hN,
      ← boundedIntrinsicNonterminalResidualMass_eq_sectorResidualMassNat
        hN K]
    unfold intrinsicNonterminalMassEnvelope
      intrinsicNonterminalEffectiveCardinality
      intrinsicNonterminalCardinality
    rw [dif_pos hN]
    calc
      (boundedIntrinsicNonterminalResidualMass
          N M A L hN K : ℝ) ≤
          (((boundedIntrinsicNonterminalPairs
              N M A L hN K).card : ℝ) *
            ((4 * 2 ^ (L + 1) : ℕ) : ℝ)) /
              ((2 ^ (terminalRankBudget K L + 1) : ℕ) : ℝ) :=
        (le_div_iff₀ hdenominator).2 hcast
      _ =
          ((boundedIntrinsicNonterminalPairs
              N M A L hN K).card : ℝ) /
              ((2 ^ (terminalRankBudget K L + 1) : ℕ) : ℝ) *
            ((4 * 2 ^ (L + 1) : ℕ) : ℝ) := by
        ring
  · rw [sectorResidualMass, dif_neg hN]
    unfold intrinsicNonterminalMassEnvelope
      intrinsicNonterminalEffectiveCardinality
      intrinsicNonterminalCardinality
    rw [dif_neg hN]
    norm_num

/-! ## Critical-window closure -/

/--
On the critical window the exact mass envelope is bounded by a fixed
multiple of the normalized effective cardinality.
-/
theorem intrinsicNonterminalMassEnvelope_le_normalizedCardinality
    {C : ℝ} {A N M L : ℕ} {K : ℝ}
    (hN : 0 < N)
    (hrun : CriticalRunWindow.InRunLengthWindow C N L) :
    intrinsicNonterminalMassEnvelope A K N M L ≤
      (8 * CriticalRunWindow.balanceConstant C) *
        intrinsicNonterminalNormalizedCardinality A K N M L := by
  have hpower :=
    CriticalChannelPowers.two_pow_runLength_le_balance_mul hN hrun
  have hweight :
      ((4 * 2 ^ (L + 1) : ℕ) : ℝ) ≤
        (8 * CriticalRunWindow.balanceConstant C) * (N : ℝ) := by
    calc
      ((4 * 2 ^ (L + 1) : ℕ) : ℝ) =
          8 * (2 : ℝ) ^ L := by
        push_cast
        rw [pow_succ]
        ring
      _ ≤
          8 *
            (CriticalRunWindow.balanceConstant C * (N : ℝ)) :=
        mul_le_mul_of_nonneg_left hpower (by norm_num)
      _ =
          (8 * CriticalRunWindow.balanceConstant C) * (N : ℝ) := by
        ring
  unfold intrinsicNonterminalMassEnvelope
    intrinsicNonterminalNormalizedCardinality
  calc
    intrinsicNonterminalEffectiveCardinality A K N M L *
          ((4 * 2 ^ (L + 1) : ℕ) : ℝ) ≤
        intrinsicNonterminalEffectiveCardinality A K N M L *
          ((8 * CriticalRunWindow.balanceConstant C) * (N : ℝ)) :=
      mul_le_mul_of_nonneg_left hweight
        (intrinsicNonterminalEffectiveCardinality_nonneg A K N M L)
    _ =
        (8 * CriticalRunWindow.balanceConstant C) *
          ((N : ℝ) *
            intrinsicNonterminalEffectiveCardinality A K N M L) := by
      ring

/--
Exact-envelope form of Lemma 17.28: once the explicit finite envelope is
uniformly `o(N²)`, so is the public sixth-sector mass.
-/
theorem intrinsicNonterminalSector_uniformLittleO_of_massEnvelope
    {C : ℝ} {κ₀ A : ℕ} {K : ℝ}
    (henvelope :
      UniformLittleOInBoundedRatioWindow C κ₀
        (intrinsicNonterminalMassEnvelope A K)) :
    UniformLittleOInBoundedRatioWindow C κ₀
      (sectorResidualMass A
        (boundedIntrinsicTerminalPredicate A K) .nonterminal) := by
  intro ε hε
  obtain ⟨Nenv, hNenv⟩ := henvelope ε hε
  refine ⟨max 2 Nenv, ?_⟩
  intro N hN M L hNM hMκ hrun
  have hNtwo : 2 ≤ N := (le_max_left _ _).trans hN
  have hNenvN : Nenv ≤ N := (le_max_right _ _).trans hN
  have hmassNonneg :
      0 ≤ sectorResidualMass A
        (boundedIntrinsicTerminalPredicate A K)
        .nonterminal N M L := by
    rw [sectorResidualMass, dif_pos hNtwo]
    positivity
  rw [abs_of_nonneg hmassNonneg]
  exact
    (intrinsicNonterminalSectorResidualMass_le_massEnvelope
      A K N M L).trans
      (by
        simpa only [abs_of_nonneg
          (intrinsicNonterminalMassEnvelope_nonneg A K N M L)] using
          hNenv N hNenvN M L hNM hMκ hrun)

/--
Minimal cardinal form of Lemma 17.28.  The hypothesis is an unweighted
counting invariant: the effective cardinality, after the already proved
rank extraction, is `o(N)`.  The pointwise weights and all critical-window
calculus are discharged here.
-/
theorem intrinsicNonterminalSector_uniformLittleO_of_normalizedCardinality
    {C : ℝ} {κ₀ A : ℕ} {K : ℝ}
    (hcard :
      UniformLittleOInBoundedRatioWindow C κ₀
        (intrinsicNonterminalNormalizedCardinality A K)) :
    UniformLittleOInBoundedRatioWindow C κ₀
      (sectorResidualMass A
        (boundedIntrinsicTerminalPredicate A K) .nonterminal) := by
  let balance := CriticalRunWindow.balanceConstant C
  let denominator : ℝ := 8 * balance + 1
  have hbalance : 0 ≤ balance := by
    dsimp only [balance]
    exact CriticalRunWindow.balanceConstant_nonneg C
  have hdenominator : 0 < denominator := by
    dsimp only [denominator]
    positivity
  intro ε hε
  have hsmallEpsilon : 0 < ε / denominator :=
    div_pos hε hdenominator
  obtain ⟨Ncard, hNcard⟩ := hcard
    (ε / denominator) hsmallEpsilon
  refine ⟨max 2 Ncard, ?_⟩
  intro N hN M L hNM hMκ hrun
  have hNtwo : 2 ≤ N := (le_max_left _ _).trans hN
  have hNcardN : Ncard ≤ N := (le_max_right _ _).trans hN
  have hNpos : 0 < N := by omega
  have hnormalizedSmall :
      intrinsicNonterminalNormalizedCardinality A K N M L ≤
        (ε / denominator) * (N : ℝ) ^ 2 := by
    simpa only [abs_of_nonneg
        (intrinsicNonterminalNormalizedCardinality_nonneg A K N M L),
      abs_of_nonneg (sq_nonneg (N : ℝ))] using
      hNcard N hNcardN M L hNM hMκ hrun
  have hmassNonneg :
      0 ≤ sectorResidualMass A
        (boundedIntrinsicTerminalPredicate A K)
        .nonterminal N M L := by
    rw [sectorResidualMass, dif_pos hNtwo]
    positivity
  rw [abs_of_nonneg hmassNonneg,
    abs_of_nonneg (sq_nonneg (N : ℝ))]
  calc
    sectorResidualMass A
          (boundedIntrinsicTerminalPredicate A K)
          .nonterminal N M L ≤
        intrinsicNonterminalMassEnvelope A K N M L :=
      intrinsicNonterminalSectorResidualMass_le_massEnvelope
        A K N M L
    _ ≤
        (8 * balance) *
          intrinsicNonterminalNormalizedCardinality A K N M L := by
      simpa only [balance] using
        intrinsicNonterminalMassEnvelope_le_normalizedCardinality
          (A := A) (M := M) (K := K) hNpos hrun
    _ ≤
        (8 * balance) *
          ((ε / denominator) * (N : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hnormalizedSmall (by positivity)
    _ ≤ ε * (N : ℝ) ^ 2 := by
      have hcoefficient :
          (8 * balance) * (ε / denominator) ≤ ε := by
        calc
          (8 * balance) * (ε / denominator) =
              (ε / denominator) * (8 * balance) := by ring
          _ ≤ ε := by
            rw [div_mul_eq_mul_div]
            apply (div_le_iff₀ hdenominator).2
            dsimp only [denominator]
            nlinarith [mul_pos hε hdenominator]
      calc
        (8 * balance) *
              ((ε / denominator) * (N : ℝ) ^ 2) =
            ((8 * balance) * (ε / denominator)) *
              (N : ℝ) ^ 2 := by ring
        _ ≤ ε * (N : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right hcoefficient (sq_nonneg (N : ℝ))

/--
The registered Lemma 17.28 interface follows from the exact mass envelope.
Its two historical Diophantine antecedents are ignored because neither
participates in the sixth-sector rank-saving argument.
-/
theorem nonterminalSectorStability_of_massEnvelope
    {C : ℝ} {κ₀ A : ℕ} {K : ℝ}
    (henvelope :
      UniformLittleOInBoundedRatioWindow C κ₀
        (intrinsicNonterminalMassEnvelope A K)) :
    NonterminalSectorStabilityStatement C κ₀ A
      (boundedIntrinsicTerminalPredicate A K) := by
  intro _hES _hPell
  exact
    intrinsicNonterminalSector_uniformLittleO_of_massEnvelope
      henvelope

/--
Cardinality-normalized specialization of the preceding registered
interface.
-/
theorem nonterminalSectorStability_of_normalizedCardinality
    {C : ℝ} {κ₀ A : ℕ} {K : ℝ}
    (hcard :
      UniformLittleOInBoundedRatioWindow C κ₀
        (intrinsicNonterminalNormalizedCardinality A K)) :
    NonterminalSectorStabilityStatement C κ₀ A
      (boundedIntrinsicTerminalPredicate A K) := by
  intro _hES _hPell
  exact
    intrinsicNonterminalSector_uniformLittleO_of_normalizedCardinality
      hcard

end

end BoundedRatioNonterminalClosure
end PaperC
