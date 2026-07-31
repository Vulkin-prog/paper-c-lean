import PaperC.Asymptotics.BoundedRatioTerminalPartnerClosure
import PaperC.Asymptotics.BoundedRatioDistinctKernelTwoDefects
import PaperC.Asymptotics.RationalPowerClosure
import PaperC.Asymptotics.ShallowCoreRationalClosure
import PaperC.Asymptotics.BoundedRatioSmallProductSector
import PaperC.Combinatorics.BoundedRatioIntrinsicTerminalPopulation

set_option maxHeartbeats 3200000

/-!
# Summation of the bounded-ratio terminal fibres

This module performs the global summation left after the fixed-first-start
analysis in `BoundedRatioTerminalPartnerClosure`.

The finite argument has two independent inputs:

* the first-start incidence bound by twice the number of possible kernel
  values;
* the generalized-Pell bound for every fixed first-start partner fibre.

Their product gives a literal bound for the whole rank-defined terminal
population.  The finite set of small odd parts is then replaced by the
elementary Chebyshev smooth-kernel envelope.  The resulting partner factor
is uniformly subpolynomial in the critical run-length window, so multiplying
it by the existing `N^(3/4+o(1))` kernel-value count closes the rank-defined
cardinality and residual-mass estimates.

The last section records the exact, pointwise transport to the intrinsic
terminal population.  The source-scoped arithmetic equivalence of Lemma
9.10 is constructed internally on the nonaligned core, so this transport
has no additional bridge.
-/

namespace PaperC
namespace BoundedRatioTerminalSummation

open scoped BigOperators
open BoundedRatioCanonicalTerminalPopulation
open BoundedRatioDistinctKernelTwoDefects
open BoundedRatioIntrinsicTerminalPopulation
open BoundedRatioTerminalClosure
open BoundedRatioTerminalPartnerClosure
open CanonicalSmallRows
open PropositionSixteenOne

noncomputable section

/-! ## Real-valued disintegration over first starts -/

/--
Real-valued form of the exact first-coordinate disintegration.  It is useful
when the common partner bound is an exponential real envelope rather than a
natural number.
-/
theorem card_boundedRankTerminalPairs_cast_le_firstStarts_mul
    {N M A L : ℕ} (hN : 2 ≤ N) (K : ℝ) (Q : ℝ)
    (hpartners :
      ∀ x ∈ boundedRankTerminalFirstStarts N M A L hN K,
        ((boundedRankTerminalPartnerFiber
          N M A L hN K x).card : ℝ) ≤ Q) :
    ((boundedRankTerminalPairs N M A L hN K).card : ℝ) ≤
      ((boundedRankTerminalFirstStarts N M A L hN K).card : ℝ) * Q := by
  have hdisintegration :=
    card_boundedRankTerminalPairs_eq_sum_partnerFibers
      (N := N) (M := M) (A := A) (L := L) hN K
  calc
    ((boundedRankTerminalPairs N M A L hN K).card : ℝ) =
        ∑ x ∈ boundedRankTerminalFirstStarts N M A L hN K,
          ((boundedRankTerminalPartnerFiber
            N M A L hN K x).card : ℝ) := by
      exact_mod_cast hdisintegration
    _ ≤
        ∑ _x ∈ boundedRankTerminalFirstStarts N M A L hN K, Q :=
      Finset.sum_le_sum hpartners
    _ =
        ((boundedRankTerminalFirstStarts
          N M A L hN K).card : ℝ) * Q := by
      simp

/-! ## Explicit finite population envelopes -/

/-- The literal product of the first-start and fixed-partner envelopes. -/
noncomputable def terminalPopulationRawEnvelope
    (κ₀ : ℕ) (c : ℝ) (N L : ℕ) : ℝ :=
  2 * ((possibleKernelValues κ₀ N L).card : ℝ) *
    ((((L + 1 : ℕ) : ℝ) ^ 4 *
      ((terminalSmallParts κ₀ N L).card : ℝ) ^ 2) *
      PellInput.expLogLogBound c (terminalLabelCutoff κ₀ N))

/--
Global finite summation: a common partner-fibre bound and the incidence
bound control the complete rank-defined terminal population.
-/
theorem card_boundedRankTerminalPairs_cast_le_rawEnvelope
    {κ₀ N M A L : ℕ} (hN : 2 ≤ N) (hA : 1 ≤ A)
    (hMκ : M ≤ κ₀ * N) (hL : L ≤ N) (K c : ℝ)
    (hpartners :
      ∀ x,
        ((boundedRankTerminalPartnerFiber
          N M A L hN K x).card : ℝ) ≤
          ((L + 1 : ℕ) : ℝ) ^ 4 *
            ((terminalSmallParts κ₀ N L).card : ℝ) ^ 2 *
            PellInput.expLogLogBound c
              (terminalLabelCutoff κ₀ N))
    (hhalf :
      L + 1 ≤
        2 * (L + 1 - 3 * terminalRankBudget K L - 1)) :
    ((boundedRankTerminalPairs N M A L hN K).card : ℝ) ≤
      terminalPopulationRawEnvelope κ₀ c N L := by
  let Q : ℝ :=
    ((L + 1 : ℕ) : ℝ) ^ 4 *
      ((terminalSmallParts κ₀ N L).card : ℝ) ^ 2 *
      PellInput.expLogLogBound c (terminalLabelCutoff κ₀ N)
  have hsum :
      ((boundedRankTerminalPairs N M A L hN K).card : ℝ) ≤
        ((boundedRankTerminalFirstStarts
          N M A L hN K).card : ℝ) * Q :=
    card_boundedRankTerminalPairs_cast_le_firstStarts_mul
      hN K Q (fun x _hx ↦ hpartners x)
  have hfirstNat :=
    card_boundedRankTerminalFirstStarts_le_twice_possibleKernelValues
      hN hA hMκ hL K hhalf
  have hfirst :
      ((boundedRankTerminalFirstStarts
        N M A L hN K).card : ℝ) ≤
        2 * ((possibleKernelValues κ₀ N L).card : ℝ) := by
    exact_mod_cast hfirstNat
  have hQ : 0 ≤ Q := by
    dsimp only [Q]
    unfold PellInput.expLogLogBound
    positivity
  calc
    ((boundedRankTerminalPairs N M A L hN K).card : ℝ) ≤
        ((boundedRankTerminalFirstStarts
          N M A L hN K).card : ℝ) * Q :=
      hsum
    _ ≤
        (2 * ((possibleKernelValues κ₀ N L).card : ℝ)) * Q :=
      mul_le_mul_of_nonneg_right hfirst hQ
    _ = terminalPopulationRawEnvelope κ₀ c N L := by
      unfold terminalPopulationRawEnvelope
      dsimp only [Q]

/--
The generalized-Pell input supplies the common partner estimate, hence the
complete raw finite population bound.
-/
theorem generalizedPell_implies_boundedRankTerminalPairs_rawEnvelope
    (hPell : PellInput.GeneralizedPellPolynomialBoxStatement) :
    ∃ c : ℝ, 0 ≤ c ∧
      ∃ X₀ : ℕ, ∀ X ≥ X₀,
        ∀ (κ₀ N M A L : ℕ) (hN : 2 ≤ N),
          2 ≤ κ₀ →
          1 ≤ A →
          M ≤ κ₀ * N →
          L ≤ N →
          terminalLabelCutoff κ₀ N = X →
          ∀ K : ℝ,
            2 ≤ L + 1 - 3 * terminalRankBudget K L →
            L + 1 ≤
              2 * (L + 1 - 3 * terminalRankBudget K L - 1) →
            ((boundedRankTerminalPairs
              N M A L hN K).card : ℝ) ≤
              terminalPopulationRawEnvelope κ₀ c N L := by
  obtain ⟨c, hc, X₀, hpartners⟩ :=
    boundedRankTerminalPartnerFiber_polynomialBound hPell
  refine ⟨c, hc, X₀, ?_⟩
  intro X hX κ₀ N M A L hN hκ₀ hA hMκ hL hcutoff
    K htwo hhalf
  apply
    card_boundedRankTerminalPairs_cast_le_rawEnvelope
      hN hA hMκ hL K c _ hhalf
  intro x
  simpa only [hcutoff] using
    (hpartners X hX κ₀ N M A L hN hκ₀ hMκ hL hcutoff
      K x htwo)

/-! ## Chebyshev replacement of the small odd parts -/

/-- The complete first-start-independent partner loss after Chebyshev. -/
noncomputable def terminalPartnerEnvelope
    (κ₀ : ℕ) (c : ℝ) (N L : ℕ) : ℝ :=
  2 *
    ((((L + 1 : ℕ) : ℝ) ^ 4 *
      smoothKernelChebyshevEnvelope (L + 1) ^ 2) *
      PellInput.expLogLogBound c (terminalLabelCutoff κ₀ N))

/-- The smooth Chebyshev replacement of the raw population envelope. -/
noncomputable def terminalPopulationEnvelope
    (κ₀ : ℕ) (c : ℝ) (N L : ℕ) : ℝ :=
  terminalPartnerEnvelope κ₀ c N L *
    ((possibleKernelValues κ₀ N L).card : ℝ)

/-- The literal small-part set is bounded by the Chebyshev envelope. -/
theorem card_terminalSmallParts_le_smoothKernelChebyshevEnvelope
    {κ₀ N L : ℕ} (hB : 4 ≤ L + 1) :
    ((terminalSmallParts κ₀ N L).card : ℝ) ≤
      smoothKernelChebyshevEnvelope (L + 1) := by
  simpa only [terminalSmallParts] using
    (card_squarefreeSmoothUpTo_le_smoothKernelChebyshevEnvelope
      (B := L + 1) (X := terminalLabelCutoff κ₀ N) hB)

/-- The raw finite envelope is dominated by its smooth replacement. -/
theorem terminalPopulationRawEnvelope_le_terminalPopulationEnvelope
    {κ₀ N L : ℕ} {c : ℝ} (hB : 4 ≤ L + 1) :
    terminalPopulationRawEnvelope κ₀ c N L ≤
      terminalPopulationEnvelope κ₀ c N L := by
  have hsmooth :=
    card_terminalSmallParts_le_smoothKernelChebyshevEnvelope
      (κ₀ := κ₀) (N := N) hB
  have hcardNonneg :
      0 ≤ ((terminalSmallParts κ₀ N L).card : ℝ) := by
    positivity
  have hsmoothNonneg :
      0 ≤ smoothKernelChebyshevEnvelope (L + 1) := by
    unfold smoothKernelChebyshevEnvelope
    positivity
  have hsquare :
      ((terminalSmallParts κ₀ N L).card : ℝ) ^ 2 ≤
        smoothKernelChebyshevEnvelope (L + 1) ^ 2 := by
    nlinarith [mul_nonneg
      (sub_nonneg.mpr hsmooth)
      (add_nonneg hcardNonneg hsmoothNonneg)]
  unfold terminalPopulationRawEnvelope terminalPopulationEnvelope
    terminalPartnerEnvelope
  have hpell :
      0 ≤ PellInput.expLogLogBound c
        (terminalLabelCutoff κ₀ N) := by
    unfold PellInput.expLogLogBound
    positivity
  have hkernel :
      0 ≤ ((possibleKernelValues κ₀ N L).card : ℝ) := by
    positivity
  have hoffset :
      0 ≤ ((L + 1 : ℕ) : ℝ) ^ 4 := by
    positivity
  calc
    2 * ((possibleKernelValues κ₀ N L).card : ℝ) *
          (((L + 1 : ℕ) : ℝ) ^ 4 *
            ((terminalSmallParts κ₀ N L).card : ℝ) ^ 2 *
            PellInput.expLogLogBound c
              (terminalLabelCutoff κ₀ N)) ≤
        2 * ((possibleKernelValues κ₀ N L).card : ℝ) *
          (((L + 1 : ℕ) : ℝ) ^ 4 *
            smoothKernelChebyshevEnvelope (L + 1) ^ 2 *
            PellInput.expLogLogBound c
              (terminalLabelCutoff κ₀ N)) := by
      gcongr
    _ =
        2 *
          (((L + 1 : ℕ) : ℝ) ^ 4 *
            smoothKernelChebyshevEnvelope (L + 1) ^ 2 *
            PellInput.expLogLogBound c
              (terminalLabelCutoff κ₀ N)) *
          ((possibleKernelValues κ₀ N L).card : ℝ) := by
      ring

/-! ## Uniform subpolynomial partner loss -/

/--
Replacing the Pell height `N` by the fixed bounded-ratio multiple
`(κ₀+1)N` preserves uniform subpolynomiality.
-/
theorem expLogLogBound_terminalLabelCutoff_uniformSubpolynomial
    {C c : ℝ} (hc : 0 ≤ c) (κ₀ : ℕ) :
    UniformSubpolynomialOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun N _ ↦
        PellInput.expLogLogBound c (terminalLabelCutoff κ₀ N)) := by
  let D : ℝ := 2 * c
  have hD : 0 ≤ D := by
    dsimp only [D]
    positivity
  apply
    ExpLogDivLogLog.uniformSubpolynomialOn_exp_log_div_loglog_eventually
      (CriticalRunWindow.InRunLengthWindow C)
      (fun N _ ↦
        c * Real.log (terminalLabelCutoff κ₀ N) /
          Real.log (Real.log (terminalLabelCutoff κ₀ N)))
      D hD
  obtain ⟨Nlog, hNlog⟩ :=
    exists_nat_gt (Real.exp (Real.exp 1))
  refine ⟨max Nlog (κ₀ + 1), ?_⟩
  intro N hN L _hrun
  have hNlogN : Nlog ≤ N :=
    (le_max_left Nlog (κ₀ + 1)).trans hN
  have hfactorN : κ₀ + 1 ≤ N :=
    (le_max_right Nlog (κ₀ + 1)).trans hN
  have hthreshold :
      Real.exp (Real.exp 1) < (N : ℝ) :=
    hNlog.trans_le (by exact_mod_cast hNlogN)
  have hNpos : 0 < (N : ℝ) :=
    (Real.exp_pos _).trans hthreshold
  have hlogN :
      Real.exp 1 < Real.log (N : ℝ) := by
    have hmono :=
      Real.log_lt_log
        (Real.exp_pos (Real.exp 1)) hthreshold
    simpa only [Real.log_exp] using hmono
  have hlogNpos : 0 < Real.log (N : ℝ) :=
    (Real.exp_pos 1).trans hlogN
  have hloglogN :
      1 < Real.log (Real.log (N : ℝ)) := by
    have hmono :=
      Real.log_lt_log (Real.exp_pos 1) hlogN
    simpa only [Real.log_exp] using hmono
  have hloglogNpos :
      0 < Real.log (Real.log (N : ℝ)) :=
    zero_lt_one.trans hloglogN
  have hfactorPos : 0 < ((κ₀ + 1 : ℕ) : ℝ) := by
    positivity
  have hlogFactor :
      Real.log ((κ₀ + 1 : ℕ) : ℝ) ≤
        Real.log (N : ℝ) := by
    apply Real.log_le_log hfactorPos
    exact_mod_cast hfactorN
  have hcutoffPos :
      0 < ((terminalLabelCutoff κ₀ N : ℕ) : ℝ) := by
    unfold terminalLabelCutoff
    norm_num only [Nat.cast_mul]
    exact mul_pos hfactorPos hNpos
  have hlogCutoff :
      Real.log ((terminalLabelCutoff κ₀ N : ℕ) : ℝ) =
        Real.log ((κ₀ + 1 : ℕ) : ℝ) +
          Real.log (N : ℝ) := by
    unfold terminalLabelCutoff
    norm_num only [Nat.cast_mul]
    rw [Real.log_mul hfactorPos.ne' hNpos.ne']
  have hlogCutoffLe :
      Real.log ((terminalLabelCutoff κ₀ N : ℕ) : ℝ) ≤
        2 * Real.log (N : ℝ) := by
    rw [hlogCutoff]
    linarith
  have hNleCutoff : N ≤ terminalLabelCutoff κ₀ N := by
    unfold terminalLabelCutoff
    exact Nat.le_mul_of_pos_left N (by omega)
  have hlogNleCutoff :
      Real.log (N : ℝ) ≤
        Real.log ((terminalLabelCutoff κ₀ N : ℕ) : ℝ) := by
    apply Real.log_le_log hNpos
    exact_mod_cast hNleCutoff
  have hloglogMono :
      Real.log (Real.log (N : ℝ)) ≤
        Real.log
          (Real.log ((terminalLabelCutoff κ₀ N : ℕ) : ℝ)) := by
    apply Real.log_le_log hlogNpos
    exact hlogNleCutoff
  have hloglogCutoffPos :
      0 <
        Real.log
          (Real.log ((terminalLabelCutoff κ₀ N : ℕ) : ℝ)) :=
    hloglogNpos.trans_le hloglogMono
  have hratio :
      Real.log ((terminalLabelCutoff κ₀ N : ℕ) : ℝ) /
          Real.log
            (Real.log ((terminalLabelCutoff κ₀ N : ℕ) : ℝ)) ≤
        2 * Real.log (N : ℝ) /
          Real.log (Real.log (N : ℝ)) := by
    calc
      Real.log ((terminalLabelCutoff κ₀ N : ℕ) : ℝ) /
            Real.log
              (Real.log ((terminalLabelCutoff κ₀ N : ℕ) : ℝ)) ≤
          (2 * Real.log (N : ℝ)) /
            Real.log
              (Real.log ((terminalLabelCutoff κ₀ N : ℕ) : ℝ)) :=
        div_le_div_of_nonneg_right
          hlogCutoffLe hloglogCutoffPos.le
      _ ≤
          (2 * Real.log (N : ℝ)) /
            Real.log (Real.log (N : ℝ)) :=
        div_le_div_of_nonneg_left
          (by positivity) hloglogNpos hloglogMono
  calc
    c * Real.log (terminalLabelCutoff κ₀ N) /
          Real.log (Real.log (terminalLabelCutoff κ₀ N)) =
        c *
          (Real.log (terminalLabelCutoff κ₀ N) /
            Real.log (Real.log (terminalLabelCutoff κ₀ N))) := by
      ring
    _ ≤
        c *
          (2 * Real.log (N : ℝ) /
            Real.log (Real.log (N : ℝ))) :=
      mul_le_mul_of_nonneg_left hratio hc
    _ =
        D * Real.log (N : ℝ) /
          Real.log (Real.log (N : ℝ)) := by
      dsimp only [D]
      ring

/-- Fixed positive powers preserve uniform subpolynomiality. -/
theorem uniformSubpolynomialOn_fixedPower
    {admissible : ℕ → ℕ → Prop}
    {f : ℕ → ℕ → ℝ}
    (hf : UniformSubpolynomialOn admissible f)
    (d : ℕ) (hd : 0 < d) :
    UniformSubpolynomialOn admissible
      (fun N L ↦ f N L ^ d) := by
  intro k hk
  have hdk : 0 < d * k :=
    Nat.mul_pos hd hk
  obtain ⟨N₀, hN₀⟩ := hf (d * k) hdk
  refine ⟨N₀, ?_⟩
  intro N hN L hNL
  simpa only [abs_pow, pow_mul] using
    hN₀ N hN L hNL

/--
All factors introduced by summing a fixed first-start partner fibre are
uniformly `N^o(1)`.
-/
theorem terminalPartnerEnvelope_uniformSubpolynomial
    {C c : ℝ} (hC : 0 ≤ C) (hc : 0 ≤ c) (κ₀ : ℕ) :
    UniformSubpolynomialOn
      (CriticalRunWindow.InRunLengthWindow C)
      (terminalPartnerEnvelope κ₀ c) := by
  have hheight :=
    CriticalRationalMassEnvelopes.runLengthAddOne_uniformSubpolynomial
      hC
  have hheightFourth :=
    uniformSubpolynomialOn_fixedPower hheight 4 (by omega)
  have hsmooth :=
    smoothKernelChebyshevEnvelope_uniformSubpolynomial hC
  have hsmoothSquare :=
    uniformSubpolynomialOn_fixedPower hsmooth 2 (by omega)
  have hpell :=
    expLogLogBound_terminalLabelCutoff_uniformSubpolynomial
      (C := C) hc κ₀
  have hproduct :=
    ExpSqrtLog.uniformSubpolynomialOn_mul
      (ExpSqrtLog.uniformSubpolynomialOn_mul
        hheightFourth hsmoothSquare)
      hpell
  unfold terminalPartnerEnvelope
  simpa only [mul_assoc] using
    ExpSqrtLog.uniformSubpolynomialOn_const_mul 2 hproduct

/--
The complete smooth population envelope retains the existing
`N^(3/4+o(1))` exponent.
-/
theorem terminalPopulationEnvelope_uniformThreeQuarter
    {C c : ℝ} (hC : 0 ≤ C) (hc : 0 ≤ c) (κ₀ : ℕ) :
    UniformRationalPowerSubpolynomialOn 3 4
      (CriticalRunWindow.InRunLengthWindow C)
      (terminalPopulationEnvelope κ₀ c) := by
  have hkernel :=
    card_possibleKernelValues_uniformThreeQuarter hC κ₀
  have hpartner :=
    terminalPartnerEnvelope_uniformSubpolynomial hC hc κ₀
  simpa only [terminalPopulationEnvelope] using
    (UniformRationalPower.mul_subpolynomial
      (p := 3) (q := 4) (by omega) hkernel hpartner)

/-! ## The source-exact seven-fourths mass envelope -/

/--
Endpoint-independent envelope for the weighted terminal mass.  The factor
`8 * balanceConstant C * N` is the critical-window upper bound for the
pointwise weight `4 * 2^(L+1)`.
-/
noncomputable def terminalRankMassEnvelope
    (C : ℝ) (κ₀ : ℕ) (c : ℝ) (N L : ℕ) : ℝ :=
  (N : ℝ) *
    ((8 * CriticalRunWindow.balanceConstant C) *
      terminalPopulationEnvelope κ₀ c N L)

theorem terminalPopulationEnvelope_nonneg
    (κ₀ : ℕ) (c : ℝ) (N L : ℕ) :
    0 ≤ terminalPopulationEnvelope κ₀ c N L := by
  unfold terminalPopulationEnvelope terminalPartnerEnvelope
    smoothKernelChebyshevEnvelope PellInput.expLogLogBound
  positivity

theorem terminalRankMassEnvelope_nonneg
    (C : ℝ) (κ₀ : ℕ) (c : ℝ) (N L : ℕ) :
    0 ≤ terminalRankMassEnvelope C κ₀ c N L := by
  unfold terminalRankMassEnvelope
  have hbalance :
      0 ≤ CriticalRunWindow.balanceConstant C :=
    CriticalRunWindow.balanceConstant_nonneg C
  exact mul_nonneg (by positivity) <|
    mul_nonneg (mul_nonneg (by norm_num) hbalance)
      (terminalPopulationEnvelope_nonneg κ₀ c N L)

/--
The weighted terminal envelope has the manuscript exponent
`N^(7/4+o_{C,κ₀}(1))`: multiplication of the cardinal exponent `3/4` by the
exact critical-window factor `N` shifts the numerator from `3` to `7`.
-/
theorem terminalRankMassEnvelope_uniformSevenFourths
    {C c : ℝ} (hC : 0 ≤ C) (hc : 0 ≤ c) (κ₀ : ℕ) :
    UniformRationalPowerSubpolynomialOn 7 4
      (CriticalRunWindow.InRunLengthWindow C)
      (terminalRankMassEnvelope C κ₀ c) := by
  have hpopulation :=
    terminalPopulationEnvelope_uniformThreeQuarter hC hc κ₀
  have hconstant :
      UniformSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C)
        (fun _ _ ↦ 8 * CriticalRunWindow.balanceConstant C) :=
    ExpSqrtLog.uniformSubpolynomialOn_const
      (CriticalRunWindow.InRunLengthWindow C)
      (8 * CriticalRunWindow.balanceConstant C)
  have hscaled :=
    UniformRationalPower.mul_subpolynomial
      (p := 3) (q := 4) (by omega) hpopulation hconstant
  have hshifted :=
    UniformRationalPower.natPower_mul (r := 1) hscaled
  simpa only [terminalRankMassEnvelope, pow_one, Nat.one_mul,
    Nat.add_comm] using hshifted

/-! ## Eventual finite domination in the critical window -/

/--
Generalized Pell now controls the complete rank-defined terminal population
by the smooth `N^(3/4+o(1))` envelope, uniformly in bounded-ratio endpoints.
-/
theorem generalizedPell_implies_boundedRankTerminalPairs_le_envelope
    {C : ℝ} (hC : 0 ≤ C) (κ₀ A : ℕ) (K : ℝ)
    (hκ₀ : 2 ≤ κ₀) (hA : 1 ≤ A) (hK : 0 ≤ K)
    (hPell : PellInput.GeneralizedPellPolynomialBoxStatement) :
    ∃ c : ℝ, 0 ≤ c ∧
      ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ M L (hN : 2 ≤ N),
        2 * N ≤ M →
        M ≤ κ₀ * N →
        CriticalRunWindow.InRunLengthWindow C N L →
        ((boundedRankTerminalPairs N M A L hN K).card : ℝ) ≤
          terminalPopulationEnvelope κ₀ c N L := by
  obtain ⟨c, hc, X₀, hraw⟩ :=
    generalizedPell_implies_boundedRankTerminalPairs_rawEnvelope
      hPell
  have hheightSubpoly :=
    CriticalRationalMassEnvelopes.runLengthAddOne_uniformSubpolynomial
      hC
  obtain ⟨Nheight, hheight⟩ :=
    hheightSubpoly 1 (by omega)
  obtain ⟨Nfour, hfour⟩ :=
    DependencyEdgesCritical.runLengthAddOne_tends_to_infinity
      hC 4
  obtain ⟨Nslack, hslack⟩ :=
    terminalRankBudget_slack_conditions_eventually hC hK
  refine
    ⟨c, hc, max X₀ (max Nheight (max Nfour Nslack)), ?_⟩
  intro N hN M L hNtwo _hNM hMκ hrun
  have hX₀N : X₀ ≤ N :=
    (le_max_left X₀ (max Nheight (max Nfour Nslack))).trans hN
  have htail :
      max Nheight (max Nfour Nslack) ≤ N :=
    (le_max_right X₀ (max Nheight (max Nfour Nslack))).trans hN
  have hNheight : Nheight ≤ N :=
    (le_max_left Nheight (max Nfour Nslack)).trans htail
  have htail₂ : max Nfour Nslack ≤ N :=
    (le_max_right Nheight (max Nfour Nslack)).trans htail
  have hNfour : Nfour ≤ N :=
    (le_max_left Nfour Nslack).trans htail₂
  have hNslack : Nslack ≤ N :=
    (le_max_right Nfour Nslack).trans htail₂
  have hheightReal :
      (((L + 1 : ℕ) : ℝ)) ≤ (N : ℝ) := by
    have hbound := hheight N hNheight L hrun
    have hnonneg : 0 ≤ (((L + 1 : ℕ) : ℝ)) := by
      positivity
    simpa only [abs_of_nonneg hnonneg, pow_one] using hbound
  have hheightNat : L + 1 ≤ N := by
    exact_mod_cast hheightReal
  have hL : L ≤ N := by omega
  have hBfour : 4 ≤ L + 1 :=
    hfour N hNfour L hrun
  obtain ⟨htwo, hhalf⟩ :=
    hslack N hNslack L hrun
  have hNleCutoff :
      N ≤ terminalLabelCutoff κ₀ N := by
    unfold terminalLabelCutoff
    exact Nat.le_mul_of_pos_left N (by omega)
  have hX₀ :
      X₀ ≤ terminalLabelCutoff κ₀ N :=
    hX₀N.trans hNleCutoff
  have hfinite :=
    hraw (terminalLabelCutoff κ₀ N) hX₀
      κ₀ N M A L hNtwo hκ₀ hA hMκ hL rfl
      K htwo hhalf
  exact
    hfinite.trans
      (terminalPopulationRawEnvelope_le_terminalPopulationEnvelope
        (κ₀ := κ₀) (N := N) (c := c) hBfour)

/--
Finite weighted transfer from a terminal-cardinality envelope to the
source-exact `7/4` mass envelope.
-/
theorem rankTerminalSectorResidualMass_le_massEnvelope
    {C : ℝ} {κ₀ N M A L : ℕ} (hN : 2 ≤ N) (K c : ℝ)
    (hrun : CriticalRunWindow.InRunLengthWindow C N L)
    (hcard :
      ((boundedRankTerminalPairs N M A L hN K).card : ℝ) ≤
        terminalPopulationEnvelope κ₀ c N L) :
    |sectorResidualMass A
        (boundedRankTerminalPredicate A K)
        .terminal N M L| ≤
      terminalRankMassEnvelope C κ₀ c N L := by
  have hpower :=
    CriticalChannelPowers.two_pow_runLength_le_balance_mul
      (show 0 < N by omega) hrun
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
  have hmassNat :=
    boundedRankTerminalResidualMass_le_card_mul_weight
      (N := N) (M := M) (A := A) (L := L) hN K
  have hmassCast :
      ((boundedRankTerminalResidualMass
        N M A L hN K : ℕ) : ℝ) ≤
        ((boundedRankTerminalPairs N M A L hN K).card : ℝ) *
          ((4 * 2 ^ (L + 1) : ℕ) : ℝ) := by
    exact_mod_cast hmassNat
  have hpopulationNonneg :
      0 ≤ terminalPopulationEnvelope κ₀ c N L :=
    terminalPopulationEnvelope_nonneg κ₀ c N L
  have htarget :
      ((boundedRankTerminalResidualMass
        N M A L hN K : ℕ) : ℝ) ≤
        terminalRankMassEnvelope C κ₀ c N L := by
    calc
      ((boundedRankTerminalResidualMass
          N M A L hN K : ℕ) : ℝ) ≤
          ((boundedRankTerminalPairs N M A L hN K).card : ℝ) *
            ((4 * 2 ^ (L + 1) : ℕ) : ℝ) :=
        hmassCast
      _ ≤
          terminalPopulationEnvelope κ₀ c N L *
            ((4 * 2 ^ (L + 1) : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      _ ≤
          terminalPopulationEnvelope κ₀ c N L *
            ((8 * CriticalRunWindow.balanceConstant C) * (N : ℝ)) :=
        mul_le_mul_of_nonneg_left hweight hpopulationNonneg
      _ = terminalRankMassEnvelope C κ₀ c N L := by
        unfold terminalRankMassEnvelope
        ring
  rw [sectorResidualMass, dif_pos hN]
  rw [←
    boundedRankTerminalResidualMass_eq_sectorResidualMassNat
      hN K]
  rw [abs_of_nonneg (by positivity)]
  exact htarget

/--
Literal bounded-ratio form of Lemma 17.30 for the rank-defined terminal
population.  This records the full `N^(7/4+o_{C,κ₀}(1))` exponent, uniformly
in the endpoint `M`, rather than only its consequence `o(N²)`.
-/
theorem generalizedPell_implies_rankTerminalSector_uniformSevenFourths
    {C : ℝ} (hC : 0 ≤ C) (κ₀ A : ℕ) (K : ℝ)
    (hκ₀ : 2 ≤ κ₀) (hA : 1 ≤ A) (hK : 0 ≤ K)
    (hPell : PellInput.GeneralizedPellPolynomialBoxStatement) :
    BoundedRatioSmallProductSector.UniformSevenFourthsInBoundedRatioWindow
      C κ₀
      (sectorResidualMass A
        (boundedRankTerminalPredicate A K)
        .terminal) := by
  obtain ⟨c, hc, Nfinite, hfinite⟩ :=
    generalizedPell_implies_boundedRankTerminalPairs_le_envelope
      hC κ₀ A K hκ₀ hA hK hPell
  have henvelope :=
    terminalRankMassEnvelope_uniformSevenFourths hC hc κ₀
  intro k hk
  obtain ⟨Nenv, hNenv⟩ := henvelope k hk
  refine ⟨max 2 (max Nfinite Nenv), ?_⟩
  intro N hN M L hNM hMκ hrun
  have hNtwo : 2 ≤ N :=
    (le_max_left 2 (max Nfinite Nenv)).trans hN
  have htail : max Nfinite Nenv ≤ N :=
    (le_max_right 2 (max Nfinite Nenv)).trans hN
  have hNfiniteN : Nfinite ≤ N :=
    (le_max_left Nfinite Nenv).trans htail
  have hNenvN : Nenv ≤ N :=
    (le_max_right Nfinite Nenv).trans htail
  have hcard :=
    hfinite N hNfiniteN M L hNtwo hNM hMκ hrun
  have hmass :=
    rankTerminalSectorResidualMass_le_massEnvelope
      (κ₀ := κ₀) hNtwo K c hrun hcard
  have hmassNonneg :
      0 ≤
        |sectorResidualMass A
          (boundedRankTerminalPredicate A K)
          .terminal N M L| :=
    abs_nonneg _
  have henvelopeNonneg :
      0 ≤ terminalRankMassEnvelope C κ₀ c N L :=
    terminalRankMassEnvelope_nonneg C κ₀ c N L
  calc
    |sectorResidualMass A
        (boundedRankTerminalPredicate A K)
        .terminal N M L| ^ (4 * k) ≤
        |terminalRankMassEnvelope C κ₀ c N L| ^ (4 * k) := by
      rw [abs_of_nonneg henvelopeNonneg]
      exact pow_le_pow_left₀ hmassNonneg hmass _
    _ ≤ (N : ℝ) ^ (7 * k + 1) :=
      hNenv N hNenvN L hrun

/-! ## From eventual cardinal domination to terminal mass -/

/--
Eventual variant of the terminal weighted-transfer theorem.  Finite
domination naturally starts after the Pell, Chebyshev and slack thresholds,
and those thresholds can be absorbed into the little-oh quantifier.
-/
theorem rankTerminalSector_uniformLittleO_of_eventual_card_envelope
    {C : ℝ} (κ₀ A : ℕ) (K : ℝ)
    (cardEnvelope : ℕ → ℕ → ℝ)
    (henvelope :
      UniformRationalPowerSubpolynomialOn 3 4
        (CriticalRunWindow.InRunLengthWindow C)
        cardEnvelope)
    (hcard :
      ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ M L (hNtwo : 2 ≤ N),
        2 * N ≤ M →
        M ≤ κ₀ * N →
        CriticalRunWindow.InRunLengthWindow C N L →
        ((boundedRankTerminalPairs
          N M A L hNtwo K).card : ℝ) ≤
          |cardEnvelope N L|) :
    UniformLittleOInBoundedRatioWindow C κ₀
      (sectorResidualMass A
        (boundedRankTerminalPredicate A K)
        .terminal) := by
  have hsmallPow :=
    UniformRationalPower.littleO_natPower_of_lt
      (p := 3) (q := 4) (r := 1) (by omega) henvelope
  have hsmall :
      UniformLittleOOn
        (CriticalRunWindow.InRunLengthWindow C)
        cardEnvelope
        (fun N _ ↦ (N : ℝ)) := by
    simpa only [pow_one] using hsmallPow
  obtain ⟨Nfinite, hfinite⟩ := hcard
  intro ε hε
  let balance := CriticalRunWindow.balanceConstant C
  let denominator : ℝ := 8 * balance + 1
  have hbalance : 0 ≤ balance := by
    dsimp only [balance]
    exact CriticalRunWindow.balanceConstant_nonneg C
  have hdenominator : 0 < denominator := by
    dsimp only [denominator]
    positivity
  have hsmallEpsilon : 0 < ε / denominator :=
    div_pos hε hdenominator
  obtain ⟨Ncard, hNcard⟩ :=
    hsmall (ε / denominator) hsmallEpsilon
  refine ⟨max 2 (max Ncard Nfinite), ?_⟩
  intro N hN M L hNM hMκ hrun
  have hNtwo : 2 ≤ N :=
    (le_max_left 2 (max Ncard Nfinite)).trans hN
  have htail : max Ncard Nfinite ≤ N :=
    (le_max_right 2 (max Ncard Nfinite)).trans hN
  have hNcardN : Ncard ≤ N :=
    (le_max_left Ncard Nfinite).trans htail
  have hNfiniteN : Nfinite ≤ N :=
    (le_max_right Ncard Nfinite).trans htail
  have hNpos : 0 < N := by omega
  have hcardFinite :=
    hfinite N hNfiniteN M L hNtwo hNM hMκ hrun
  have hcardSmall :
      |cardEnvelope N L| ≤
        (ε / denominator) * (N : ℝ) := by
    simpa only [abs_of_nonneg
      (show 0 ≤ (N : ℝ) by positivity)] using
      hNcard N hNcardN L hrun
  have hpower :=
    CriticalChannelPowers.two_pow_runLength_le_balance_mul
      hNpos hrun
  have hweight :
      ((4 * 2 ^ (L + 1) : ℕ) : ℝ) ≤
        (8 * balance) * (N : ℝ) := by
    calc
      ((4 * 2 ^ (L + 1) : ℕ) : ℝ) =
          8 * (2 : ℝ) ^ L := by
        push_cast
        rw [pow_succ]
        ring
      _ ≤ 8 * (balance * (N : ℝ)) :=
        mul_le_mul_of_nonneg_left hpower (by norm_num)
      _ = (8 * balance) * (N : ℝ) := by ring
  have hmassNat :=
    boundedRankTerminalResidualMass_le_card_mul_weight
      (N := N) (M := M) (A := A) (L := L) hNtwo K
  have hmassCast :
      ((boundedRankTerminalResidualMass
        N M A L hNtwo K : ℕ) : ℝ) ≤
        ((boundedRankTerminalPairs
          N M A L hNtwo K).card : ℝ) *
          ((4 * 2 ^ (L + 1) : ℕ) : ℝ) := by
    exact_mod_cast hmassNat
  have hmassNonneg :
      0 ≤
        ((boundedRankTerminalResidualMass
          N M A L hNtwo K : ℕ) : ℝ) := by
    positivity
  have htarget :
      ((boundedRankTerminalResidualMass
        N M A L hNtwo K : ℕ) : ℝ) ≤
        ε * (N : ℝ) ^ 2 := by
    calc
      ((boundedRankTerminalResidualMass
        N M A L hNtwo K : ℕ) : ℝ) ≤
          ((boundedRankTerminalPairs
            N M A L hNtwo K).card : ℝ) *
            ((4 * 2 ^ (L + 1) : ℕ) : ℝ) :=
        hmassCast
      _ ≤ |cardEnvelope N L| *
            ((4 * 2 ^ (L + 1) : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right hcardFinite (by positivity)
      _ ≤ ((ε / denominator) * (N : ℝ)) *
            ((8 * balance) * (N : ℝ)) :=
        mul_le_mul hcardSmall hweight
          (by positivity) (by positivity)
      _ ≤ ε * (N : ℝ) ^ 2 := by
        have hratio :
            (ε / denominator) * (8 * balance) ≤ ε := by
          rw [div_mul_eq_mul_div]
          apply (div_le_iff₀ hdenominator).2
          dsimp only [denominator]
          nlinarith [mul_pos hε hdenominator]
        calc
          ((ε / denominator) * (N : ℝ)) *
                ((8 * balance) * (N : ℝ)) =
              ((ε / denominator) * (8 * balance)) *
                (N : ℝ) ^ 2 := by ring
          _ ≤ ε * (N : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_right hratio (by positivity)
  rw [sectorResidualMass, dif_pos hNtwo]
  rw [←
    boundedRankTerminalResidualMass_eq_sectorResidualMassNat
      hNtwo K]
  rw [abs_of_nonneg hmassNonneg,
    abs_of_nonneg (by positivity : 0 ≤ (N : ℝ) ^ 2)]
  exact htarget

/--
Lemma 17.30 for the literal rank-defined population: generalized Pell is
the only arithmetic antecedent.
-/
theorem generalizedPell_implies_rankTerminalSector_uniformLittleO
    {C : ℝ} (hC : 0 ≤ C) (κ₀ A : ℕ) (K : ℝ)
    (hκ₀ : 2 ≤ κ₀) (hA : 1 ≤ A) (hK : 0 ≤ K)
    (hPell : PellInput.GeneralizedPellPolynomialBoxStatement) :
    UniformLittleOInBoundedRatioWindow C κ₀
      (sectorResidualMass A
        (boundedRankTerminalPredicate A K)
        .terminal) := by
  obtain ⟨c, hc, N₀, hfinite⟩ :=
    generalizedPell_implies_boundedRankTerminalPairs_le_envelope
      hC κ₀ A K hκ₀ hA hK hPell
  apply
    rankTerminalSector_uniformLittleO_of_eventual_card_envelope
      κ₀ A K (terminalPopulationEnvelope κ₀ c)
      (terminalPopulationEnvelope_uniformThreeQuarter hC hc κ₀)
  refine ⟨N₀, ?_⟩
  intro N hN M L hNtwo hNM hMκ hrun
  have hbound :=
    hfinite N hN M L hNtwo hNM hMκ hrun
  have henvelopeNonneg :
      0 ≤ terminalPopulationEnvelope κ₀ c N L := by
    unfold terminalPopulationEnvelope terminalPartnerEnvelope
      smoothKernelChebyshevEnvelope PellInput.expLogLogBound
    positivity
  simpa only [abs_of_nonneg henvelopeNonneg] using hbound

/-! ## Explicit transport through the proved Lemma 9.10 -/

/--
Pointwise equality of the rank-defined and intrinsic terminal finsets.
The arithmetic-kernel equivalence is constructed internally on the
nonaligned core where both populations live.
-/
theorem boundedRankTerminalPairs_eq_boundedIntrinsicTerminalPairs
    {N M A L : ℕ} (hN : 2 ≤ N) (K : ℝ) :
    boundedRankTerminalPairs N M A L hN K =
      boundedIntrinsicTerminalPairs N M A L hN K := by
  classical
  ext pair
  exact
    mem_rankTerminalPairs_iff_mem_intrinsicTerminalPairs
      hN K pair

/-- Pointwise equality of the two terminal sector masses by Lemma 9.10. -/
theorem sectorResidualMass_rank_eq_intrinsic
    {N M A L : ℕ} (hN : 2 ≤ N) (K : ℝ) :
    sectorResidualMass A
        (boundedRankTerminalPredicate A K) .terminal N M L =
      sectorResidualMass A
        (boundedIntrinsicTerminalPredicate A K) .terminal N M L := by
  classical
  unfold sectorResidualMass
  rw [dif_pos hN, dif_pos hN]
  congr 1
  unfold sectorResidualMassNat
  rw [boundedRatioSectorPairs_terminal_eq_rankTerminalPairs hN K,
    boundedRatioSectorPairs_terminal_eq_intrinsicTerminalPairs hN K,
    boundedRankTerminalPairs_eq_boundedIntrinsicTerminalPairs
      hN K]

/--
Functional equality of the public rank-defined and intrinsic terminal
masses.  All arithmetic transport is proved internally.
-/
theorem sectorResidualMass_rank_eq_intrinsic_fun
    (A : ℕ) (K : ℝ) :
    sectorResidualMass A
        (boundedRankTerminalPredicate A K) .terminal =
      sectorResidualMass A
        (boundedIntrinsicTerminalPredicate A K) .terminal := by
  funext N M L
  by_cases hN : 2 ≤ N
  · exact
      sectorResidualMass_rank_eq_intrinsic
        hN K
  · unfold sectorResidualMass
    rw [dif_neg hN, dif_neg hN]

/--
The public terminal-sector conclusion for the intrinsic classifier.  Its
only arithmetic premise is generalized Pell; Lemma 9.10 is proved above.
-/
theorem TerminalSectorStabilityStatement
    {C : ℝ} (hC : 0 ≤ C) (κ₀ A : ℕ) (K : ℝ)
    (hκ₀ : 2 ≤ κ₀) (hA : 1 ≤ A) (hK : 0 ≤ K)
    (hPell : PellInput.GeneralizedPellPolynomialBoxStatement) :
    UniformLittleOInBoundedRatioWindow C κ₀
      (sectorResidualMass A
        (boundedIntrinsicTerminalPredicate A K)
        .terminal) := by
  have hrank :=
    generalizedPell_implies_rankTerminalSector_uniformLittleO
      hC κ₀ A K hκ₀ hA hK hPell
  have hmass :=
    sectorResidualMass_rank_eq_intrinsic_fun A K
  rw [← hmass]
  exact hrank

/--
Curried form matching the historical Section 17 interface: the former
Lemma 17.30 bridge follows from generalized Pell alone.
-/
theorem intrinsicTerminalSectorStability
    {C : ℝ} (hC : 0 ≤ C) (κ₀ A : ℕ) (K : ℝ)
    (hκ₀ : 2 ≤ κ₀) (hA : 1 ≤ A) (hK : 0 ≤ K) :
    PropositionSixteenOne.TerminalSectorStabilityStatement
      C κ₀ A (boundedIntrinsicTerminalPredicate A K) := by
  intro hPell
  exact
    TerminalSectorStabilityStatement
      hC κ₀ A K hκ₀ hA hK hPell

/--
Source-exact `N^(7/4+o_{C,κ₀}(1))` terminal-mass estimate for the canonical
intrinsic classifier.  Generalized Pell controls the rank-defined population;
the Lemma 9.10 transport is proved internally.
-/
theorem generalizedPell_implies_intrinsicTerminalSector_uniformSevenFourths
    {C : ℝ} (hC : 0 ≤ C) (κ₀ A : ℕ) (K : ℝ)
    (hκ₀ : 2 ≤ κ₀) (hA : 1 ≤ A) (hK : 0 ≤ K)
    (hPell : PellInput.GeneralizedPellPolynomialBoxStatement) :
    BoundedRatioSmallProductSector.UniformSevenFourthsInBoundedRatioWindow
      C κ₀
      (sectorResidualMass A
        (boundedIntrinsicTerminalPredicate A K)
        .terminal) := by
  rw [←
    sectorResidualMass_rank_eq_intrinsic_fun A K]
  exact
    generalizedPell_implies_rankTerminalSector_uniformSevenFourths
      hC κ₀ A K hκ₀ hA hK hPell

end

end BoundedRatioTerminalSummation
end PaperC
