import PaperC.Asymptotics.PolynomialZoneCritical
import Mathlib.Analysis.SpecificLimits.Basic

set_option maxHeartbeats 1200000

/-!
# Summing the polynomial zone in Lemma 15.2

This module closes the summation step left after the pointwise estimate
in `PolynomialZoneCritical`.  It uses exactly the manuscript band

`L + 2 < x ≤ 2 L²`

and proves that its total start probability tends to zero under the two
registered external inputs used by Lemma 15.2: Laishram--Shorey and PNT.
-/

namespace PaperC
namespace PolynomialZoneSum

open PolynomialZoneCritical
open PolynomialZoneLargePrimes
open LaishramShoreyInput
open PrimeNumberTheoremInput
open Filter

noncomputable section

/-- The integer starts in the polynomial band of Lemma 15.2. -/
def polynomialZoneStarts (L : ℕ) : Finset ℕ :=
  Finset.Ioc (L + 2) (2 * L ^ 2)

@[simp]
theorem mem_polynomialZoneStarts {L x : ℕ} :
    x ∈ polynomialZoneStarts L ↔
      L + 2 < x ∧ x ≤ 2 * L ^ 2 := by
  simp [polynomialZoneStarts]

/-- The rational total probability of starts in the polynomial band. -/
noncomputable def polynomialZoneProbabilityMassQ (L : ℕ) : ℚ :=
  ∑ x ∈ polynomialZoneStarts L, startProbability x L x

/-- Real-valued form of the same probability mass. -/
noncomputable def polynomialZoneProbabilityMass (L : ℕ) : ℝ :=
  polynomialZoneProbabilityMassQ L

theorem card_polynomialZoneStarts_le (L : ℕ) :
    (polynomialZoneStarts L).card ≤ 2 * L ^ 2 := by
  rw [polynomialZoneStarts, Nat.card_Ioc]
  omega

theorem polynomialZoneProbabilityMassQ_nonneg (L : ℕ) :
    0 ≤ polynomialZoneProbabilityMassQ L := by
  unfold polynomialZoneProbabilityMassQ
  exact Finset.sum_nonneg fun x _ ↦
    BadStartMass.startProbability_nonneg x L x

theorem polynomialZoneProbabilityMass_nonneg (L : ℕ) :
    0 ≤ polynomialZoneProbabilityMass L := by
  unfold polynomialZoneProbabilityMass
  exact Rat.cast_nonneg.mpr
    (polynomialZoneProbabilityMassQ_nonneg L)

/--
The pointwise estimate (15.1), rewritten as `2 / 2^R` for any common
rank `R` below the exact Laishram--Shorey rank.
-/
theorem startProbability_le_two_div_pow_of_rank
    (hLS : LaishramShoreyStatement)
    {x L R : ℕ}
    (hx : x ∈ polynomialZoneStarts L)
    (hR : R ≤ polynomialVertexRank (L + 1)) :
    startProbability x L x ≤
      (2 : ℚ) / (2 : ℚ) ^ R := by
  classical
  have hleft := (mem_polynomialZoneStarts.mp hx).1
  have hright := (mem_polynomialZoneStarts.mp hx).2
  have hpoint :=
    laishramShorey_startProbability_bound
      hLS hleft hright
  have hpoint' :
      startProbability x L x ≤
        (2 : ℚ) ^
            (L + 1 - polynomialVertexRank (L + 1)) /
          (2 : ℚ) ^ L := by
    simpa [polynomialVertexRank, polynomialPrimeExcess] using
      hpoint
  have hrank :
      polynomialVertexRank (L + 1) ≤ L + 1 := by
    have hlower :=
      laishramShorey_completeWindow_lower_bound
        hLS hleft hright
    have hcard :
        (nondefectiveWindowIndices
          (L + 1) (x - 1) (L + 1)).card ≤ L + 1 := by
      calc
        (nondefectiveWindowIndices
            (L + 1) (x - 1) (L + 1)).card ≤
            (Finset.range (L + 1)).card := by
          exact Finset.card_filter_le _ _
        _ = L + 1 := by simp
    exact hlower.trans hcard
  have hrewrite :
      (2 : ℚ) ^
            (L + 1 - polynomialVertexRank (L + 1)) /
          (2 : ℚ) ^ L =
        (2 : ℚ) /
          (2 : ℚ) ^ polynomialVertexRank (L + 1) := by
    rw [div_eq_div_iff]
    · calc
        (2 : ℚ) ^
              (L + 1 - polynomialVertexRank (L + 1)) *
            (2 : ℚ) ^ polynomialVertexRank (L + 1) =
            (2 : ℚ) ^
              ((L + 1 - polynomialVertexRank (L + 1)) +
                polynomialVertexRank (L + 1)) := by
              rw [pow_add]
        _ = (2 : ℚ) ^ (L + 1) := by
              congr 1
              omega
        _ = (2 : ℚ) * (2 : ℚ) ^ L := by
              rw [pow_succ']
    · positivity
    · positivity
  rw [hrewrite] at hpoint'
  exact hpoint'.trans
    (div_le_div_of_nonneg_left
      (by norm_num)
      (by positivity)
      (pow_le_pow_right₀ (by norm_num) hR))

/-- Finite common-rank sum bound over the complete polynomial band. -/
theorem polynomialZoneProbabilityMassQ_le_rankEnvelope
    (hLS : LaishramShoreyStatement)
    {L R : ℕ}
    (hR : R ≤ polynomialVertexRank (L + 1)) :
    polynomialZoneProbabilityMassQ L ≤
      (4 * L ^ 2 : ℚ) / (2 : ℚ) ^ R := by
  calc
    polynomialZoneProbabilityMassQ L ≤
        ∑ x ∈ polynomialZoneStarts L,
          (2 : ℚ) / (2 : ℚ) ^ R := by
      apply Finset.sum_le_sum
      intro x hx
      exact startProbability_le_two_div_pow_of_rank
        hLS hx hR
    _ =
        ((polynomialZoneStarts L).card : ℚ) *
          ((2 : ℚ) / (2 : ℚ) ^ R) := by
      simp
    _ ≤
        (2 * L ^ 2 : ℚ) *
          ((2 : ℚ) / (2 : ℚ) ^ R) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast card_polynomialZoneStarts_le L
      · positivity
    _ = (4 * L ^ 2 : ℚ) / (2 : ℚ) ^ R := by
      ring

/-- Real form of the finite common-rank sum bound. -/
theorem polynomialZoneProbabilityMass_le_rankEnvelope
    (hLS : LaishramShoreyStatement)
    {L R : ℕ}
    (hR : R ≤ polynomialVertexRank (L + 1)) :
    polynomialZoneProbabilityMass L ≤
      (4 : ℝ) * (L : ℝ) ^ 2 / (2 : ℝ) ^ R := by
  have hq :=
    polynomialZoneProbabilityMassQ_le_rankEnvelope
      hLS hR
  have hcast := (Rat.cast_le (K := ℝ)).2 hq
  push_cast at hcast
  simpa [polynomialZoneProbabilityMass] using hcast

/-- A convenient logarithmic common rank for the polynomial zone. -/
def polynomialZoneLogRank (L : ℕ) : ℕ :=
  4 * Nat.log 2 L

/--
The source-level PNT eventually makes the exact polynomial-zone rank at
least `4 log₂ L`.  This is a derived estimate, not a new bridge.
-/
theorem primeNumberTheorem_implies_polynomialZoneLogRank
    (hpnt : PrimeNumberTheoremStatement) :
    ∃ L₀ : ℕ, ∀ L ≥ L₀,
      polynomialZoneLogRank L ≤
        polynomialVertexRank (L + 1) := by
  obtain ⟨B₀, hB₀⟩ :=
    primeNumberTheorem_implies_polynomialVertexRank_lower hpnt
  have hlogSquareRaw :
      ∀ᶠ B : ℕ in atTop,
        ‖Real.log (B : ℝ) ^ 2‖ ≤
          (Real.log 2 / 128) * ‖(B : ℝ)‖ :=
    tendsto_natCast_atTop_atTop.eventually
      (Real.isLittleO_pow_log_id_atTop.bound
        (div_pos (Real.log_pos one_lt_two) (by norm_num)))
  obtain ⟨B₁, hB₁⟩ :=
    eventually_atTop.mp hlogSquareRaw
  refine ⟨max 1 (max B₀ B₁), ?_⟩
  intro L hL
  have hLone : 1 ≤ L :=
    (le_max_left 1 (max B₀ B₁)).trans hL
  have hB₀' : B₀ ≤ L + 1 := by
    have := (le_max_left B₀ B₁).trans
      ((le_max_right 1 (max B₀ B₁)).trans hL)
    omega
  have hB₁' : B₁ ≤ L + 1 := by
    have := (le_max_right B₀ B₁).trans
      ((le_max_right 1 (max B₀ B₁)).trans hL)
    omega
  have hLpos : (0 : ℝ) < (L : ℝ) := by
    exact_mod_cast hLone
  have hBtwo : 2 ≤ L + 1 := by omega
  have hBpos : (0 : ℝ) < ((L + 1 : ℕ) : ℝ) := by
    positivity
  have hlogBpos :
      0 < Real.log ((L + 1 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast hBtwo)
  have hlogTwoPos : 0 < Real.log 2 :=
    Real.log_pos one_lt_two
  have hpowNat :
      2 ^ Nat.log 2 L ≤ L :=
    Nat.pow_log_le_self 2 (by omega)
  have hpowReal :
      ((2 ^ Nat.log 2 L : ℕ) : ℝ) ≤ (L : ℝ) := by
    exact_mod_cast hpowNat
  have hnatLog :
      (Nat.log 2 L : ℝ) ≤
        Real.log (L : ℝ) / Real.log 2 := by
    have hlogs :=
      Real.log_le_log
        (by positivity :
          (0 : ℝ) < ((2 ^ Nat.log 2 L : ℕ) : ℝ))
        hpowReal
    rw [Nat.cast_pow, Real.log_pow] at hlogs
    rw [le_div_iff₀ hlogTwoPos]
    simpa [mul_comm] using hlogs
  have hlogMono :
      Real.log (L : ℝ) ≤
        Real.log ((L + 1 : ℕ) : ℝ) := by
    apply Real.log_le_log hLpos
    exact_mod_cast (Nat.le_succ L)
  have hlogSquare :=
    hB₁ (L + 1) hB₁'
  rw [Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg _),
    Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg _)] at hlogSquare
  have hanalytic :
      (4 : ℝ) *
          Real.log ((L + 1 : ℕ) : ℝ) / Real.log 2 ≤
        (1 / 32 : ℝ) *
          (((L + 1 : ℕ) : ℝ) /
            Real.log ((L + 1 : ℕ) : ℝ)) := by
    rw [show
      (1 / 32 : ℝ) *
          (((L + 1 : ℕ) : ℝ) /
            Real.log ((L + 1 : ℕ) : ℝ)) =
        ((1 / 32 : ℝ) * ((L + 1 : ℕ) : ℝ)) /
          Real.log ((L + 1 : ℕ) : ℝ) by ring]
    rw [div_le_div_iff₀ hlogTwoPos hlogBpos]
    nlinarith
  have hlogRankReal :
      (polynomialZoneLogRank L : ℝ) ≤
        (1 / 32 : ℝ) *
          (((L + 1 : ℕ) : ℝ) /
            Real.log ((L + 1 : ℕ) : ℝ)) := by
    calc
      (polynomialZoneLogRank L : ℝ) =
          4 * (Nat.log 2 L : ℝ) := by
        simp [polynomialZoneLogRank]
      _ ≤
          4 *
            (Real.log (L : ℝ) / Real.log 2) := by
        nlinarith
      _ ≤
          4 *
            (Real.log ((L + 1 : ℕ) : ℝ) /
              Real.log 2) := by
        exact mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right hlogMono hlogTwoPos.le)
          (by norm_num)
      _ ≤
          (1 / 32 : ℝ) *
            (((L + 1 : ℕ) : ℝ) /
              Real.log ((L + 1 : ℕ) : ℝ)) :=
        by
          convert hanalytic using 1
          ring
  have hrank :=
    hB₀ (L + 1) hB₀'
  exact_mod_cast hlogRankReal.trans hrank

/-- The explicit elementary envelope used after the PNT rank estimate. -/
def polynomialZonePowerEnvelope (L : ℕ) : ℝ :=
  (4 : ℝ) * (L : ℝ) ^ 2 /
    (2 : ℝ) ^ polynomialZoneLogRank L

/-- The logarithmic-rank envelope tends to zero. -/
theorem polynomialZonePowerEnvelope_tendsto_zero :
    Tendsto polynomialZonePowerEnvelope atTop (nhds 0) := by
  have hcomparison :
      ∀ᶠ L : ℕ in atTop,
        polynomialZonePowerEnvelope L ≤
          (64 : ℝ) / (L : ℝ) ^ 2 := by
    filter_upwards [eventually_ge_atTop 1] with L hL
    have hLpos : (0 : ℝ) < (L : ℝ) := by
      exact_mod_cast hL
    have hlog :
        L < 2 ^ (Nat.log 2 L).succ :=
      Nat.lt_pow_succ_log_self (by norm_num) L
    have hLdouble :
        L ≤ 2 * 2 ^ Nat.log 2 L := by
      calc
        L ≤ 2 ^ (Nat.log 2 L).succ :=
          Nat.le_of_lt hlog
        _ = 2 * 2 ^ Nat.log 2 L := by
          rw [pow_succ']
    have hquarticNat :
        L ^ 4 ≤
          16 * 2 ^ polynomialZoneLogRank L := by
      calc
        L ^ 4 ≤
            (2 * 2 ^ Nat.log 2 L) ^ 4 :=
          Nat.pow_le_pow_left hLdouble 4
        _ = 16 * (2 ^ Nat.log 2 L) ^ 4 := by
          ring
        _ = 16 * 2 ^ polynomialZoneLogRank L := by
          simp only [polynomialZoneLogRank]
          rw [← pow_mul]
          congr 2
          omega
    have hquarticReal :
        (L : ℝ) ^ 4 ≤
          16 * (2 : ℝ) ^ polynomialZoneLogRank L := by
      exact_mod_cast hquarticNat
    have hdenPos :
        0 < (2 : ℝ) ^ polynomialZoneLogRank L := by
      positivity
    have hLfourPos : 0 < (L : ℝ) ^ 4 := by
      positivity
    have hinv :
        (1 : ℝ) /
            (2 : ℝ) ^ polynomialZoneLogRank L ≤
          16 / (L : ℝ) ^ 4 := by
      rw [div_le_div_iff₀ hdenPos hLfourPos]
      simpa using hquarticReal
    calc
      polynomialZonePowerEnvelope L =
          (4 * (L : ℝ) ^ 2) *
            ((1 : ℝ) /
              (2 : ℝ) ^ polynomialZoneLogRank L) := by
        simp [polynomialZonePowerEnvelope]
        ring
      _ ≤
          (4 * (L : ℝ) ^ 2) *
            (16 / (L : ℝ) ^ 4) :=
        mul_le_mul_of_nonneg_left hinv
          (by positivity)
      _ = (64 : ℝ) / (L : ℝ) ^ 2 := by
        field_simp
        ring
  have henvelopeNonneg :
      ∀ L, 0 ≤ polynomialZonePowerEnvelope L := by
    intro L
    exact div_nonneg
      (mul_nonneg (by norm_num) (sq_nonneg _))
      (pow_nonneg (by norm_num) _)
  have hden :
      Tendsto (fun L : ℕ ↦ (L : ℝ) ^ 2)
        atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp
      tendsto_natCast_atTop_atTop
  have hupper :
      Tendsto (fun L : ℕ ↦ (64 : ℝ) / (L : ℝ) ^ 2)
        atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hden
  exact squeeze_zero'
    (Eventually.of_forall henvelopeNonneg)
    hcomparison hupper

/--
Lemma 15.2: the complete probability mass of starts in the polynomial zone
is `o(1)`, conditional exactly on the registered Laishram--Shorey and PNT
statements.
-/
theorem polynomialZoneProbabilityMass_tendsto_zero
    (hLS : LaishramShoreyStatement)
    (hpnt : PrimeNumberTheoremStatement) :
    Tendsto polynomialZoneProbabilityMass atTop (nhds 0) := by
  obtain ⟨L₀, hL₀⟩ :=
    primeNumberTheorem_implies_polynomialZoneLogRank hpnt
  have hbound :
      ∀ᶠ L : ℕ in atTop,
        polynomialZoneProbabilityMass L ≤
          polynomialZonePowerEnvelope L := by
    filter_upwards [eventually_ge_atTop L₀] with L hL
    exact polynomialZoneProbabilityMass_le_rankEnvelope
      hLS (hL₀ L hL)
  exact squeeze_zero'
    (Eventually.of_forall
      polynomialZoneProbabilityMass_nonneg)
    hbound polynomialZonePowerEnvelope_tendsto_zero

end

end PolynomialZoneSum
end PaperC
