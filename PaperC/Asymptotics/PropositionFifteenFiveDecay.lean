import PaperC.Arithmetic.BalasubramanianShoreyMaximum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option maxHeartbeats 1600000

/-!
# Proposition 15.5: decay of the exceptional high-zone envelope

The Balasubramanian--Shorey gap is of order

`(L / log L) * (log log L - log log log L - θ)`.

This file proves directly, without any additional bridge, that this gap
absorbs both the generalized-Pell counting loss `exp(K L / log L)` and the
linear number of dyadic blocks.  The final theorem is the precise
exceptional envelope needed in Proposition 15.5.
-/

namespace PaperC
namespace PropositionFifteenFiveDecay

open Filter
open scoped Topology

noncomputable section

open BalasubramanianShoreyInput

/--
The parenthesized factor in the exact formula for the
Balasubramanian--Shorey gap tends to infinity.
-/
theorem gapFactor_tendsto_atTop (θ : ℝ) :
    Tendsto
      (fun k : ℕ =>
        Real.log (Real.log (k : ℝ)) -
          Real.log (Real.log (Real.log (k : ℝ))) - θ)
      atTop atTop := by
  have hlog :
      Tendsto (fun k : ℕ => Real.log (k : ℝ))
        atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog :
      Tendsto (fun k : ℕ => Real.log (Real.log (k : ℝ)))
        atTop atTop :=
    Real.tendsto_log_atTop.comp hlog
  have hratio :
      Tendsto
        (fun k : ℕ =>
          Real.log (Real.log (Real.log (k : ℝ))) /
            Real.log (Real.log (k : ℝ)))
        atTop (𝓝 0) := by
    convert
        Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
          hloglog
      using 1
    simp [Function.comp_def]
  refine tendsto_atTop.2 ?_
  intro A
  have hratioHalf :
      ∀ᶠ k : ℕ in atTop,
        Real.log (Real.log (Real.log (k : ℝ))) /
            Real.log (Real.log (k : ℝ)) <
          (1 / 2 : ℝ) :=
    hratio.eventually (Iio_mem_nhds (by norm_num))
  have hlarge :
      ∀ᶠ k : ℕ in atTop,
        2 * (|A| + |θ| + 1) ≤
          Real.log (Real.log (k : ℝ)) :=
    hloglog.eventually
      (eventually_ge_atTop (2 * (|A| + |θ| + 1)))
  filter_upwards [hratioHalf, hlarge] with k hkRatio hkLarge
  have hfactorPos :
      0 < Real.log (Real.log (k : ℝ)) := by
    have hsumPos : 0 < |A| + |θ| + 1 := by positivity
    linarith
  have hlogloglog :
      Real.log (Real.log (Real.log (k : ℝ))) ≤
        Real.log (Real.log (k : ℝ)) / 2 := by
    have h :=
      (div_le_iff₀ hfactorPos).mp hkRatio.le
    nlinarith
  have hA : A ≤ |A| := le_abs_self A
  have hθ : θ ≤ |θ| := le_abs_self θ
  linarith

/--
For a fixed coefficient `K`, the gap eventually dominates the two losses
that occur in the high-zone sum: twice the Pell exponent and three
logarithms for the dyadic-block count.
-/
theorem gap_ge_pell_and_log_eventually
    (θ K : ℝ) (hK : 0 ≤ K) :
    ∃ L₀ : ℕ, ∀ L ≥ L₀,
      (2 * K / Real.log 2) *
            ((L : ℝ) / Real.log (L : ℝ)) +
          3 * Real.log (L : ℝ) / Real.log 2 ≤
        gap (L + 1) θ := by
  have hlogTwo : 0 < Real.log (2 : ℝ) :=
    Real.log_pos one_lt_two
  let A : ℝ := 4 * K / Real.log 2 + 1
  have hfactor :
      ∀ᶠ k : ℕ in atTop,
        A ≤
          Real.log (Real.log (k : ℝ)) -
            Real.log (Real.log (Real.log (k : ℝ))) - θ :=
    (gapFactor_tendsto_atTop θ).eventually
      (eventually_ge_atTop A)
  have hfactorSucc :
      ∀ᶠ L : ℕ in atTop,
        A ≤
          Real.log (Real.log (((L + 1 : ℕ) : ℝ))) -
            Real.log
              (Real.log (Real.log (((L + 1 : ℕ) : ℝ)))) - θ := by
    obtain ⟨k₀, hk₀⟩ := eventually_atTop.mp hfactor
    filter_upwards [eventually_ge_atTop k₀] with L hL
    exact hk₀ (L + 1) (hL.trans (Nat.le_succ L))
  have hlogSqRaw :
      ∀ᶠ L : ℕ in atTop,
        ‖Real.log (L : ℝ) ^ 2‖ ≤
          (Real.log 2 / 6) * ‖(L : ℝ)‖ :=
    tendsto_natCast_atTop_atTop.eventually
      (Real.isLittleO_pow_log_id_atTop.bound
        (div_pos hlogTwo (by norm_num)))
  have heventually :
      ∀ᶠ L : ℕ in atTop,
        (2 * K / Real.log 2) *
              ((L : ℝ) / Real.log (L : ℝ)) +
            3 * Real.log (L : ℝ) / Real.log 2 ≤
          gap (L + 1) θ := by
    filter_upwards
      [hfactorSucc, hlogSqRaw, eventually_ge_atTop 2] with
        L hfactorL hlogSq hL
    have hLpos : 0 < (L : ℝ) := by positivity
    have hlogLpos : 0 < Real.log (L : ℝ) :=
      Real.log_pos (by exact_mod_cast hL)
    have hsuccPos : 0 < (((L + 1 : ℕ) : ℝ)) := by positivity
    have hlogSuccPos :
        0 < Real.log (((L + 1 : ℕ) : ℝ)) :=
      Real.log_pos (by
        exact_mod_cast (show 1 < L + 1 by omega))
    have hsuccLeSqNat : L + 1 ≤ L * L := by
      calc
        L + 1 ≤ 2 * L := by omega
        _ ≤ L * L := by
          simpa [mul_comm] using Nat.mul_le_mul_left L hL
    have hsuccLeSq :
        (((L + 1 : ℕ) : ℝ)) ≤ (L : ℝ) * (L : ℝ) := by
      exact_mod_cast hsuccLeSqNat
    have hlogSucc :
        Real.log (((L + 1 : ℕ) : ℝ)) ≤
          2 * Real.log (L : ℝ) := by
      calc
        Real.log (((L + 1 : ℕ) : ℝ)) ≤
            Real.log ((L : ℝ) * (L : ℝ)) :=
          Real.log_le_log hsuccPos hsuccLeSq
        _ = 2 * Real.log (L : ℝ) := by
          rw [Real.log_mul (ne_of_gt hLpos) (ne_of_gt hLpos)]
          ring
    have hlogSq' :
        Real.log (L : ℝ) ^ 2 ≤
          (Real.log 2 / 6) * (L : ℝ) := by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
        Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)] at hlogSq
      exact hlogSq
    have hhalf :
        (1 / 2 : ℝ) *
              ((L : ℝ) / Real.log (L : ℝ)) ≤
            (((L + 1 : ℕ) : ℝ)) /
              Real.log (((L + 1 : ℕ) : ℝ)) := by
      rw [le_div_iff₀ hlogSuccPos]
      calc
        (1 / 2 : ℝ) *
              ((L : ℝ) / Real.log (L : ℝ)) *
              Real.log (((L + 1 : ℕ) : ℝ)) ≤
            (1 / 2 : ℝ) *
              ((L : ℝ) / Real.log (L : ℝ)) *
              (2 * Real.log (L : ℝ)) := by
          gcongr
        _ = (L : ℝ) := by field_simp
        _ ≤ (((L + 1 : ℕ) : ℝ)) := by norm_num
    have hlogTerm :
        3 * Real.log (L : ℝ) / Real.log 2 ≤
            (((L + 1 : ℕ) : ℝ)) /
              Real.log (((L + 1 : ℕ) : ℝ)) := by
      rw [le_div_iff₀ hlogSuccPos]
      calc
        (3 * Real.log (L : ℝ) / Real.log 2) *
              Real.log (((L + 1 : ℕ) : ℝ)) ≤
            (3 * Real.log (L : ℝ) / Real.log 2) *
              (2 * Real.log (L : ℝ)) := by
          gcongr
        _ = (6 / Real.log 2) *
              Real.log (L : ℝ) ^ 2 := by ring
        _ ≤ (L : ℝ) := by
          rw [div_mul_eq_mul_div, div_le_iff₀ hlogTwo]
          nlinarith [hlogSq']
        _ ≤ (((L + 1 : ℕ) : ℝ)) := by norm_num
    have hquotNonneg :
        0 ≤ (((L + 1 : ℕ) : ℝ)) /
            Real.log (((L + 1 : ℕ) : ℝ)) := by positivity
    have hA_nonneg : 0 ≤ A := by
      dsimp only [A]
      positivity
    have hgapFormula :
        gap (L + 1) θ =
          ((((L + 1 : ℕ) : ℝ)) /
              Real.log (((L + 1 : ℕ) : ℝ))) *
            (Real.log (Real.log (((L + 1 : ℕ) : ℝ))) -
              Real.log
                (Real.log (Real.log (((L + 1 : ℕ) : ℝ)))) - θ) :=
      gap_eq (ne_of_gt hlogSuccPos)
    rw [hgapFormula]
    calc
      (2 * K / Real.log 2) *
              ((L : ℝ) / Real.log (L : ℝ)) +
            3 * Real.log (L : ℝ) / Real.log 2 ≤
          (4 * K / Real.log 2) *
              ((((L + 1 : ℕ) : ℝ)) /
                Real.log (((L + 1 : ℕ) : ℝ))) +
            (((L + 1 : ℕ) : ℝ)) /
                Real.log (((L + 1 : ℕ) : ℝ)) := by
        have hcoef : 0 ≤ 4 * K / Real.log 2 := by positivity
        have hfirst :=
          mul_le_mul_of_nonneg_left hhalf hcoef
        have hfirst' :
            (2 * K / Real.log 2) *
                ((L : ℝ) / Real.log (L : ℝ)) ≤
              (4 * K / Real.log 2) *
                ((((L + 1 : ℕ) : ℝ)) /
                  Real.log (((L + 1 : ℕ) : ℝ))) := by
          calc
            (2 * K / Real.log 2) *
                  ((L : ℝ) / Real.log (L : ℝ)) =
                (4 * K / Real.log 2) *
                  ((1 / 2 : ℝ) *
                    ((L : ℝ) / Real.log (L : ℝ))) := by ring
            _ ≤
                (4 * K / Real.log 2) *
                  ((((L + 1 : ℕ) : ℝ)) /
                    Real.log (((L + 1 : ℕ) : ℝ))) :=
              hfirst
        exact add_le_add hfirst' hlogTerm
      _ = A *
            ((((L + 1 : ℕ) : ℝ)) /
              Real.log (((L + 1 : ℕ) : ℝ))) := by
        dsimp only [A]
        ring
      _ ≤
          ((((L + 1 : ℕ) : ℝ)) /
              Real.log (((L + 1 : ℕ) : ℝ))) *
            (Real.log (Real.log (((L + 1 : ℕ) : ℝ))) -
              Real.log
                (Real.log (Real.log (((L + 1 : ℕ) : ℝ)))) - θ) := by
        rw [mul_comm A]
        exact mul_le_mul_of_nonneg_left hfactorL hquotNonneg
  exact eventually_atTop.mp heventually

/--
The complete exceptional high-zone envelope tends to zero.  The factor
`exp(K L / log L)` is the Lemma 15.3 counting loss, `L` bounds the number
of dyadic blocks, and the real power of two is the probability gain supplied
by the Balasubramanian--Shorey gap.
-/
theorem highZoneExceptionalEnvelope_tendsto_zero
    (θ K : ℝ) (hK : 0 ≤ K) :
    Tendsto
      (fun L : ℕ =>
        (L : ℝ) *
          Real.exp
            (K * (L : ℝ) / Real.log (L : ℝ)) *
          (2 : ℝ) ^ (1 - gap (L + 1) θ))
      atTop (𝓝 0) := by
  obtain ⟨L₀, hgap⟩ :=
    gap_ge_pell_and_log_eventually θ K hK
  have hupper :
      ∀ᶠ L : ℕ in atTop,
        (L : ℝ) *
            Real.exp
              (K * (L : ℝ) / Real.log (L : ℝ)) *
            (2 : ℝ) ^ (1 - gap (L + 1) θ) ≤
          2 / (L : ℝ) := by
    filter_upwards [eventually_ge_atTop (max L₀ 2)] with L hL
    have hL₀ : L₀ ≤ L := (le_max_left L₀ 2).trans hL
    have hLtwo : 2 ≤ L := (le_max_right L₀ 2).trans hL
    have hLpos : 0 < (L : ℝ) := by positivity
    have hlogLpos : 0 < Real.log (L : ℝ) :=
      Real.log_pos (by exact_mod_cast hLtwo)
    have hlogTwo : 0 < Real.log (2 : ℝ) :=
      Real.log_pos one_lt_two
    have htNonneg :
        0 ≤ K * (L : ℝ) / Real.log (L : ℝ) := by
      positivity
    have hgapScaled :
        2 * K * ((L : ℝ) / Real.log (L : ℝ)) +
              3 * Real.log (L : ℝ) ≤
            gap (L + 1) θ * Real.log 2 := by
      calc
        2 * K * ((L : ℝ) / Real.log (L : ℝ)) +
              3 * Real.log (L : ℝ) =
            ((2 * K / Real.log 2) *
                ((L : ℝ) / Real.log (L : ℝ)) +
              3 * Real.log (L : ℝ) / Real.log 2) *
                Real.log 2 := by
          field_simp [ne_of_gt hlogTwo]
        _ ≤ gap (L + 1) θ * Real.log 2 :=
          mul_le_mul_of_nonneg_right (hgap L hL₀) hlogTwo.le
    have hgapScaled' :
        2 * (K * (L : ℝ) / Real.log (L : ℝ)) +
              3 * Real.log (L : ℝ) ≤
            gap (L + 1) θ * Real.log 2 := by
      convert hgapScaled using 1
      ring
    have hexponent :
        Real.log (L : ℝ) +
              K * (L : ℝ) / Real.log (L : ℝ) +
              Real.log 2 * (1 - gap (L + 1) θ) ≤
            Real.log 2 - Real.log (L : ℝ) := by
      nlinarith [hgapScaled', hlogLpos.le]
    have hrexp :
        (L : ℝ) *
              Real.exp
                (K * (L : ℝ) / Real.log (L : ℝ)) *
              (2 : ℝ) ^ (1 - gap (L + 1) θ) =
            Real.exp
              (Real.log (L : ℝ) +
                K * (L : ℝ) / Real.log (L : ℝ) +
                Real.log 2 * (1 - gap (L + 1) θ)) := by
      calc
        (L : ℝ) *
              Real.exp
                (K * (L : ℝ) / Real.log (L : ℝ)) *
              (2 : ℝ) ^ (1 - gap (L + 1) θ) =
            Real.exp (Real.log (L : ℝ)) *
              Real.exp
                (K * (L : ℝ) / Real.log (L : ℝ)) *
              Real.exp
                (Real.log 2 * (1 - gap (L + 1) θ)) := by
          rw [Real.exp_log hLpos,
            Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
        _ = Real.exp
              (Real.log (L : ℝ) +
                K * (L : ℝ) / Real.log (L : ℝ) +
                Real.log 2 * (1 - gap (L + 1) θ)) := by
          rw [← Real.exp_add, ← Real.exp_add]
    rw [hrexp]
    calc
      Real.exp
          (Real.log (L : ℝ) +
            K * (L : ℝ) / Real.log (L : ℝ) +
            Real.log 2 * (1 - gap (L + 1) θ)) ≤
          Real.exp (Real.log 2 - Real.log (L : ℝ)) :=
        Real.exp_le_exp.mpr hexponent
      _ = 2 / (L : ℝ) := by
        rw [Real.exp_sub, Real.exp_log (by norm_num),
          Real.exp_log hLpos]
  have hnonneg :
      ∀ L : ℕ,
        0 ≤
          (L : ℝ) *
            Real.exp
              (K * (L : ℝ) / Real.log (L : ℝ)) *
            (2 : ℝ) ^ (1 - gap (L + 1) θ) := by
    intro L
    positivity
  exact squeeze_zero'
    (Eventually.of_forall hnonneg) hupper
    (tendsto_const_div_atTop_nhds_zero_nat 2)

end

end PropositionFifteenFiveDecay
end PaperC
