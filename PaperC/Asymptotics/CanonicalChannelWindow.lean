import PaperC.Arithmetic.CanonicalChannel
import PaperC.Asymptotics.ExpSqrtLog
import PaperC.Probability.CriticalRunWindow

/-!
# Canonical channels in the critical run-length window

This module supplies the uniform asymptotic threshold used in Lemma 5.2.
For fixed `A` and `C`, the determinant condition

`4 * ((L + 1) ^ A) ^ 2 * (L + 1) < x`

holds for every `x ∈ [N,2N)` once `N` is sufficiently large and
`|L - log₂ N| ≤ C`.  Consequently the finite set of reduced channel
candidates has cardinality at most one, uniformly in `x` and `y`.
-/

namespace PaperC
namespace CanonicalChannelWindow

/--
The two extra powers of `B + 1` absorb the numerical factor `4`.
The strict inequality comes from replacing `B` by `B + 1` in the positive
power `e`.
-/
theorem four_mul_pow_lt_succ_pow_add_two
    (B e : ℕ) (hB : 0 < B) (he : 0 < e) :
    4 * B ^ e < (B + 1) ^ (e + 2) := by
  have hpow : B ^ e < (B + 1) ^ e :=
    Nat.pow_lt_pow_left (Nat.lt_succ_self B) he.ne'
  have hfour : 4 ≤ (B + 1) ^ 2 := by
    have htwo : 2 ≤ B + 1 := by omega
    nlinarith
  calc
    4 * B ^ e < 4 * (B + 1) ^ e :=
      (Nat.mul_lt_mul_left (by omega : 0 < 4)).2 hpow
    _ ≤ (B + 1) ^ 2 * (B + 1) ^ e :=
      Nat.mul_le_mul_right ((B + 1) ^ e) hfour
    _ = (B + 1) ^ (2 + e) := (pow_add (B + 1) 2 e).symm
    _ = (B + 1) ^ (e + 2) :=
      congrArg (fun n : ℕ ↦ (B + 1) ^ n) (by omega)

/--
Numerical form matched to the determinant threshold when the channel height
is `B ^ A`.
-/
theorem four_mul_height_sq_mul_lt_succ_pow
    (B A : ℕ) (hB : 0 < B) :
    4 * (B ^ A) ^ 2 * B < (B + 1) ^ (2 * A + 3) := by
  have hcore :=
    four_mul_pow_lt_succ_pow_add_two B (2 * A + 1) hB (by omega)
  calc
    4 * (B ^ A) ^ 2 * B = 4 * (B ^ (A * 2) * B) := by
      rw [← pow_mul, mul_assoc]
    _ = 4 * B ^ (A * 2 + 1) := by
      rw [← pow_succ]
    _ = 4 * B ^ (2 * A + 1) := by
      congr 2
      omega
    _ < (B + 1) ^ ((2 * A + 1) + 2) := hcore
    _ = (B + 1) ^ (2 * A + 3) :=
      congrArg (fun n : ℕ ↦ (B + 1) ^ n) (by omega)

/--
Uniform form of the determinant threshold in the manuscript's literal
critical run-length window.
-/
theorem determinantThreshold_eventually
    {C : ℝ} (hC : 0 ≤ C) (A : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L,
      CriticalRunWindow.InRunLengthWindow C N L →
      4 * ((L + 1) ^ A) ^ 2 * (L + 1) < N := by
  have hupperNonneg : 0 ≤ CriticalRunWindow.upperConstant :=
    (CriticalRunWindow.lowerConstant_pos.trans
      CriticalRunWindow.lowerConstant_lt_upperConstant).le
  obtain ⟨Nwindow, hwindow⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  obtain ⟨Npower, hpower⟩ :=
    ExpSqrtLog.linear_log_add_one_pow_le_nat_eventually
      CriticalRunWindow.upperConstant hupperNonneg
      (2 * A + 3) (by omega)
  refine ⟨max Nwindow Npower, ?_⟩
  intro N hN L hrun
  have hNwindow : Nwindow ≤ N :=
    (le_max_left Nwindow Npower).trans hN
  have hNpower : Npower ≤ N :=
    (le_max_right Nwindow Npower).trans hN
  have hfirstMoment := hwindow N hNwindow L hrun
  have hlengthUpper :
      (((L + 1 : ℕ) : ℝ) ≤
        CriticalRunWindow.upperConstant * Real.log N) :=
    hfirstMoment.1.2.2.2
  have hpowerReal :=
    hpower N hNpower (L + 1) hlengthUpper
  have hpowerNat :
      ((L + 1) + 1) ^ (2 * A + 3) ≤ N := by
    exact_mod_cast hpowerReal
  exact
    (four_mul_height_sq_mul_lt_succ_pow (L + 1) A (by omega)).trans_le
      hpowerNat

/--
Lemma 5.2, uniform asymptotic form: for fixed `A,C`, sufficiently far in the
critical window there is at most one positive reduced pair of height at most
`(L+1)^A` satisfying the channel inequality.  The threshold is independent
of both `x` in the dyadic block and `y`.
-/
theorem card_reducedChannelCandidates_le_one_eventually
    {C : ℝ} (hC : 0 ≤ C) (A : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L,
      CriticalRunWindow.InRunLengthWindow C N L →
      ∀ x ∈ dyadicBlock N, ∀ y,
        (reducedChannelCandidates
          x y (L + 1) ((L + 1) ^ A)).card ≤ 1 := by
  obtain ⟨N₀, hthreshold⟩ :=
    determinantThreshold_eventually hC A
  refine ⟨N₀, ?_⟩
  intro N hN L hrun x hx y
  have hxLower : N ≤ x := by
    exact (Finset.mem_Ico.mp (by simpa [dyadicBlock] using hx)).1
  exact
    card_reducedChannelCandidates_le_one
      ((hthreshold N hN L hrun).trans_le hxLower)

end CanonicalChannelWindow
end PaperC
