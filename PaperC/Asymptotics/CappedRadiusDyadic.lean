import PaperC.Analysis.RungeLogarithmicGrowth
import PaperC.Asymptotics.Uniform

/-!
# The dyadic Hamming loss is subpolynomial

The finite coding argument produces a factor `2^(D*t)`, where `t` is the
floored Runge radius.  This file records the exact logarithmic comparison
which turns every fixed power of that factor into at most `N`.
-/

namespace PaperC
namespace CappedRadiusDyadic

/--
Any fixed power of the dyadic loss attached to the capped Runge radius is
bounded by `N` as soon as `log H` dominates the corresponding fixed constant.

This is the finite inequality behind the `N^{o(1)}` contribution of the
Hamming factor in Proposition 3.2.
-/
theorem pow_two_cappedRadius_le
    {N H T D k : ℕ}
    (hN : 1 ≤ N)
    (hH : 2 ≤ H)
    (hT : 1 ≤ T)
    (hlogH :
      ((D * k : ℕ) : ℝ) * Real.log 2 ≤ 8 * Real.log H) :
    (((2 ^ (D * RungeLogarithmicGrowth.cappedRadius N H T) : ℕ) :
          ℝ) ^ k) ≤
      (N : ℝ) := by
  let t := RungeLogarithmicGrowth.cappedRadius N H T
  have hHpos : 0 < (H : ℝ) := by positivity
  have hcapNat : H ≤ 256 * T * H := by
    have hfactor : 1 ≤ 256 * T := by omega
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      Nat.mul_le_mul_right H hfactor
  have hlogMono :
      Real.log (H : ℝ) ≤ Real.log (256 * T * H : ℝ) := by
    apply Real.log_le_log hHpos
    exact_mod_cast hcapNat
  have hconstant :
      ((D * k : ℕ) : ℝ) * Real.log 2 ≤
        8 * Real.log (256 * T * H : ℝ) :=
    hlogH.trans (mul_le_mul_of_nonneg_left hlogMono (by norm_num))
  have htNonneg : 0 ≤ (t : ℝ) := by positivity
  have hscaled :
      (t : ℝ) * (((D * k : ℕ) : ℝ) * Real.log 2) ≤
        (t : ℝ) * (8 * Real.log (256 * T * H : ℝ)) :=
    mul_le_mul_of_nonneg_left hconstant htNonneg
  have hcap :
      (8 * t : ℝ) * Real.log (256 * T * H : ℝ) ≤
        Real.log N := by
    simpa only [t] using
      RungeLogarithmicGrowth.cappedRadius_log_condition hN (by omega) hT
  have hlogBound :
      Real.log
          ((((2 ^ (D * t) : ℕ) : ℝ) ^ k)) ≤
        Real.log (N : ℝ) := by
    calc
      Real.log ((((2 ^ (D * t) : ℕ) : ℝ) ^ k))
          = (t : ℝ) * (((D * k : ℕ) : ℝ) * Real.log 2) := by
              simp only [Real.log_pow, Nat.cast_ofNat, Nat.cast_pow]
              push_cast
              ring
      _ ≤ (t : ℝ) * (8 * Real.log (256 * T * H : ℝ)) := hscaled
      _ = (8 * t : ℝ) * Real.log (256 * T * H : ℝ) := by ring
      _ ≤ Real.log N := hcap
  exact
    (Real.log_le_log_iff
      (by positivity :
        0 < ((((2 ^ (D * t) : ℕ) : ℝ) ^ k)))
      (by exact_mod_cast (show 0 < N by omega))).mp hlogBound

/--
A purely natural-number sufficient condition: once `H` exceeds the fixed
threshold `2^(D*k)`, the `k`-th power of the Hamming loss is at most `N`.
-/
theorem pow_two_cappedRadius_le_of_threshold
    {N H T D k : ℕ}
    (hN : 1 ≤ N)
    (hH : 2 ≤ H)
    (hT : 1 ≤ T)
    (hthreshold : 2 ^ (D * k) ≤ H) :
    (((2 ^ (D * RungeLogarithmicGrowth.cappedRadius N H T) : ℕ) :
          ℝ) ^ k) ≤
      (N : ℝ) := by
  apply pow_two_cappedRadius_le hN hH hT
  have hpowPos : 0 < (((2 ^ (D * k) : ℕ) : ℝ)) := by positivity
  have hlogMono :
      Real.log (((2 ^ (D * k) : ℕ) : ℝ)) ≤ Real.log (H : ℝ) := by
    apply Real.log_le_log hpowPos
    exact_mod_cast hthreshold
  have hlogHpos : 0 < Real.log (H : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < H by omega)
  calc
    ((D * k : ℕ) : ℝ) * Real.log 2
        = Real.log (((2 ^ (D * k) : ℕ) : ℝ)) := by
          simp only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
    _ ≤ Real.log H := hlogMono
    _ ≤ 8 * Real.log H := by nlinarith

/--
Uniform `N^{o(1)}` form of the preceding finite estimate.  The only
asymptotic input is that the admissible values of `H` tend uniformly to
infinity; the cap parameter merely has to be eventually positive.
-/
theorem uniformSubpolynomialOn_two_cappedRadius
    (admissible : ℕ → ℕ → Prop)
    (T : ℕ → ℕ → ℕ)
    (D : ℕ)
    (hT :
      ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ H, admissible N H → 1 ≤ T N H)
    (hHdiverges :
      ∀ M : ℕ, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ H,
        admissible N H → M ≤ H) :
    UniformSubpolynomialOn admissible
      (fun N H =>
        ((2 ^ (D * RungeLogarithmicGrowth.cappedRadius N H (T N H)) :
            ℕ) : ℝ)) := by
  intro k hk
  rcases hT with ⟨NT, hNT⟩
  rcases hHdiverges (max 2 (2 ^ (D * k))) with ⟨NH, hNH⟩
  refine ⟨max 1 (max NT NH), ?_⟩
  intro N hN H hAdm
  have hNone : 1 ≤ N := le_trans (le_max_left 1 (max NT NH)) hN
  have hN_T : NT ≤ N :=
    le_trans (le_trans (le_max_left NT NH) (le_max_right 1 (max NT NH))) hN
  have hN_H : NH ≤ N :=
    le_trans (le_trans (le_max_right NT NH) (le_max_right 1 (max NT NH))) hN
  have hTpos : 1 ≤ T N H := hNT N hN_T H hAdm
  have hthresholds :
      max 2 (2 ^ (D * k)) ≤ H := hNH N hN_H H hAdm
  rw [abs_of_nonneg (by positivity)]
  exact
    pow_two_cappedRadius_le_of_threshold hNone
      ((le_max_left 2 (2 ^ (D * k))).trans hthresholds)
      hTpos
      ((le_max_right 2 (2 ^ (D * k))).trans hthresholds)

end CappedRadiusDyadic
end PaperC
