import PaperC.Arithmetic.WeightedChannelMass
import PaperC.Asymptotics.CriticalChannelPowers
import PaperC.Asymptotics.LinearPower

/-!
# Lemma 5.5 in the critical run-length window

The finite channel sum is first compressed to a polynomial factor times
`4^(L/2)`.  In the critical window the latter is at most a fixed
`C`-dependent constant times `N`, while the polynomial in `L` is uniformly
subpolynomial.  This yields the quantified `N^(1+o_C(1))` form of Lemma 5.5.
-/

namespace PaperC
namespace WeightedChannelMassCritical

/--
The explicit finite estimate can be compressed to one fourth-degree
polynomial envelope.  The numerical constant `46 = 40 + 6` records the
height-two and height-at-least-three contributions respectively.
-/
theorem weightedChannelMass_le_poly_four_pow_half
    (L : ℕ) :
    weightedChannelMass L ≤
      46 * (L + 1) ^ 4 * 4 ^ (L / 2) := by
  have hfinite :=
    weightedChannelMass_le_small_add_large L
  have hLB : L ≤ L + 1 := Nat.le_succ L
  have hBpos : 0 < L + 1 := Nat.succ_pos L
  have hBpow : L + 1 ≤ (L + 1) ^ 4 := by
    simpa using
      Nat.pow_le_pow_right hBpos (by omega : 1 ≤ 4)
  have hsmallBase : 4 * L + 1 ≤ 5 * (L + 1) := by
    omega
  have hsmallCoeff :
      8 * (4 * L + 1) ≤ 40 * (L + 1) ^ 4 := by
    calc
      8 * (4 * L + 1) ≤ 8 * (5 * (L + 1)) :=
        Nat.mul_le_mul_left 8 hsmallBase
      _ = 40 * (L + 1) := by ring
      _ ≤ 40 * (L + 1) ^ 4 :=
        Nat.mul_le_mul_left 40 hBpow
  have htwo : 2 * L ≤ 2 * (L + 1) :=
    Nat.mul_le_mul_left 2 hLB
  have honeSquare : 1 ≤ (L + 1) * (L + 1) := by
    have hpos : 0 < (L + 1) * (L + 1) :=
      Nat.mul_pos (Nat.succ_pos L) (Nat.succ_pos L)
    omega
  have hinner :
      (2 * L) * L + 1 ≤
        (2 * (L + 1)) * (L + 1) +
          (L + 1) * (L + 1) :=
    Nat.add_le_add
      (Nat.mul_le_mul htwo hLB) honeSquare
  have hfront :
      L * (2 * L) ≤ (L + 1) * (2 * (L + 1)) :=
    Nat.mul_le_mul hLB htwo
  have hlargeCoeff :
      L * (2 * L) * ((2 * L) * L + 1) ≤
        6 * (L + 1) ^ 4 := by
    calc
      L * (2 * L) * ((2 * L) * L + 1) ≤
          ((L + 1) * (2 * (L + 1))) *
            ((2 * (L + 1)) * (L + 1) +
              (L + 1) * (L + 1)) :=
        Nat.mul_le_mul hfront hinner
      _ = 6 * (L + 1) ^ 4 := by ring
  have hdiv : L / 3 ≤ L / 2 :=
    Nat.div_le_div_left (by omega) (by omega)
  have hpower :
      4 ^ (L / 3) ≤ 4 ^ (L / 2) :=
    Nat.pow_le_pow_right (by norm_num) hdiv
  calc
    weightedChannelMass L ≤
        8 * ((4 * L + 1) * 4 ^ (L / 2)) +
          L * (2 * L) *
            (((2 * L) * L + 1) * 4 ^ (L / 3)) :=
      by simpa [Nat.mul_assoc] using hfinite
    _ ≤ (40 * (L + 1) ^ 4) * 4 ^ (L / 2) +
          (6 * (L + 1) ^ 4) * 4 ^ (L / 2) := by
      apply Nat.add_le_add
      · calc
          8 * ((4 * L + 1) * 4 ^ (L / 2)) =
              (8 * (4 * L + 1)) * 4 ^ (L / 2) := by ring
          _ ≤ (40 * (L + 1) ^ 4) * 4 ^ (L / 2) :=
            Nat.mul_le_mul_right _ hsmallCoeff
      · calc
          L * (2 * L) *
                (((2 * L) * L + 1) * 4 ^ (L / 3)) =
              (L * (2 * L) * ((2 * L) * L + 1)) *
                4 ^ (L / 3) := by ring
          _ ≤ (6 * (L + 1) ^ 4) * 4 ^ (L / 2) :=
            Nat.mul_le_mul hlargeCoeff hpower
    _ = 46 * (L + 1) ^ 4 * 4 ^ (L / 2) := by ring

/--
Cast form of the finite envelope after replacing `4^(L/2)` by its critical
window bound.
-/
theorem weightedChannelMass_cast_le_linear_poly
    {C : ℝ} {N L : ℕ}
    (hN : 0 < N)
    (hrun : CriticalRunWindow.InRunLengthWindow C N L) :
    (weightedChannelMass L : ℝ) ≤
      (N : ℝ) *
        ((46 * CriticalRunWindow.balanceConstant C) *
          (((L + 1 : ℕ) : ℝ) ^ 4)) := by
  have hfinite :=
    weightedChannelMass_le_poly_four_pow_half L
  have hfiniteCast :
      (weightedChannelMass L : ℝ) ≤
        (46 : ℝ) * (((L + 1 : ℕ) : ℝ) ^ 4) *
          ((4 ^ (L / 2) : ℕ) : ℝ) := by
    exact_mod_cast hfinite
  have hpower :=
    CriticalChannelPowers.four_pow_half_cast_le_balance_mul
      hN hrun
  calc
    (weightedChannelMass L : ℝ) ≤
        (46 : ℝ) * (((L + 1 : ℕ) : ℝ) ^ 4) *
          ((4 ^ (L / 2) : ℕ) : ℝ) :=
      hfiniteCast
    _ ≤ (46 : ℝ) * (((L + 1 : ℕ) : ℝ) ^ 4) *
          (CriticalRunWindow.balanceConstant C * (N : ℝ)) :=
      mul_le_mul_of_nonneg_left hpower (by positivity)
    _ = (N : ℝ) *
        ((46 * CriticalRunWindow.balanceConstant C) *
          (((L + 1 : ℕ) : ℝ) ^ 4)) := by ring

/--
Fully quantified conclusion of Lemma 5.5:

`weightedChannelMass L = N^(1+o_C(1))`

as an upper bound, uniformly for `|L-log₂ N| ≤ C`.
-/
theorem weightedChannelMass_uniformLinearSubpolynomial
    {C : ℝ} (hC : 0 ≤ C) :
    UniformLinearSubpolynomialOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun _ L => (weightedChannelMass L : ℝ)) := by
  have hupperNonneg : 0 ≤ CriticalRunWindow.upperConstant :=
    (CriticalRunWindow.lowerConstant_pos.trans
      CriticalRunWindow.lowerConstant_lt_upperConstant).le
  obtain ⟨Nwindow, hwindow⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  let admissibleLarge : ℕ → ℕ → Prop :=
    fun N L ↦
      CriticalRunWindow.InRunLengthWindow C N L ∧ Nwindow ≤ N
  let ell : ℕ → ℕ → ℝ :=
    fun _ L ↦ ((L + 1 : ℕ) : ℝ)
  have hlinearLarge :
      UniformSubpolynomialOn admissibleLarge ell := by
    have hheight :
        ∀ N L, admissibleLarge N L →
          (L : ℝ) ≤
            CriticalRunWindow.upperConstant * Real.log N := by
      intro N L hNL
      have hLcast :
          (L : ℝ) ≤ ((L + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.le_succ L
      exact hLcast.trans
        (hwindow N hNL.2 L hNL.1).1.2.2.2
    have hcore :=
      ExpSqrtLog.uniformSubpolynomialOn_linear_log_add_one
        admissibleLarge (fun _ L ↦ L)
        CriticalRunWindow.upperConstant hupperNonneg
        hheight
    simpa only [ell, Nat.cast_add, Nat.cast_one] using hcore
  have hlinear :
      UniformSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C) ell := by
    intro k hk
    obtain ⟨Nlinear, hNlinear⟩ := hlinearLarge k hk
    refine ⟨max Nwindow Nlinear, ?_⟩
    intro N hN L hrun
    exact
      hNlinear N ((le_max_right _ _).trans hN) L
        ⟨hrun, (le_max_left _ _).trans hN⟩
  have hquadratic :
      UniformSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C)
        (fun N L ↦ ell N L * ell N L) :=
    ExpSqrtLog.uniformSubpolynomialOn_mul hlinear hlinear
  have hquartic :
      UniformSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C)
        (fun N L ↦
          (ell N L * ell N L) * (ell N L * ell N L)) :=
    ExpSqrtLog.uniformSubpolynomialOn_mul hquadratic hquadratic
  have hfactor :
      UniformSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C)
        (fun N L ↦
          (46 * CriticalRunWindow.balanceConstant C) *
            ((ell N L * ell N L) *
              (ell N L * ell N L))) :=
    ExpSqrtLog.uniformSubpolynomialOn_const_mul
      (46 * CriticalRunWindow.balanceConstant C) hquartic
  apply UniformLinear.of_linear_mul_subpolynomial hfactor
  refine ⟨1, ?_⟩
  intro N hN L hrun
  have hNpos : 0 < N := by omega
  have hmassNonneg : 0 ≤ (weightedChannelMass L : ℝ) := by
    positivity
  have hfactorNonneg :
      0 ≤
        (46 * CriticalRunWindow.balanceConstant C) *
          ((ell N L * ell N L) *
            (ell N L * ell N L)) := by
    dsimp only [ell]
    exact mul_nonneg
      (mul_nonneg (by norm_num)
        (CriticalRunWindow.balanceConstant_nonneg C))
      (by positivity)
  rw [abs_of_nonneg hmassNonneg, abs_of_nonneg hfactorNonneg]
  calc
    (weightedChannelMass L : ℝ) ≤
        (N : ℝ) *
          ((46 * CriticalRunWindow.balanceConstant C) *
            (((L + 1 : ℕ) : ℝ) ^ 4)) :=
      weightedChannelMass_cast_le_linear_poly hNpos hrun
    _ = (N : ℝ) *
        ((46 * CriticalRunWindow.balanceConstant C) *
          ((ell N L * ell N L) *
            (ell N L * ell N L))) := by
      dsimp only [ell]
      ring

end WeightedChannelMassCritical
end PaperC
