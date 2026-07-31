import PaperC.Arithmetic.RationalMassFinite
import PaperC.Asymptotics.CriticalChannelPowers
import PaperC.Asymptotics.ExpSqrtLog
import PaperC.Asymptotics.RationalPowers

set_option maxHeartbeats 1800000

/-!
# Critical-window rates for the finite rational-mass envelope

The finite decomposition in `RationalMassFinite` naturally produces

`2(6(L+1)+1)² base^(L/2)
  + L(2L)(2L²+1)(N+1) base^(L/3)`.

For `base = 2` its cube is `N⁴` times a uniformly subpolynomial factor;
for `base = 4` its cube is `N⁵` times such a factor.  These are the
division-free `N^(4/3+o(1))` and `N^(5/3+o(1))` estimates.
-/

namespace PaperC
namespace CriticalRationalMassEnvelopes

/-- Explicit finite envelope associated with the rational-channel split. -/
def rationalMassEnvelope (base N L : ℕ) : ℕ :=
  2 * (6 * (L + 1) + 1) ^ 2 * base ^ (L / 2) +
    L * (2 * L) * ((2 * L) * L + 1) * (N + 1) *
      base ^ (L / 3)

/--
A common polynomial envelope for both summands.  The constant `128` is a
convenient integral majorant for all displayed coefficients.
-/
theorem rationalMassEnvelope_le_common
    {base N L : ℕ} (hN : 0 < N) :
    rationalMassEnvelope base N L ≤
      128 * (L + 1) ^ 4 *
        (base ^ (L / 2) + N * base ^ (L / 3)) := by
  have hHpos : 0 < L + 1 := Nat.succ_pos L
  have hHone : 1 ≤ L + 1 := hHpos
  have hlinear : 6 * (L + 1) + 1 ≤ 7 * (L + 1) := by
    omega
  have hsquare :
      (6 * (L + 1) + 1) ^ 2 ≤
        (7 * (L + 1)) ^ 2 :=
    Nat.pow_le_pow_left hlinear 2
  have hpow :
      (L + 1) ^ 2 ≤ (L + 1) ^ 4 :=
    Nat.pow_le_pow_right hHpos (by omega)
  have hsmallCoeff :
      2 * (6 * (L + 1) + 1) ^ 2 ≤
        128 * (L + 1) ^ 4 := by
    calc
      2 * (6 * (L + 1) + 1) ^ 2 ≤
          2 * (7 * (L + 1)) ^ 2 :=
        Nat.mul_le_mul_left 2 hsquare
      _ = 98 * (L + 1) ^ 2 := by ring
      _ ≤ 98 * (L + 1) ^ 4 :=
        Nat.mul_le_mul_left 98 hpow
      _ ≤ 128 * (L + 1) ^ 4 :=
        Nat.mul_le_mul_right ((L + 1) ^ 4) (by omega)
  have hL : L ≤ L + 1 := Nat.le_succ L
  have htwoL : 2 * L ≤ 2 * (L + 1) :=
    Nat.mul_le_mul_left 2 hL
  have honeSquare : 1 ≤ (L + 1) * (L + 1) := by
    nlinarith
  have hinner :
      (2 * L) * L + 1 ≤
        (2 * (L + 1)) * (L + 1) +
          (L + 1) * (L + 1) :=
    Nat.add_le_add
      (Nat.mul_le_mul htwoL hL) honeSquare
  have hfront :
      L * (2 * L) ≤
        (L + 1) * (2 * (L + 1)) :=
    Nat.mul_le_mul hL htwoL
  have hlargePoly :
      L * (2 * L) * ((2 * L) * L + 1) ≤
        6 * (L + 1) ^ 4 := by
    calc
      L * (2 * L) * ((2 * L) * L + 1) ≤
          ((L + 1) * (2 * (L + 1))) *
            ((2 * (L + 1)) * (L + 1) +
              (L + 1) * (L + 1)) :=
        Nat.mul_le_mul hfront hinner
      _ = 6 * (L + 1) ^ 4 := by ring
  have hNadd : N + 1 ≤ 2 * N := by
    omega
  have hlargeCoeff :
      L * (2 * L) * ((2 * L) * L + 1) * (N + 1) ≤
        128 * (L + 1) ^ 4 * N := by
    calc
      L * (2 * L) * ((2 * L) * L + 1) * (N + 1) ≤
          (6 * (L + 1) ^ 4) * (2 * N) :=
        Nat.mul_le_mul hlargePoly hNadd
      _ = 12 * (L + 1) ^ 4 * N := by ring
      _ ≤ 128 * (L + 1) ^ 4 * N := by
        exact Nat.mul_le_mul_right N <|
          Nat.mul_le_mul_right ((L + 1) ^ 4) (by omega)
  unfold rationalMassEnvelope
  calc
    2 * (6 * (L + 1) + 1) ^ 2 * base ^ (L / 2) +
          L * (2 * L) * ((2 * L) * L + 1) *
            (N + 1) * base ^ (L / 3) ≤
        (128 * (L + 1) ^ 4) * base ^ (L / 2) +
          (128 * (L + 1) ^ 4 * N) * base ^ (L / 3) :=
      Nat.add_le_add
        (Nat.mul_le_mul_right _ hsmallCoeff)
        (Nat.mul_le_mul_right _ hlargeCoeff)
    _ = 128 * (L + 1) ^ 4 *
        (base ^ (L / 2) + N * base ^ (L / 3)) := by
      ring

/-- Cubing a sum of nonnegative reals costs at most a factor four. -/
private theorem add_cube_le_four_sum_cubes
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) ^ 3 ≤ 4 * (a ^ 3 + b ^ 3) := by
  have hnonneg :
      0 ≤ 3 * (a + b) * (a - b) ^ 2 :=
    mul_nonneg
      (mul_nonneg (by norm_num) (add_nonneg ha hb))
      (sq_nonneg (a - b))
  nlinarith [hnonneg]

/-- A fixed positive natural power of a subpolynomial function remains so. -/
private theorem uniformSubpolynomialOn_pow
    {admissible : ℕ → ℕ → Prop}
    {f : ℕ → ℕ → ℝ}
    (hf : UniformSubpolynomialOn admissible f)
    (d : ℕ) (hd : 0 < d) :
    UniformSubpolynomialOn admissible
      (fun N L => f N L ^ d) := by
  intro k hk
  have hdk : 0 < d * k :=
    Nat.mul_pos hd hk
  obtain ⟨N₀, hN₀⟩ := hf (d * k) hdk
  refine ⟨N₀, ?_⟩
  intro N hN L hNL
  simpa only [abs_pow, pow_mul] using
    hN₀ N hN L hNL

/--
The elementary height `L+1` is uniformly subpolynomial in the literal
critical window.
-/
theorem runLengthAddOne_uniformSubpolynomial
    {C : ℝ} (hC : 0 ≤ C) :
    UniformSubpolynomialOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun _ L => (((L + 1 : ℕ) : ℝ))) := by
  have hupperNonneg : 0 ≤ CriticalRunWindow.upperConstant :=
    (CriticalRunWindow.lowerConstant_pos.trans
      CriticalRunWindow.lowerConstant_lt_upperConstant).le
  obtain ⟨Nwindow, hwindow⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  let admissibleLarge : ℕ → ℕ → Prop :=
    fun N L ↦
      CriticalRunWindow.InRunLengthWindow C N L ∧
        Nwindow ≤ N
  have hlarge :
      UniformSubpolynomialOn admissibleLarge
        (fun _ L => (((L + 1 : ℕ) : ℝ))) := by
    have hheight :
        ∀ N L, admissibleLarge N L →
          (L : ℝ) ≤
            CriticalRunWindow.upperConstant * Real.log N := by
      intro N L hNL
      have hLcast :
          (L : ℝ) ≤ (((L + 1 : ℕ) : ℝ)) := by
        exact_mod_cast Nat.le_succ L
      exact hLcast.trans
        (hwindow N hNL.2 L hNL.1).1.2.2.2
    have hcore :=
      ExpSqrtLog.uniformSubpolynomialOn_linear_log_add_one
        admissibleLarge (fun _ L => L)
        CriticalRunWindow.upperConstant hupperNonneg
        hheight
    simpa only [Nat.cast_add, Nat.cast_one] using hcore
  intro k hk
  obtain ⟨Nlarge, hNlarge⟩ := hlarge k hk
  refine ⟨max Nwindow Nlarge, ?_⟩
  intro N hN L hrun
  exact
    hNlarge N ((le_max_right _ _).trans hN) L
      ⟨hrun, (le_max_left _ _).trans hN⟩

/-- Residual factor for the `4/3` envelope. -/
noncomputable def fourThirdResidual
    (C : ℝ) (_N L : ℕ) : ℝ :=
  (4 * (128 : ℝ) ^ 3) *
    ((CriticalRunWindow.balanceConstant C) ^ 3 +
      CriticalRunWindow.balanceConstant C) *
    (((L + 1 : ℕ) : ℝ) ^ 12)

/-- Residual factor for the `5/3` envelope. -/
noncomputable def fiveThirdResidual
    (C : ℝ) (_N L : ℕ) : ℝ :=
  (4 * (128 : ℝ) ^ 3) *
    ((CriticalRunWindow.balanceConstant C) ^ 3 +
      (CriticalRunWindow.balanceConstant C) ^ 2) *
    (((L + 1 : ℕ) : ℝ) ^ 12)

theorem fourThirdResidual_uniformSubpolynomial
    {C : ℝ} (hC : 0 ≤ C) :
    UniformSubpolynomialOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fourThirdResidual C) := by
  have hheight12 :=
    uniformSubpolynomialOn_pow
      (runLengthAddOne_uniformSubpolynomial hC) 12 (by omega)
  unfold fourThirdResidual
  exact
    ExpSqrtLog.uniformSubpolynomialOn_const_mul
      ((4 * (128 : ℝ) ^ 3) *
        ((CriticalRunWindow.balanceConstant C) ^ 3 +
          CriticalRunWindow.balanceConstant C))
      hheight12

theorem fiveThirdResidual_uniformSubpolynomial
    {C : ℝ} (hC : 0 ≤ C) :
    UniformSubpolynomialOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fiveThirdResidual C) := by
  have hheight12 :=
    uniformSubpolynomialOn_pow
      (runLengthAddOne_uniformSubpolynomial hC) 12 (by omega)
  unfold fiveThirdResidual
  exact
    ExpSqrtLog.uniformSubpolynomialOn_const_mul
      ((4 * (128 : ℝ) ^ 3) *
        ((CriticalRunWindow.balanceConstant C) ^ 3 +
          (CriticalRunWindow.balanceConstant C) ^ 2))
      hheight12

/-- Cubed pointwise estimate for the base-two finite envelope. -/
theorem rationalMassEnvelope_two_cube_bound
    {C : ℝ} {N L : ℕ}
    (hN : 0 < N)
    (hrun : CriticalRunWindow.InRunLengthWindow C N L) :
    |((rationalMassEnvelope 2 N L : ℕ) : ℝ)| ^ 3 ≤
      (N : ℝ) ^ 4 * |fourThirdResidual C N L| := by
  let K := CriticalRunWindow.balanceConstant C
  let H : ℝ := ((L + 1 : ℕ) : ℝ)
  let A : ℝ := ((2 ^ (L / 2) : ℕ) : ℝ)
  let B : ℝ := ((2 ^ (L / 3) : ℕ) : ℝ)
  have hK : 0 ≤ K :=
    CriticalRunWindow.balanceConstant_nonneg C
  have hNreal : 1 ≤ (N : ℝ) := by
    exact_mod_cast hN
  have henvNat :=
    rationalMassEnvelope_le_common
      (base := 2) (L := L) hN
  have henv :
      ((rationalMassEnvelope 2 N L : ℕ) : ℝ) ≤
        (128 : ℝ) * H ^ 4 *
          (A + (N : ℝ) * B) := by
    dsimp only [H, A, B]
    exact_mod_cast henvNat
  have hA_le_four :
      A ≤ ((4 ^ (L / 2) : ℕ) : ℝ) := by
    dsimp only [A]
    exact_mod_cast
      Nat.pow_le_pow_left (by norm_num : 2 ≤ 4) (L / 2)
  have hA :
      A ≤ K * (N : ℝ) :=
    hA_le_four.trans
      (CriticalChannelPowers.four_pow_half_cast_le_balance_mul
        hN hrun)
  have hAcube :
      A ^ 3 ≤ K ^ 3 * (N : ℝ) ^ 3 := by
    have hp := pow_le_pow_left₀ (by positivity) hA 3
    simpa only [mul_pow] using hp
  have hN34 : (N : ℝ) ^ 3 ≤ (N : ℝ) ^ 4 := by
    calc
      (N : ℝ) ^ 3 = (N : ℝ) ^ 3 * 1 := by ring
      _ ≤ (N : ℝ) ^ 3 * (N : ℝ) :=
        mul_le_mul_of_nonneg_left hNreal (by positivity)
      _ = (N : ℝ) ^ 4 := by ring
  have hAcube' :
      A ^ 3 ≤ K ^ 3 * (N : ℝ) ^ 4 :=
    hAcube.trans
      (mul_le_mul_of_nonneg_left hN34 (by positivity))
  have hBcube :
      B ^ 3 ≤ K * (N : ℝ) := by
    dsimp only [B, K]
    exact
      CriticalChannelPowers.two_pow_third_cast_cube_le_balance_mul
        hN hrun
  have hNBcube :
      ((N : ℝ) * B) ^ 3 ≤ K * (N : ℝ) ^ 4 := by
    rw [mul_pow]
    calc
      (N : ℝ) ^ 3 * B ^ 3 ≤
          (N : ℝ) ^ 3 * (K * (N : ℝ)) :=
        mul_le_mul_of_nonneg_left hBcube (by positivity)
      _ = K * (N : ℝ) ^ 4 := by ring
  have hsumCubes :
      A ^ 3 + ((N : ℝ) * B) ^ 3 ≤
        (K ^ 3 + K) * (N : ℝ) ^ 4 := by
    calc
      A ^ 3 + ((N : ℝ) * B) ^ 3 ≤
          K ^ 3 * (N : ℝ) ^ 4 +
            K * (N : ℝ) ^ 4 :=
        add_le_add hAcube' hNBcube
      _ = (K ^ 3 + K) * (N : ℝ) ^ 4 := by ring
  have hsumCube :
      (A + (N : ℝ) * B) ^ 3 ≤
        4 * (A ^ 3 + ((N : ℝ) * B) ^ 3) :=
    add_cube_le_four_sum_cubes (by positivity) (by positivity)
  have henvNonneg :
      0 ≤ ((rationalMassEnvelope 2 N L : ℕ) : ℝ) := by
    positivity
  have hcommonNonneg :
      0 ≤ (128 : ℝ) * H ^ 4 := by
    positivity
  rw [abs_of_nonneg henvNonneg]
  have hcube :=
    pow_le_pow_left₀ henvNonneg henv 3
  rw [abs_of_nonneg] <;>
    try
      · unfold fourThirdResidual
        positivity
  calc
    ((rationalMassEnvelope 2 N L : ℕ) : ℝ) ^ 3 ≤
        ((128 : ℝ) * H ^ 4 *
          (A + (N : ℝ) * B)) ^ 3 :=
      hcube
    _ = (128 : ℝ) ^ 3 * H ^ 12 *
        (A + (N : ℝ) * B) ^ 3 := by ring
    _ ≤ (128 : ℝ) ^ 3 * H ^ 12 *
        (4 * (A ^ 3 + ((N : ℝ) * B) ^ 3)) :=
      mul_le_mul_of_nonneg_left hsumCube (by positivity)
    _ ≤ (128 : ℝ) ^ 3 * H ^ 12 *
        (4 * ((K ^ 3 + K) * (N : ℝ) ^ 4)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hsumCubes (by norm_num))
        (by positivity)
    _ = (N : ℝ) ^ 4 * fourThirdResidual C N L := by
      dsimp only [K, H]
      unfold fourThirdResidual
      ring

/-- Cubed pointwise estimate for the base-four finite envelope. -/
theorem rationalMassEnvelope_four_cube_bound
    {C : ℝ} {N L : ℕ}
    (hN : 0 < N)
    (hrun : CriticalRunWindow.InRunLengthWindow C N L) :
    |((rationalMassEnvelope 4 N L : ℕ) : ℝ)| ^ 3 ≤
      (N : ℝ) ^ 5 * |fiveThirdResidual C N L| := by
  let K := CriticalRunWindow.balanceConstant C
  let H : ℝ := ((L + 1 : ℕ) : ℝ)
  let A : ℝ := ((4 ^ (L / 2) : ℕ) : ℝ)
  let B : ℝ := ((4 ^ (L / 3) : ℕ) : ℝ)
  have hK : 0 ≤ K :=
    CriticalRunWindow.balanceConstant_nonneg C
  have hNreal : 1 ≤ (N : ℝ) := by
    exact_mod_cast hN
  have henvNat :=
    rationalMassEnvelope_le_common
      (base := 4) (L := L) hN
  have henv :
      ((rationalMassEnvelope 4 N L : ℕ) : ℝ) ≤
        (128 : ℝ) * H ^ 4 *
          (A + (N : ℝ) * B) := by
    dsimp only [H, A, B]
    exact_mod_cast henvNat
  have hA :
      A ≤ K * (N : ℝ) := by
    dsimp only [A, K]
    exact
      CriticalChannelPowers.four_pow_half_cast_le_balance_mul
        hN hrun
  have hAcube :
      A ^ 3 ≤ K ^ 3 * (N : ℝ) ^ 3 := by
    have hp := pow_le_pow_left₀ (by positivity) hA 3
    simpa only [mul_pow] using hp
  have hN35 : (N : ℝ) ^ 3 ≤ (N : ℝ) ^ 5 := by
    calc
      (N : ℝ) ^ 3 = (N : ℝ) ^ 3 * 1 := by ring
      _ ≤ (N : ℝ) ^ 3 * (N : ℝ) ^ 2 := by
        apply mul_le_mul_of_nonneg_left
        · nlinarith
        · positivity
      _ = (N : ℝ) ^ 5 := by ring
  have hAcube' :
      A ^ 3 ≤ K ^ 3 * (N : ℝ) ^ 5 :=
    hAcube.trans
      (mul_le_mul_of_nonneg_left hN35 (by positivity))
  have hBcube :
      B ^ 3 ≤ K ^ 2 * (N : ℝ) ^ 2 := by
    dsimp only [B, K]
    exact
      CriticalChannelPowers.four_pow_third_cast_cube_le_balance_sq_mul
        hN hrun
  have hNBcube :
      ((N : ℝ) * B) ^ 3 ≤
        K ^ 2 * (N : ℝ) ^ 5 := by
    rw [mul_pow]
    calc
      (N : ℝ) ^ 3 * B ^ 3 ≤
          (N : ℝ) ^ 3 *
            (K ^ 2 * (N : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hBcube (by positivity)
      _ = K ^ 2 * (N : ℝ) ^ 5 := by ring
  have hsumCubes :
      A ^ 3 + ((N : ℝ) * B) ^ 3 ≤
        (K ^ 3 + K ^ 2) * (N : ℝ) ^ 5 := by
    calc
      A ^ 3 + ((N : ℝ) * B) ^ 3 ≤
          K ^ 3 * (N : ℝ) ^ 5 +
            K ^ 2 * (N : ℝ) ^ 5 :=
        add_le_add hAcube' hNBcube
      _ = (K ^ 3 + K ^ 2) * (N : ℝ) ^ 5 := by ring
  have hsumCube :
      (A + (N : ℝ) * B) ^ 3 ≤
        4 * (A ^ 3 + ((N : ℝ) * B) ^ 3) :=
    add_cube_le_four_sum_cubes (by positivity) (by positivity)
  have henvNonneg :
      0 ≤ ((rationalMassEnvelope 4 N L : ℕ) : ℝ) := by
    positivity
  rw [abs_of_nonneg henvNonneg]
  have hcube :=
    pow_le_pow_left₀ henvNonneg henv 3
  rw [abs_of_nonneg] <;>
    try
      · unfold fiveThirdResidual
        positivity
  calc
    ((rationalMassEnvelope 4 N L : ℕ) : ℝ) ^ 3 ≤
        ((128 : ℝ) * H ^ 4 *
          (A + (N : ℝ) * B)) ^ 3 :=
      hcube
    _ = (128 : ℝ) ^ 3 * H ^ 12 *
        (A + (N : ℝ) * B) ^ 3 := by ring
    _ ≤ (128 : ℝ) ^ 3 * H ^ 12 *
        (4 * (A ^ 3 + ((N : ℝ) * B) ^ 3)) :=
      mul_le_mul_of_nonneg_left hsumCube (by positivity)
    _ ≤ (128 : ℝ) ^ 3 * H ^ 12 *
        (4 * ((K ^ 3 + K ^ 2) * (N : ℝ) ^ 5)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hsumCubes (by norm_num))
        (by positivity)
    _ = (N : ℝ) ^ 5 * fiveThirdResidual C N L := by
      dsimp only [K, H]
      unfold fiveThirdResidual
      ring

/-- The base-two envelope is uniformly `N^(4/3+o_C(1))`. -/
theorem rationalMassEnvelope_two_uniformFourThird
    {C : ℝ} (hC : 0 ≤ C) :
    UniformFourThirdSubpolynomialOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun N L => ((rationalMassEnvelope 2 N L : ℕ) : ℝ)) := by
  apply UniformRationalPower.of_cube_bound
    (fourThirdResidual_uniformSubpolynomial hC)
  refine ⟨1, ?_⟩
  intro N hN L hrun
  exact rationalMassEnvelope_two_cube_bound (by omega) hrun

/-- The base-four envelope is uniformly `N^(5/3+o_C(1))`. -/
theorem rationalMassEnvelope_four_uniformFiveThird
    {C : ℝ} (hC : 0 ≤ C) :
    UniformFiveThirdSubpolynomialOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun N L => ((rationalMassEnvelope 4 N L : ℕ) : ℝ)) := by
  apply UniformRationalPower.of_cube_bound
    (fiveThirdResidual_uniformSubpolynomial hC)
  refine ⟨1, ?_⟩
  intro N hN L hrun
  exact rationalMassEnvelope_four_cube_bound (by omega) hrun

end CriticalRationalMassEnvelopes
end PaperC
