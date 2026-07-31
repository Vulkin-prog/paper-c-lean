import PaperC.Analysis.CriticalWeightedDefect
import PaperC.Arithmetic.ChebyshevPrimeCount
import PaperC.Asymptotics.FourPowLittleOHeight
import PaperC.Combinatorics.SmallHeightResidualComponentEnvelope
import PaperC.Probability.CriticalRunWindow

/-!
# The small-height component envelope in the critical window

For `B=L+1`, put

`qmax = sqrt (Nat.log 2 B)` and `X = 4*qmax*B`.

The elementary Chebyshev estimate already available in the repository gives

`Nat.log 2 X * π(X) ≤ 7X`.

Since `B ≤ X` and `qmax^2 ≤ Nat.log 2 B`, cancellation of one positive
factor `qmax` yields

`qmax * π(X) ≤ 28B`.

As `qmax` tends to infinity uniformly in the critical run-length window,
the finite component envelope `2 + π(X)` is uniformly `o(B)`.  The generic
closure theorem in `FourPowLittleOHeight` then turns this into the
subpolynomial estimate `4^envelope = N^o(1)`.
-/

namespace PaperC
namespace SmallHeightComponentEnvelopeCritical

open SmallHeightResidualComponentEnvelope

noncomputable section

/--
The square-root logarithmic factor times the prime count in the small-height
cutoff is at most `28B`.
-/
private theorem sqrtLog_mul_primeCount_le
    (L : ℕ)
    (hqpos : 0 < Nat.sqrt (Nat.log 2 (L + 1))) :
    Nat.sqrt (Nat.log 2 (L + 1)) *
        PrimesUpTo.count (smallHeightPrimeCutoff L) ≤
      28 * (L + 1) := by
  let B := L + 1
  let q := Nat.sqrt (Nat.log 2 B)
  let X := smallHeightPrimeCutoff L
  have hqOne : 1 ≤ q := by
    simpa only [q, B] using hqpos
  have hX :
      X = 4 * q * B := by
    simp only [X, q, B, smallHeightPrimeCutoff]
  have hBOne : 1 ≤ B := by
    dsimp only [B]
    omega
  have hXfour : 4 ≤ X := by
    rw [hX]
    have hfourLeFourQ : 4 ≤ 4 * q := by
      simpa only [mul_one] using
        Nat.mul_le_mul_left 4 hqOne
    have hfourQLe : 4 * q ≤ 4 * q * B := by
      simpa only [mul_one] using
        Nat.mul_le_mul_left (4 * q) hBOne
    exact hfourLeFourQ.trans hfourQLe
  have hBLeX : B ≤ X := by
    rw [hX]
    have hOneLeFourQ : 1 ≤ 4 * q :=
      (by norm_num : 1 ≤ 4).trans
        (by
          simpa only [mul_one] using
            Nat.mul_le_mul_left 4 hqOne)
    simpa only [one_mul] using
      Nat.mul_le_mul_right B hOneLeFourQ
  have hlogMono :
      Nat.log 2 B ≤ Nat.log 2 X :=
    Nat.log_mono_right hBLeX
  have hqSquare :
      q * q ≤ Nat.log 2 B := by
    simpa only [q] using Nat.sqrt_le (Nat.log 2 B)
  have hchebyshev :
      Nat.log 2 X * PrimesUpTo.count X ≤ 7 * X :=
    ChebyshevPrimeCount.log_mul_count_le_seven_mul hXfour
  have hwithFactor :
      q * (q * PrimesUpTo.count X) ≤
        q * (28 * B) := by
    calc
      q * (q * PrimesUpTo.count X) =
          (q * q) * PrimesUpTo.count X := by ring
      _ ≤
          Nat.log 2 B * PrimesUpTo.count X :=
        Nat.mul_le_mul_right _ hqSquare
      _ ≤
          Nat.log 2 X * PrimesUpTo.count X :=
        Nat.mul_le_mul_right _ hlogMono
      _ ≤ 7 * X :=
        hchebyshev
      _ = q * (28 * B) := by
        rw [hX]
        ring
  have hcancel :
      q * PrimesUpTo.count X ≤ 28 * B :=
    Nat.le_of_mul_le_mul_left hwithFactor hqpos
  simpa only [q, X, B] using hcancel

/--
The integral square-root logarithm tends to infinity once the height does.
The power threshold is chosen so that monotonicity of `Nat.log` gives the
required square inequality.
-/
private theorem le_sqrtLog_of_pow_sq_le
    {M B : ℕ}
    (hB : 2 ^ (M ^ 2) ≤ B) :
    M ≤ Nat.sqrt (Nat.log 2 B) := by
  apply (Nat.le_sqrt').2
  exact Nat.le_log_of_pow_le (by omega) hB

/--
Uniform little-oh form of the component envelope in the literal run-length
window:

`smallHeightResidualComponentEnvelope L = o_C(L+1)`.
-/
theorem smallHeightResidualComponentEnvelope_uniformLittleO
    {C : ℝ} (hC : 0 ≤ C) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun _ L =>
        (smallHeightResidualComponentEnvelope L : ℝ))
      (fun _ L => ((L + 1 : ℕ) : ℝ)) := by
  intro ε hε
  obtain ⟨M : ℕ, hM⟩ :=
    exists_nat_gt (56 / ε)
  obtain ⟨K : ℕ, hK⟩ :=
    exists_nat_gt (4 / ε)
  have hMposReal : (0 : ℝ) < (M : ℝ) := by
    have hratioPos : 0 < 56 / ε := by positivity
    exact hratioPos.trans hM
  have hMpos : 0 < M := by
    exact_mod_cast hMposReal
  let T : ℕ := max (2 ^ (M ^ 2)) K
  obtain ⟨Nwindow, hNwindow⟩ :=
    CriticalRunWindow.firstMomentWindow_eventually hC
  obtain ⟨Nadm, hNadm⟩ :=
    CriticalWeightedDefect.admissible_eventually
      CriticalRunWindow.lowerConstant_pos
      CriticalRunWindow.lowerConstant_lt_upperConstant
  obtain ⟨Nheight, hNheight⟩ :=
    CriticalWeightedDefect.height_tends_to_infinity
      (c₂ := CriticalRunWindow.upperConstant)
      CriticalRunWindow.lowerConstant_pos T
  refine ⟨max Nwindow (max Nadm Nheight), ?_⟩
  intro N hN L hrun
  have hNwindowN : Nwindow ≤ N :=
    (le_max_left _ _).trans hN
  have hNtail : max Nadm Nheight ≤ N :=
    (le_max_right _ _).trans hN
  have hNadmN : Nadm ≤ N :=
    (le_max_left _ _).trans hNtail
  have hNheightN : Nheight ≤ N :=
    (le_max_right _ _).trans hNtail
  have hfirst :=
    hNwindow N hNwindowN L hrun
  have hadmissible :
      CriticalWeightedDefect.Admissible
        CriticalRunWindow.lowerConstant
        CriticalRunWindow.upperConstant N (L + 1) :=
    hNadm N hNadmN (L + 1) hfirst.1
  have hheight : T ≤ L + 1 :=
    hNheight N hNheightN (L + 1) hadmissible
  have hpower :
      2 ^ (M ^ 2) ≤ L + 1 :=
    (le_max_left _ _).trans hheight
  have hKheight : K ≤ L + 1 :=
    (le_max_right _ _).trans hheight
  have hMq :
      M ≤ Nat.sqrt (Nat.log 2 (L + 1)) :=
    le_sqrtLog_of_pow_sq_le hpower
  have hqpos :
      0 < Nat.sqrt (Nat.log 2 (L + 1)) :=
    hMpos.trans_le hMq
  have hprime :=
    sqrtLog_mul_primeCount_le L hqpos
  have hMprime :
      M * PrimesUpTo.count (smallHeightPrimeCutoff L) ≤
        28 * (L + 1) :=
    (Nat.mul_le_mul_right
        (PrimesUpTo.count (smallHeightPrimeCutoff L)) hMq).trans
      hprime
  have hMprimeReal :
      (M : ℝ) *
          (PrimesUpTo.count (smallHeightPrimeCutoff L) : ℝ) ≤
        28 * ((L + 1 : ℕ) : ℝ) := by
    exact_mod_cast hMprime
  have hprimeReal :
      (PrimesUpTo.count (smallHeightPrimeCutoff L) : ℝ) ≤
        (28 / (M : ℝ)) * ((L + 1 : ℕ) : ℝ) := by
    calc
      (PrimesUpTo.count (smallHeightPrimeCutoff L) : ℝ) ≤
          (28 * ((L + 1 : ℕ) : ℝ)) / (M : ℝ) := by
        apply (le_div_iff₀ hMposReal).2
        simpa only [mul_comm] using hMprimeReal
      _ =
          (28 / (M : ℝ)) * ((L + 1 : ℕ) : ℝ) := by ring
  have hratio :
      28 / (M : ℝ) < ε / 2 := by
    apply (div_lt_iff₀ hMposReal).2
    have hscaled :
        (56 : ℝ) < (M : ℝ) * ε :=
      (div_lt_iff₀ hε).1 hM
    nlinarith
  have hprimeHalf :
      (PrimesUpTo.count (smallHeightPrimeCutoff L) : ℝ) ≤
        (ε / 2) * ((L + 1 : ℕ) : ℝ) :=
    hprimeReal.trans
      (mul_le_mul_of_nonneg_right hratio.le (by positivity))
  have hKcast :
      (K : ℝ) ≤ ((L + 1 : ℕ) : ℝ) := by
    exact_mod_cast hKheight
  have hfourHeight :
      4 / ε < ((L + 1 : ℕ) : ℝ) :=
    hK.trans_le hKcast
  have hconstantHalf :
      (2 : ℝ) ≤
        (ε / 2) * ((L + 1 : ℕ) : ℝ) := by
    have hscaled :
        (4 : ℝ) <
          ((L + 1 : ℕ) : ℝ) * ε :=
      (div_lt_iff₀ hε).1 hfourHeight
    nlinarith
  rw [abs_of_nonneg
      (show 0 ≤
        (smallHeightResidualComponentEnvelope L : ℝ) by positivity),
    abs_of_nonneg
      (show 0 ≤ ((L + 1 : ℕ) : ℝ) by positivity)]
  unfold smallHeightResidualComponentEnvelope
  norm_num only [Nat.cast_add, Nat.cast_ofNat]
  calc
    2 + (PrimesUpTo.count (smallHeightPrimeCutoff L) : ℝ) ≤
        (ε / 2) * ((L + 1 : ℕ) : ℝ) +
          (ε / 2) * ((L + 1 : ℕ) : ℝ) :=
      add_le_add hconstantHalf hprimeHalf
    _ = ε * ((L : ℝ) + 1) := by
      push_cast
      ring

/--
Exponentiating the small-height residual-component envelope produces a
uniformly subpolynomial factor in the critical window.
-/
theorem four_pow_smallHeightResidualComponentEnvelope_uniformSubpolynomial
    {C : ℝ} (hC : 0 ≤ C) :
    UniformSubpolynomialOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun _ L =>
        (((4 ^ smallHeightResidualComponentEnvelope L : ℕ) : ℝ))) := by
  have hupperNonneg :
      0 ≤ CriticalRunWindow.upperConstant :=
    (CriticalRunWindow.lowerConstant_pos.trans
      CriticalRunWindow.lowerConstant_lt_upperConstant).le
  apply
    FourPowLittleOHeight.uniformSubpolynomialOn_four_pow_of_uniformLittleO_height
      (fun _ L => smallHeightResidualComponentEnvelope L)
      (fun _ L => ((L + 1 : ℕ) : ℝ))
      CriticalRunWindow.upperConstant hupperNonneg
  · exact smallHeightResidualComponentEnvelope_uniformLittleO hC
  · intro N L _hrun
    positivity
  · obtain ⟨Nwindow, hNwindow⟩ :=
      CriticalRunWindow.firstMomentWindow_eventually hC
    refine ⟨Nwindow, ?_⟩
    intro N hN L hrun
    exact (hNwindow N hN L hrun).1.2.2.2

end

end SmallHeightComponentEnvelopeCritical
end PaperC
