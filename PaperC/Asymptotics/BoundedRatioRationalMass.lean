import PaperC.Combinatorics.BoundedRatioGeometry
import PaperC.Asymptotics.CriticalChannelPowers
import PaperC.Asymptotics.CriticalRationalMassEnvelopes
import PaperC.Asymptotics.RationalPowerLittleO
import PaperC.Asymptotics.ThreeHalvesPower
import PaperC.Asymptotics.WeightedChannelMassCritical

set_option maxHeartbeats 1800000

/-!
# Critical bounded-ratio rational mass

The finite estimate in `BoundedRatioGeometry` contains a volumetric
height-two term

`O_{κ₀}(N (L+1) 2^(L/2))`.

In the critical window, `2^(L/2) = O_C(√N)` and every fixed power of
`L+1` is uniformly subpolynomial.  Thus the complete systematic mass is
`N^(3/2+o_{C,κ₀}(1))`, in particular `o_{C,κ₀}(N²)`.

This file is independent of `PropositionSixteenOne`: its final theorem uses
literal quantifiers in `N,M,L`, so the proposition module can consume it
without an import cycle.
-/

namespace PaperC
namespace BoundedRatioRationalMass

open BoundedRatioGeometry

noncomputable section

/--
Maximum base-two systematic mass over all integral endpoints satisfying
`2N≤M≤κ₀N`.
-/
noncomputable def boundedRationalMassSup
    (κ₀ A N L : ℕ) : ℕ :=
  (Finset.Icc (2 * N) (κ₀ * N)).sup fun M =>
    boundedRationalMass N M A L 2

/-- Every admissible endpoint is bounded by the finite supremum. -/
theorem boundedRationalMass_le_sup
    {κ₀ A N M L : ℕ}
    (hNM : 2 * N ≤ M) (hM : M ≤ κ₀ * N) :
    boundedRationalMass N M A L 2 ≤
      boundedRationalMassSup κ₀ A N L := by
  exact Finset.le_sup
    (f := fun M => boundedRationalMass N M A L 2)
    (Finset.mem_Icc.mpr ⟨hNM, hM⟩)

/-- Uniform finite envelope for the endpoint supremum. -/
theorem boundedRationalMassSup_le_common
    {κ₀ A N L : ℕ}
    (hN : 1 ≤ N) (hA : 1 ≤ A) :
    boundedRationalMassSup κ₀ A N L ≤
      16 * (κ₀ + 1) * (L + 1) ^ 4 * N *
        2 ^ (L / 2) := by
  unfold boundedRationalMassSup
  apply Finset.sup_le
  intro M hM
  have hdata := Finset.mem_Icc.mp hM
  exact boundedRationalMass_two_le_common
    hN (by omega) hdata.2 hA

/-- Subpolynomial factor accompanying `N√N`. -/
noncomputable def boundedRatioThreeHalvesResidual
    (C : ℝ) (κ₀ : ℕ) (_N L : ℕ) : ℝ :=
  (16 * (κ₀ + 1) : ℝ) *
    Real.sqrt (CriticalRunWindow.balanceConstant C) *
    (((L + 1 : ℕ) : ℝ) ^ 4)

/-- The residual factor is uniformly subpolynomial in the critical window. -/
theorem boundedRatioThreeHalvesResidual_uniformSubpolynomial
    {C : ℝ} (hC : 0 ≤ C) (κ₀ : ℕ) :
    UniformSubpolynomialOn
      (CriticalRunWindow.InRunLengthWindow C)
      (boundedRatioThreeHalvesResidual C κ₀) := by
  have hH :=
    CriticalRationalMassEnvelopes.runLengthAddOne_uniformSubpolynomial hC
  have hH2 :=
    ExpSqrtLog.uniformSubpolynomialOn_mul hH hH
  have hH4 :=
    ExpSqrtLog.uniformSubpolynomialOn_mul hH2 hH2
  have hconst :=
    ExpSqrtLog.uniformSubpolynomialOn_const_mul
      ((16 * (κ₀ + 1) : ℝ) *
        Real.sqrt (CriticalRunWindow.balanceConstant C))
      hH4
  convert hconst using 1
  funext N L
  unfold boundedRatioThreeHalvesResidual
  ring

/-- The endpoint supremum is uniformly `N^(3/2+o_C,κ₀(1))`. -/
theorem boundedRationalMassSup_uniformThreeHalves
    {C : ℝ} (hC : 0 ≤ C) (κ₀ A : ℕ) (hA : 1 ≤ A) :
    UniformThreeHalvesSubpolynomialOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun N L =>
        ((boundedRationalMassSup κ₀ A N L : ℕ) : ℝ)) := by
  apply UniformThreeHalves.of_linear_sqrt_mul_subpolynomial
    (boundedRatioThreeHalvesResidual_uniformSubpolynomial hC κ₀)
  refine ⟨1, ?_⟩
  intro N hN L hrun
  have hNpos : 0 < N := by omega
  have hfinite :=
    boundedRationalMassSup_le_common
      (κ₀ := κ₀) (A := A) (L := L) hN hA
  have hfiniteCast :
      ((boundedRationalMassSup κ₀ A N L : ℕ) : ℝ) ≤
        (16 * (κ₀ + 1) : ℝ) *
          (((L + 1 : ℕ) : ℝ) ^ 4) *
          (N : ℝ) * ((2 ^ (L / 2) : ℕ) : ℝ) := by
    exact_mod_cast hfinite
  let K := CriticalRunWindow.balanceConstant C
  let P : ℝ := ((2 ^ (L / 2) : ℕ) : ℝ)
  have hK : 0 ≤ K :=
    CriticalRunWindow.balanceConstant_nonneg C
  have hPnonneg : 0 ≤ P := by positivity
  have hPsquare :
      P ^ 2 ≤ K * (N : ℝ) := by
    have hfour :=
      CriticalChannelPowers.four_pow_half_cast_le_balance_mul
        hNpos hrun
    calc
      P ^ 2 = ((4 ^ (L / 2) : ℕ) : ℝ) := by
        dsimp only [P]
        norm_num [pow_two, ← mul_pow]
      _ ≤ K * (N : ℝ) := by
        simpa only [K] using hfour
  have hP :
      P ≤ Real.sqrt (K * (N : ℝ)) :=
    Real.le_sqrt_of_sq_le hPsquare
  have hP' :
      P ≤ Real.sqrt K * Real.sqrt N := by
    rw [← Real.sqrt_mul hK]
    exact hP
  have hmassNonneg :
      0 ≤ ((boundedRationalMassSup κ₀ A N L : ℕ) : ℝ) := by
    positivity
  have hresidualNonneg :
      0 ≤ boundedRatioThreeHalvesResidual C κ₀ N L := by
    unfold boundedRatioThreeHalvesResidual
    positivity
  rw [abs_of_nonneg hmassNonneg,
    abs_of_nonneg hresidualNonneg]
  calc
    ((boundedRationalMassSup κ₀ A N L : ℕ) : ℝ) ≤
        (16 * (κ₀ + 1) : ℝ) *
          (((L + 1 : ℕ) : ℝ) ^ 4) *
          (N : ℝ) * P := by
      simpa only [P] using hfiniteCast
    _ ≤
        (16 * (κ₀ + 1) : ℝ) *
          (((L + 1 : ℕ) : ℝ) ^ 4) *
          (N : ℝ) *
            (Real.sqrt K * Real.sqrt N) :=
      mul_le_mul_of_nonneg_left hP' (by positivity)
    _ =
        (N : ℝ) * Real.sqrt N *
          boundedRatioThreeHalvesResidual C κ₀ N L := by
      unfold boundedRatioThreeHalvesResidual
      dsimp only [K]
      ring

/-- The endpoint supremum is uniformly little-oh of `N²`. -/
theorem boundedRationalMassSup_uniformLittleO_square
    {C : ℝ} (hC : 0 ≤ C) (κ₀ A : ℕ) (hA : 1 ≤ A) :
    UniformLittleOOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun N L =>
        ((boundedRationalMassSup κ₀ A N L : ℕ) : ℝ))
      (fun N _ => (N : ℝ) ^ 2) := by
  apply UniformRationalPower.littleO_natPower_of_lt
    (p := 3) (q := 2) (r := 2) (by omega)
  simpa only [UniformThreeHalvesSubpolynomialOn,
    UniformRationalPowerSubpolynomialOn] using
      boundedRationalMassSup_uniformThreeHalves
        hC κ₀ A hA

/--
Literal quantified bounded-ratio conclusion needed for Lemma 17.5 and
Proposition 16.1.
-/
theorem boundedRationalMass_uniformLittleO_square
    {C : ℝ} (hC : 0 ≤ C) (κ₀ A : ℕ) (hA : 1 ≤ A) :
    ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ M L,
        2 * N ≤ M →
        M ≤ κ₀ * N →
        CriticalRunWindow.InRunLengthWindow C N L →
        |((boundedRationalMass N M A L 2 : ℕ) : ℝ)| ≤
          ε * |(N : ℝ) ^ 2| := by
  intro ε hε
  obtain ⟨N₀, hN₀⟩ :=
    boundedRationalMassSup_uniformLittleO_square
      hC κ₀ A hA ε hε
  refine ⟨N₀, ?_⟩
  intro N hN M L hNM hM hrun
  have hfinite :=
    boundedRationalMass_le_sup
      (κ₀ := κ₀) (A := A) (L := L) hNM hM
  have hcast :
      ((boundedRationalMass N M A L 2 : ℕ) : ℝ) ≤
        ((boundedRationalMassSup κ₀ A N L : ℕ) : ℝ) := by
    exact_mod_cast hfinite
  have hsup := hN₀ N hN L hrun
  rw [abs_of_nonneg (by positivity :
      (0 : ℝ) ≤ (boundedRationalMassSup κ₀ A N L : ℕ))] at hsup
  rw [abs_of_nonneg (by positivity :
      (0 : ℝ) ≤ (boundedRationalMass N M A L 2 : ℕ))]
  exact hcast.trans hsup

/--
Lemma 17.6 is literally the already certified geometry-only channel sum:
there is no endpoint or translation variable to transport.
-/
theorem boundedRatio_weightedChannelGeometry_uniformLinearSubpolynomial
    {C : ℝ} (hC : 0 ≤ C) :
    UniformLinearSubpolynomialOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun _ L => (weightedChannelMass L : ℝ)) :=
  WeightedChannelMassCritical.weightedChannelMass_uniformLinearSubpolynomial
    hC

end

end BoundedRatioRationalMass
end PaperC
