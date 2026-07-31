import PaperC.Model.FiniteRademacher
import Mathlib.Analysis.BoxIntegral.UnitPartition
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Spatial Riemann sums on the dyadic block

This module supplies the analytic limit used in Sections 14.2 and 14.4.
The interval `[1,2)` is first represented as a one-dimensional box inside
`PUnit → ℝ`; this is the native form of Mathlib's unit-lattice Riemann-sum
theorem.  A later section identifies the lattice sum with the literal
integer grid `x / N`, `N ≤ x < 2N`.
-/

namespace PaperC
namespace SpatialRiemannSums

open scoped BigOperators Pointwise Topology
open Filter MeasureTheory Set Submodule

noncomputable section

/-- The one-dimensional Euclidean space used by the unit-lattice theorem. -/
abbrev Line := Unit → ℝ

/-- Evaluation of a point of the one-dimensional model. -/
def coordinate (z : Line) : ℝ := z Unit.unit

/-- The half-open spatial interval `[1,2)` in the one-dimensional model. -/
def spatialStrip : Set Line :=
  coordinate ⁻¹' Set.Ico (1 : ℝ) 2

/-- The standard integer lattice in the one-dimensional model. -/
def integerLattice : Submodule ℤ Line :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ Unit))

/--
The normalized lattice Riemann sum on `[1,2)`.

Its indexing set says literally that `z ∈ [1,2)` and that `N z` has an
integer coordinate.
-/
def spatialRiemannSum (N : ℕ) (f : ℝ → ℝ) : ℝ :=
  (∑' z : ↑(spatialStrip ∩ (N : ℝ)⁻¹ • integerLattice),
      f (coordinate z.1)) / (N : ℝ)

/-- The literal normalized sum over `x ∈ [N,2N)`. -/
def dyadicRiemannSum (N : ℕ) (f : ℝ → ℝ) : ℝ :=
  (∑ x ∈ dyadicBlock N, f ((x : ℝ) / (N : ℝ))) / (N : ℝ)

private theorem continuous_coordinate : Continuous coordinate := by
  exact continuous_apply Unit.unit

private theorem isBounded_spatialStrip : Bornology.IsBounded spatialStrip := by
  rw [isBounded_iff_forall_norm_le]
  refine ⟨2, ?_⟩
  intro z hz
  have hz' : coordinate z ∈ Set.Ico (1 : ℝ) 2 := hz
  have hcoord : |coordinate z| ≤ 2 := by
    rw [abs_le]
    exact ⟨by linarith [hz'.1], hz'.2.le⟩
  simpa only [show ‖z‖ = ‖z ()‖ by rw [Pi.norm_def]; simp,
    Real.norm_eq_abs, coordinate] using hcoord

private theorem measurableSet_spatialStrip : MeasurableSet spatialStrip :=
  measurableSet_Ico.preimage continuous_coordinate.measurable

private theorem volume_frontier_spatialStrip :
    volume (frontier spatialStrip) = 0 := by
  let e : Line ≃ₜ ℝ := Homeomorph.piUnique (fun _ : Unit ↦ ℝ)
  have hs : spatialStrip = e ⁻¹' Set.Ico (1 : ℝ) 2 := rfl
  rw [hs, ← e.preimage_frontier]
  have hfront : frontier (Set.Ico (1 : ℝ) 2) = ({1, 2} : Set ℝ) :=
    frontier_Ico (by norm_num)
  rw [hfront]
  exact
    (volume_preserving_piUnique (fun _ : Unit ↦ ℝ)).measure_preimage
      (by measurability : MeasurableSet ({1, 2} : Set ℝ)).nullMeasurableSet
      |>.trans ((Set.toFinite {1, 2}).measure_zero volume)

private theorem integral_lift_eq (f : ℝ → ℝ) :
    (∫ z in spatialStrip, f (coordinate z)) =
      ∫ t in Set.Ico (1 : ℝ) 2, f t := by
  let e : Line ≃ᵐ ℝ := MeasurableEquiv.piUnique (fun _ : Unit ↦ ℝ)
  have hmp : MeasurePreserving e volume volume :=
    volume_preserving_piUnique (fun _ : Unit ↦ ℝ)
  have hs : spatialStrip = e ⁻¹' Set.Ico (1 : ℝ) 2 := rfl
  calc
    (∫ z in spatialStrip, f (coordinate z)) =
        ∫ z, spatialStrip.indicator (fun z ↦ f (coordinate z)) z :=
      (integral_indicator measurableSet_spatialStrip).symm
    _ = ∫ z, (Set.Ico (1 : ℝ) 2).indicator f (e z) := by
      rfl
    _ = ∫ t, (Set.Ico (1 : ℝ) 2).indicator f t :=
      hmp.integral_comp' _
    _ = ∫ t in Set.Ico (1 : ℝ) 2, f t :=
      integral_indicator measurableSet_Ico

/--
Riemann sums over the normalized lattice in `[1,2)` converge to the
Lebesgue integral of every continuous test function.
-/
theorem tendsto_spatialRiemannSum
    {f : ℝ → ℝ} (hf : Continuous f) :
    Tendsto (fun N : ℕ ↦ spatialRiemannSum N f) atTop
      (𝓝 (∫ t in Set.Ico (1 : ℝ) 2, f t)) := by
  have h :=
    tendsto_tsum_div_pow_atTop_integral
      spatialStrip (fun z : Line ↦ f (coordinate z))
      (hf.comp continuous_coordinate)
      isBounded_spatialStrip measurableSet_spatialStrip
      volume_frontier_spatialStrip
  have hcard : Fintype.card Unit = 1 := Fintype.card_unique
  simpa only [spatialRiemannSum, integerLattice, hcard, pow_one,
    integral_lift_eq] using h

private def natGridPoint (N x : ℕ) : Line :=
  fun _ ↦ (x : ℝ) / (N : ℝ)

private theorem natGridPoint_mem
    {N x : ℕ} (hN : 0 < N) (hx : x ∈ dyadicBlock N) :
    natGridPoint N x ∈
      spatialStrip ∩ (N : ℝ)⁻¹ • integerLattice := by
  haveI : NeZero N := ⟨hN.ne'⟩
  have hx' : N ≤ x ∧ x < 2 * N := by
    simpa only [dyadicBlock] using Finset.mem_Ico.mp hx
  constructor
  · change (x : ℝ) / (N : ℝ) ∈ Set.Ico (1 : ℝ) 2
    constructor
    · rw [le_div_iff₀ (Nat.cast_pos.mpr hN)]
      simpa using (show (N : ℝ) ≤ (x : ℝ) by exact_mod_cast hx'.1)
    · rw [div_lt_iff₀ (Nat.cast_pos.mpr hN)]
      exact_mod_cast hx'.2
  · change natGridPoint N x ∈
      (N : ℝ)⁻¹ •
        (Submodule.span ℤ
          (Set.range (Pi.basisFun ℝ Unit)) : Set Line)
    have hmem :
        natGridPoint N x ∈
          (N : ℝ)⁻¹ •
            Submodule.span ℤ
              (Set.range (Pi.basisFun ℝ Unit)) := by
      apply
        (BoxIntegral.unitPartition.mem_smul_span_iff
          (n := N) (v := natGridPoint N x)).2
      intro i
      refine ⟨(x : ℤ), ?_⟩
      simp only [natGridPoint, algebraMap_int_eq, map_natCast]
      field_simp
    exact hmem

private def dyadicGridEmbedding
    (N : ℕ) (hN : 0 < N) :
    {x // x ∈ dyadicBlock N} →
      ↑(spatialStrip ∩ (N : ℝ)⁻¹ • integerLattice) :=
  fun x ↦ ⟨natGridPoint N x.1, natGridPoint_mem hN x.2⟩

private theorem dyadicGridEmbedding_injective
    (N : ℕ) (hN : 0 < N) :
    Function.Injective (dyadicGridEmbedding N hN) := by
  intro x y hxy
  apply Subtype.ext
  have hcoord :
      (x.1 : ℝ) / (N : ℝ) = (y.1 : ℝ) / (N : ℝ) := by
    have := congr_fun (congr_arg Subtype.val hxy) Unit.unit
    simpa only [dyadicGridEmbedding, natGridPoint] using this
  have hcast : (x.1 : ℝ) = (y.1 : ℝ) := by
    exact (div_left_inj' (Nat.cast_ne_zero.mpr hN.ne')).mp hcoord
  exact_mod_cast hcast

private noncomputable def gridInteger
    (N : ℕ) (hN : 0 < N)
    (z : ↑(spatialStrip ∩ (N : ℝ)⁻¹ • integerLattice)) : ℤ := by
  letI : NeZero N := ⟨hN.ne'⟩
  exact Classical.choose
    ((BoxIntegral.unitPartition.mem_smul_span_iff.mp
      (by
        change z.1 ∈
          (N : ℝ)⁻¹ •
            (Submodule.span ℤ
              (Set.range (Pi.basisFun ℝ Unit)) : Set Line)
        simpa only [integerLattice] using z.2.2)) Unit.unit)

private theorem gridInteger_spec
    (N : ℕ) (hN : 0 < N)
    (z : ↑(spatialStrip ∩ (N : ℝ)⁻¹ • integerLattice)) :
    (gridInteger N hN z : ℝ) =
      (N : ℝ) * coordinate z.1 := by
  letI : NeZero N := ⟨hN.ne'⟩
  exact Classical.choose_spec
    ((BoxIntegral.unitPartition.mem_smul_span_iff.mp
      (by
        change z.1 ∈
          (N : ℝ)⁻¹ •
            (Submodule.span ℤ
              (Set.range (Pi.basisFun ℝ Unit)) : Set Line)
        simpa only [integerLattice] using z.2.2)) Unit.unit)

private theorem gridInteger_nonneg
    (N : ℕ) (hN : 0 < N)
    (z : ↑(spatialStrip ∩ (N : ℝ)⁻¹ • integerLattice)) :
    0 ≤ gridInteger N hN z := by
  have hz : (1 : ℝ) ≤ coordinate z.1 := z.2.1.1
  have hreal : (0 : ℝ) ≤ (gridInteger N hN z : ℝ) := by
    rw [gridInteger_spec]
    positivity
  exact_mod_cast hreal

private theorem gridInteger_toNat_mem
    (N : ℕ) (hN : 0 < N)
    (z : ↑(spatialStrip ∩ (N : ℝ)⁻¹ • integerLattice)) :
    (gridInteger N hN z).toNat ∈ dyadicBlock N := by
  have hz : coordinate z.1 ∈ Set.Ico (1 : ℝ) 2 := z.2.1
  have hto :
      ((gridInteger N hN z).toNat : ℤ) =
        gridInteger N hN z :=
    Int.toNat_of_nonneg (gridInteger_nonneg N hN z)
  have htoReal :
      ((gridInteger N hN z).toNat : ℝ) =
        (gridInteger N hN z : ℝ) := by
    exact_mod_cast hto
  simp only [dyadicBlock, Finset.mem_Ico]
  have hlowReal : (N : ℝ) ≤
      ((gridInteger N hN z).toNat : ℝ) := by
    rw [htoReal, gridInteger_spec]
    have := mul_le_mul_of_nonneg_left hz.1
      (Nat.cast_nonneg N)
    simpa using this
  have hhighReal :
      ((gridInteger N hN z).toNat : ℝ) <
        ((2 * N : ℕ) : ℝ) := by
    rw [htoReal, gridInteger_spec]
    calc
      (N : ℝ) * coordinate z.1 < (N : ℝ) * 2 :=
        mul_lt_mul_of_pos_left hz.2 (Nat.cast_pos.mpr hN)
      _ = ((2 * N : ℕ) : ℝ) := by push_cast; ring
  exact ⟨by exact_mod_cast hlowReal, by exact_mod_cast hhighReal⟩

private theorem dyadicGridEmbedding_surjective
    (N : ℕ) (hN : 0 < N) :
    Function.Surjective (dyadicGridEmbedding N hN) := by
  intro z
  let x : {x // x ∈ dyadicBlock N} :=
    ⟨(gridInteger N hN z).toNat,
      gridInteger_toNat_mem N hN z⟩
  refine ⟨x, Subtype.ext ?_⟩
  funext i
  have hto :
      ((gridInteger N hN z).toNat : ℤ) =
        gridInteger N hN z :=
    Int.toNat_of_nonneg (gridInteger_nonneg N hN z)
  have htoReal :
      ((gridInteger N hN z).toNat : ℝ) =
        (gridInteger N hN z : ℝ) := by
    exact_mod_cast hto
  simp only [dyadicGridEmbedding, natGridPoint, x]
  rw [htoReal, gridInteger_spec, coordinate]
  field_simp

private noncomputable def dyadicGridEquiv
    (N : ℕ) (hN : 0 < N) :
    {x // x ∈ dyadicBlock N} ≃
      ↑(spatialStrip ∩ (N : ℝ)⁻¹ • integerLattice) :=
  Equiv.ofBijective (dyadicGridEmbedding N hN)
    ⟨dyadicGridEmbedding_injective N hN,
      dyadicGridEmbedding_surjective N hN⟩

/--
The lattice formulation is exactly the manuscript's finite sum over
`N ≤ x < 2N`; this is not merely an asymptotic comparison.
-/
theorem spatialRiemannSum_eq_dyadicRiemannSum
    {N : ℕ} (hN : 0 < N) (f : ℝ → ℝ) :
    spatialRiemannSum N f = dyadicRiemannSum N f := by
  classical
  unfold spatialRiemannSum dyadicRiemannSum
  congr 1
  calc
    (∑' z : ↑(spatialStrip ∩ (N : ℝ)⁻¹ • integerLattice),
        f (coordinate z.1)) =
        ∑' x : {x // x ∈ dyadicBlock N},
          f (coordinate ((dyadicGridEquiv N hN) x).1) :=
      ((dyadicGridEquiv N hN).tsum_eq
        (fun z ↦ f (coordinate z.1))).symm
    _ = ∑' x : {x // x ∈ dyadicBlock N},
          f ((x.1 : ℝ) / (N : ℝ)) := by
      apply tsum_congr
      intro x
      rfl
    _ = ∑ x : {x // x ∈ dyadicBlock N},
          f ((x.1 : ℝ) / (N : ℝ)) := by
      rw [tsum_fintype]
    _ = ∑ x ∈ dyadicBlock N,
          f ((x : ℝ) / (N : ℝ)) := by
      exact (Finset.sum_subtype (dyadicBlock N)
        (fun _ ↦ Iff.rfl)
        (fun x ↦ f ((x : ℝ) / (N : ℝ)))).symm

/--
Literal Riemann sums on the dyadic integer block converge to the integral
over `[1,2)`.
-/
theorem tendsto_dyadicRiemannSum
    {f : ℝ → ℝ} (hf : Continuous f) :
    Tendsto (fun N : ℕ ↦ dyadicRiemannSum N f) atTop
      (𝓝 (∫ t in Set.Ico (1 : ℝ) 2, f t)) := by
  apply (tendsto_spatialRiemannSum hf).congr'
  filter_upwards [eventually_atTop.2 ⟨1, fun N hN ↦ hN⟩] with N hN
  exact spatialRiemannSum_eq_dyadicRiemannSum
    (Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hN)) f

/-- Clamp the real line to the compact interval `[1,2]`. -/
def dyadicClamp (t : ℝ) : ℝ :=
  max 1 (min t 2)

theorem continuous_dyadicClamp :
    Continuous dyadicClamp := by
  exact continuous_const.max (continuous_id.min continuous_const)

theorem dyadicClamp_mem_Icc (t : ℝ) :
    dyadicClamp t ∈ Set.Icc (1 : ℝ) 2 := by
  constructor
  · exact le_max_left _ _
  · unfold dyadicClamp
    exact max_le (by norm_num) (min_le_right _ _)

theorem dyadicClamp_eq_self
    {t : ℝ} (ht : t ∈ Set.Icc (1 : ℝ) 2) :
    dyadicClamp t = t := by
  unfold dyadicClamp
  rw [min_eq_left ht.2, max_eq_right ht.1]

private theorem continuous_clampExtension
    {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc (1 : ℝ) 2)) :
    Continuous (fun t ↦ f (dyadicClamp t)) := by
  rw [← continuousOn_univ]
  exact hf.comp continuous_dyadicClamp.continuousOn
    (fun t _ht ↦ dyadicClamp_mem_Icc t)

private theorem dyadicRiemannSum_clampExtension_eq
    {N : ℕ} (hN : 0 < N) (f : ℝ → ℝ) :
    dyadicRiemannSum N (fun t ↦ f (dyadicClamp t)) =
      dyadicRiemannSum N f := by
  unfold dyadicRiemannSum
  apply congrArg (fun a : ℝ ↦ a / (N : ℝ))
  apply Finset.sum_congr rfl
  intro x hx
  change f (dyadicClamp ((x : ℝ) / (N : ℝ))) =
    f ((x : ℝ) / (N : ℝ))
  apply congrArg f
  apply dyadicClamp_eq_self
  have hx' : N ≤ x ∧ x < 2 * N := by
    simpa only [dyadicBlock] using Finset.mem_Ico.mp hx
  constructor
  · rw [le_div_iff₀ (Nat.cast_pos.mpr hN)]
    simpa using (show (N : ℝ) ≤ (x : ℝ) by exact_mod_cast hx'.1)
  · rw [div_le_iff₀ (Nat.cast_pos.mpr hN)]
    exact_mod_cast hx'.2.le

private theorem integral_clampExtension_eq
    (f : ℝ → ℝ) :
    (∫ t in Set.Ico (1 : ℝ) 2, f (dyadicClamp t)) =
      ∫ t in Set.Ico (1 : ℝ) 2, f t := by
  apply setIntegral_congr_fun measurableSet_Ico
  intro t ht
  change f (dyadicClamp t) = f t
  rw [dyadicClamp_eq_self ⟨ht.1, ht.2.le⟩]

/--
Source-shaped version: continuity is required only on `[1,2]`, exactly as
in the manuscript.
-/
theorem tendsto_dyadicRiemannSum_of_continuousOn
    {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc (1 : ℝ) 2)) :
    Tendsto (fun N : ℕ ↦ dyadicRiemannSum N f) atTop
      (𝓝 (∫ t in Set.Ico (1 : ℝ) 2, f t)) := by
  have h :=
    tendsto_dyadicRiemannSum
      (continuous_clampExtension hf)
  rw [integral_clampExtension_eq] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact dyadicRiemannSum_clampExtension_eq
    (Nat.zero_lt_of_lt hN) f

end

end SpatialRiemannSums
end PaperC
