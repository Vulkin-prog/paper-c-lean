import PaperCV282.GeneralPoissonMarking
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Probability.Distributions.Uniform

/-! # Uniform spatial cells and the deterministic grid approximation -/
namespace PaperC.V282.UniformSpatialGrid

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

noncomputable section

def unitIntervalUniformMeasure : Measure unitInterval :=
  volume.comap ((↑) : unitInterval → ℝ)

instance instProbabilityUnitIntervalUniform : IsProbabilityMeasure unitIntervalUniformMeasure := by
  constructor
  rw [unitIntervalUniformMeasure,comap_subtype_coe_apply measurableSet_Icc,
    Set.image_univ,Subtype.range_coe]
  norm_num [Real.volume_Icc]

theorem unitIntervalUniform_coe_preimage (t : Set ℝ) :
    unitIntervalUniformMeasure (((↑) : unitInterval → ℝ) ⁻¹' t)=
      volume (t ∩ Set.Icc (0 : ℝ) 1) := by
  rw [unitIntervalUniformMeasure,comap_subtype_coe_apply measurableSet_Icc]
  congr 1
  ext x
  simp only [Set.mem_image,Set.mem_preimage,Set.mem_inter_iff,Set.mem_Icc]
  constructor
  · rintro ⟨u,hu,rfl⟩
    exact ⟨hu,u.property⟩
  · rintro ⟨hx,hbound⟩
    exact ⟨⟨x,hbound⟩,hx,rfl⟩

theorem ae_unitInterval_lt_one :
    ∀ᵐ u : unitInterval ∂unitIntervalUniformMeasure, (u : ℝ)<1 := by
  have hne : ∀ᵐ u : unitInterval ∂unitIntervalUniformMeasure, (u : ℝ)≠1 := by
    rw [ae_iff]
    simp only [not_not]
    have hset : {u : unitInterval | (u : ℝ)=1}=((↑) : unitInterval → ℝ) ⁻¹' {1} := by ext u; simp
    rw [hset,unitIntervalUniform_coe_preimage]
    simp
  filter_upwards [hne] with u hu
  exact lt_of_le_of_ne u.property.2 hu

def gridSite (N : ℕ) (hN : 0<N) (u : unitInterval) : Fin N :=
  ⟨min ⌊(N : ℝ)*(u : ℝ)⌋₊ (N-1),lt_of_le_of_lt (min_le_right _ _) (by omega)⟩

def uniformGridMeasure (N : ℕ) (hN : 0<N) : Measure (Fin N) := by
  letI : NeZero N := ⟨ne_of_gt hN⟩
  exact (PMF.uniformOfFintype (Fin N)).toMeasure

instance instProbabilityUniformGrid (N : ℕ) (hN : 0<N) :
    IsProbabilityMeasure (uniformGridMeasure N hN) := by
  unfold uniformGridMeasure
  infer_instance

theorem measurable_gridSite (N : ℕ) (hN : 0<N) : Measurable (gridSite N hN) := by
  exact (measurable_of_countable (fun k : ℕ =>
    (⟨min k (N-1),lt_of_le_of_lt (min_le_right _ _) (by omega)⟩ : Fin N))).comp
      ((measurable_const.mul measurable_subtype_coe).nat_floor)

theorem gridSite_eq_iff_of_lt_one (N : ℕ) (hN : 0<N) (u : unitInterval)
    (hu : (u : ℝ)<1) (i : Fin N) :
    gridSite N hN u=i ↔ (i.val : ℝ)/(N : ℝ)≤(u : ℝ) ∧
      (u : ℝ)<((i.val : ℝ)+1)/(N : ℝ) := by
  have hNR : 0<(N : ℝ) := by exact_mod_cast hN
  have hpos : 0≤(N : ℝ)*(u : ℝ) := mul_nonneg hNR.le u.property.1
  have hfloor : ⌊(N : ℝ)*(u : ℝ)⌋₊<N := (Nat.floor_lt hpos).mpr (by nlinarith)
  rw [Fin.ext_iff]
  change min ⌊(N : ℝ)*(u : ℝ)⌋₊ (N-1)=i.val ↔ _
  rw [min_eq_left (by omega),Nat.floor_eq_iff hpos,
    div_le_iff₀ hNR,lt_div_iff₀ hNR]
  simp only [mul_comm]

theorem grid_cell_probability (N : ℕ) (hN : 0<N) (i : Fin N) :
    unitIntervalUniformMeasure {u | gridSite N hN u=i}=(N : ℝ≥0∞)⁻¹ := by
  have hNR : 0<(N : ℝ) := by exact_mod_cast hN
  have hsub : Set.Ico ((i.val : ℝ)/(N : ℝ)) (((i.val : ℝ)+1)/(N : ℝ)) ⊆
      Set.Icc (0 : ℝ) 1 := by
    intro x hx
    refine ⟨(div_nonneg (Nat.cast_nonneg _) hNR.le).trans hx.1,?_⟩
    have hi : (i.val : ℝ)+1≤(N : ℝ) := by exact_mod_cast i.isLt
    exact hx.2.le.trans ((div_le_one hNR).mpr hi)
  calc
    _ = unitIntervalUniformMeasure (((↑) : unitInterval → ℝ) ⁻¹'
        Set.Ico ((i.val : ℝ)/(N : ℝ)) (((i.val : ℝ)+1)/(N : ℝ))) := by
      apply measure_congr
      filter_upwards [ae_unitInterval_lt_one] with u hu
      exact propext (gridSite_eq_iff_of_lt_one N hN u hu i)
    _ = volume (Set.Ico ((i.val : ℝ)/(N : ℝ)) (((i.val : ℝ)+1)/(N : ℝ))) := by
      rw [unitIntervalUniform_coe_preimage,Set.inter_eq_left.mpr hsub]
    _ = ENNReal.ofReal ((N : ℝ)⁻¹) := by
      rw [Real.volume_Ico]
      congr 1
      field_simp
      ring
    _ = _ := by rw [ENNReal.ofReal_inv_of_pos hNR]; simp

theorem hasLaw_gridSite (N : ℕ) (hN : 0<N) :
    HasLaw (gridSite N hN) (uniformGridMeasure N hN) unitIntervalUniformMeasure := by
  refine ⟨(measurable_gridSite N hN).aemeasurable,?_⟩
  apply Measure.ext_of_singleton
  intro i
  rw [Measure.map_apply (measurable_gridSite N hN) (measurableSet_singleton _)]
  have hset : gridSite N hN ⁻¹' {i}={u | gridSite N hN u=i} := by ext u; simp
  rw [hset,grid_cell_probability]
  simp [uniformGridMeasure,PMF.uniformOfFintype_apply]


theorem gridSite_position_bounds (N : ℕ) (hN : 0<N) (u : unitInterval) :
    ((gridSite N hN u).val : ℝ)/(N : ℝ)≤(u : ℝ) ∧
      (u : ℝ)≤((gridSite N hN u).val : ℝ)/(N : ℝ)+1/(N : ℝ) := by
  have hNR : 0<(N : ℝ) := by exact_mod_cast hN
  have hpos : 0≤(N : ℝ)*(u : ℝ) := mul_nonneg hNR.le u.property.1
  have hfloor := Nat.floor_le hpos
  have hlow : ((gridSite N hN u).val : ℝ)≤(N : ℝ)*(u : ℝ) := by
    have hmin : ((gridSite N hN u).val : ℝ)≤(⌊(N : ℝ)*(u : ℝ)⌋₊ : ℝ) := by
      exact_mod_cast (min_le_left ⌊(N : ℝ)*(u : ℝ)⌋₊ (N-1))
    exact hmin.trans hfloor
  have hupp : (N : ℝ)*(u : ℝ)≤((gridSite N hN u).val : ℝ)+1 := by
    by_cases h : ⌊(N : ℝ)*(u : ℝ)⌋₊≤N-1
    · change (N : ℝ)*(u : ℝ)≤(min ⌊(N : ℝ)*(u : ℝ)⌋₊ (N-1) : ℕ)+1
      rw [min_eq_left h]
      exact (Nat.lt_floor_add_one _).le
    · change (N : ℝ)*(u : ℝ)≤(min ⌊(N : ℝ)*(u : ℝ)⌋₊ (N-1) : ℕ)+1
      rw [min_eq_right (by omega)]
      have hsub : ((N-1 : ℕ) : ℝ)+1=(N : ℝ) := by
        exact_mod_cast (Nat.sub_add_cancel (by omega : 1≤N))
      rw [hsub]
      nlinarith [u.property.2]
  constructor
  · apply (div_le_iff₀ hNR).mpr
    nlinarith
  · rw [← add_div]
    apply (le_div_iff₀ hNR).mpr
    nlinarith

theorem gridSite_position_error_le (N : ℕ) (hN : 0<N) (u : unitInterval) :
    |((gridSite N hN u).val : ℝ)/(N : ℝ)-(u : ℝ)|≤1/(N : ℝ) := by
  obtain ⟨hlo,hhi⟩ := gridSite_position_bounds N hN u
  rw [abs_of_nonpos (sub_nonpos.mpr hlo)]
  linarith

theorem physical_grid_position_error_le (N : ℕ) (hN : 0<N) (u : unitInterval) :
    |(1+((gridSite N hN u).val : ℝ)/(N : ℝ))-(1+(u : ℝ))|≤1/(N : ℝ) := by
  simpa only [add_sub_add_left_eq_sub] using gridSite_position_error_le N hN u


theorem gridSite_position_tendsto (N : ℕ → ℕ) (hN : ∀ n,0<N n)
    (hlim : Filter.Tendsto N Filter.atTop Filter.atTop) (u : unitInterval) :
    Filter.Tendsto (fun n => ((gridSite (N n) (hN n) u).val : ℝ)/(N n : ℝ))
      Filter.atTop (nhds (u : ℝ)) := by
  rw [← tendsto_sub_nhds_zero_iff]
  apply squeeze_zero_norm (fun n => ?_)
    ((tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hlim)
  simpa only [Real.norm_eq_abs,Function.comp_apply] using gridSite_position_error_le (N n) (hN n) u

theorem physical_grid_position_tendsto (N : ℕ → ℕ) (hN : ∀ n,0<N n)
    (hlim : Filter.Tendsto N Filter.atTop Filter.atTop) (u : unitInterval) :
    Filter.Tendsto (fun n => 1+((gridSite (N n) (hN n) u).val : ℝ)/(N n : ℝ))
      Filter.atTop (nhds (1+(u : ℝ))) :=
  Filter.Tendsto.const_add 1 (gridSite_position_tendsto N hN hlim u)

end
end PaperC.V282.UniformSpatialGrid
