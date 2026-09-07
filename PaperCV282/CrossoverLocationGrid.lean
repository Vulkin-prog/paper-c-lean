import PaperCV282.BulkPopulation
import PaperCV282.CrossoverBulkOnePoint
import PaperCV282.CountableWeakTransfer

/-! # A true uniform bulk site coupled to Lebesgue measure on the unit interval -/
namespace PaperC.V282.CrossoverLocationGrid

open MeasureTheory ProbabilityTheory Filter Topology BulkPopulation BulkMarkedGeometry
open CrossoverBulkOnePoint UniformSpatialGrid CountableWeakTransfer
open scoped NNReal ENNReal BoundedContinuousFunction

noncomputable section
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

/-- Increasing enumeration of the literal integer interval, including both endpoints. -/
def intervalSiteEquiv (a b : ℕ) : Fin (Finset.Icc a b).card ≃ {x // x∈Finset.Icc a b} where
  toFun i := ⟨a+i.val, by
    have hi : i.val < b+1-a := by simpa only [Nat.card_Icc] using i.isLt
    exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩⟩
  invFun x := ⟨x.val-a, by
    have hx := Finset.mem_Icc.mp x.property
    rw [Nat.card_Icc]
    omega⟩
  left_inv i := by apply Fin.ext; dsimp; omega
  right_inv x := by apply Subtype.ext; have hx := Finset.mem_Icc.mp x.property; dsimp; omega

/-- The sampled site has exactly the uniform distribution on the contained population. -/
def bulkGridSite (M L : ℕ) (delta : ℝ) (hs : (bulkStarts M L delta).Nonempty)
    (u : unitInterval) : bulkStarts M L delta :=
  intervalSiteEquiv ⌈(M : ℝ)^delta⌉₊ (M-L+1)
    (gridSite (bulkStarts M L delta).card (Finset.card_pos.mpr hs) u)

theorem measurable_bulkGridSite (M L : ℕ) (delta : ℝ) (hs : (bulkStarts M L delta).Nonempty) :
    Measurable (bulkGridSite M L delta hs) :=
  (measurable_of_countable _).comp (measurable_gridSite _ _)

theorem bulkGridSite_coe (M L : ℕ) (delta : ℝ) (hs : (bulkStarts M L delta).Nonempty) (u : unitInterval) :
    (bulkGridSite M L delta hs u).val = ⌈(M : ℝ)^delta⌉₊+
      (gridSite (bulkStarts M L delta).card (Finset.card_pos.mpr hs) u).val := rfl

theorem hasLaw_bulkGridSite (M L : ℕ) (delta : ℝ) (hs : (bulkStarts M L delta).Nonempty) :
    HasLaw (bulkGridSite M L delta hs) (uniformSiteMeasure (bulkStarts M L delta) hs)
      unitIntervalUniformMeasure := by
  refine ⟨(measurable_bulkGridSite M L delta hs).aemeasurable,?_⟩
  apply Measure.ext_of_singleton
  intro x
  rw [Measure.map_apply (measurable_bulkGridSite M L delta hs) (measurableSet_singleton _)]
  have he : bulkGridSite M L delta hs ⁻¹' {x} =
      {u | gridSite (bulkStarts M L delta).card (Finset.card_pos.mpr hs) u =
        (intervalSiteEquiv ⌈(M : ℝ)^delta⌉₊ (M-L+1)).symm x} := by
    ext u
    simp only [bulkGridSite,Set.mem_preimage,Set.mem_singleton_iff,Set.mem_setOf_eq]
    exact (intervalSiteEquiv ⌈(M : ℝ)^delta⌉₊ (M-L+1)).apply_eq_iff_eq_symm_apply
  rw [he,grid_cell_probability]
  simp [uniformSiteMeasure,PMF.uniformOfFintype_apply]

/-- The fallback is irrelevant eventually but makes the law total for all prefix sizes. -/
def bulkGridPosition (M L : ℕ) (delta : ℝ) (u : unitInterval) : ℝ :=
  if hs : (bulkStarts M L delta).Nonempty then (bulkGridSite M L delta hs u).val/M else 0

theorem measurable_bulkGridPosition (M L : ℕ) (delta : ℝ) : Measurable (bulkGridPosition M L delta) := by
  unfold bulkGridPosition
  split_ifs with hs
  · exact ((measurable_of_countable (fun k : ℕ => (k : ℝ))).comp
      (measurable_bulkGridSite M L delta hs).subtype_coe).div_const _
  · exact measurable_const

/-- This is the actual uniform-site image law, with a harmless atom for an empty population. -/
def bulkLocationLaw (M L : ℕ) (delta : ℝ) : ProbabilityMeasure ℝ :=
  imageProbabilityLaw unitIntervalUniformMeasure (bulkGridPosition M L delta)
    (measurable_bulkGridPosition M L delta)

def unitIntervalLaw : ProbabilityMeasure ℝ :=
  imageProbabilityLaw unitIntervalUniformMeasure ((↑) : unitInterval→ℝ) measurable_subtype_coe

/-- The continuous target is literally Lebesgue measure restricted to the unit interval. -/
theorem unitIntervalLaw_eq_volume_restrict :
    (unitIntervalLaw : Measure ℝ) = volume.restrict (Set.Icc (0 : ℝ) 1) := by
  ext A hA
  change (unitIntervalUniformMeasure.map ((↑) : unitInterval→ℝ)) A = _
  rw [Measure.map_apply measurable_subtype_coe hA,unitIntervalUniform_coe_preimage,
    Measure.restrict_apply hA]

theorem bulkLocationLaw_eq_uniform_site (M L : ℕ) (delta : ℝ) (hs : (bulkStarts M L delta).Nonempty) :
    (bulkLocationLaw M L delta : Measure ℝ) =
      (uniformSiteMeasure (bulkStarts M L delta) hs).map (fun x => (x.val : ℝ)/M) := by
  have h := (hasLaw_bulkGridSite M L delta hs).map_eq
  rw [← h,Measure.map_map (measurable_of_countable _) (measurable_bulkGridSite M L delta hs)]
  change unitIntervalUniformMeasure.map (bulkGridPosition M L delta) = _
  congr 1
  funext u
  simp only [bulkGridPosition, dif_pos hs, Function.comp_def]

theorem bulk_nonempty_eventually
    (sizes lengths : ℕ→ℕ) (hsizes : Tendsto sizes atTop atTop)
    (beta delta : ℝ) (hdelta : 0<delta) (hdeltaOne : delta<1)
    (hupper : ∀ᶠ n in atTop,(lengths n : ℝ)≤beta*Real.log (sizes n))
    (hpositive : ∀ᶠ n in atTop,1≤lengths n) :
    ∀ᶠ n in atTop,(bulkStarts (sizes n) (lengths n) delta).Nonempty := by
  have ht := population_ratio_tendsto_one sizes lengths hsizes beta delta hdelta hdeltaOne hupper hpositive
  filter_upwards [ht.eventually (lt_mem_nhds (by norm_num : (0 : ℝ)<1))] with n hn
  apply Finset.card_pos.mp
  by_contra hc
  have he : (bulkStarts (sizes n) (lengths n) delta).card=0 := by omega
  simp only [he,Nat.cast_zero,zero_div,lt_self_iff_false] at hn

theorem bulkGridPosition_error_le {M L : ℕ} {delta : ℝ} (hM : 0<M)
    (hs : (bulkStarts M L delta).Nonempty) (u : unitInterval) :
    |bulkGridPosition M L delta u-(u : ℝ)| ≤
      (⌈(M : ℝ)^delta⌉₊ : ℝ)/M +
        |((bulkStarts M L delta).card : ℝ)/M-1|+1/(M : ℝ) := by
  let K := (bulkStarts M L delta).card
  have hK : 0<K := Finset.card_pos.mpr hs
  have hMr : (0 : ℝ)<M := by exact_mod_cast hM
  have hKr : (0 : ℝ)<K := by exact_mod_cast hK
  have hgrid := gridSite_position_error_le K hK u
  have hscaled := mul_le_mul_of_nonneg_right hgrid (div_nonneg hKr.le hMr.le)
  have he : |((gridSite K hK u).val : ℝ)/M - ((K : ℝ)/M)*(u : ℝ)| ≤ 1/(M : ℝ) := by
    have hid : (((gridSite K hK u).val : ℝ)/K-(u : ℝ))*((K : ℝ)/M) =
        ((gridSite K hK u).val : ℝ)/M-((K : ℝ)/M)*(u : ℝ) := by field_simp
    have habs : |(((gridSite K hK u).val : ℝ)/K-(u : ℝ))*((K : ℝ)/M)| =
        |((gridSite K hK u).val : ℝ)/K-(u : ℝ)| * ((K : ℝ)/M) := by
      rw [abs_mul, abs_of_nonneg (div_nonneg hKr.le hMr.le)]
    rw [← habs, hid] at hscaled
    have hr : (1/(K : ℝ))*((K : ℝ)/M)=1/(M : ℝ) := by field_simp
    simpa only [hr] using hscaled
  have hu := mul_le_mul_of_nonneg_left u.property.2 (abs_nonneg ((K : ℝ)/M-1))
  have ht := abs_add_le (((gridSite K hK u).val : ℝ)/M-((K : ℝ)/M)*(u : ℝ))
    ((((K : ℝ)/M)-1)*(u : ℝ))
  rw [mul_one] at hu
  rw [abs_mul,abs_of_nonneg u.property.1] at ht
  have ht2 := abs_add_le ((⌈(M : ℝ)^delta⌉₊ : ℝ)/M)
    (((gridSite K hK u).val : ℝ)/M-(u : ℝ))
  rw [abs_of_nonneg (by positivity : (0 : ℝ)≤(⌈(M : ℝ)^delta⌉₊ : ℝ)/M)] at ht2
  have hx : bulkGridPosition M L delta u-(u : ℝ)=
      (⌈(M : ℝ)^delta⌉₊ : ℝ)/M+((gridSite K hK u).val : ℝ)/M-(u : ℝ) := by
    simp only [bulkGridPosition,dif_pos hs,bulkGridSite_coe,Nat.cast_add,add_div]
    rfl
  rw [hx]
  have hy : ((gridSite K hK u).val : ℝ)/M-((K : ℝ)/M)*(u : ℝ)+
      (((K : ℝ)/M)-1)*(u : ℝ)=((gridSite K hK u).val : ℝ)/M-(u : ℝ) := by ring
  rw [hy] at ht
  have hz : (⌈(M : ℝ)^delta⌉₊ : ℝ)/M+((gridSite K hK u).val : ℝ)/M-(u : ℝ)=
      (⌈(M : ℝ)^delta⌉₊ : ℝ)/M+(((gridSite K hK u).val : ℝ)/M-(u : ℝ)) := by ring
  rw [hz]
  dsimp [K] at he hu ht ht2 ⊢
  linarith

/-- The actual contained uniform grid converges pointwise under a common continuous coupling. -/
theorem bulkGridPosition_tendsto
    (sizes lengths : ℕ→ℕ) (hsizes : Tendsto sizes atTop atTop)
    (beta delta : ℝ) (hdelta : 0<delta) (hdeltaOne : delta<1)
    (hupper : ∀ᶠ n in atTop,(lengths n : ℝ)≤beta*Real.log (sizes n))
    (hpositive : ∀ᶠ n in atTop,1≤lengths n) (u : unitInterval) :
    Tendsto (fun n => bulkGridPosition (sizes n) (lengths n) delta u) atTop (𝓝 (u : ℝ)) := by
  have hc := ((population_ratio_tendsto_one sizes lengths hsizes beta delta hdelta hdeltaOne hupper hpositive).sub_const 1).abs
  have hi : Tendsto (fun n => (1 : ℝ)/(sizes n : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,one_div] using tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hsizes)
  have hh := ((lower_endpoint_div_size_tendsto_zero sizes hsizes delta hdeltaOne).add hc).add hi
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (by simpa only [sub_self,abs_zero,add_zero] using hh)
  filter_upwards [hsizes.eventually (eventually_ge_atTop 1),
    bulk_nonempty_eventually sizes lengths hsizes beta delta hdelta hdeltaOne hupper hpositive] with n hn hne
  simpa only [Real.norm_eq_abs] using bulkGridPosition_error_le (by omega : 0<sizes n) hne u

/-- Genuine weak convergence of the uniform site law, with no implicit regularity assumption on the grid. -/
theorem bulkLocationLaw_tendsto
    (sizes lengths : ℕ→ℕ) (hsizes : Tendsto sizes atTop atTop)
    (beta delta : ℝ) (hdelta : 0<delta) (hdeltaOne : delta<1)
    (hupper : ∀ᶠ n in atTop,(lengths n : ℝ)≤beta*Real.log (sizes n))
    (hpositive : ∀ᶠ n in atTop,1≤lengths n) :
    Tendsto (fun n => bulkLocationLaw (sizes n) (lengths n) delta) atTop (𝓝 unitIntervalLaw) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro F
  simp only [bulkLocationLaw,unitIntervalLaw,integral_imageProbabilityLaw]
  apply tendsto_integral_of_dominated_convergence (fun _ => ‖F‖)
  · intro n
    exact (F.continuous.measurable.comp (measurable_bulkGridPosition (sizes n) (lengths n) delta)).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    exact Eventually.of_forall fun _ => F.norm_coe_le_norm _
  · exact Eventually.of_forall fun u => F.continuous.continuousAt.tendsto.comp
      (bulkGridPosition_tendsto sizes lengths hsizes beta delta hdelta hdeltaOne hupper hpositive u)

end
end PaperC.V282.CrossoverLocationGrid
