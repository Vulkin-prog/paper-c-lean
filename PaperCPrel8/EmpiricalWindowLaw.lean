import PaperCPrel8.EmpiricalWindowVariance
import PaperCV282.SharpConditioning

/-! # Exact window laws, means and one-event transfer of empirical tails

The comparison is applied once to the entire empirical statistic. There is
no union bound over origins and hence no spurious factor N in the TV error.
-/
namespace PaperC.Prel8.EmpiricalWindowLaw
open MeasureTheory ProbabilityTheory
open PaperC.V282.PoissonFieldMeasure PaperC.V282.SharpConditioning
open PaperC.Prel8.EmpiricalWindowVariance
open scoped BigOperators NNReal ENNReal
noncomputable section

/-- A contained length-h window has exactly h sites. -/
theorem window_card {n h u : ℕ} (hu : u+h ≤ n) : (window n h u).card = h := by
  have he : (window n h u).image Fin.val = Finset.Ico u (u+h) := by
    ext j
    simp only [Finset.mem_image, Finset.mem_Ico]
    constructor
    · rintro ⟨i,hi,rfl⟩
      simpa [window] using hi
    · intro hj
      refine ⟨⟨j,by omega⟩, ?_, rfl⟩
      simpa [window] using hj
  rw [← Finset.card_image_of_injective _ Fin.val_injective, he, Nat.card_Ico]
  omega

/-- The product-field window count has the literal Poisson(h*p) law. -/
theorem window_hasLaw {n h u : ℕ} (p : ℝ≥0) (hu : u+h ≤ n) :
    HasLaw (windowCount (n := n) h u) (poissonMeasure (h*p))
      (fieldMeasure (fun _ : Fin n => p)) := by
  unfold windowCount
  have hl := hasLaw_coordinate_sum (fun _ : Fin n => p) (window n h u)
  simpa [windowCount, window_card hu, nsmul_eq_mul] using hl

/-- Exact mean of a window indicator. -/
theorem hit_mean {n h u : ℕ} (p : ℝ≥0) (hu : u+h ≤ n) (r : ℕ) :
    (∫ x, hit (n := n) h u r x ∂fieldMeasure (fun _ : Fin n => p)) =
      (poissonMeasure (h*p)).real {r} := by
  have he : hit (n := n) h u r =
      (windowCount (n := n) h u ⁻¹' {r}).indicator (fun _ => (1:ℝ)) := by
    ext x
    simp [hit, Set.indicator, Set.mem_preimage]
  rw [he, integral_indicator_const (1:ℝ)
    ((measurable_of_countable (windowCount (n := n) h u)) (measurableSet_singleton r))]
  simp only [smul_eq_mul, mul_one]
  exact (window_hasLaw p hu).measureReal_eq (measurableSet_singleton r)

/-- The frequency is square-integrable. -/
theorem frequency_memLp {n : ℕ} (rate : Fin n → ℝ≥0) (N h r : ℕ) :
    MemLp (frequency (n := n) N h r) 2 (fieldMeasure rate) := by
  have hm : MemLp (fun x : Fin n → ℕ => ∑ u : Fin N, hit h u.val r x) 2
      (fieldMeasure rate) := memLp_finsetSum _ (fun u _ => hit_memLp rate h u.val r)
  unfold frequency
  simpa only [div_eq_mul_inv] using hm.mul_const (N:ℝ)⁻¹

/-- Every contained-origin empirical frequency has the same exact Poisson mean. -/
theorem frequency_mean {n N h : ℕ} (p : ℝ≥0) (hN : 0 < N)
    (hfit : N+h ≤ n+1) (r : ℕ) :
    (∫ x, frequency (n := n) N h r x ∂fieldMeasure (fun _ : Fin n => p)) =
      (poissonMeasure (h*p)).real {r} := by
  unfold frequency
  rw [integral_div, integral_finsetSum]
  · have hm (u : Fin N) := hit_mean p (show u.val+h ≤ n by omega) r
    simp_rw [hm]
    simp [Nat.ne_of_gt hN]
  · intro u _
    exact (hit_memLp (fun _ : Fin n => p) h u.val r).integrable (by norm_num)

/-- Chebyshev with the exact overlap constant and the actual Poisson mean. -/
theorem frequency_tail_le {n N h : ℕ} (p : ℝ≥0) (hN : 0 < N) (hh : 0 < h)
    (hfit : N+h ≤ n+1) (r : ℕ) {eta : ℝ} (heta : 0 < eta) :
    (fieldMeasure (fun _ : Fin n => p)).real
      {x | eta < |frequency N h r x-(poissonMeasure (h*p)).real {r}|} ≤
        (2*(h:ℝ)-1)/(4*N*eta^2) := by
  let μ := fieldMeasure (fun _ : Fin n => p)
  have hc := meas_ge_le_variance_div_sq (frequency_memLp (fun _ : Fin n => p) N h r) heta
  rw [frequency_mean p hN hfit r] at hc
  have hc' := ENNReal.toReal_mono ENNReal.ofReal_ne_top hc
  rw [ENNReal.toReal_ofReal (div_nonneg (variance_nonneg _ _) (sq_nonneg _))] at hc'
  have hs : μ.real {x | eta < |frequency N h r x-(poissonMeasure (h*p)).real {r}|} ≤
      μ.real {x | eta ≤ |frequency N h r x-(poissonMeasure (h*p)).real {r}|} := by
    apply measureReal_mono _ (measure_ne_top _ _)
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    exact le_of_lt hx
  calc
    _ ≤ variance (frequency (n := n) N h r) μ / eta^2 := hs.trans hc'
    _ ≤ ((2*(h:ℝ)-1)/(4*N))/eta^2 :=
      div_le_div_of_nonneg_right (frequency_variance_le _ hN hh r) (sq_nonneg _)
    _ = _ := by ring

/-- A whole-frequency deviation transfers with one field-TV error, independent of N. -/
theorem source_frequency_tail_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n N h : ℕ}
    (X : Ω → Fin n → ℕ) (hX : Measurable X) (p : ℝ≥0)
    (hN : 0 < N) (hh : 0 < h) (hfit : N+h ≤ n+1)
    (delta : ℝ) (hTV : measureTotalVariation (μ.map X)
      (fieldMeasure (fun _ : Fin n => p)) ≤ delta) (r : ℕ)
    {eta : ℝ} (heta : 0 < eta) :
    μ.real {ω | eta < |frequency N h r (X ω)-(poissonMeasure (h*p)).real {r}|} ≤
      delta+(2*(h:ℝ)-1)/(4*N*eta^2) := by
  let E : Set (Fin n → ℕ) :=
    {x | eta < |frequency N h r x-(poissonMeasure (h*p)).real {r}|}
  have hE : MeasurableSet E := Set.to_countable _ |>.measurableSet
  let : IsProbabilityMeasure (μ.map X) :=
    (Measure.isProbabilityMeasure_map_iff hX.aemeasurable).mpr inferInstance
  have ht := (measureTotalVariation_le_iff _ _ _).mp hTV E hE
  rw [map_measureReal_apply hX hE] at ht
  have hb := frequency_tail_le p hN hh hfit r heta
  have h := (abs_le.mp ht).2
  change μ.real (X ⁻¹' E) ≤ _
  change (fieldMeasure (fun _ : Fin n => p)).real E ≤ _ at hb
  linarith

end
end PaperC.Prel8.EmpiricalWindowLaw
