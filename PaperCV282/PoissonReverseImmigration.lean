import PaperCV282.PoissonResolvedLowerComparison

/-! # Explicit reverse Poisson increments remain independent of the whole resolved future -/
namespace PaperC.V282.PoissonReverseImmigration

open MeasureTheory ProbabilityTheory PoissonResolvedTarget PoissonResolvedPast
open PoissonConfigurationSplit PoissonResolvedLowerComparison GeometricConfigurationCounts
open GeometricMarkedConfiguration GeometricClusterTarget CompoundPoissonTarget
open ThresholdPathEquivalence PoissonThresholdTarget PoissonFieldMeasure
open scoped NNReal ENNReal

noncomputable section

@[reducible]
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

theorem thin_configuration_size_ae (n : ℕ) :
    ∀ᵐ c ∂thinConfigurationMeasure n, configurationSize c=n := by
  rw [thinConfigurationMeasure]
  apply (ae_map_iff (measurable_fixed_configuration n).aemeasurable
    ((Set.to_countable _).measurableSet)).mpr
  have hp (i : ℕ) : ∀ᵐ marks ∂markSequenceMeasure geometricClusterMeasure, 1≤marks i :=
    (hasLaw_mark_coordinate geometricClusterMeasure i).ae_iff
      (measurable_of_countable _) |>.mpr geometricClusterMeasure_positive
  filter_upwards [ae_all_iff.mpr hp] with marks hmarks
  rw [configurationSize_clusterConfiguration]
  simp [show ∀ i, 0<marks i from fun i => by have := hmarks i; omega]

theorem merge_tail_present (k : ℕ) (p : (Fin k → ℕ) × (ℕ →₀ ℕ)) :
    tailCount (mergeConfiguration k p) k = configurationSize p.2 := by
  rw [← size_shifted_eq_tail]
  have hs := congrArg Prod.snd (split_mergeConfiguration k p)
  exact congrArg configurationSize hs

theorem merge_tail_future (k : ℕ) (p : (Fin k → ℕ) × (ℕ →₀ ℕ)) (j : ℕ) :
    tailCount (mergeConfiguration k p) (k+j) = tailCount p.2 j := by
  rw [← size_shifted_eq_tail, ← size_shifted_eq_tail]
  congr 1
  ext e
  simp only [shiftedConfiguration_apply]
  rw [Nat.add_assoc, mergeConfiguration_high]

theorem merge_tail_lower (k : ℕ) (p : (Fin k → ℕ) × (ℕ →₀ ℕ))
    (j : ℕ) (hj : j≤k) :
    tailCount (mergeConfiguration k p) j = configurationSize p.2 +
      ∑ i : Fin k, if j≤ i.val then p.1 i else 0 := by
  have h := tailCount_eq_sum_Ico (mergeConfiguration k p) j k hj
  rw [merge_tail_present] at h
  have hsum : (∑ i : Fin k, if j≤ i.val then p.1 i else 0) =
      ∑ i ∈ Finset.Ico j k, mergeConfiguration k p i := by
    simp_rw [← mergeConfiguration_low k p]
    rw [Fin.sum_univ_eq_sum_range (fun i => if j≤ i then mergeConfiguration k p i else 0) k,
      ← Finset.sum_filter]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [hsum]
  omega

/-- The finite immigration coordinates and the whole geometric future are jointly a product law. -/
theorem hasLaw_independent_immigration_future (rate : ℝ≥0) (k n : ℕ) :
    HasLaw (fun p : (Fin k → ℕ) × (ℕ →₀ ℕ) => (p.1, thresholdFunction p.2))
      ((fieldMeasure (lowerRates rate k)).prod (thinningPathMeasure n))
      ((fieldMeasure (lowerRates rate k)).prod (thinConfigurationMeasure n)) := by
  refine ⟨(measurable_of_countable _).aemeasurable, ?_⟩
  change ((fieldMeasure (lowerRates rate k)).prod (thinConfigurationMeasure n)).map
    (Prod.map id thresholdFunction) = _
  rw [← Measure.map_prod_map _ _ measurable_id (measurable_of_countable _),
    Measure.map_id, thinConfiguration_path]

/-- These are the actual lower exact-level immigration variables; each is Poisson and all are independent. -/
theorem independent_lower_coordinates (rate : ℝ≥0) (k : ℕ) :
    iIndepFun (fun i : Fin k => fun a : Fin k → ℕ => a i) (fieldMeasure (lowerRates rate k)) :=
  iIndepFun_pi (fun _ => measurable_id.aemeasurable)

theorem hasLaw_lower_coordinate (rate : ℝ≥0) (k : ℕ) (i : Fin k) :
    HasLaw (fun a : Fin k → ℕ => a i) (poissonMeasure (rate / 2^(i.val+1)))
      (fieldMeasure (lowerRates rate k)) := by
  exact (measurePreserving_eval (fun j => poissonMeasure (lowerRates rate k j)) i).hasLaw

/-- An arbitrary finite reverse increment has its exact Poisson sum rate. -/
theorem hasLaw_reverse_increment (rate : ℝ≥0) (k j : ℕ) :
    HasLaw (fun a : Fin k → ℕ => ∑ i ∈ Finset.univ.filter (fun i : Fin k => k-j≤ i.val), a i)
      (poissonMeasure (∑ i ∈ Finset.univ.filter (fun i : Fin k => k-j≤ i.val),
        lowerRates rate k i)) (fieldMeasure (lowerRates rate k)) :=
  hasLaw_coordinate_sum _ _

/-- Under the true joint target, all retained past counts are n plus their Poisson immigration sums. -/
theorem reverse_path_coordinates_ae (rate : ℝ≥0) (k n : ℕ) :
    ∀ᵐ p ∂(fieldMeasure (lowerRates rate k)).prod (thinConfigurationMeasure n),
      (∀ j, j≤k → tailCount (mergeConfiguration k p) (k-j) = n +
        ∑ i : Fin k, if k-j≤ i.val then p.1 i else 0) ∧
      (∀ j, tailCount (mergeConfiguration k p) (k+j) = thresholdFunction p.2 j) := by
  have hs : ∀ᵐ p ∂(fieldMeasure (lowerRates rate k)).prod (thinConfigurationMeasure n),
      configurationSize p.2=n := by
    exact (measurePreserving_snd (μ := fieldMeasure (lowerRates rate k))
      (ν := thinConfigurationMeasure n)).hasLaw.ae_iff (measurable_of_countable _) |>.mpr
        (thin_configuration_size_ae n)
  filter_upwards [hs] with p hp
  constructor
  · intro j hj
    rw [merge_tail_lower k p (k-j) (by omega), hp]
  · intro j
    exact merge_tail_future k p j


/-- The finite reverse sum is exactly the printed rate lambda_present * (2^j - 1). -/
theorem reverse_increment_rate (rate : ℝ≥0) (k j : ℕ) (hj : j≤k) :
    ((∑ i ∈ Finset.univ.filter (fun i : Fin k => k-j ≤ i.val), lowerRates rate k i : ℝ≥0) : ℝ) =
      ((rate : ℝ)/2^k) * ((2 : ℝ)^j-1) := by
  have hsum :
      ((∑ i ∈ Finset.univ.filter (fun i : Fin k => k-j ≤ i.val), lowerRates rate k i : ℝ≥0) : ℝ) =
      (rate : ℝ) * ∑ i ∈ Finset.Ico (k-j) k, 1/(2 : ℝ)^(i+1) := by
    rw [NNReal.coe_sum]
    simp only [lowerRates, NNReal.coe_div, NNReal.coe_pow, NNReal.coe_ofNat]
    rw [Finset.sum_filter]
    rw [Fin.sum_univ_eq_sum_range (fun i => if k-j ≤ i then (rate : ℝ)/2^(i+1) else 0) k,
      ← Finset.sum_filter]
    have hset : (Finset.range k).filter (fun i => k-j ≤ i) = Finset.Ico (k-j) k := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      omega
    rw [hset, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hsum]
  have hg := GaussianThresholdIncrements.tail_geometric_sum (k-j) k (by omega)
  have hp : (2 : ℝ)^k = (2 : ℝ)^(k-j) * (2 : ℝ)^j := by
    rw [← pow_add]
    congr 1
    omega
  have ht : (∑ i ∈ Finset.Ico (k-j) k, 1/(2 : ℝ)^(i+1)) =
      1/(2 : ℝ)^(k-j) - 1/(2 : ℝ)^k := by linarith
  rw [ht]
  field_simp
  nlinarith

end
end PaperC.V282.PoissonReverseImmigration
