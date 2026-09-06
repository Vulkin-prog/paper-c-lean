import PaperCV282.GaussianThresholdIncrements
import PaperCV282.GeometricMarkedConfiguration
import PaperCV282.ThresholdPathEquivalence

/-! # Finite threshold projections of the genuine geometric configuration

The last finite category collects the entire infinite upper tail. It is not
obtained by discarding large marks.
-/
namespace PaperC.V282.PoissonThresholdTarget

open MeasureTheory ProbabilityTheory WithLp Filter
open GaussianThresholdIncrements GaussianThresholdCovariance FinitePoissonCLT PoissonCLT
open GeometricMarkedConfiguration GeometricClusterTarget ThresholdPathEquivalence
open CompoundPoissonTarget CompoundPoissonMarking PoissonFieldMeasure
open scoped Topology NNReal

noncomputable section

def clippedCategory (J h : ℕ) : Option (Fin (J+1)) :=
  if 0 < h then some ⟨min (h-1) J, by omega⟩ else none

def clippedCounts (J : ℕ) (c : ℕ →₀ ℕ) (i : Fin (J+1)) : ℕ :=
  if i.val = J then tailCount c J else c i.val

theorem clippedCategory_eq_some_iff (J h : ℕ) (i : Fin (J+1)) :
    clippedCategory J h = some i ↔ if i.val = J then J < h else h = i.val+1 := by
  unfold clippedCategory
  split_ifs with hh hi
  · simp only [Option.some.injEq, Fin.ext_iff]
    omega
  · simp only [Option.some.injEq, Fin.ext_iff]
    have := i.isLt
    omega
  · simp only [false_iff]
    omega
  · simp only [false_iff]
    omega

theorem tailCount_clusterConfiguration (sample : ℕ × (ℕ → ℕ)) (m : ℕ) :
    tailCount (clusterConfiguration sample) m =
      ∑ i ∈ Finset.range sample.1, if m < sample.2 i then 1 else 0 := by
  classical
  change (clusterConfiguration sample).sum (fun e n => if m ≤ e then n else 0) = _
  unfold clusterConfiguration
  rw [← Finsupp.sum_finsetSum_index]
  · apply Finset.sum_congr rfl
    intro i hi
    by_cases hp : 0 < sample.2 i
    · rw [if_pos hp, Finsupp.sum_single_index (by simp)]
      have he : m ≤ sample.2 i-1 ↔ m < sample.2 i := by omega
      simp [he]
    · rw [if_neg hp, Finsupp.sum_zero_index]
      have he : ¬m < sample.2 i := by omega
      simp [he]
  · intro e
    simp
  · intro e n k
    split_ifs <;> simp

theorem clippedCounts_clusterConfiguration (J : ℕ) :
    (fun sample => clippedCounts J (clusterConfiguration sample)) =
      categoryCounts (clippedCategory J) := by
  funext sample i
  simp only [clippedCounts, categoryCounts, clippedCategory_eq_some_iff]
  split_ifs with hi
  · exact tailCount_clusterConfiguration sample J
  · exact clusterConfiguration_apply sample i.val

theorem geometricCluster_strict_tail (J : ℕ) :
    geometricClusterMeasure.real {h : ℕ | J < h} = 1/(2 : ℝ)^J := by
  cases J with
  | zero =>
    have he : geometricClusterMeasure {h : ℕ | 0 < h} = 1 := by
      have hae : {h : ℕ | 0 < h} =ᵐ[geometricClusterMeasure] Set.univ := by
        filter_upwards [geometricClusterMeasure_positive] with h hh
        apply propext
        change (0 < h) ↔ True
        simp [show 0 < h by omega]
      rw [measure_congr hae, measure_univ]
    simp [Measure.real, he]
  | succ J => exact geometricCluster_tail_real J

theorem categoryRates_clipped (rate : ℝ≥0) (J : ℕ) :
    categoryRates rate geometricClusterMeasure (clippedCategory J) =
      fun i => rate * incrementVariance J i := by
  funext i
  apply NNReal.coe_injective
  rw [categoryRates_coe]
  by_cases hi : i.val = J
  · have he : {h : ℕ | clippedCategory J h = some i} = {h : ℕ | J < h} := by
      ext h
      simp [clippedCategory_eq_some_iff, hi]
    rw [he, geometricCluster_strict_tail]
    simp [incrementVariance, hi, div_eq_mul_inv]
  · have he : {h : ℕ | clippedCategory J h = some i} = {i.val+1} := by
      ext h
      simp [clippedCategory_eq_some_iff, hi]
    rw [he, geometricClusterMeasure_real_succ]
    simp [incrementVariance, hi, div_eq_mul_inv]

/-- The clipped exact levels, with the entire upper tail, are independent Poisson variables. -/
theorem hasLaw_clippedCounts (rate : ℝ≥0) (J : ℕ) :
    HasLaw (clippedCounts J) (fieldMeasure (fun i => rate * incrementVariance J i))
      (configurationMeasure rate) := by
  have h := hasLaw_categoryCounts rate geometricClusterMeasure (clippedCategory J)
  rw [categoryRates_clipped] at h
  refine ⟨(measurable_of_countable _).aemeasurable, ?_⟩
  rw [configurationMeasure, Measure.map_map (measurable_of_countable _) measurable_clusterConfiguration]
  rw [show (clippedCounts J) ∘ clusterConfiguration = categoryCounts (clippedCategory J) from
    clippedCounts_clusterConfiguration J]
  exact h.map_eq

theorem tailCount_eq_sum_Ico (c : ℕ →₀ ℕ) (k J : ℕ) (hk : k ≤ J) :
    (∑ i ∈ Finset.Ico k J, c i) + tailCount c J = tailCount c k := by
  induction J generalizing k with
  | zero =>
    obtain rfl : k = 0 := by omega
    simp
  | succ J ih =>
    by_cases h : k ≤ J
    · rw [Finset.sum_Ico_succ_top h, add_assoc, ← tailCount_succ]
      exact ih k h
    · obtain rfl : k = J+1 := by omega
      simp

theorem sum_clippedCounts_tail (J k : ℕ) (hk : k ≤ J) (c : ℕ →₀ ℕ) :
    (∑ i : Fin (J+1), if k ≤ i.val then clippedCounts J c i else 0) = tailCount c k := by
  rw [Fin.sum_univ_castSucc]
  have hlast : (if k ≤ (Fin.last J).val then clippedCounts J c (Fin.last J) else 0) =
      tailCount c J := by simp [clippedCounts, hk]
  rw [hlast]
  have heq : (∑ i : Fin J, if k ≤ i.castSucc.val then clippedCounts J c i.castSucc else 0) =
      ∑ i ∈ Finset.Ico k J, c i := by
    simp only [Fin.val_castSucc]
    have hi (i : Fin J) : clippedCounts J c i.castSucc = c i.val := by
      simp [clippedCounts, ne_of_lt i.isLt]
    simp_rw [hi]
    rw [Fin.sum_univ_eq_sum_range (fun i => if k ≤ i then c i else 0) J,
      ← Finset.sum_filter]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [heq]
  exact tailCount_eq_sum_Ico c k J hk

def normalizedThresholdVector (rate : ℝ≥0) (J : ℕ) (c : ℕ →₀ ℕ) :
    EuclideanSpace ℝ (Fin (J+1)) :=
  toLp 2 (fun j => ((tailCount c j.val : ℝ) - (rate : ℝ)/(2 : ℝ)^j.val) / Real.sqrt rate)

theorem normalizedThresholdVector_eq_sum (rate : ℝ≥0) (J : ℕ) (c : ℕ →₀ ℕ) :
    normalizedThresholdVector rate J c = thresholdSum J
      (normalizedPoissonVector (fun i => rate * incrementVariance J i) rate (clippedCounts J c)) := by
  ext j
  simp only [normalizedThresholdVector, thresholdSum, normalizedPoissonVector]
  have heq (i : Fin (J+1)) :
      (if j.val ≤ i.val then ((clippedCounts J c i : ℝ) -
          ((rate * incrementVariance J i : ℝ≥0) : ℝ))/Real.sqrt rate else 0) =
      ((if j.val ≤ i.val then (clippedCounts J c i : ℝ) else 0) -
        (rate : ℝ)*(if j.val ≤ i.val then (incrementVariance J i : ℝ) else 0))/Real.sqrt rate := by
    split_ifs <;> simp
  simp_rw [heq]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum,
    sum_tail_incrementVariance J j.val (by omega)]
  have hnat := congrArg (fun n : ℕ => (n : ℝ)) (sum_clippedCounts_tail J j.val (by omega) c)
  push_cast at hnat
  rw [hnat]
  ring

def normalizedThresholdLaw (rate : ℝ≥0) (J : ℕ) :
    ProbabilityMeasure (EuclideanSpace ℝ (Fin (J+1))) :=
  ⟨(configurationMeasure rate).map (normalizedThresholdVector rate J),
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable⟩

theorem normalizedThresholdLaw_eq (rate : ℝ≥0) (J : ℕ) :
    normalizedThresholdLaw rate J =
      (euclideanProductLaw (fun i => centeredScaledPoissonLaw (rate * incrementVariance J i)
        (Real.sqrt rate))).map (continuous_thresholdSum J).measurable.aemeasurable := by
  apply Subtype.ext
  have h := (hasLaw_normalizedPoissonVector (fun i => rate * incrementVariance J i) rate).fun_comp
    (hasLaw_clippedCounts rate J)
  change (configurationMeasure rate).map (normalizedThresholdVector rate J) =
    (euclideanProductLaw (fun i => centeredScaledPoissonLaw (rate * incrementVariance J i)
      (Real.sqrt rate)) : Measure _).map (thresholdSum J)
  rw [← h.map_eq, Measure.map_map (continuous_thresholdSum J).measurable (measurable_of_countable _)]
  congr 1
  funext c
  exact normalizedThresholdVector_eq_sum rate J c

/-- The true full-tail vector converges to the Gaussian with covariance 2^(-max). -/
theorem normalizedThresholdLaw_tendsto (rates : ℕ → ℝ≥0) (J : ℕ)
    (hrates : Tendsto (fun n => (rates n : ℝ)) atTop atTop) :
    Tendsto (fun n => normalizedThresholdLaw (rates n) J) atTop (𝓝 (gaussianThresholdLaw J)) := by
  have hprod : Tendsto (fun n => euclideanProductLaw (fun i : Fin (J+1) =>
      centeredScaledPoissonLaw (rates n * incrementVariance J i) (Real.sqrt (rates n)))) atTop
      (𝓝 (euclideanProductLaw (fun i => centeredGaussianLaw (incrementVariance J i)))) := by
    apply euclideanProductLaw_tendsto
    intro i
    apply centeredPoisson_tendsto_of_rate_ratio _ _ _ hrates
    apply tendsto_const_nhds.congr'
    filter_upwards [hrates.eventually_gt_atTop 0] with n hn
    simp only [NNReal.coe_mul]
    field_simp
  have h := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hprod
    (continuous_thresholdSum J)
  simpa only [normalizedThresholdLaw_eq, map_gaussian_increments] using h

end
end PaperC.V282.PoissonThresholdTarget
