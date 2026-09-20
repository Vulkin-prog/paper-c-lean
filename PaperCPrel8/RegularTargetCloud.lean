import PaperCPrel8.OrderedLabelCloud
import PaperCV282.BulkMarkedTargetTail

/-! # Private pivots for the full signed/excess target cloud

The regular set is an intrinsic set of finite marked configurations, defined
by a finite enumeration. Its complement is bounded under the existing target
measure, using the actual Poisson sample and the full geometric mark tail.
-/
namespace PaperC.Prel8.RegularTargetCloud
open MeasureTheory ProbabilityTheory Finset
open V282.BulkMarkedTypes V282.BulkMarkedTarget V282.BulkMarkedTargetTail
open V282.CrossoverBulkOnePoint V282.GeneralPoissonMarking V282.FiniteStartMaskAverages
open BulkCloudIdentification OrderedLabelCloud RoughKernelRegularity RoughKernelAllocation
open PoissonRegularCloud LargeOddKernel
open scoped NNReal ENNReal
noncomputable section
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- The regular target set, retaining every sign and exact excess. The empty
configuration is allowed by the enumeration of length zero. -/
def RegularConfiguration (sites : Finset ℕ) (Q Y K E : ℕ) (G : Finset ℕ)
    (c : SpatialMarkedConfig sites) : Prop :=
  ∃ k≤K, ∃ labels : Fin k → SpatialMarkedIndex sites,
    c=∑ i, Finsupp.single (labels i) 1 ∧
    (∀ i, (labels i).1.val∈G) ∧
    Regular Q Y (fun i ↦ (labels i).1.val) ∧
    (∀ i, (labels i).2.1≤E)

/-- The enumeration cutoff is exactly a bound on the actual total multiplicity. -/
theorem regular_size_le (sites : Finset ℕ) (Q Y K E : ℕ) (G : Finset ℕ)
    (c : SpatialMarkedConfig sites) (hc : RegularConfiguration sites Q Y K E G c) :
    V282.CrossoverBulkAtoms.totalSize sites c≤K := by
  obtain ⟨k,hk,labels,rfl,_⟩ := hc
  unfold V282.CrossoverBulkAtoms.totalSize
  rw [← Finsupp.sum_finsetSum_index (fun _ ↦ rfl) (fun _ _ _ ↦ rfl)]
  simpa using hk

/-- The intrinsic regular set excludes every configuration with a high excess. -/
theorem regular_not_tail (sites : Finset ℕ) (Q Y K E : ℕ) (G : Finset ℕ)
    (c : SpatialMarkedConfig sites) (hc : RegularConfiguration sites Q Y K E G c) :
    c∉spatialTargetTail sites E := by
  obtain ⟨k,hk,labels,rfl,_,_,hlow⟩ := hc
  rintro ⟨j,hj,hne⟩
  apply hne
  simp only [Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro i hi
  have he : labels i≠j := by intro h; have := hlow i; rw [h] at this; omega
  simp [Finsupp.single_apply,he]

/-- Empty configurations satisfy every size and mark cutoff. -/
theorem regular_empty (sites : Finset ℕ) (Q Y K E : ℕ) (G : Finset ℕ) :
    RegularConfiguration sites Q Y K E G 0 := by
  refine ⟨0,Nat.zero_le _,Fin.elim0,?_⟩
  simp [Regular]

/-- Every sampled label has positive multiplicity in the complete configuration. -/
theorem sampled_label_pos (sites : Finset ℕ)
    (sample : ℕ × (ℕ → SpatialMarkedIndex sites)) (i : ℕ) (hi : i<sample.1) :
    0<sampledConfiguration sites id sample (sample.2 i) := by
  simp only [sampledConfiguration,Finsupp.finsetSum_apply,id_eq]
  apply Finset.sum_pos'
  · intro j hj; exact Nat.zero_le _
  · exact ⟨i,mem_range.mpr hi,by simp⟩

/-- Absence of the full target high-mark event forces every sampled label below the cutoff. -/
theorem sampled_labels_low (sites : Finset ℕ) (E : ℕ)
    (sample : ℕ × (ℕ → SpatialMarkedIndex sites))
    (h : sampledConfiguration sites id sample ∉ spatialTargetTail sites E) :
    ∀ i : Fin sample.1, (sample.2 i.val).2.1≤E := by
  intro i
  by_contra hi
  exact h ⟨sample.2 i.val,by omega,(sampled_label_pos sites sample i.val i.isLt).ne'⟩

/-- Good ordered positions and absence of high marks produce an intrinsic regular configuration. -/
theorem regular_of_positions (n Q Y K E : ℕ) (G : Finset ℕ)
    (sample : ℕ × (ℕ → SpatialMarkedIndex (Icc 1 n)))
    (hp : ¬badCloud n Q Y K G (positions n sample))
    (ht : sampledConfiguration (Icc 1 n) id sample ∉ spatialTargetTail (Icc 1 n) E) :
    RegularConfiguration (Icc 1 n) Q Y K E G (sampledConfiguration (Icc 1 n) id sample) := by
  have hsize : sample.1≤K := by
    by_contra h
    exact hp (Or.inl (by simpa only [positions] using (show K<sample.1 by omega)))
  have hgood : (∀ i : Fin sample.1, (sample.2 i.val).1.val∈G) ∧
      Regular Q Y (fun i : Fin sample.1 ↦ (sample.2 i.val).1.val) := by
    by_contra h
    exact hp (Or.inr h)
  refine ⟨sample.1,hsize,(fun i ↦ sample.2 i.val),?_,hgood.1,hgood.2,sampled_labels_low _ E sample ht⟩
  exact (Fin.sum_univ_eq_sum_range (fun i ↦ Finsupp.single (sample.2 i) (1:ℕ)) sample.1).symm

/-- Finite G.3 estimate under the actual complete target: bad sites, private
pivot failures, the Poisson upper tail, and every excluded geometric excess. -/
theorem target_failure_le (n L Q Y K E : ℕ) (hn : 0<n) (hK : 1≤K)
    (hQn : Q≤n) (hQY : Q<Y) (G : Finset ℕ) (T : ℝ) (hT : 0<T)
    (hsize : 2*(maskRate L (Icc 1 n):ℝ)≤K)
    (hzY : 3*(K:ℝ)*(Q+1)<Y)
    (hgood : ∀ j∈G, ∀ a : Fin (Q+1), T≤(largeOddKernel Y (j+a.val):ℝ)) :
    (spatialTargetMeasure (Icc 1 n) L).real
      {c | ¬RegularConfiguration (Icc 1 n) Q Y K E G c} ≤
      (maskRate L (Icc 1 n):ℝ)*(((Icc 1 n) \ G).card:ℝ)/n+
      (K:ℝ)*(Q+1)*T^(-1+Real.log (3*(K:ℝ)*(Q+1))/Real.log Y)+
      Real.exp (-((2*Real.log 2-1)*(maskRate L (Icc 1 n):ℝ)))+
      (maskRate L (Icc 1 n):ℝ)/(2:ℝ)^(E+1) := by
  let mu := markSampleMeasure (maskRate L (Icc 1 n)) (labelMeasure (Icc 1 n) (sites_nonempty hn))
  let f := sampledConfiguration (Icc 1 n) id
  have hlaw := hasLaw_label_configuration (Icc 1 n) (sites_nonempty hn) L
  have hpre := hlaw.measureReal_eq ((Set.to_countable {c | ¬RegularConfiguration (Icc 1 n) Q Y K E G c}).measurableSet)
  have htail := hlaw.measureReal_eq ((Set.to_countable (spatialTargetTail (Icc 1 n) E)).measurableSet)
  have hc : {sample | ¬RegularConfiguration (Icc 1 n) Q Y K E G (f sample)} ⊆
      {sample | badCloud n Q Y K G (positions n sample)} ∪ {sample | f sample ∈ spatialTargetTail (Icc 1 n) E} := by
    intro sample hs
    by_cases hp : badCloud n Q Y K G (positions n sample)
    · exact Or.inl hp
    · exact Or.inr (by by_contra ht; exact hs (regular_of_positions n Q Y K E G sample hp ht))
  calc
    _ = mu.real {sample | ¬RegularConfiguration (Icc 1 n) Q Y K E G (f sample)} := hpre.symm
    _ ≤ mu.real {sample | badCloud n Q Y K G (positions n sample)}+
        mu.real {sample | f sample ∈ spatialTargetTail (Icc 1 n) E} :=
      (measureReal_mono hc).trans (measureReal_union_le _ _)
    _ = PoissonCloudMixture.probability (maskRate L (Icc 1 n)) (fun k ↦ gridLaw n k hn) (badCloud n Q Y K G)+
        (spatialTargetMeasure (Icc 1 n) L).real (spatialTargetTail (Icc 1 n) E) := by
      rw [show mu.real {sample | badCloud n Q Y K G (positions n sample)} = _ from positions_event n hn _ _]
      rw [show mu.real {sample | f sample ∈ spatialTargetTail (Icc 1 n) E} = _ from htail]
      rfl
    _ ≤ _ := add_le_add (poisson_failure_le n Q Y K hn hK hQn hQY _ hsize G T hT hzY hgood)
      (spatial_target_tail_probability_le (Icc 1 n) L E)

end
end PaperC.Prel8.RegularTargetCloud
