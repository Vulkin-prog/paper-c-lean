import PaperCV282.ConstantWindowBoundary
import PaperCV282.FullBandArithmetic
import PaperCV282.MaskedBadMass

/-!
# The genuine untruncated cluster count and its uniform source tail

The truncation removes actual marks exceeding E. The source laws are
coupled on the infinite Rademacher space, and the tail is estimated at
the longer start length K=L+E+1.
-/
namespace PaperC.V282.ExactMarkedSourceTail

open MeasureTheory InfiniteRademacher InfiniteExactLengthProbabilityTransfer
open ConstantWindowClusters ConstantWindowBoundary ExactLengthDecomposition
open MixedLengthAffine SectionTwelveMoments MarkedDetruncation InfiniteMassCoupling
open FiniteFieldTotalVariation FullBandArithmetic MaskedBadMass MaskedArithmeticGeometry
open AllStartSoftPoisson Filter Topology
open scoped BigOperators

noncomputable section

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

local instance instIsProbabilityMeasureInfiniteRademacher : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

@[reducible]
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

/-- The actual finite weighted excess sum on the source sample. -/
def truncatedExactClusterCount (N L E : ℕ) (omega : InfiniteSample) : ℕ :=
  ∑ x ∈ dyadicBlock N, ∑ e : Fin (E+1),
    if ExactLengthEvent (infiniteValueBit omega) x (excessRowCount L e.val) then e.val+1 else 0

theorem measurable_truncatedExactClusterCount (N L E : ℕ) :
    Measurable (truncatedExactClusterCount N L E) := by
  unfold truncatedExactClusterCount
  apply Finset.measurable_sum
  intro x hx
  apply Finset.measurable_sum
  intro e he
  exact measurable_const.ite (measurableSet_infiniteExactLengthEvent x (excessRowCount L e.val))
    measurable_const

/-- The finite vector of mark counts is aggregated with its true cluster sizes. -/
theorem truncatedExactClusterCount_eq_weighted_counts (N L E : ℕ) (omega : InfiniteSample) :
    truncatedExactClusterCount N L E omega =
      ∑ e : Fin (E+1), (e.val+1)*infiniteExactLengthCount N L e.val omega := by
  unfold truncatedExactClusterCount infiniteExactLengthCount
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  split_ifs <;> simp

/-- Agreement holds on every source sample with no discarded mark, without a moment assumption. -/
theorem exactClusterCount_eq_truncated_off_tail (N L E : ℕ) (omega : InfiniteSample)
    (h : omega ∉ infiniteMarkTailEvent N L E) :
    infiniteExactClusterCount N L omega=truncatedExactClusterCount N L E omega := by
  unfold infiniteExactClusterCount exactClusterCount truncatedExactClusterCount
  apply Finset.sum_congr rfl
  intro x hx
  rw [tsum_eq_sum (s := Finset.range (E+1))]
  · exact Finset.sum_range _
  · intro e he
    apply if_neg
    intro hex
    have hEe : E<e := by
      have hh : ¬e<E+1 := by simpa only [Finset.mem_range] using he
      omega
    exact h ⟨x,hx,e,hEe,hex⟩

/-- The two actual source laws are coupled by the actual mark-tail event. -/
theorem source_cluster_truncation_tv_le (N L E : ℕ) :
    massTotalVariation
      (observableLaw infiniteRademacherMeasure (infiniteExactClusterCount N L))
      (observableLaw infiniteRademacherMeasure (truncatedExactClusterCount N L E)) ≤
        infiniteMarkTailProbability N L E := by
  exact massTotalVariation_observableLaw_le_event infiniteRademacherMeasure
    (measurable_infiniteExactClusterCount N L) (measurable_truncatedExactClusterCount N L E)
    (exactClusterCount_eq_truncated_off_tail N L E)

/-- A finite full-defect bound at the longer start length controls the actual tail. -/
theorem source_mark_tail_le_fullDefects {N L E : ℕ} (hN : 2 ≤ N) :
    infiniteMarkTailProbability N L E ≤
      ((fullDefectMass (L+E+1) (dyadicBlock N) : ℝ)+(N : ℝ))/(2 : ℝ)^(L+E+1) := by
  apply (infiniteMarkTailProbability_le_longStartExpectation N L E).trans
  have hh := (Rat.cast_le (K := ℝ)).mpr
    (startProbabilityMass_le_mask_defects hN (by omega : 0 < L+E+1)
      (dyadicBlock N) (Finset.Subset.refl _))
  simpa only [dyadicExpectation,Rat.cast_sum,Rat.cast_div,Rat.cast_add,Rat.cast_natCast,
    Rat.cast_pow,Rat.cast_ofNat,TouchingPairs.card_dyadicBlock] using hh

/-- The uniform tail estimate keeps the exact geometric factor and the true long-support error. -/
theorem source_mark_tail_le_eventually
    (betaMin betaMax epsilon : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hepsilon : 0 < epsilon) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L E : ℕ,
      betaMin*Real.log N ≤ (L+E+2 : ℝ) → (L+E+2 : ℝ) ≤ betaMax*Real.log N →
      infiniteMarkTailProbability N L E ≤
        ((fullRate N L : ℝ)/(2 : ℝ)^(E+1))*
          (1+(N : ℝ)^(-(1/(2 : ℝ))+epsilon)) := by
  obtain ⟨Nzero,hzero⟩ := fullDefectMass_div_block_le_eventually
    betaMin betaMax epsilon hbetaMin hbeta hepsilon
  refine ⟨max Nzero 2,?_⟩
  intro N hN L E hlo hhi
  have hn : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hlower : betaMin*Real.log N ≤ ((L+E+1 : ℕ)+1 : ℝ) := by push_cast;linarith
  have hupper : ((L+E+1 : ℕ)+1 : ℝ)≤betaMax*Real.log N := by push_cast;linarith
  have hdef := hzero N (by omega) (L+E+1) hlower hupper (dyadicBlock N) (Finset.Subset.refl _)
  have hdef' := (div_le_iff₀ hn).mp hdef
  calc
    _ ≤ ((fullDefectMass (L+E+1) (dyadicBlock N) : ℝ)+(N : ℝ))/(2 : ℝ)^(L+E+1) :=
      source_mark_tail_le_fullDefects (by omega)
    _ ≤ ((N : ℝ)^(-(1/(2 : ℝ))+epsilon)*(N : ℝ)+(N : ℝ))/(2 : ℝ)^(L+E+1) :=
      div_le_div_of_nonneg_right (by linarith only [hdef']) (by positivity)
    _ = _ := by
      rw [fullRate_coe]
      simp only [pow_add]
      field_simp
      ring

/-- The same explicit tail controls total variation of the two actual cluster-count laws. -/
theorem source_cluster_truncation_tv_le_eventually
    (betaMin betaMax epsilon : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hepsilon : 0 < epsilon) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L E : ℕ,
      betaMin*Real.log N ≤ (L+E+2 : ℝ) → (L+E+2 : ℝ) ≤ betaMax*Real.log N →
      massTotalVariation
        (observableLaw infiniteRademacherMeasure (infiniteExactClusterCount N L))
        (observableLaw infiniteRademacherMeasure (truncatedExactClusterCount N L E)) ≤
          ((fullRate N L : ℝ)/(2 : ℝ)^(E+1))*
            (1+(N : ℝ)^(-(1/(2 : ℝ))+epsilon)) := by
  obtain ⟨Nzero,hzero⟩ := source_mark_tail_le_eventually betaMin betaMax epsilon hbetaMin hbeta hepsilon
  exact ⟨Nzero,fun N hN L E hlo hhi =>
    (source_cluster_truncation_tv_le N L E).trans (hzero N hN L E hlo hhi)⟩


/-- Every growing truncation has negligible source tail when the intensity stays bounded. -/
theorem source_mark_tail_tendsto_zero (betaMin betaMax K : ℝ)
    (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax) (hK : 0 ≤ K)
    (L E : ℕ → ℕ) (hE : Tendsto E atTop atTop)
    (hlower : ∀ᶠ N : ℕ in atTop, betaMin*Real.log N ≤ (L N+E N+2 : ℝ))
    (hupper : ∀ᶠ N : ℕ in atTop, (L N+E N+2 : ℝ)≤betaMax*Real.log N)
    (hrate : ∀ᶠ N : ℕ in atTop, (fullRate N (L N) : ℝ)≤K) :
    Tendsto (fun N => infiniteMarkTailProbability N (L N) (E N)) atTop (𝓝 0) := by
  obtain ⟨Nzero,hzero⟩ := source_mark_tail_le_eventually betaMin betaMax (1/4)
    hbetaMin hbeta (by norm_num)
  have ht : Tendsto (fun N => (2*K)*(1/(2 : ℝ))^(E N)) atTop (𝓝 0) := by
    have hg := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ)≤1/2)
      (by norm_num : (1/(2 : ℝ))<1)).comp hE
    simpa only [mul_zero,Function.comp_def] using hg.const_mul (2*K)
  apply squeeze_zero' (Filter.Eventually.of_forall (fun N => ENNReal.toReal_nonneg)) _ ht
  filter_upwards [eventually_ge_atTop (max Nzero 1),hlower,hupper,hrate] with N hN hlo hhi hr
  have hone : (1 : ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
  have hp : (N : ℝ)^(-(1/(2 : ℝ))+(1/4))≤1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hone (by norm_num)
  have hb := hzero N (by omega) (L N) (E N) hlo hhi
  have hd : (0 : ℝ)<(2 : ℝ)^(E N+1) := by positivity
  calc
    _ ≤ ((fullRate N (L N) : ℝ)/(2 : ℝ)^(E N+1))*
        (1+(N : ℝ)^(-(1/(2 : ℝ))+(1/4))) := hb
    _ ≤ (K/(2 : ℝ)^(E N+1))*2 := by gcongr;linarith
    _ ≤ (K/(2 : ℝ)^(E N))*2 := by
      apply mul_le_mul_of_nonneg_right _ (by norm_num)
      exact div_le_div_of_nonneg_left hK (by positivity)
        (pow_le_pow_right₀ (by norm_num) (by omega : E N≤E N+1))
    _ = _ := by simp only [div_pow,one_pow];ring

/-- The unbounded actual cluster count is recovered in total variation along growing truncations. -/
theorem source_cluster_truncation_tv_tendsto_zero (betaMin betaMax K : ℝ)
    (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax) (hK : 0 ≤ K)
    (L E : ℕ → ℕ) (hE : Tendsto E atTop atTop)
    (hlower : ∀ᶠ N : ℕ in atTop, betaMin*Real.log N ≤ (L N+E N+2 : ℝ))
    (hupper : ∀ᶠ N : ℕ in atTop, (L N+E N+2 : ℝ)≤betaMax*Real.log N)
    (hrate : ∀ᶠ N : ℕ in atTop, (fullRate N (L N) : ℝ)≤K) :
    Tendsto (fun N => massTotalVariation
      (observableLaw infiniteRademacherMeasure (infiniteExactClusterCount N (L N)))
      (observableLaw infiniteRademacherMeasure (truncatedExactClusterCount N (L N) (E N))))
      atTop (𝓝 0) := by
  exact squeeze_zero' (Filter.Eventually.of_forall (fun N => massTotalVariation_nonneg _ _))
    (Filter.Eventually.of_forall (fun N => source_cluster_truncation_tv_le N (L N) (E N)))
    (source_mark_tail_tendsto_zero betaMin betaMax K hbetaMin hbeta hK L E hE hlower hupper hrate)

end
end PaperC.V282.ExactMarkedSourceTail
