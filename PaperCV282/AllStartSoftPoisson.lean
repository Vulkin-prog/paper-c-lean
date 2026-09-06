import PaperCV282.SoftConditionalPoisson
import PaperCV282.AllStartConditionalDependency

/-!
# Soft retention for the actual conditional dyadic count

The companion's finite soft lemma is instantiated on every dyadic site,
with the complete-support exceptional set (including the root). The
neighbour costs below are the actual unconditional start and pair
probabilities, even when the neighbour is exceptional. The only literature
input is the classical scalar Stein solution estimate.
-/

namespace PaperC.V282.AllStartSoftPoisson

open ArratiaGoldsteinGordonInput IndependentThinning SectionThirteenFiniteBound
open ConditionalAGGInstantiation ConditionalAGGAverage ConditionalStartProbability
open SectionTwelveMoments MaskedArithmeticGeometry AllStartConditionalDependency
open ScalarSteinInput SoftConditionalPoisson
open scoped BigOperators NNReal

noncomputable section

/-- Good indices inside the whole dyadic index type. -/
def goodSiteIndices (N L Y : ℕ) : Finset {x : ℕ // x ∈ dyadicBlock N} :=
  Finset.univ.filter (fun x => x.val ∉ fullBadStarts N L Y)

/-- The target rate retains the entire dyadic population, including bad sites. -/
def fullRate (N L : ℕ) : ℝ≥0 := ⟨(N : ℝ) / 2 ^ L, by positivity⟩

@[simp]
theorem fullRate_coe (N L : ℕ) : (fullRate N L : ℝ) = (N : ℝ) / 2 ^ L := rfl

/-- The small-prime averaging convention is precisely the uniform finite PMF. -/
theorem expectation_uniform_eq_average {Θ : Type*} [Fintype Θ] [Nonempty Θ]
    (f : Θ → ℝ) :
    finitePMFExpectation (FinitePMF.uniform Θ) f = finiteUniformAverage f := by
  simp only [finitePMFExpectation, FinitePMF.uniform_prob, finiteUniformAverage]
  rw [← Finset.mul_sum]
  ring

@[simp]
theorem mem_goodSiteIndices (N L Y : ℕ) (x : {x : ℕ // x ∈ dyadicBlock N}) :
    x ∈ goodSiteIndices N L Y ↔ x.val ∉ fullBadStarts N L Y := by
  classical
  simp [goodSiteIndices]

/-- Actual model instance of companion (B.4), with the true exceptional-neighbour costs. -/
theorem average_full_count_soft_poisson_le (hStein : ScalarSteinFactorsStatement)
    {N L Y : ℕ} (hN : 2 ≤ N) (hL : 0 < L) (hLY : L + 1 ≤ Y) :
    finiteUniformAverage (fun sigma : SmallSample (dyadicCutoff N L) Y =>
      natTotalVariation
        (finiteNatLaw (largeUniformPMF (dyadicCutoff N L) Y)
          (indicatorSum (conditionedAllStartIndicator N L Y sigma)))
        (poissonMass (fullRate N L))) ≤
      firstSteinFactor (fullRate N L) *
        ((goodSiteIndices N L Y).card * (1 / (2 : ℝ) ^ L) ^ 2 +
          (1 / (2 : ℝ) ^ L) *
            (∑ i ∈ goodSiteIndices N L Y,
              ∑ j ∈ (closedNeighborhood (allStartDependencyGraph N L Y) i).erase i,
                (startProbability N L j.val : ℝ)) +
          ∑ i ∈ goodSiteIndices N L Y,
            ∑ j ∈ (closedNeighborhood (allStartDependencyGraph N L Y) i).erase i,
              (jointStartProbability N L i.val j.val : ℝ)) +
      zeroSteinFactor (fullRate N L) *
        ((Finset.univ \ goodSiteIndices N L Y).card / (2 : ℝ) ^ L +
          ∑ i ∈ Finset.univ \ goodSiteIndices N L Y,
            (startProbability N L i.val : ℝ)) := by
  classical
  have hrate : (fullRate N L : ℝ) =
      (Fintype.card {x : ℕ // x ∈ dyadicBlock N} : ℝ) * (1 / (2 : ℝ) ^ L) := by
    simp only [fullRate_coe, Fintype.card_coe, TouchingPairs.card_dyadicBlock]
    ring
  have h := lemma_b_two_average hStein
    (FinitePMF.uniform (SmallSample (dyadicCutoff N L) Y))
    (fun _ => largeUniformPMF (dyadicCutoff N L) Y)
    (conditionedAllStartIndicator N L Y) (allStartDependencyGraph N L Y)
    (hasExactDependencyGraph_conditionedAllStartIndicator hL)
    (goodSiteIndices N L Y) (by positivity : 0 ≤ 1 / (2 : ℝ) ^ L)
    (fun sigma i hi => marginal_conditionedAllStartIndicator_of_not_fullBad
      hN hL hLY sigma i ((mem_goodSiteIndices N L Y i).mp hi))
    (fullRate N L) hrate
  simp only [expectation_uniform_eq_average,
    average_marginal_conditionedAllStartIndicator_eq,
    average_jointMarginal_conditionedAllStartIndicator_eq] at h
  simpa only [mul_one_div] using h

end
end PaperC.V282.AllStartSoftPoisson
