import PaperCPrel8.ActualSignedPairs

/-! # Source-facing microscopic comparison with explicit arithmetic pair weights -/
namespace PaperC.Prel8.MicroscopicPairLedger
open PaperC.Prel8.ActualSignedPalm PaperC.Prel8.ActualSignedPairs
open PaperC.Prel8.MicroscopicFiniteLedger PaperC.Prel8.MicroscopicGoodField
open PaperC.V282.ExactMarkedModel PaperC.V282.DictionaryMarginalCap
open PaperC.ConditionalStartProbability PaperC.ArratiaGoldsteinGordonInput
open PaperC.IndependentThinning PaperC.V282.SteinFiniteExpectation
open PaperC.V282.DirectionalSteinInput
open PaperC.V282.FiniteFieldTotalVariation PaperC.V282.FiniteFieldPoissonCoupling
open scoped BigOperators NNReal
noncomputable section
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P
variable {C Y L E : ℕ} {G : Finset ℕ}

/-- The close-pair estimate is fibrewise; the full-value rank estimate pays the event mass. -/
def pairFactor (C L E : ℕ) (a : ℝ) (j k : ℕ) : ℝ :=
  if Nat.dist j k ≤ L+E+1 then 4 else
    (2:ℝ) ^ PaperC.Affine.relationRho (jointValueSystem C (j+1) (k+1) (L+E+2)) / a

def weightedEdges (h : GoodGeometry C Y L E G) (a : ℝ) : ℝ :=
  ∑ j : Site G, ∑ k : Site G, if edge h j k then pairFactor C L E a j.val k.val else 0

/-- The explicit pair weight is always nonnegative for positive conditioning mass. -/
theorem pairFactor_nonneg (C L E : ℕ) {a : ℝ} (ha : 0 < a) (j k : ℕ) :
    0 ≤ pairFactor C L E a j k := by
  unfold pairFactor
  split_ifs <;> positivity

/-- Uniform in every retained excess and sign, with the actual full-value rank. -/
theorem pair_bound (h : GoodGeometry C Y L E G) (hY : 2*(L+E+2) ≤ Y)
    (A : SmallSample C Y → Prop)
    (hA : 0 < eventProbability (FinitePMF.uniform (SampleSpace C))
      (fun ω => A (restrictSmall C Y ω))) (i k : Index G E) (hne : i.1.val ≠ k.1.val) :
    finitePMFExpectation (sourceLaw A hA)
      (fun ω => (field C L E G ω i : ℝ) * field C L E G ω k) ≤
      (rate L i : ℝ)*rate L k * pairFactor C L E
        (eventProbability (FinitePMF.uniform (SampleSpace C)) (fun ω => A (restrictSmall C Y ω)))
        i.1.val k.1.val := by
  unfold pairFactor
  split_ifs with hd
  · have hh := local_pair_bound_dist h hY A hA i k hne hd
    nlinarith
  · convert conditional_relation_bound h.length_pos A hA i k using 1
    ring

/-- Sum the mark rates before bounding a single directed site pair. -/
theorem summed_pair_bound (h : GoodGeometry C Y L E G) (hY : 2*(L+E+2) ≤ Y)
    (A : SmallSample C Y → Prop)
    (hA : 0 < eventProbability (FinitePMF.uniform (SampleSpace C))
      (fun ω => A (restrictSmall C Y ω))) (j k : Site G) (hne : k ≠ j) :
    (∑ a : Fin (E+1) × F₂, ∑ b : Fin (E+1) × F₂,
      finitePMFExpectation (sourceLaw A hA)
        (fun ω => (field C L E G ω (j,a) : ℝ) * field C L E G ω (k,b))) ≤
    (retainedRate L E)^2 * pairFactor C L E
      (eventProbability (FinitePMF.uniform (SampleSpace C)) (fun ω => A (restrictSmall C Y ω)))
      j.val k.val := by
  calc
    _ ≤ ∑ a : Fin (E+1) × F₂, ∑ b : Fin (E+1) × F₂,
        (signedMarkRate L a.1.val : ℝ)*signedMarkRate L b.1.val * pairFactor C L E
          (eventProbability (FinitePMF.uniform (SampleSpace C)) (fun ω => A (restrictSmall C Y ω)))
          j.val k.val := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro b _
      exact pair_bound h hY A hA (j,a) (k,b) (fun he => hne (Subtype.ext he.symm))
    _ = _ := by
      simp only [retainedRate, sq, Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_comm

/-- All conditional joint costs reduce to a directed site sum, without a label factor. -/
theorem joint_cost_bound (h : GoodGeometry C Y L E G) (hY : 2*(L+E+2) ≤ Y)
    (A : SmallSample C Y → Prop)
    (hA : 0 < eventProbability (FinitePMF.uniform (SampleSpace C))
      (fun ω => A (restrictSmall C Y ω))) :
    jointCost h (sourceLaw A hA) ≤ (retainedRate L E)^2 * weightedEdges h
      (eventProbability (FinitePMF.uniform (SampleSpace C)) (fun ω => A (restrictSmall C Y ω))) := by
  unfold jointCost weightedEdges
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  apply Finset.sum_le_sum
  intro k _
  by_cases he : edge h j k
  · simp only [he, ite_true]
    exact summed_pair_bound h hY A hA j k he.1
  · simp [he]

/-- Complete finite comparison of the actual retained field, with explicit arithmetic costs. -/
theorem finite_arithmetic_comparison (h : GoodGeometry C Y L E G)
    (hY : 2*(L+E+2) ≤ Y) (A : SmallSample C Y → Prop)
    (hA : 0 < eventProbability (FinitePMF.uniform (SampleSpace C))
      (fun ω => A (restrictSmall C Y ω)))
    (hsolution : DirectionalSolutionBounds (rate L : Index G E → ℝ≥0)) :
    massTotalVariation (finiteFieldLaw (sourceLaw A hA) (field C L E G))
      (poissonFieldMass (rate L)) ≤
      (1/(2:ℝ)^L)^2 * ((G.card : ℝ) + edgeCount h + weightedEdges h
        (eventProbability (FinitePMF.uniform (SampleSpace C)) (fun ω => A (restrictSmall C Y ω)))) := by
  have hc := base_rate_comparison h A hA hsolution
  have hj := joint_cost_bound h hY A hA
  have hr := retainedRate_le_base L E
  have hs : (retainedRate L E)^2 ≤ (1/(2:ℝ)^L)^2 :=
    (sq_le_sq₀ hr.1 (by positivity)).mpr hr.2
  have hw : 0 ≤ weightedEdges h
      (eventProbability (FinitePMF.uniform (SampleSpace C)) (fun ω => A (restrictSmall C Y ω))) := by
    apply Finset.sum_nonneg
    intro j _
    apply Finset.sum_nonneg
    intro k _
    split_ifs
    · exact pairFactor_nonneg C L E hA j.val k.val
    · rfl
  nlinarith [mul_le_mul_of_nonneg_right hs hw]

end
end PaperC.Prel8.MicroscopicPairLedger
