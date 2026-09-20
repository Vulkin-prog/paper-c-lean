import PaperCPrel8.MicroscopicGoodField
import PaperCPrel8.CategoricalSummation

/-! # Finite microscopic costs after summing all excess-sign categories -/
namespace PaperC.Prel8.MicroscopicFiniteLedger
open PaperC.Prel8.ActualSignedPalm PaperC.Prel8.MicroscopicGoodField
open PaperC.Prel8.PrimeForcing PaperC.Prel8.CategoricalSummation
open PaperC.V282.ExactMarkedModel PaperC.ConditionalStartProbability
open PaperC.V282.DirectionalSteinInput
open PaperC.V282.FiniteFieldTotalVariation PaperC.V282.FiniteFieldPoissonCoupling
open PaperC.ArratiaGoldsteinGordonInput PaperC.IndependentThinning
open scoped BigOperators NNReal
noncomputable section
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P
variable {C Y L E : ℕ} {G : Finset ℕ}

abbrev Site (G : Finset ℕ) := {j // j ∈ G}

def retainedRate (L E : ℕ) : ℝ := ∑ a : Fin (E+1) × F₂, (signedMarkRate L a.1.val : ℝ)

def edge (h : GoodGeometry C Y L E G) (j k : Site G) : Prop :=
  k ≠ j ∧ k.val ∈ directedFootprint G (L+E+1) (maximalPivots h j)

def edgeCount (h : GoodGeometry C Y L E G) : ℝ :=
  ∑ j : Site G, ∑ k : Site G, if edge h j k then 1 else 0

def jointCost (h : GoodGeometry C Y L E G) (μ : FinitePMF (SampleSpace C)) : ℝ :=
  ∑ j : Site G, ∑ k : Site G, if edge h j k then
    ∑ a : Fin (E+1) × F₂, ∑ b : Fin (E+1) × F₂,
      finitePMFExpectation μ (fun ω =>
        (field C L E G ω (j,a) : ℝ) * field C L E G ω (k,b)) else 0

/-- The sum of all retained excess-sign rates never exceeds the base start rate. -/
theorem retainedRate_le_base (L E : ℕ) : 0 ≤ retainedRate L E ∧ retainedRate L E ≤ 1/(2:ℝ)^L := by
  refine ⟨Finset.sum_nonneg (fun a _ => (signedMarkRate L a.1.val).coe_nonneg), ?_⟩
  simpa only [retainedRate, Fintype.sum_prod_type] using sum_all_signedMarkRate_le_base L E

/-- The finite categorical comparison with all labels summed before any estimates. -/
theorem grouped_comparison (h : GoodGeometry C Y L E G) (A : SmallSample C Y → Prop)
    (hA : 0 < eventProbability (FinitePMF.uniform (SampleSpace C))
      (fun ω => A (restrictSmall C Y ω)))
    (hsolution : DirectionalSolutionBounds (rate L : Index G E → ℝ≥0)) :
    massTotalVariation (finiteFieldLaw (sourceLaw A hA) (field C L E G))
      (poissonFieldMass (rate L)) ≤
      (G.card : ℝ) * (retainedRate L E)^2 + edgeCount h * (retainedRate L E)^2 +
        jointCost h (sourceLaw A hA) := by
  have hc := maximal_categorical_comparison h A hA hsolution
  have he := ledger_decomposition
    (fun a : Fin (E+1) × F₂ => (signedMarkRate L a.1.val : ℝ))
    (fun j k : Site G => k.val ∈ directedFootprint G (L+E+1) (maximalPivots h j))
    (fun i k => finitePMFExpectation (sourceLaw A hA)
      (fun ω => (field C L E G ω i : ℝ) * field C L E G ω k))
  have hleft : (∑ i : Index G E, ∑ k : Index G E,
        if k.1.val = i.1.val then (rate L i : ℝ) * rate L k else
        if k.1.val ∈ directedFootprint G (L+E+1) (maximalPivots h i.1) then
          (rate L i : ℝ) * rate L k +
          finitePMFExpectation (sourceLaw A hA)
            (fun ω => (field C L E G ω i : ℝ) * field C L E G ω k) else 0) =
      (G.card : ℝ) * (retainedRate L E)^2 + edgeCount h * (retainedRate L E)^2 +
        jointCost h (sourceLaw A hA) := by
    simp only [Site, Fintype.card_coe, rate, retainedRate, edgeCount, jointCost,
      edge, Subtype.val_inj] at he ⊢
    convert he using 1
    congr!
    all_goals exact congrArg (fun d => @ite ℝ _ d) (Subsingleton.elim _ _)
  exact hc.trans_eq hleft

/-- The same-site and product terms contain no factor depending on the number of categories. -/
theorem base_rate_comparison (h : GoodGeometry C Y L E G) (A : SmallSample C Y → Prop)
    (hA : 0 < eventProbability (FinitePMF.uniform (SampleSpace C))
      (fun ω => A (restrictSmall C Y ω)))
    (hsolution : DirectionalSolutionBounds (rate L : Index G E → ℝ≥0)) :
    massTotalVariation (finiteFieldLaw (sourceLaw A hA) (field C L E G))
      (poissonFieldMass (rate L)) ≤
      ((G.card : ℝ) + edgeCount h) * (1/(2:ℝ)^L)^2 + jointCost h (sourceLaw A hA) := by
  have hr := retainedRate_le_base L E
  have hs : (retainedRate L E)^2 ≤ (1/(2:ℝ)^L)^2 :=
    (sq_le_sq₀ hr.1 (by positivity)).mpr hr.2
  have hd : 0 ≤ edgeCount h := by
    apply Finset.sum_nonneg
    intro j _
    apply Finset.sum_nonneg
    intro k _
    split_ifs <;> norm_num
  calc
    _ ≤ _ := grouped_comparison h A hA hsolution
    _ = ((G.card : ℝ) + edgeCount h) * (retainedRate L E)^2 + jointCost h (sourceLaw A hA) := by ring
    _ ≤ _ := by gcongr

end
end PaperC.Prel8.MicroscopicFiniteLedger
