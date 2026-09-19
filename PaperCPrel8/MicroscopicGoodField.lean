import PaperCPrel8.ActualSignedPalm

/-! # The paper's maximal-support microscopic good set

Left boundaries are retained on `1..n`; the first value of a run is `j+1`.
The deep-start cutoff and all odd-valuation pivots are literal source data.
-/
namespace PaperC.Prel8.MicroscopicGoodField
open PaperC.Prel8.ActualSignedPalm PaperC.Prel8.OddPrimePivot
open PaperC.Prel8.PrimeForcing PaperC.Prel8.PivotGeometry
open PaperC.ConditionalStartProbability
open PaperC.V282.ExactMarkedModel PaperC.V282.SignedExactMarks
open PaperC.V282.DirectionalSteinInput
open PaperC.V282.FiniteFieldTotalVariation PaperC.V282.FiniteFieldPoissonCoupling
open PaperC.ArratiaGoldsteinGordonInput PaperC.IndependentThinning
open PaperC.V282.SteinFiniteExpectation
open scoped BigOperators NNReal
noncomputable section
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- The actual `G₀`, including the ceiling of the square-root start cutoff. -/
def goodSites (M n L E Y : ℕ) : Finset ℕ :=
  (Finset.Icc 1 n).filter fun j => ⌈Real.sqrt M⌉₊ ≤ j+1 ∧
    ∀ a : Fin (L+E+2), Y < largestOddPrime (j+a.val)

/-- Every retained left boundary lies in the observation interval. -/
theorem goodSites_subset (M n L E Y : ℕ) : goodSites M n L E Y ⊆ Finset.Icc 1 n :=
  Finset.filter_subset _ _

/-- The finite source geometry is discharged for the literal microscopic set. -/
theorem goodSites_geometry {C M n L E Y : ℕ} (hL : 1 ≤ L) (hY : 1 ≤ Y)
    (hB : L+E+2 ≤ Y) (hC : n+(L+E+2) ≤ C+1) :
    GoodGeometry C Y L E (goodSites M n L E Y) where
  length_pos := hL
  cutoff_pos := hY
  support_le := hB
  start_pos j hj := (Finset.mem_Icc.mp (goodSites_subset M n L E Y hj)).1
  cylinder_le j hj := by
    have := (Finset.mem_Icc.mp (goodSites_subset M n L E Y hj)).2
    omega
  good j hj := (Finset.mem_filter.mp hj).2.2

variable {C Y L E : ℕ} {G : Finset ℕ}

/-- Maximal support pivots are used for a common directed change set at each site. -/
def maximalPivots (h : GoodGeometry C Y L E G) (j : {j // j ∈ G}) :
    Fin (L+E+2) → PrimeUpTo C :=
  cylinderPivot (h.start_pos _ j.property) (h.cylinder_le _ j.property)
    (fun a => h.cutoff_pos.trans_lt (h.good _ j.property a))

/-- A shorter marked-word forcing has a subset of the maximal directed footprint. -/
theorem mark_footprint_subset (h : GoodGeometry C Y L E G) (i : Index G E) :
    directedFootprint G (L+E+1) (pivots h i) ⊆
      directedFootprint G (L+E+1) (maximalPivots h i.1) := by
  classical
  intro k hk
  simp only [directedFootprint, Finset.mem_filter] at hk ⊢
  obtain ⟨hk, a, b, hab⟩ := hk
  refine ⟨hk, ⟨⟨a.val, ?_⟩, b, hab⟩⟩
  have := a.isLt
  have := i.2.1.isLt
  omega

/-- The entire categorical field is unchanged outside the site's maximal directed set. -/
theorem field_unchanged_outside_maximal (h : GoodGeometry C Y L E G) (i k : Index G E)
    (hout : k.1.val ∉ directedFootprint G (L+E+1) (maximalPivots h i.1))
    (ω : SampleSpace C) : coupledField h i ω k = field C L E G ω k :=
  unchanged_outside h i k (fun hk => hout (mark_footprint_subset h i hk)) ω

/-- Finite microscopic ledger for the whole retained field, with one footprint per site. -/
theorem maximal_categorical_comparison (h : GoodGeometry C Y L E G)
    (A : SmallSample C Y → Prop)
    (hA : 0 < eventProbability (FinitePMF.uniform (SampleSpace C))
      (fun ω => A (restrictSmall C Y ω)))
    (hsolution : DirectionalSolutionBounds (rate L : Index G E → ℝ≥0)) :
    massTotalVariation (finiteFieldLaw (sourceLaw A hA) (field C L E G))
      (poissonFieldMass (rate L)) ≤
      ∑ i : Index G E, ∑ k : Index G E,
        if k.1.val = i.1.val then (rate L i : ℝ) * rate L k else
        if k.1.val ∈ directedFootprint G (L+E+1) (maximalPivots h i.1) then
          (rate L i : ℝ) * rate L k +
          finitePMFExpectation (sourceLaw A hA)
            (fun ω => (field C L E G ω i : ℝ) * field C L E G ω k) else 0 := by
  convert CategoricalPalm.categorical_stein_bound (sourceLaw A hA) (field C L E G)
    (coupledField h) (rate L) (fun i => i.1.val)
    (fun i k => k.1.val ∈ directedFootprint G (L+E+1) (maximalPivots h i.1))
    (actual_palm_law h A hA) (planted h)
    (fun i ω k hs hne => exclusive h i k ω hs hne)
    (fun i k _ hout ω => field_unchanged_outside_maximal h i k hout ω)
    hsolution using 1
  congr!

end
end PaperC.Prel8.MicroscopicGoodField
