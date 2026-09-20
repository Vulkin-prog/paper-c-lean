import PaperCPrel8.FiniteConditioning
import PaperCPrel8.CategoricalPalm
import PaperCPrel8.SignedPalmForcing

/-! # The actual retained signed field and its arithmetic Palm coupling

The cylinder may extend past the observation endpoint. The maximal support
certifies every retained mark, but each forcing changes only its own word.
-/
namespace PaperC.Prel8.ActualSignedPalm
open PaperC.Prel8.FiniteConditioning PaperC.Prel8.CategoricalPalm PaperC.Prel8.PalmStein
open PaperC.Prel8.SignedPalmForcing PaperC.Prel8.PrimeForcing
open PaperC.Prel8.PivotGeometry PaperC.Prel8.OddPrimePivot
open PaperC.ConditionalStartProbability PaperC.V282.PrescribedValues
open PaperC.V282.SignedExactMarks PaperC.V282.ExactMarkedModel
open PaperC.IndependentThinning PaperC.ArratiaGoldsteinGordonInput
open PaperC.V282.SteinFiniteExpectation
open PaperC.V282.DirectionalSteinInput
open PaperC.V282.FiniteFieldTotalVariation PaperC.V282.FiniteFieldPoissonCoupling
open scoped BigOperators NNReal
noncomputable section
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- Verifiable arithmetic conditions for a set of retained left boundaries. -/
structure GoodGeometry (C Y L E : ℕ) (G : Finset ℕ) : Prop where
  length_pos : 1 ≤ L
  cutoff_pos : 1 ≤ Y
  support_le : L+E+2 ≤ Y
  start_pos : ∀ j ∈ G, 0 < j
  cylinder_le : ∀ j ∈ G, j+(L+E+2) ≤ C+1
  good : ∀ j ∈ G, ∀ a : Fin (L+E+2), Y < largestOddPrime (j+a.val)

abbrev Index (G : Finset ℕ) (E : ℕ) := {j // j ∈ G} × (Fin (E+1) × F₂)

def field (C L E : ℕ) (G : Finset ℕ) (ω : SampleSpace C) (i : Index G E) : ℕ :=
  signedMarkValue (valueBit ω) (i.1.val+1) L i.2.1.val i.2.2

def rate (L : ℕ) {G : Finset ℕ} {E : ℕ} (i : Index G E) : ℝ≥0 :=
  signedMarkRate L i.2.1.val

variable {C Y L E : ℕ} {G : Finset ℕ}

/-- The maximal good support contains the shorter word of each category. -/
theorem mark_good (h : GoodGeometry C Y L E G) (i : Index G E)
    (a : Fin (L+i.2.1.val+2)) : Y < largestOddPrime (i.1.val+a.val) :=
  h.good i.1.val i.1.property ⟨a.val, by have := i.2.1.isLt; have := a.isLt; omega⟩

/-- Each mark fits in the common arithmetic cylinder. -/
theorem mark_cylinder (h : GoodGeometry C Y L E G) (i : Index G E) :
    i.1.val+(L+i.2.1.val+2) ≤ C+1 := by
  have := h.cylinder_le i.1.val i.1.property
  have := i.2.1.isLt
  omega

/-- The selected prime is the actual largest odd-valuation divisor. -/
def pivots (h : GoodGeometry C Y L E G) (i : Index G E) :
    Fin (L+i.2.1.val+2) → PrimeUpTo C :=
  cylinderPivot (h.start_pos _ i.1.property) (mark_cylinder h i)
    (fun a => h.cutoff_pos.trans_lt (mark_good h i a))

def force (h : GoodGeometry C Y L E G) (i : Index G E) : SampleSpace C → SampleSpace C :=
  forceWord (fun a : Fin (L+i.2.1.val+2) => i.1.val+a.val)
    (pivots h i) (signedExactWord L i.2.1.val i.2.2)

def coupledField (h : GoodGeometry C Y L E G) (i : Index G E) (ω : SampleSpace C) :
    Index G E → ℕ := field C L E G (force h i ω)

/-- The source law conditions the full prime sample on the actual small-prime event. -/
def sourceLaw (A : SmallSample C Y → Prop)
    (hA : 0 < eventProbability (FinitePMF.uniform (SampleSpace C))
      (fun ω => A (restrictSmall C Y ω))) : FinitePMF (SampleSpace C) :=
  conditional (FinitePMF.uniform (SampleSpace C)) (fun ω => A (restrictSmall C Y ω)) hA

/-- The arithmetic coupling plants the requested category, pointwise. -/
theorem planted (h : GoodGeometry C Y L E G) (i : Index G E) (ω : SampleSpace C) :
    coupledField h i ω i = 1 := by
  have hb : L+i.2.1.val+2 ≤ Y := by have := h.support_le; have := i.2.1.isLt; omega
  have hh := signedForcing_hits h.length_pos (pivots h i)
    (cylinderPivot_basis (h.start_pos _ i.1.property) (mark_cylinder h i) _
      (fun a => hb.trans (mark_good h i a).le)) i.2.2 ω
  exact ite_eq_left hh

/-- Other categories at the planted site vanish, using uniqueness of exact signed marks. -/
theorem exclusive (h : GoodGeometry C Y L E G) (i k : Index G E) (ω : SampleSpace C)
    (hs : k.1.val = i.1.val) (hne : k ≠ i) : coupledField h i ω k = 0 := by
  have hi : SignedExactMark (valueBit (force h i ω)) (i.1.val+1) L i.2.1.val i.2.2 := by
    have := planted h i ω
    simpa only [coupledField, field, signedMarkValue, ite_eq_left_iff,
      zero_ne_one, imp_false, not_not] using this
  apply ite_eq_right
  intro hk
  change SignedExactMark _ (k.1.val+1) L k.2.1.val k.2.2 at hk
  rw [hs] at hk
  obtain ⟨he, ht⟩ := signedExactMark_unique h.length_pos hk hi
  exact hne (Prod.ext (Subtype.ext hs) (Prod.ext (Fin.ext he) ht))

/-- Exact Palm laws of the complete retained field, derived from prime forcing. -/
theorem actual_palm_law (h : GoodGeometry C Y L E G) (A : SmallSample C Y → Prop)
    (hA : 0 < eventProbability (FinitePMF.uniform (SampleSpace C))
      (fun ω => A (restrictSmall C Y ω))) :
    HasPalmLaw (sourceLaw A hA) (field C L E G) (coupledField h) (rate L) := by
  intro i f
  have hb : L+i.2.1.val+2 ≤ Y := by have := h.support_le; have := i.2.1.isLt; omega
  have hf := actual_signed_hard_conditional (h.start_pos _ i.1.property) h.length_pos
    (mark_cylinder h i) h.cutoff_pos hb (mark_good h i) i.2.2 A hA
    (fun ω => f (field C L E G ω))
  have hp := actual_signed_small_probability (h.start_pos _ i.1.property) h.length_pos
    (mark_cylinder h i) h.cutoff_pos hb (mark_good h i) i.2.2 A
  change (rate L i : ℝ) * finitePMFExpectation
    (conditional _ _ hA) (fun ω => f (coupledField h i ω)) = _
  rw [expectation_conditional]
  change (signedMarkRate L i.2.1.val : ℝ) * _ = _
  change (signedMarkRate L i.2.1.val : ℝ) * _ =
    finitePMFExpectation (conditional _ _ hA) _
  rw [expectation_conditional]
  have he : (fun ω : SampleSpace C => if A (restrictSmall C Y ω) then
      (field C L E G ω i : ℝ) * f (field C L E G ω) else 0) =
      (fun ω => if A (restrictSmall C Y ω) ∧
        SignedExactMark (valueBit ω) (i.1.val+1) L i.2.1.val i.2.2 then
        f (field C L E G ω) else 0) := by
    funext ω
    simp only [field, signedMarkValue]
    split_ifs <;> simp_all
  rw [he]
  change (signedMarkRate L i.2.1.val : ℝ) * _ = _
  rw [show finitePMFExpectation (FinitePMF.uniform (SampleSpace C))
      (fun ω => if A (restrictSmall C Y ω) then f (coupledField h i ω) else 0) /
      eventProbability (FinitePMF.uniform (SampleSpace C)) (fun ω => A (restrictSmall C Y ω)) =
      _ from hf, hp]
  have hr : (signedMarkRate L i.2.1.val : ℝ) ≠ 0 := by
    rw [signedMarkRate_coe]; positivity
  field_simp

/-- Every other retained mark is unchanged outside the forcing's directed footprint. -/
theorem unchanged_outside (h : GoodGeometry C Y L E G) (i k : Index G E)
    (hout : k.1.val ∉ directedFootprint G (L+E+1) (pivots h i)) (ω : SampleSpace C) :
    coupledField h i ω k = field C L E G ω k := by
  have hv : valueSystem C (fun a : Fin (L+k.2.1.val+2) => k.1.val+a.val) (force h i ω) =
      valueSystem C (fun a : Fin (L+k.2.1.val+2) => k.1.val+a.val) ω := by
    funext a
    exact forceWord_outside_footprint _ (pivots h i) _ ω G (L+E+1) k.1.val
      k.1.property hout ⟨a.val, by have := a.isLt; have := k.2.1.isLt; omega⟩
  have he : SignedExactMark (valueBit (force h i ω)) (k.1.val+1) L k.2.1.val k.2.2 ↔
      SignedExactMark (valueBit ω) (k.1.val+1) L k.2.1.val k.2.2 := by
    rw [← signedWord_iff h.length_pos, ← signedWord_iff h.length_pos, hv]
  simp only [coupledField, field, signedMarkValue, he]

/-- Source-facing finite categorical comparison under any positive small-prime event. -/
theorem actual_categorical_comparison (h : GoodGeometry C Y L E G)
    (A : SmallSample C Y → Prop)
    (hA : 0 < eventProbability (FinitePMF.uniform (SampleSpace C))
      (fun ω => A (restrictSmall C Y ω)))
    (hsolution : DirectionalSolutionBounds (rate L : Index G E → ℝ≥0)) :
    massTotalVariation (finiteFieldLaw (sourceLaw A hA) (field C L E G))
      (poissonFieldMass (rate L)) ≤
      ∑ i : Index G E, ∑ k : Index G E,
        if k.1.val = i.1.val then (rate L i : ℝ) * rate L k else
        if k.1.val ∈ directedFootprint G (L+E+1) (pivots h i) then
          (rate L i : ℝ) * rate L k +
          finitePMFExpectation (sourceLaw A hA)
            (fun ω => (field C L E G ω i : ℝ) * field C L E G ω k) else 0 := by
  convert categorical_stein_bound (sourceLaw A hA) (field C L E G) (coupledField h)
    (rate L) (fun i => i.1.val)
    (fun i k => k.1.val ∈ directedFootprint G (L+E+1) (pivots h i))
    (actual_palm_law h A hA) (planted h)
    (fun i ω k hs hne => exclusive h i k ω hs hne)
    (fun i k _ hout ω => unchanged_outside h i k hout ω) hsolution using 1
  congr!

end
end PaperC.Prel8.ActualSignedPalm
