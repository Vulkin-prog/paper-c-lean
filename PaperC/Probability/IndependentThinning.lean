import PaperC.Probability.PoissonVoidApproximation
import PaperC.Probability.SpatialThinningFinite

set_option maxHeartbeats 1800000

/-!
# Independent thinning of a finite indicator family

This module packages the auxiliary Bernoulli variables used in the Laplace
functional argument of §14.  It constructs the product probability space,
computes the one- and two-point marginals after thinning, and identifies its
void probability with the exact exponential functional of the original
indicator configuration.

The preservation of a dependency graph is kept separate from these purely
finite product identities.
-/

namespace PaperC
namespace IndependentThinning

open scoped BigOperators

open ArratiaGoldsteinGordonInput
open SpatialThinningFinite

noncomputable section

universe u v w

variable {Ω : Type u} {Ξ : Type v} {ι : Type w}

local instance (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- Product of two finite probability mass functions. -/
def productPMF
    [Fintype Ω] [Fintype Ξ]
    (μ : FinitePMF Ω) (ν : FinitePMF Ξ) :
    FinitePMF (Ω × Ξ) where
  prob z := μ.prob z.1 * ν.prob z.2
  nonneg z := mul_nonneg (μ.nonneg z.1) (ν.nonneg z.2)
  sum_prob := by
    rw [Fintype.sum_prod_type]
    simp only [Prod.fst, Prod.snd, ← Finset.mul_sum,
      ν.sum_prob, mul_one, μ.sum_prob]

/-- Rectangular events factor under the product PMF. -/
theorem eventProbability_product_and
    [Fintype Ω] [Fintype Ξ]
    (μ : FinitePMF Ω) (ν : FinitePMF Ξ)
    (P : Ω → Prop) (Q : Ξ → Prop) :
    eventProbability (productPMF μ ν)
        (fun z ↦ P z.1 ∧ Q z.2) =
      eventProbability μ P * eventProbability ν Q := by
  classical
  unfold eventProbability productPMF
  rw [Fintype.sum_prod_type]
  simp only [Prod.fst, Prod.snd]
  calc
    (∑ ω, ∑ ξ,
        if P ω ∧ Q ξ then μ.prob ω * ν.prob ξ else 0) =
        ∑ ω,
          (if P ω then μ.prob ω else 0) *
            (∑ ξ, if Q ξ then ν.prob ξ else 0) := by
      apply Finset.sum_congr rfl
      intro ω _hω
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ξ _hξ
      by_cases hP : P ω <;> by_cases hQ : Q ξ <;>
        simp [hP, hQ]
    _ =
        (∑ ω, if P ω then μ.prob ω else 0) *
          ∑ ξ, if Q ξ then ν.prob ξ else 0 := by
      rw [Finset.sum_mul]

/-! ## Weighted consequence of an exact dependency graph -/

/-- Expectation of a real function under a finite PMF. -/
def finitePMFExpectation
    [Fintype Ω] (μ : FinitePMF Ω) (F : Ω → ℝ) : ℝ :=
  ∑ ω, μ.prob ω * F ω

/-- Event probabilities are expectations of their `0/1` indicators. -/
theorem finitePMFExpectation_indicator
    [Fintype Ω] (μ : FinitePMF Ω) (P : Ω → Prop) :
    finitePMFExpectation μ
        (fun ω ↦ if P ω then (1 : ℝ) else 0) =
      eventProbability μ P := by
  classical
  unfold finitePMFExpectation eventProbability
  apply Finset.sum_congr rfl
  intro ω _hω
  by_cases hP : P ω <;> simp [hP]

/-- Fubini identity for an event under the finite product PMF. -/
theorem eventProbability_product_eq_iterated
    [Fintype Ω] [Fintype Ξ]
    (μ : FinitePMF Ω) (ν : FinitePMF Ξ)
    (P : Ω × Ξ → Prop) :
    eventProbability (productPMF μ ν) P =
      finitePMFExpectation μ
        (fun ω ↦ eventProbability ν (fun ξ ↦ P (ω, ξ))) := by
  classical
  unfold eventProbability finitePMFExpectation productPMF
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro ω _hω
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ξ _hξ
  by_cases hP : P (ω, ξ) <;> simp [hP]

/-- Disintegrate a finite expectation over the fibers of a finite-valued
map. -/
theorem finitePMFExpectation_eq_sum_fibers
    [Fintype Ω] {κ : Type*} [Fintype κ]
    (μ : FinitePMF Ω) (f : Ω → κ) (h : κ → ℝ) :
    finitePMFExpectation μ (fun ω ↦ h (f ω)) =
      ∑ y, eventProbability μ (fun ω ↦ f ω = y) * h y := by
  classical
  calc
    finitePMFExpectation μ (fun ω ↦ h (f ω)) =
        ∑ ω, ∑ y,
          if f ω = y then μ.prob ω * h y else 0 := by
      unfold finitePMFExpectation
      apply Finset.sum_congr rfl
      intro ω _hω
      simp
    _ =
        ∑ y, ∑ ω,
          if f ω = y then μ.prob ω * h y else 0 :=
      Finset.sum_comm
    _ =
        ∑ y,
          eventProbability μ (fun ω ↦ f ω = y) * h y := by
      apply Finset.sum_congr rfl
      intro y _hy
      unfold eventProbability
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro ω _hω
      by_cases heq : f ω = y <;> simp [heq]

/-- Complete outside Boolean vector at one graph vertex. -/
def outsideVector
    [Fintype ι] [DecidableEq ι]
    (X : ι → Ω → Bool) (G : SimpleGraph ι) (α : ι)
    (ω : Ω) : OutsideIndex G α → Bool :=
  fun β ↦ X β.1 ω

/--
Atomwise exact dependence implies factorization for arbitrary real weights
of the local Boolean value and of the complete outside Boolean vector.
-/
theorem finitePMFExpectation_mul_of_hasExactDependencyGraph
    [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (μ : FinitePMF Ω) (X : ι → Ω → Bool)
    (G : SimpleGraph ι)
    (hDependency : HasExactDependencyGraph μ X G)
    (α : ι) (u : Bool → ℝ)
    (v : (OutsideIndex G α → Bool) → ℝ) :
    finitePMFExpectation μ
        (fun ω ↦ u (X α ω) * v (outsideVector X G α ω)) =
      finitePMFExpectation μ (fun ω ↦ u (X α ω)) *
        finitePMFExpectation μ
          (fun ω ↦ v (outsideVector X G α ω)) := by
  classical
  letI : Finite (OutsideIndex G α) :=
    Finite.of_injective Subtype.val Subtype.coe_injective
  letI : Fintype (OutsideIndex G α) := Fintype.ofFinite _
  let out : Ω → (OutsideIndex G α → Bool) :=
    outsideVector X G α
  have hjoint :
      ∀ a : Bool, ∀ b : OutsideIndex G α → Bool,
        eventProbability μ
            (fun ω ↦ (X α ω, out ω) = (a, b)) =
          eventProbability μ (fun ω ↦ X α ω = a) *
            eventProbability μ (fun ω ↦ out ω = b) := by
    intro a b
    have hleft :
        (fun ω ↦ (X α ω, out ω) = (a, b)) =
          (fun ω ↦
            X α ω = a ∧ HasOutsidePattern X G α b ω) := by
      funext ω
      apply propext
      constructor
      · intro h
        have h₁ := congrArg Prod.fst h
        have h₂ := congrArg Prod.snd h
        refine ⟨h₁, ?_⟩
        intro β
        exact congrFun h₂ β
      · rintro ⟨h₁, h₂⟩
        apply Prod.ext
        · exact h₁
        · funext β
          exact h₂ β
    have hout :
        (fun ω ↦ out ω = b) =
          HasOutsidePattern X G α b := by
      funext ω
      apply propext
      exact ⟨fun h β ↦ congrFun h β,
        fun h ↦ funext h⟩
    rw [hleft, hout]
    exact hDependency α a b
  rw [finitePMFExpectation_eq_sum_fibers μ
      (fun ω ↦ (X α ω, out ω))
      (fun z ↦ u z.1 * v z.2),
    Fintype.sum_prod_type]
  simp_rw [hjoint]
  rw [finitePMFExpectation_eq_sum_fibers μ
      (fun ω ↦ X α ω) u,
    finitePMFExpectation_eq_sum_fibers μ out v]
  calc
    (∑ a, ∑ b,
        (eventProbability μ fun ω ↦ X α ω = a) *
            eventProbability μ (fun ω ↦ out ω = b) *
          (u a * v b)) =
      ∑ a,
        (eventProbability μ fun ω ↦ X α ω = a) * u a *
          (∑ b,
            eventProbability μ (fun ω ↦ out ω = b) * v b) := by
      apply Finset.sum_congr rfl
      intro a _ha
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _hb
      ring
    _ =
      (∑ a,
          eventProbability μ (fun ω ↦ X α ω = a) * u a) *
        ∑ b,
          eventProbability μ (fun ω ↦ out ω = b) * v b := by
      rw [Finset.sum_mul]

/-- Coordinates required to be retained are simultaneously true with the
expected Bernoulli product probability. -/
theorem eventProbability_all_true_eq_prod
    [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ)
    (hq0 : ∀ i, 0 ≤ q i)
    (hq1 : ∀ i, q i ≤ 1)
    (s : Finset ι) :
    eventProbability
        (bernoulliProductPMF q hq0 hq1)
        (fun ξ ↦ ∀ i ∈ s, ξ i = true) =
      ∏ i ∈ s, q i := by
  classical
  unfold eventProbability
  simp only [bernoulliProductPMF]
  have hindicator :
      ∀ ξ : ι → Bool,
        (if (∀ i ∈ s, ξ i = true) then
            ∏ i, bernoulliWeight q i (ξ i)
          else 0) =
        ∏ i,
          if i ∈ s ∧ ξ i = false then
            0
          else bernoulliWeight q i (ξ i) := by
    intro ξ
    by_cases h : ∀ i ∈ s, ξ i = true
    · rw [if_pos h]
      apply Finset.prod_congr rfl
      intro i _hi
      rw [if_neg]
      rintro ⟨his, hfalse⟩
      have := h i his
      simp_all
    · rw [if_neg h]
      push Not at h
      obtain ⟨i, his, hnotTrue⟩ := h
      have hfalse : ξ i = false := by
        cases hi : ξ i
        · rfl
        · exact (hnotTrue hi).elim
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      rw [if_pos]
      exact ⟨his, hfalse⟩
  simp_rw [hindicator]
  let f : ι → Bool → ℝ :=
    fun i b ↦
      if i ∈ s ∧ b = false then 0
      else bernoulliWeight q i b
  calc
    (∑ ξ : ι → Bool,
        ∏ i,
          if i ∈ s ∧ ξ i = false then
            0
          else bernoulliWeight q i (ξ i)) =
        ∑ ξ : ι → Bool, ∏ i, f i (ξ i) := rfl
    _ = ∏ i, ∑ b, f i b :=
      (Fintype.prod_sum f).symm
    _ = ∏ i, if i ∈ s then q i else 1 := by
      apply Finset.prod_congr rfl
      intro i _hi
      by_cases his : i ∈ s
      · simp [f, his, bernoulliWeight]
      · simp [f, his, bernoulliWeight]
    _ = ∏ i ∈ s, q i := by
      rw [Finset.prod_ite_mem]
      simp

/-! ## Coordinate events under the Bernoulli product law -/

/-- An event imposing a one-coordinate predicate on every member of `s`. -/
def CoordinateEvent
    [Fintype ι]
    (s : Finset ι) (P : ι → Bool → Prop)
    (ξ : ι → Bool) : Prop :=
  ∀ i ∈ s, P i (ξ i)

/-- Exact probability of a finite coordinate event. -/
theorem eventProbability_coordinateEvent_eq_prod
    [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ)
    (hq0 : ∀ i, 0 ≤ q i)
    (hq1 : ∀ i, q i ≤ 1)
    (s : Finset ι) (P : ι → Bool → Prop) :
    eventProbability
        (bernoulliProductPMF q hq0 hq1)
        (CoordinateEvent s P) =
      ∏ i ∈ s,
        ∑ b : Bool,
          if P i b then bernoulliWeight q i b else 0 := by
  classical
  unfold eventProbability CoordinateEvent
  simp only [bernoulliProductPMF]
  have hindicator :
      ∀ ξ : ι → Bool,
        (if (∀ i ∈ s, P i (ξ i)) then
            ∏ i, bernoulliWeight q i (ξ i)
          else 0) =
        ∏ i,
          if i ∈ s ∧ ¬P i (ξ i) then
            0
          else bernoulliWeight q i (ξ i) := by
    intro ξ
    by_cases h : ∀ i ∈ s, P i (ξ i)
    · rw [if_pos h]
      apply Finset.prod_congr rfl
      intro i _hi
      rw [if_neg]
      rintro ⟨his, hnot⟩
      exact hnot (h i his)
    · rw [if_neg h]
      push Not at h
      obtain ⟨i, his, hnot⟩ := h
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      rw [if_pos]
      exact ⟨his, hnot⟩
  simp_rw [hindicator]
  let f : ι → Bool → ℝ :=
    fun i b ↦
      if i ∈ s ∧ ¬P i b then 0
      else bernoulliWeight q i b
  calc
    (∑ ξ : ι → Bool,
        ∏ i,
          if i ∈ s ∧ ¬P i (ξ i) then
            0
          else bernoulliWeight q i (ξ i)) =
        ∑ ξ : ι → Bool, ∏ i, f i (ξ i) := rfl
    _ = ∏ i, ∑ b, f i b :=
      (Fintype.prod_sum f).symm
    _ =
        ∏ i,
          if i ∈ s then
            ∑ b : Bool,
              if P i b then bernoulliWeight q i b else 0
          else 1 := by
      apply Finset.prod_congr rfl
      intro i _hi
      by_cases his : i ∈ s
      · rw [if_pos his]
        apply Finset.sum_congr rfl
        intro b _hb
        by_cases hP : P i b <;>
          simp [f, his, hP]
      · rw [if_neg his]
        simp [f, his, bernoulliWeight]
    _ =
        ∏ i ∈ s,
          ∑ b : Bool,
            if P i b then bernoulliWeight q i b else 0 := by
      rw [Finset.prod_ite_mem]
      simp

/-- Coordinate events on disjoint sets are independent. -/
theorem eventProbability_coordinateEvent_and_of_disjoint
    [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ)
    (hq0 : ∀ i, 0 ≤ q i)
    (hq1 : ∀ i, q i ≤ 1)
    {s t : Finset ι} (hst : Disjoint s t)
    (P Q : ι → Bool → Prop) :
    eventProbability
        (bernoulliProductPMF q hq0 hq1)
        (fun ξ ↦ CoordinateEvent s P ξ ∧ CoordinateEvent t Q ξ) =
      eventProbability
          (bernoulliProductPMF q hq0 hq1)
          (CoordinateEvent s P) *
        eventProbability
          (bernoulliProductPMF q hq0 hq1)
          (CoordinateEvent t Q) := by
  classical
  let R : ι → Bool → Prop :=
    fun i b ↦ if i ∈ s then P i b else Q i b
  have hevent :
      (fun ξ : ι → Bool ↦
        CoordinateEvent s P ξ ∧ CoordinateEvent t Q ξ) =
      CoordinateEvent (s ∪ t) R := by
    funext ξ
    apply propext
    constructor
    · rintro ⟨hs, ht⟩ i hi
      rcases Finset.mem_union.mp hi with his | hit
      · simpa [R, his] using hs i his
      · have hnotS : i ∉ s := by
          intro his
          exact Finset.disjoint_left.mp hst his hit
        simpa [R, hnotS] using ht i hit
    · intro h
      constructor
      · intro i his
        have hi : i ∈ s ∪ t := Finset.mem_union_left t his
        simpa [R, his] using h i hi
      · intro i hit
        have hi : i ∈ s ∪ t := Finset.mem_union_right s hit
        have hnotS : i ∉ s := by
          intro his
          exact Finset.disjoint_left.mp hst his hit
        simpa [R, hnotS] using h i hi
  rw [hevent,
    eventProbability_coordinateEvent_eq_prod,
    eventProbability_coordinateEvent_eq_prod,
    eventProbability_coordinateEvent_eq_prod,
    Finset.prod_union hst]
  congr 1
  · apply Finset.prod_congr rfl
    intro i his
    apply Finset.sum_congr rfl
    intro b _hb
    simp [R, his]
  · apply Finset.prod_congr rfl
    intro i hit
    have hnotS : i ∉ s := by
      intro his
      exact Finset.disjoint_left.mp hst his hit
    apply Finset.sum_congr rfl
    intro b _hb
    simp [R, hnotS]

theorem eventProbability_coordinate_true
    [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ)
    (hq0 : ∀ i, 0 ≤ q i)
    (hq1 : ∀ i, q i ≤ 1)
    (i : ι) :
    eventProbability
        (bernoulliProductPMF q hq0 hq1)
        (fun ξ ↦ ξ i = true) =
      q i := by
  simpa using
    eventProbability_all_true_eq_prod q hq0 hq1 ({i} : Finset ι)

theorem eventProbability_two_coordinates_true
    [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ)
    (hq0 : ∀ i, 0 ≤ q i)
    (hq1 : ∀ i, q i ≤ 1)
    {i j : ι} (hij : i ≠ j) :
    eventProbability
        (bernoulliProductPMF q hq0 hq1)
        (fun ξ ↦ ξ i = true ∧ ξ j = true) =
      q i * q j := by
  have h :=
    eventProbability_all_true_eq_prod
      q hq0 hq1 ({i, j} : Finset ι)
  simpa [hij] using h

/-! ## The retention coordinates have every supergraph as dependency graph -/

/-- Boolean coordinate projection on the retention sample. -/
def coordinateIndicator (i : ι) (ξ : ι → Bool) : Bool :=
  ξ i

/-- Vertices outside the closed neighborhood of `α`. -/
def outsideVertices
    [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) (α : ι) : Finset ι :=
  Finset.univ.filter fun i ↦ i ∉ closedNeighborhood G α

@[simp]
theorem mem_outsideVertices
    [Fintype ι] [DecidableEq ι]
    {G : SimpleGraph ι} {α i : ι} :
    i ∈ outsideVertices G α ↔
      i ∉ closedNeighborhood G α := by
  simp [outsideVertices]

/-- Coordinate predicate encoding one prescribed outside pattern. -/
def outsidePatternPredicate
    [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) (α : ι)
    (pattern : OutsideIndex G α → Bool)
    (i : ι) (b : Bool) : Prop :=
  ∀ h : i ∉ closedNeighborhood G α,
    b = pattern ⟨i, h⟩

/--
Independent Bernoulli coordinates satisfy the exact dependency-graph
identity for every simple graph: enlarging the graph only removes
coordinates from the outside vector.
-/
theorem hasExactDependencyGraph_coordinateIndicator
    [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ)
    (hq0 : ∀ i, 0 ≤ q i)
    (hq1 : ∀ i, q i ≤ 1)
    (G : SimpleGraph ι) :
    HasExactDependencyGraph
      (bernoulliProductPMF q hq0 hq1)
      coordinateIndicator G := by
  classical
  intro α value pattern
  let s : Finset ι := {α}
  let t : Finset ι := outsideVertices G α
  let P : ι → Bool → Prop := fun _ b ↦ b = value
  let Q : ι → Bool → Prop :=
    outsidePatternPredicate G α pattern
  have hdisjoint : Disjoint s t := by
    rw [Finset.disjoint_left]
    intro i his hit
    have hi : i = α := Finset.mem_singleton.mp his
    subst i
    exact (mem_outsideVertices.mp hit)
      (self_mem_closedNeighborhood G α)
  have hlocal :
      (fun ξ : ι → Bool ↦ coordinateIndicator α ξ = value) =
        CoordinateEvent s P := by
    funext ξ
    apply propext
    simp [CoordinateEvent, coordinateIndicator, s, P]
  have houtside :
      HasOutsidePattern coordinateIndicator G α pattern =
        CoordinateEvent t Q := by
    funext ξ
    apply propext
    constructor
    · intro h i hit
      have hi :
          i ∉ closedNeighborhood G α :=
        mem_outsideVertices.mp hit
      intro hi'
      have hv := h ⟨i, hi⟩
      simpa [coordinateIndicator, Q, outsidePatternPredicate]
        using hv
    · intro h β
      have hit : β.1 ∈ t :=
        mem_outsideVertices.mpr β.2
      have hv := h β.1 hit β.2
      simpa [coordinateIndicator, Q, outsidePatternPredicate]
        using hv
  have hjoint :
      (fun ξ : ι → Bool ↦
        coordinateIndicator α ξ = value ∧
          HasOutsidePattern coordinateIndicator G α pattern ξ) =
        (fun ξ ↦
          CoordinateEvent s P ξ ∧ CoordinateEvent t Q ξ) := by
    funext ξ
    apply propext
    rw [congrFun hlocal ξ, congrFun houtside ξ]
  rw [hjoint, hlocal, houtside]
  exact
    eventProbability_coordinateEvent_and_of_disjoint
      q hq0 hq1 hdisjoint P Q

/-- Coordinatewise combination of two indicator families on a product
sample space. -/
def combineIndicator
    (op : Bool → Bool → Bool)
    (X : ι → Ω → Bool) (R : ι → Ξ → Bool)
    (i : ι) (z : Ω × Ξ) : Bool :=
  op (X i z.1) (R i z.2)

/--
The product of two exact dependency-graph families, combined
coordinatewise by an arbitrary Boolean operation, has the same exact
dependency graph.
-/
theorem hasExactDependencyGraph_combineIndicator
    [Fintype Ω] [Fintype Ξ] [Fintype ι] [DecidableEq ι]
    (μ : FinitePMF Ω) (ν : FinitePMF Ξ)
    (X : ι → Ω → Bool) (R : ι → Ξ → Bool)
    (G : SimpleGraph ι)
    (hX : HasExactDependencyGraph μ X G)
    (hR : HasExactDependencyGraph ν R G)
    (op : Bool → Bool → Bool) :
    HasExactDependencyGraph
      (productPMF μ ν) (combineIndicator op X R) G := by
  classical
  intro α value pattern
  let outX : Ω → (OutsideIndex G α → Bool) :=
    outsideVector X G α
  let outR : Ξ → (OutsideIndex G α → Bool) :=
    outsideVector R G α
  let F : Bool → Bool → Prop :=
    fun a c ↦ op a c = value
  let Q :
      (OutsideIndex G α → Bool) →
        (OutsideIndex G α → Bool) → Prop :=
    fun b d ↦ ∀ β, op (b β) (d β) = pattern β
  let aWeight : Bool → ℝ :=
    fun a ↦
      finitePMFExpectation ν
        (fun ξ ↦ if F a (R α ξ) then 1 else 0)
  let bWeight : (OutsideIndex G α → Bool) → ℝ :=
    fun b ↦
      finitePMFExpectation ν
        (fun ξ ↦ if Q b (outR ξ) then 1 else 0)
  have ha :
      ∀ a : Bool,
        eventProbability ν (fun ξ ↦ F a (R α ξ)) =
          aWeight a := by
    intro a
    unfold aWeight finitePMFExpectation eventProbability
    apply Finset.sum_congr rfl
    intro ξ _hξ
    by_cases hF : F a (R α ξ) <;> simp [hF]
  have hb :
      ∀ b : OutsideIndex G α → Bool,
        eventProbability ν (fun ξ ↦ Q b (outR ξ)) =
          bWeight b := by
    intro b
    unfold bWeight finitePMFExpectation eventProbability
    apply Finset.sum_congr rfl
    intro ξ _hξ
    by_cases hQ : Q b (outR ξ) <;> simp [hQ]
  have hconditional :
      ∀ ω : Ω,
        eventProbability ν
            (fun ξ ↦
              F (X α ω) (R α ξ) ∧
                Q (outX ω) (outR ξ)) =
          aWeight (X α ω) * bWeight (outX ω) := by
    intro ω
    have hfactor :=
      finitePMFExpectation_mul_of_hasExactDependencyGraph
        ν R G hR α
        (fun c ↦ if F (X α ω) c then 1 else 0)
        (fun d ↦ if Q (outX ω) d then 1 else 0)
    calc
      eventProbability ν
          (fun ξ ↦
            F (X α ω) (R α ξ) ∧
              Q (outX ω) (outR ξ)) =
        finitePMFExpectation ν
          (fun ξ ↦
            (if F (X α ω) (R α ξ) then 1 else 0) *
              (if Q (outX ω) (outR ξ) then 1 else 0)) := by
        rw [← finitePMFExpectation_indicator]
        congr 1
        funext ξ
        by_cases hF : F (X α ω) (R α ξ) <;>
          by_cases hQ : Q (outX ω) (outR ξ) <;>
            simp [hF, hQ]
      _ =
        finitePMFExpectation ν
            (fun ξ ↦
              if F (X α ω) (R α ξ) then 1 else 0) *
          finitePMFExpectation ν
            (fun ξ ↦
              if Q (outX ω) (outR ξ) then 1 else 0) := by
        simpa only [outR] using hfactor
      _ = aWeight (X α ω) * bWeight (outX ω) := rfl
  have hlocal :
      eventProbability (productPMF μ ν)
          (fun z ↦ F (X α z.1) (R α z.2)) =
        finitePMFExpectation μ
          (fun ω ↦ aWeight (X α ω)) := by
    rw [eventProbability_product_eq_iterated]
    simp only [Prod.fst, Prod.snd]
    unfold finitePMFExpectation
    apply Finset.sum_congr rfl
    intro ω _hω
    exact congrArg (fun r : ℝ ↦ μ.prob ω * r)
      (ha (X α ω))
  have houtside :
      eventProbability (productPMF μ ν)
          (fun z ↦ Q (outX z.1) (outR z.2)) =
        finitePMFExpectation μ
          (fun ω ↦ bWeight (outX ω)) := by
    rw [eventProbability_product_eq_iterated]
    simp only [Prod.fst, Prod.snd]
    unfold finitePMFExpectation
    apply Finset.sum_congr rfl
    intro ω _hω
    exact congrArg (fun r : ℝ ↦ μ.prob ω * r)
      (hb (outX ω))
  have hjoint :
      eventProbability (productPMF μ ν)
          (fun z ↦
            F (X α z.1) (R α z.2) ∧
              Q (outX z.1) (outR z.2)) =
        eventProbability (productPMF μ ν)
            (fun z ↦ F (X α z.1) (R α z.2)) *
          eventProbability (productPMF μ ν)
            (fun z ↦ Q (outX z.1) (outR z.2)) := by
    rw [eventProbability_product_eq_iterated]
    simp only [Prod.fst, Prod.snd]
    calc
      finitePMFExpectation μ
          (fun ω ↦
            eventProbability ν
              (fun ξ ↦
                F (X α ω) (R α ξ) ∧
                  Q (outX ω) (outR ξ))) =
        finitePMFExpectation μ
          (fun ω ↦
            aWeight (X α ω) * bWeight (outX ω)) := by
        unfold finitePMFExpectation
        apply Finset.sum_congr rfl
        intro ω _hω
        exact congrArg (fun r : ℝ ↦ μ.prob ω * r)
          (hconditional ω)
      _ =
        finitePMFExpectation μ
            (fun ω ↦ aWeight (X α ω)) *
          finitePMFExpectation μ
            (fun ω ↦ bWeight (outX ω)) := by
        exact
          finitePMFExpectation_mul_of_hasExactDependencyGraph
            μ X G hX α aWeight bWeight
      _ =
        eventProbability (productPMF μ ν)
            (fun z ↦ F (X α z.1) (R α z.2)) *
          eventProbability (productPMF μ ν)
            (fun z ↦ Q (outX z.1) (outR z.2)) := by
        rw [hlocal, houtside]
  have heventLocal :
      (fun z : Ω × Ξ ↦
        combineIndicator op X R α z = value) =
      (fun z ↦ F (X α z.1) (R α z.2)) := by
    rfl
  have heventOutside :
      HasOutsidePattern
          (combineIndicator op X R) G α pattern =
        (fun z : Ω × Ξ ↦
          Q (outX z.1) (outR z.2)) := by
    funext z
    apply propext
    rfl
  have heventJoint :
      (fun z : Ω × Ξ ↦
        combineIndicator op X R α z = value ∧
          HasOutsidePattern
            (combineIndicator op X R) G α pattern z) =
      (fun z ↦
        F (X α z.1) (R α z.2) ∧
          Q (outX z.1) (outR z.2)) := by
    funext z
    apply propext
    rw [congrFun heventLocal z, congrFun heventOutside z]
  rw [heventJoint, heventLocal, heventOutside]
  exact hjoint

/-- Indicator family after independent coordinatewise retention. -/
def thinnedIndicator
    (X : ι → Ω → Bool)
    (i : ι) (z : Ω × (ι → Bool)) : Bool :=
  X i z.1 && z.2 i

@[simp]
theorem thinnedIndicator_eq_true_iff
    (X : ι → Ω → Bool) (i : ι)
    (z : Ω × (ι → Bool)) :
    thinnedIndicator X i z = true ↔
      X i z.1 = true ∧ z.2 i = true := by
  simp [thinnedIndicator]

/--
Independent thinning preserves every exact dependency graph of the original
indicator family.
-/
theorem hasExactDependencyGraph_thinnedIndicator
    [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (μ : FinitePMF Ω) (X : ι → Ω → Bool)
    (G : SimpleGraph ι)
    (hDependency : HasExactDependencyGraph μ X G)
    (q : ι → ℝ)
    (hq0 : ∀ i, 0 ≤ q i)
    (hq1 : ∀ i, q i ≤ 1) :
    HasExactDependencyGraph
      (productPMF μ (bernoulliProductPMF q hq0 hq1))
      (thinnedIndicator X) G := by
  have hcoordinates :
      HasExactDependencyGraph
        (bernoulliProductPMF q hq0 hq1)
        coordinateIndicator G :=
    hasExactDependencyGraph_coordinateIndicator q hq0 hq1 G
  have hcombine :=
    hasExactDependencyGraph_combineIndicator
      μ (bernoulliProductPMF q hq0 hq1)
      X coordinateIndicator G hDependency hcoordinates Bool.and
  have hfamily :
      thinnedIndicator X =
        combineIndicator Bool.and X coordinateIndicator := by
    rfl
  rw [hfamily]
  exact hcombine

/-- Marginals are multiplied by their retention probabilities. -/
theorem marginal_thinnedIndicator
    [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (μ : FinitePMF Ω) (X : ι → Ω → Bool)
    (q : ι → ℝ)
    (hq0 : ∀ i, 0 ≤ q i)
    (hq1 : ∀ i, q i ≤ 1)
    (i : ι) :
    marginal
        (productPMF μ (bernoulliProductPMF q hq0 hq1))
        (thinnedIndicator X) i =
      marginal μ X i * q i := by
  unfold marginal
  rw [show
      (fun z : Ω × (ι → Bool) ↦
        thinnedIndicator X i z = true) =
      (fun z ↦ X i z.1 = true ∧ z.2 i = true) by
        funext z
        apply propext
        exact thinnedIndicator_eq_true_iff X i z]
  calc
    eventProbability
        (productPMF μ (bernoulliProductPMF q hq0 hq1))
        (fun z ↦ X i z.1 = true ∧ z.2 i = true) =
      eventProbability μ (fun ω ↦ X i ω = true) *
        eventProbability (bernoulliProductPMF q hq0 hq1)
          (fun ξ ↦ ξ i = true) :=
      eventProbability_product_and μ
        (bernoulliProductPMF q hq0 hq1)
        (fun ω ↦ X i ω = true) (fun ξ ↦ ξ i = true)
    _ = marginal μ X i * q i := by
      rw [eventProbability_coordinate_true]
      rfl

/-- Distinct joint marginals acquire the product of the two retentions. -/
theorem jointMarginal_thinnedIndicator
    [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (μ : FinitePMF Ω) (X : ι → Ω → Bool)
    (q : ι → ℝ)
    (hq0 : ∀ i, 0 ≤ q i)
    (hq1 : ∀ i, q i ≤ 1)
    {i j : ι} (hij : i ≠ j) :
    jointMarginal
        (productPMF μ (bernoulliProductPMF q hq0 hq1))
        (thinnedIndicator X) i j =
      jointMarginal μ X i j * (q i * q j) := by
  unfold jointMarginal
  rw [show
      (fun z : Ω × (ι → Bool) ↦
        thinnedIndicator X i z = true ∧
          thinnedIndicator X j z = true) =
      (fun z ↦
        (X i z.1 = true ∧ X j z.1 = true) ∧
          (z.2 i = true ∧ z.2 j = true)) by
        funext z
        apply propext
        simp only [thinnedIndicator_eq_true_iff]
        tauto]
  calc
    eventProbability
        (productPMF μ (bernoulliProductPMF q hq0 hq1))
        (fun z ↦
          (X i z.1 = true ∧ X j z.1 = true) ∧
            (z.2 i = true ∧ z.2 j = true)) =
      eventProbability μ
          (fun ω ↦ X i ω = true ∧ X j ω = true) *
        eventProbability (bernoulliProductPMF q hq0 hq1)
          (fun ξ ↦ ξ i = true ∧ ξ j = true) :=
      eventProbability_product_and μ
        (bernoulliProductPMF q hq0 hq1)
        (fun ω ↦ X i ω = true ∧ X j ω = true)
        (fun ξ ↦ ξ i = true ∧ ξ j = true)
    _ = jointMarginal μ X i j * (q i * q j) := by
      rw [eventProbability_two_coordinates_true q hq0 hq1 hij]
      rfl

/-- The first AGG term cannot increase under independent thinning. -/
theorem bOne_thinnedIndicator_le
    [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (μ : FinitePMF Ω) (X : ι → Ω → Bool)
    (G : SimpleGraph ι)
    (q : ι → ℝ)
    (hq0 : ∀ i, 0 ≤ q i)
    (hq1 : ∀ i, q i ≤ 1) :
    bOne
        (productPMF μ (bernoulliProductPMF q hq0 hq1))
        (thinnedIndicator X) G ≤
      bOne μ X G := by
  unfold bOne
  simp_rw [marginal_thinnedIndicator μ X q hq0 hq1]
  apply Finset.sum_le_sum
  intro i _hi
  apply Finset.sum_le_sum
  intro j _hj
  have hpi := marginal_nonneg μ X i
  have hpj := marginal_nonneg μ X j
  have hqi := hq0 i
  have hqj := hq0 j
  have hqq : q i * q j ≤ 1 := by
    nlinarith [hq1 i, hq1 j]
  calc
    (marginal μ X i * q i) *
          (marginal μ X j * q j) =
        (marginal μ X i * marginal μ X j) *
          (q i * q j) := by ring
    _ ≤ marginal μ X i * marginal μ X j :=
      mul_le_of_le_one_right (mul_nonneg hpi hpj) hqq

/-- The second AGG term cannot increase under independent thinning. -/
theorem bTwo_thinnedIndicator_le
    [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (μ : FinitePMF Ω) (X : ι → Ω → Bool)
    (G : SimpleGraph ι)
    (q : ι → ℝ)
    (hq0 : ∀ i, 0 ≤ q i)
    (hq1 : ∀ i, q i ≤ 1) :
    bTwo
        (productPMF μ (bernoulliProductPMF q hq0 hq1))
        (thinnedIndicator X) G ≤
      bTwo μ X G := by
  unfold bTwo
  apply Finset.sum_le_sum
  intro i _hi
  apply Finset.sum_le_sum
  intro j hj
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  rw [jointMarginal_thinnedIndicator
    μ X q hq0 hq1 hji.symm]
  have hp := jointMarginal_nonneg μ X i j
  have hqq0 : 0 ≤ q i * q j :=
    mul_nonneg (hq0 i) (hq0 j)
  have hqq1 : q i * q j ≤ 1 := by
    nlinarith [hq0 i, hq0 j, hq1 i, hq1 j]
  exact mul_le_of_le_one_right hp hqq1

/-- Finite exponential functional of an indicator configuration. -/
def exponentialFunctional
    [Fintype ι]
    (g : ι → ℝ) (X : ι → Ω → Bool) (ω : Ω) : ℝ :=
  Real.exp (-(∑ i, if X i ω = true then g i else 0))

/--
The auxiliary void probability is exactly the expectation of the
exponential functional of the unthinned configuration.
-/
theorem eventProbability_no_thinned_active_eq_exponentialFunctional
    [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (μ : FinitePMF Ω) (X : ι → Ω → Bool)
    (g : ι → ℝ) (hg : ∀ i, 0 ≤ g i) :
    eventProbability
        (productPMF μ
          (bernoulliProductPMF
            (exponentialRetention g)
            (fun i ↦ exponentialRetention_nonneg g hg i)
            (fun i ↦ exponentialRetention_le_one g i)))
        (fun z ↦ NoRetainedActive (fun i ↦ X i z.1) z.2) =
      ∑ ω, μ.prob ω * exponentialFunctional g X ω := by
  classical
  unfold eventProbability productPMF
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro ω _hω
  simp only [Prod.fst, Prod.snd]
  let ν :=
    bernoulliProductPMF
      (exponentialRetention g)
      (fun i ↦ exponentialRetention_nonneg g hg i)
      (fun i ↦ exponentialRetention_le_one g i)
  calc
    (∑ ξ,
        if NoRetainedActive (fun i ↦ X i ω) ξ then
          μ.prob ω * ν.prob ξ
        else 0) =
      μ.prob ω *
        eventProbability ν
          (NoRetainedActive (fun i ↦ X i ω)) := by
      unfold eventProbability
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ξ _hξ
      by_cases hvoid :
          NoRetainedActive (fun i ↦ X i ω) ξ <;>
        simp [hvoid]
    _ = μ.prob ω * exponentialFunctional g X ω := by
      dsimp only [ν]
      rw [eventProbability_noRetainedActive_exponential_eq g hg]
      rfl

end

end IndependentThinning
end PaperC
