import PaperC.Probability.MarkedSteinChenTerms

set_option maxHeartbeats 1800000

/-!
# Explicit local/separated bound for the marked second term

This module turns the concrete local rank estimate into the finite numerator
used by the asymptotic marked Stein--Chen argument.

The local population is injected into
`overlappingPairs N (Q+1) × {0,...,E}²`; its common relation weight is at
most `2^(E+1)`.  The separated population is injected into
`separatedDependencyEdges N Q Y × {0,...,E}²`; there
`2^ρ = 1 + (2^ρ-1)`, and the second summand is exactly the §13 defect
weight.  Thus

`b₂^(E) ≤ (E+1)²
  [2^(E+1) #local(Q) + #edges(Q,Y) + R₂(Q)] / 2^(2(L+1))`.
-/

namespace PaperC
namespace MarkedSteinChenSplitBound

open scoped BigOperators

open ArratiaGoldsteinGordonInput
open ConditionalDependencyGraph
open LargePrimeDependencyGraph
open MarkedConditionalDependencyGraph
open MarkedSteinChenTerms
open SectionTwelveMoments
open SteinChenTerms

noncomputable section

/-! ## Pair populations -/

/-- All ordered marked pairs with distinct starts at distance at most `Q`. -/
def markedLocalPairs (N L E : ℕ) :
    Finset (MarkedIndex N L E × MarkedIndex N L E) := by
  classical
  exact
    (Finset.univ.product Finset.univ).filter fun pair ↦
      pair.1.1.1 ≠ pair.2.1.1 ∧
        Nat.dist pair.1.1.1 pair.2.1.1 ≤ markedCommonRowCount L E

@[simp]
theorem mem_markedLocalPairs
    {N L E : ℕ}
    {pair : MarkedIndex N L E × MarkedIndex N L E} :
    pair ∈ markedLocalPairs N L E ↔
      pair.1.1.1 ≠ pair.2.1.1 ∧
        Nat.dist pair.1.1.1 pair.2.1.1 ≤ markedCommonRowCount L E := by
  classical
  simp [markedLocalPairs]

/--
Actual nonzero separated marked dependency pairs occurring in the split
envelope.
-/
def markedSeparatedDependencyPairs (N L E : ℕ) :
    Finset (MarkedIndex N L E × MarkedIndex N L E) := by
  classical
  exact
    (Finset.univ.product Finset.univ).filter fun pair ↦
      pair.2 ∈
          (closedNeighborhood (markedDependencyGraph N L E) pair.1).erase
            pair.1 ∧
        ¬(pair.1.1.1 = pair.2.1.1 ∨
          MarkedStrictOverlap pair.1 pair.2) ∧
        markedCommonRowCount L E <
          Nat.dist pair.1.1.1 pair.2.1.1

@[simp]
theorem mem_markedSeparatedDependencyPairs
    {N L E : ℕ}
    {pair : MarkedIndex N L E × MarkedIndex N L E} :
    pair ∈ markedSeparatedDependencyPairs N L E ↔
      pair.2 ∈
          (closedNeighborhood (markedDependencyGraph N L E) pair.1).erase
            pair.1 ∧
        ¬(pair.1.1.1 = pair.2.1.1 ∨
          MarkedStrictOverlap pair.1 pair.2) ∧
        markedCommonRowCount L E <
          Nat.dist pair.1.1.1 pair.2.1.1 := by
  classical
  simp [markedSeparatedDependencyPairs]

/-! ## Local cardinality -/

abbrev MarkedLocalPair (N L E : ℕ) :=
  {pair : MarkedIndex N L E × MarkedIndex N L E //
    pair ∈ markedLocalPairs N L E}

def markedLocalPairCode
    (N L E : ℕ) :
    MarkedLocalPair N L E →
      {pair : ℕ × ℕ //
        pair ∈ overlappingPairs N (markedCommonRowCount L E + 1)} ×
        (Fin (E + 1) × Fin (E + 1)) :=
  fun pair ↦
    (⟨(pair.1.1.1.1, pair.1.2.1.1),
      by
        rw [mem_overlappingPairs]
        have hlocal := mem_markedLocalPairs.mp pair.2
        have hdist :
            Nat.dist pair.1.1.1.1 pair.1.2.1.1 <
              markedCommonRowCount L E + 1 :=
          Nat.lt_succ_iff.mpr hlocal.2
        exact
          ⟨(mem_goodStarts.mp pair.1.1.1.2).1,
            (mem_goodStarts.mp pair.1.2.1.2).1,
            hlocal.1, hdist⟩⟩,
      (pair.1.1.2, pair.1.2.2))

theorem markedLocalPairCode_injective
    (N L E : ℕ) :
    Function.Injective (markedLocalPairCode N L E) := by
  rintro ⟨⟨α, β⟩, hαβ⟩ ⟨⟨γ, δ⟩, hγδ⟩ h
  have hx : α.1.1 = γ.1.1 :=
    congrArg (fun z ↦ z.1.1.1) h
  have hy : β.1.1 = δ.1.1 :=
    congrArg (fun z ↦ z.1.1.2) h
  have he : α.2 = γ.2 :=
    congrArg (fun z ↦ z.2.1) h
  have hf : β.2 = δ.2 :=
    congrArg (fun z ↦ z.2.2) h
  apply Subtype.ext
  apply Prod.ext
  · apply Prod.ext
    · apply Subtype.ext
      exact hx
    · exact he
  · apply Prod.ext
    · apply Subtype.ext
      exact hy
    · exact hf

theorem card_markedLocalPairs_le
    (N L E : ℕ) :
    (markedLocalPairs N L E).card ≤
      (E + 1) ^ 2 *
        (overlappingPairs N (markedCommonRowCount L E + 1)).card := by
  rw [← Fintype.card_coe]
  calc
    Fintype.card (MarkedLocalPair N L E) ≤
        Fintype.card
          ({pair : ℕ × ℕ //
              pair ∈
                overlappingPairs N (markedCommonRowCount L E + 1)} ×
            (Fin (E + 1) × Fin (E + 1))) :=
      Fintype.card_le_of_injective
        (markedLocalPairCode N L E)
        (markedLocalPairCode_injective N L E)
    _ =
        (E + 1) ^ 2 *
          (overlappingPairs N (markedCommonRowCount L E + 1)).card := by
      simp [Fintype.card_prod, pow_two]
      ring

theorem card_markedLocalPairs_le_explicit
    (N L E : ℕ) :
    (markedLocalPairs N L E).card ≤
      (E + 1) ^ 2 *
        (2 * N * (markedCommonRowCount L E + 1)) := by
  exact (card_markedLocalPairs_le N L E).trans
    (Nat.mul_le_mul_left _
      (card_overlappingPairs_le_two_mul
        N (markedCommonRowCount L E + 1)))

/-! ## Separated projection -/

abbrev MarkedSeparatedPair (N L E : ℕ) :=
  {pair : MarkedIndex N L E × MarkedIndex N L E //
    pair ∈ markedSeparatedDependencyPairs N L E}

theorem commonPair_mem_separatedDependencyEdges
    {N L E : ℕ} (pair : MarkedSeparatedPair N L E) :
    (pair.1.1.1.1, pair.1.2.1.1) ∈
      separatedDependencyEdges
        N (markedCommonRowCount L E) (markedPrimeCutoff L E) := by
  rw [separatedDependencyEdges, Finset.mem_inter]
  have hp := mem_markedSeparatedDependencyPairs.mp pair.2
  have hstarts : pair.1.1.1.1 ≠ pair.1.2.1.1 :=
    fun h ↦ hp.2.1 (Or.inl h)
  constructor
  · rw [mem_orderedDependencyEdges]
    refine ⟨pair.1.1.1.2, pair.1.2.1.2, ?_⟩
    have hclosed :=
      commonStart_mem_closedNeighborhood_of_marked
        (Finset.mem_erase.mp hp.1).2
    rw [mem_closedNeighborhood] at hclosed
    rcases hclosed with heq | hadj
    · exact False.elim (hstarts (congrArg Subtype.val heq).symm)
    · exact hadj
  · rw [mem_separatedOffDiagPairs]
    exact
      ⟨(mem_goodStarts.mp pair.1.1.1.2).1,
        (mem_goodStarts.mp pair.1.2.1.2).1,
        hstarts, hp.2.2⟩

def markedSeparatedPairCode
    (N L E : ℕ) :
    MarkedSeparatedPair N L E →
      {pair : ℕ × ℕ //
        pair ∈ separatedDependencyEdges
          N (markedCommonRowCount L E) (markedPrimeCutoff L E)} ×
        (Fin (E + 1) × Fin (E + 1)) :=
  fun pair ↦
    (⟨(pair.1.1.1.1, pair.1.2.1.1),
      commonPair_mem_separatedDependencyEdges pair⟩,
      (pair.1.1.2, pair.1.2.2))

theorem markedSeparatedPairCode_injective
    (N L E : ℕ) :
    Function.Injective (markedSeparatedPairCode N L E) := by
  rintro ⟨⟨α, β⟩, hαβ⟩ ⟨⟨γ, δ⟩, hγδ⟩ h
  have hx : α.1.1 = γ.1.1 :=
    congrArg (fun z ↦ z.1.1.1) h
  have hy : β.1.1 = δ.1.1 :=
    congrArg (fun z ↦ z.1.1.2) h
  have he : α.2 = γ.2 :=
    congrArg (fun z ↦ z.2.1) h
  have hf : β.2 = δ.2 :=
    congrArg (fun z ↦ z.2.2) h
  apply Subtype.ext
  apply Prod.ext
  · apply Prod.ext
    · apply Subtype.ext
      exact hx
    · exact he
  · apply Prod.ext
    · apply Subtype.ext
      exact hy
    · exact hf

/-! ## The two finite envelope pieces -/

noncomputable def markedLocalRelationEnvelope (N L E : ℕ) : ℚ := by
  classical
  exact
    ∑ α : MarkedIndex N L E,
      ∑ β ∈
          (closedNeighborhood (markedDependencyGraph N L E) α).erase α,
        if α.1.1 = β.1.1 ∨ MarkedStrictOverlap α β then 0
        else if Nat.dist α.1.1 β.1.1 ≤ markedCommonRowCount L E then
          (2 : ℚ) ^
              jointRho N (markedCommonRowCount L E)
                (orderedMarkedStartPair α β) /
            (2 : ℚ) ^ (2 * (L + 1))
        else 0

noncomputable def markedSeparatedRelationEnvelope (N L E : ℕ) : ℚ := by
  classical
  exact
    ∑ α : MarkedIndex N L E,
      ∑ β ∈
          (closedNeighborhood (markedDependencyGraph N L E) α).erase α,
        if α.1.1 = β.1.1 ∨ MarkedStrictOverlap α β then 0
        else if markedCommonRowCount L E <
            Nat.dist α.1.1 β.1.1 then
          (2 : ℚ) ^
              jointRho N (markedCommonRowCount L E) (α.1.1, β.1.1) /
            (2 : ℚ) ^ (2 * (L + 1))
        else 0

theorem markedBTwoSplitEnvelope_eq_add
    (N L E : ℕ) :
    markedBTwoSplitEnvelope N L E =
      markedLocalRelationEnvelope N L E +
        markedSeparatedRelationEnvelope N L E := by
  classical
  unfold markedBTwoSplitEnvelope markedLocalRelationEnvelope
    markedSeparatedRelationEnvelope
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro α _hα
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro β _hβ
  by_cases hzero :
      α.1.1 = β.1.1 ∨ MarkedStrictOverlap α β
  · simp [hzero]
  · simp only [hzero, if_false]
    by_cases hlocal :
        Nat.dist α.1.1 β.1.1 ≤ markedCommonRowCount L E
    · have hnsep :
          ¬markedCommonRowCount L E < Nat.dist α.1.1 β.1.1 :=
        Nat.not_lt.mpr hlocal
      simp [hlocal, hnsep]
    · have hsep :
          markedCommonRowCount L E < Nat.dist α.1.1 β.1.1 :=
        Nat.lt_of_not_ge hlocal
      simp [hlocal, hsep]

/-! ## Quantitative bounds for the two pieces -/

/--
The local envelope is bounded by its population times the uniform
`2^(E+1)` relation weight.
-/
theorem markedLocalRelationEnvelope_le
    {N L E : ℕ} (hN : 2 ≤ N) (hL : 1 ≤ L) :
    markedLocalRelationEnvelope N L E ≤
      ((markedLocalPairs N L E).card : ℚ) *
        ((2 : ℚ) ^ (E + 1) /
          (2 : ℚ) ^ (2 * (L + 1))) := by
  classical
  let W : ℚ :=
    (2 : ℚ) ^ (E + 1) / (2 : ℚ) ^ (2 * (L + 1))
  have hpoint :
      ∀ α β : MarkedIndex N L E,
        (if α.1.1 = β.1.1 ∨ MarkedStrictOverlap α β then 0
          else if Nat.dist α.1.1 β.1.1 ≤ markedCommonRowCount L E then
            (2 : ℚ) ^
                jointRho N (markedCommonRowCount L E)
                  (orderedMarkedStartPair α β) /
              (2 : ℚ) ^ (2 * (L + 1))
          else 0) ≤
        if α.1.1 ≠ β.1.1 ∧
            Nat.dist α.1.1 β.1.1 ≤ markedCommonRowCount L E then
          W
        else 0 := by
    intro α β
    by_cases hzero :
        α.1.1 = β.1.1 ∨ MarkedStrictOverlap α β
    · rw [if_pos hzero]
      split_ifs <;> positivity
    · have hstarts : α.1.1 ≠ β.1.1 :=
        fun h ↦ hzero (Or.inl h)
      have hstrict : ¬MarkedStrictOverlap α β :=
        fun h ↦ hzero (Or.inr h)
      by_cases hlocal :
          Nat.dist α.1.1 β.1.1 ≤ markedCommonRowCount L E
      · rw [if_neg hzero, if_pos hlocal,
          if_pos ⟨hstarts, hlocal⟩]
        unfold W
        apply div_le_div_of_nonneg_right
        · exact_mod_cast
            pow_jointRho_orderedMarkedStartPair_le
              hN hL α β hstarts hstrict hlocal
        · positivity
      · simp [hzero, hlocal, W]
  unfold markedLocalRelationEnvelope
  calc
    (∑ α : MarkedIndex N L E,
        ∑ β ∈
            (closedNeighborhood (markedDependencyGraph N L E) α).erase α,
          if α.1.1 = β.1.1 ∨ MarkedStrictOverlap α β then 0
          else if Nat.dist α.1.1 β.1.1 ≤ markedCommonRowCount L E then
            (2 : ℚ) ^
                jointRho N (markedCommonRowCount L E)
                  (orderedMarkedStartPair α β) /
              (2 : ℚ) ^ (2 * (L + 1))
          else 0) ≤
        ∑ α : MarkedIndex N L E,
          ∑ β ∈
              (closedNeighborhood (markedDependencyGraph N L E) α).erase α,
            if α.1.1 ≠ β.1.1 ∧
                Nat.dist α.1.1 β.1.1 ≤ markedCommonRowCount L E then
              W
            else 0 := by
      apply Finset.sum_le_sum
      intro α _hα
      exact Finset.sum_le_sum fun β _hβ ↦ hpoint α β
    _ ≤
        ∑ α : MarkedIndex N L E,
          ∑ β : MarkedIndex N L E,
            if α.1.1 ≠ β.1.1 ∧
                Nat.dist α.1.1 β.1.1 ≤ markedCommonRowCount L E then
              W
            else 0 := by
      apply Finset.sum_le_sum
      intro α _hα
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro β _hβ _hnot
      split_ifs <;> positivity
    _ = ((markedLocalPairs N L E).card : ℚ) * W := by
      unfold markedLocalPairs
      change
        (∑ α in (Finset.univ : Finset (MarkedIndex N L E)),
          ∑ β in (Finset.univ : Finset (MarkedIndex N L E)),
            if α.1.1 ≠ β.1.1 ∧
                Nat.dist α.1.1 β.1.1 ≤ markedCommonRowCount L E then
              W
            else 0) = _
      rw [← Finset.sum_product']
      rw [← Finset.sum_filter]
      simp
    _ =
        ((markedLocalPairs N L E).card : ℚ) *
          ((2 : ℚ) ^ (E + 1) /
            (2 : ℚ) ^ (2 * (L + 1))) := rfl

/-- Sigma presentation of the literal separated population. -/
abbrev MarkedSeparatedSigma (N L E : ℕ) :=
  Σ α : MarkedIndex N L E,
    {β : MarkedIndex N L E //
      β ∈ (closedNeighborhood (markedDependencyGraph N L E) α).erase α ∧
        ¬(α.1.1 = β.1.1 ∨ MarkedStrictOverlap α β) ∧
          markedCommonRowCount L E < Nat.dist α.1.1 β.1.1}

noncomputable instance markedSeparatedFiberFintype
    (N L E : ℕ) (α : MarkedIndex N L E) :
    Fintype
      {β : MarkedIndex N L E //
        β ∈ (closedNeighborhood (markedDependencyGraph N L E) α).erase α ∧
          ¬(α.1.1 = β.1.1 ∨ MarkedStrictOverlap α β) ∧
            markedCommonRowCount L E < Nat.dist α.1.1 β.1.1} :=
  Fintype.ofFinite _

/-- Forget the sigma presentation, retaining the exact separated proof. -/
def markedSeparatedSigmaToPair
    (N L E : ℕ) :
    MarkedSeparatedSigma N L E → MarkedSeparatedPair N L E :=
  fun pair ↦
    ⟨(pair.1, pair.2.1), by
      rw [mem_markedSeparatedDependencyPairs]
      exact pair.2.2⟩

theorem markedSeparatedSigmaToPair_injective
    (N L E : ℕ) :
    Function.Injective (markedSeparatedSigmaToPair N L E) := by
  rintro ⟨α, β⟩ ⟨γ, δ⟩ h
  have hα : α = γ :=
    congrArg (fun z ↦ z.1.1) h
  subst γ
  have hβ :
      β.1 = δ.1 :=
    congrArg
      (fun z : MarkedSeparatedPair N L E ↦ z.1.2) h
  exact Sigma.ext rfl (heq_of_eq (Subtype.ext hβ))

/-- The separated envelope as a sum over its literal sigma subtype. -/
theorem markedSeparatedRelationEnvelope_eq_sigmaSum
    (N L E : ℕ) :
    markedSeparatedRelationEnvelope N L E =
      ∑ pair : MarkedSeparatedSigma N L E,
        (2 : ℚ) ^
            jointRho N (markedCommonRowCount L E)
              (pair.1.1.1, pair.2.1.1.1) /
          (2 : ℚ) ^ (2 * (L + 1)) := by
  classical
  unfold markedSeparatedRelationEnvelope
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro α _hα
  rw [← Finset.sum_subtype
    (((closedNeighborhood (markedDependencyGraph N L E) α).erase α).filter
      (fun β ↦
        ¬(α.1.1 = β.1.1 ∨ MarkedStrictOverlap α β) ∧
          markedCommonRowCount L E < Nat.dist α.1.1 β.1.1))
    (fun β ↦ by simp [and_assoc])
    (fun β ↦
      (2 : ℚ) ^
          jointRho N (markedCommonRowCount L E) (α.1.1, β.1.1) /
        (2 : ℚ) ^ (2 * (L + 1)))]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro β _hβ
  by_cases hzero :
      α.1.1 = β.1.1 ∨ MarkedStrictOverlap α β
  · simp [hzero]
  · by_cases hsep :
        markedCommonRowCount L E < Nat.dist α.1.1 β.1.1
    · simp [hzero, hsep]
    · simp [hzero, hsep]

abbrev CommonSeparatedPair (N L E : ℕ) :=
  {pair : ℕ × ℕ //
    pair ∈ separatedDependencyEdges
      N (markedCommonRowCount L E) (markedPrimeCutoff L E)}

abbrev MarkedSeparatedCodeTarget (N L E : ℕ) :=
  CommonSeparatedPair N L E ×
    (Fin (E + 1) × Fin (E + 1))

def markedSeparatedSigmaCode
    (N L E : ℕ) :
    MarkedSeparatedSigma N L E →
      MarkedSeparatedCodeTarget N L E :=
  fun pair ↦
    markedSeparatedPairCode N L E
      (markedSeparatedSigmaToPair N L E pair)

theorem markedSeparatedSigmaCode_injective
    (N L E : ℕ) :
    Function.Injective (markedSeparatedSigmaCode N L E) :=
  (markedSeparatedPairCode_injective N L E).comp
    (markedSeparatedSigmaToPair_injective N L E)

/--
The separated marked weight has multiplicity at most `(E+1)^2` over the
common separated dependency edges.
-/
theorem sum_markedSeparatedSigma_weight_le
    (N L E : ℕ) :
    (∑ pair : MarkedSeparatedSigma N L E,
        2 ^ jointRho N (markedCommonRowCount L E)
          (pair.1.1.1, pair.2.1.1.1)) ≤
      (E + 1) ^ 2 *
        ∑ pair ∈
            separatedDependencyEdges
              N (markedCommonRowCount L E) (markedPrimeCutoff L E),
          2 ^ jointRho N (markedCommonRowCount L E) pair := by
  classical
  let code :
      MarkedSeparatedSigma N L E ↪
        MarkedSeparatedCodeTarget N L E :=
    ⟨markedSeparatedSigmaCode N L E,
      markedSeparatedSigmaCode_injective N L E⟩
  let weight : MarkedSeparatedCodeTarget N L E → ℕ :=
    fun pair ↦
      2 ^ jointRho N (markedCommonRowCount L E) pair.1.1
  have hcode :
      ∀ pair : MarkedSeparatedSigma N L E,
        2 ^ jointRho N (markedCommonRowCount L E)
            (pair.1.1.1, pair.2.1.1.1) =
          weight (code pair) := by
    intro pair
    rfl
  calc
    (∑ pair : MarkedSeparatedSigma N L E,
        2 ^ jointRho N (markedCommonRowCount L E)
          (pair.1.1.1, pair.2.1.1.1)) =
        ∑ pair : MarkedSeparatedSigma N L E,
          weight (code pair) := by
      apply Finset.sum_congr rfl
      intro pair _hpair
      exact hcode pair
    _ =
        ∑ pair ∈
            (Finset.univ :
              Finset (MarkedSeparatedSigma N L E)).map code,
          weight pair := by
      rw [Finset.sum_map]
    _ ≤
        ∑ pair : MarkedSeparatedCodeTarget N L E,
          weight pair := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro pair _hpair _hnot
      exact Nat.zero_le _
    _ =
        (E + 1) ^ 2 *
          ∑ pair : CommonSeparatedPair N L E,
            2 ^ jointRho N (markedCommonRowCount L E) pair.1 := by
      unfold weight
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [← Finset.mul_sum]
      have hcard :
          Fintype.card (Fin (E + 1) × Fin (E + 1)) =
            (E + 1) ^ 2 := by
        simp [Fintype.card_prod, pow_two]
      rw [Finset.card_univ, hcard]
      norm_cast
    _ =
        (E + 1) ^ 2 *
          ∑ pair ∈
              separatedDependencyEdges
                N (markedCommonRowCount L E) (markedPrimeCutoff L E),
            2 ^ jointRho N (markedCommonRowCount L E) pair := by
      congr 1
      exact
        (Finset.sum_subtype
          (separatedDependencyEdges
            N (markedCommonRowCount L E) (markedPrimeCutoff L E))
          (fun _ ↦ Iff.rfl)
          (fun pair ↦
            2 ^ jointRho N (markedCommonRowCount L E) pair)).symm

/-- Raw common relation weights equal baseline count plus defect mass. -/
theorem sum_two_pow_jointRho_eq_card_add_defect
    (N Q : ℕ) (pairs : Finset (ℕ × ℕ)) :
    ∑ pair ∈ pairs, 2 ^ jointRho N Q pair =
      pairs.card + jointDefectMass N Q pairs := by
  classical
  unfold jointDefectMass jointDefectWeight
  rw [show pairs.card = ∑ _pair ∈ pairs, 1 by simp]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro pair _hpair
  have hone : 1 ≤ 2 ^ jointRho N Q pair :=
    Nat.one_le_two_pow
  omega

/--
Separated common weights are bounded by the full edge baseline and the full
§13 separated defect mass.
-/
theorem sum_separatedDependencyEdges_two_pow_jointRho_le
    (N Q Y : ℕ) :
    (∑ pair ∈ separatedDependencyEdges N Q Y,
        2 ^ jointRho N Q pair) ≤
      (orderedDependencyEdges N Q Y).card +
        jointDefectMass N Q (separatedOffDiagPairs N Q) := by
  rw [sum_two_pow_jointRho_eq_card_add_defect]
  exact Nat.add_le_add
    (Finset.card_le_card Finset.inter_subset_left)
    (jointDefectMass_mono Finset.inter_subset_right)

/-- Finite separated-envelope majorant in the exact §13 quantities. -/
theorem markedSeparatedRelationEnvelope_le
    (N L E : ℕ) :
    markedSeparatedRelationEnvelope N L E ≤
      (((E + 1) ^ 2 *
          ((orderedDependencyEdges
              N (markedCommonRowCount L E) (markedPrimeCutoff L E)).card +
            jointDefectMass N (markedCommonRowCount L E)
              (separatedOffDiagPairs
                N (markedCommonRowCount L E))) : ℕ) : ℚ) /
        (2 : ℚ) ^ (2 * (L + 1)) := by
  rw [markedSeparatedRelationEnvelope_eq_sigmaSum]
  rw [← Finset.sum_div]
  push_cast
  apply div_le_div_of_nonneg_right
  · exact_mod_cast
      (sum_markedSeparatedSigma_weight_le N L E).trans
        (Nat.mul_le_mul_left ((E + 1) ^ 2)
          (sum_separatedDependencyEdges_two_pow_jointRho_le
            N (markedCommonRowCount L E) (markedPrimeCutoff L E)))
  · positivity

/-- Explicit natural numerator for the marked second-term bound. -/
noncomputable def markedBTwoSplitNumerator
    (N L E : ℕ) : ℕ :=
  (E + 1) ^ 2 *
    (2 ^ (E + 1) *
        (2 * N * (markedCommonRowCount L E + 1)) +
      (orderedDependencyEdges
        N (markedCommonRowCount L E) (markedPrimeCutoff L E)).card +
      jointDefectMass N (markedCommonRowCount L E)
        (separatedOffDiagPairs N (markedCommonRowCount L E)))

/--
Complete finite numerator bound for the split marked relation envelope.
-/
theorem markedBTwoSplitEnvelope_le_explicit
    {N L E : ℕ} (hN : 2 ≤ N) (hL : 1 ≤ L) :
    markedBTwoSplitEnvelope N L E ≤
      (markedBTwoSplitNumerator N L E : ℚ) /
        (2 : ℚ) ^ (2 * (L + 1)) := by
  rw [markedBTwoSplitEnvelope_eq_add]
  have hlocal :=
    markedLocalRelationEnvelope_le (N := N) (L := L) (E := E) hN hL
  have hlocalCard := card_markedLocalPairs_le_explicit N L E
  have hlocalCardQ :
      ((markedLocalPairs N L E).card : ℚ) ≤
        (((E + 1) ^ 2 *
          (2 * N * (markedCommonRowCount L E + 1)) : ℕ) : ℚ) := by
    exact_mod_cast hlocalCard
  have hlocal' :
      markedLocalRelationEnvelope N L E ≤
        ((((E + 1) ^ 2 *
            (2 * N * (markedCommonRowCount L E + 1)) : ℕ) : ℚ) *
          ((2 : ℚ) ^ (E + 1) /
            (2 : ℚ) ^ (2 * (L + 1)))) := by
    exact hlocal.trans
      (mul_le_mul_of_nonneg_right hlocalCardQ (by positivity))
  have hsep := markedSeparatedRelationEnvelope_le N L E
  calc
    markedLocalRelationEnvelope N L E +
          markedSeparatedRelationEnvelope N L E ≤
        ((((E + 1) ^ 2 *
            (2 * N * (markedCommonRowCount L E + 1)) : ℕ) : ℚ) *
          ((2 : ℚ) ^ (E + 1) /
            (2 : ℚ) ^ (2 * (L + 1)))) +
        (((E + 1) ^ 2 *
            ((orderedDependencyEdges
                N (markedCommonRowCount L E)
                  (markedPrimeCutoff L E)).card +
              jointDefectMass N (markedCommonRowCount L E)
                (separatedOffDiagPairs
                  N (markedCommonRowCount L E))) : ℕ) : ℚ) /
          (2 : ℚ) ^ (2 * (L + 1)) :=
      add_le_add hlocal' hsep
    _ =
        (markedBTwoSplitNumerator N L E : ℚ) /
          (2 : ℚ) ^ (2 * (L + 1)) := by
      unfold markedBTwoSplitNumerator
      push_cast
      ring

end

end MarkedSteinChenSplitBound
end PaperC
