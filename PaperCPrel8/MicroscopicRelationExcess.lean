import PaperCPrel8.MicroscopicPairLedger
import PaperCPrel8.MicroscopicFootprintLedger
import PaperCPrel8.MicroscopicInfiniteField

/-! # Separate the baseline pair cost from full-value relation excess

Only the nonnegative excess `2^rho-1` is enlarged from directed pairs to all
separated pairs. The baseline unit cost stays on the sparse directed graph.
-/
namespace PaperC.Prel8.MicroscopicRelationExcess
open PaperC.Prel8.ActualSignedPalm PaperC.Prel8.MicroscopicFiniteLedger
open PaperC.Prel8.MicroscopicPairLedger PaperC.V282.DictionaryMarginalCap
open PaperC.Prel8.MicroscopicInfiniteField PaperC.ConditionalStartProbability
open PaperC.ArratiaGoldsteinGordonInput PaperC.V282.DirectionalSteinInput
open PaperC.V282.FiniteFieldTotalVariation PaperC.V282.FiniteFieldPoissonCoupling
open scoped NNReal
noncomputable section
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P
variable {C Y L E : ℕ} {G : Finset ℕ}

/-- Actual full-value relation excess, with no parity restriction. -/
def valueExcess (C L E j k : ℕ) : ℝ :=
  (2:ℝ)^PaperC.Affine.relationRho (jointValueSystem C (j+1) (k+1) (L+E+2))-1

/-- Every relation excess is nonnegative, including rank zero. -/
theorem valueExcess_nonneg (C L E j k : ℕ) : 0 ≤ valueExcess C L E j k := by
  unfold valueExcess
  have h := one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)
    (n := PaperC.Affine.relationRho (jointValueSystem C (j+1) (k+1) (L+E+2)))
  linarith

/-- All separated ordered site pairs, not just the directed ones. -/
def separatedExcess (C L E : ℕ) (G : Finset ℕ) : ℝ :=
  ∑ j : Site G, ∑ k : Site G,
    if L+E+1 < Nat.dist j.val k.val then valueExcess C L E j.val k.val else 0

/-- Close ordered directed pairs; the diagonal is already excluded by `edge`. -/
def closeEdgeCount (h : GoodGeometry C Y L E G) : ℝ :=
  ∑ j : Site G, ∑ k : Site G,
    if edge h j k ∧ Nat.dist j.val k.val ≤ L+E+1 then 1 else 0

/-- The relation baseline stays on the graph when the excess is enlarged. -/
theorem pair_weight_split (h : GoodGeometry C Y L E G) {a : ℝ} (ha : 0 < a)
    (j k : Site G) :
    (if edge h j k then pairFactor C L E a j.val k.val else 0) ≤
      4*(if edge h j k ∧ Nat.dist j.val k.val ≤ L+E+1 then 1 else 0) +
      (if edge h j k then 1 else 0)/a +
      (if L+E+1 < Nat.dist j.val k.val then valueExcess C L E j.val k.val else 0)/a := by
  have hp := valueExcess_nonneg C L E j.val k.val
  by_cases he : edge h j k <;> by_cases hd : Nat.dist j.val k.val ≤ L+E+1
  · simp [he,hd,pairFactor,Nat.not_lt.mpr hd,ha.le]
  · have hlt := Nat.lt_of_not_ge hd
    simp only [he,hd,hlt,pairFactor,ite_true,ite_false,true_and,zero_add,mul_zero]
    unfold valueExcess
    exact le_of_eq (by ring)
  · simp only [he,false_and,ite_false,mul_zero,zero_div,zero_add]
    split_ifs <;> positivity
  · simp only [he,false_and,ite_false,mul_zero,zero_div,zero_add]
    exact div_nonneg (by split_ifs <;> positivity) ha.le

/-- Sum the decomposition without replacing the sparse baseline by all pairs. -/
theorem weightedEdges_le_close_and_excess (h : GoodGeometry C Y L E G)
    {a : ℝ} (ha : 0 < a) :
    weightedEdges h a ≤ 4*closeEdgeCount h +
      (edgeCount h + separatedExcess C L E G)/a := by
  calc
    _ ≤ ∑ j : Site G, ∑ k : Site G,
        (4*(if edge h j k ∧ Nat.dist j.val k.val ≤ L+E+1 then 1 else 0) +
        (if edge h j k then 1 else 0)/a +
        (if L+E+1 < Nat.dist j.val k.val then valueExcess C L E j.val k.val else 0)/a) :=
      Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun k _ => pair_weight_split h ha j k))
    _ = _ := by
      simp only [closeEdgeCount,edgeCount,separatedExcess,Finset.sum_add_distrib,
        Finset.mul_sum,Finset.sum_div,add_div,add_assoc]

/-- A distance neighbourhood contains at most `2Q+1` integer sites. -/
theorem distance_filter_card_le (G : Finset ℕ) (j Q : ℕ) :
    (G.filter (fun k => Nat.dist j k ≤ Q)).card ≤ 2*Q+1 := by
  have hs : G.filter (fun k => Nat.dist j k ≤ Q) ⊆ Finset.Icc (j-Q) (j+Q) := by
    intro k hk
    have hd := (Finset.mem_filter.mp hk).2
    unfold Nat.dist at hd
    exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
  apply (Finset.card_le_card hs).trans
  rw [Nat.card_Icc]
  omega

/-- Local directed costs are linear in the support length, with no mark-count factor. -/
theorem closeEdgeCount_le (h : GoodGeometry C Y L E G) :
    closeEdgeCount h ≤ (G.card:ℝ)*(2*(L+E+1:ℝ)+1) := by
  have hlocal (j : Site G) :
      (∑ k : Site G, if edge h j k ∧ Nat.dist j.val k.val ≤ L+E+1 then (1:ℝ) else 0) ≤
        2*(L+E+1:ℝ)+1 := by
    let D := G.filter (fun k => Nat.dist j.val k ≤ L+E+1)
    calc
      _ ≤ ∑ k : Site G, if k.val ∈ D then (1:ℝ) else 0 := by
        apply Finset.sum_le_sum
        intro k _
        have hk := k.property
        simp only [D,Finset.mem_filter,hk,true_and]
        split_ifs <;> simp_all
      _ = (D.card:ℝ) := PaperC.Prel8.MicroscopicFootprintLedger.count_subtype_members D (Finset.filter_subset _ _)
      _ ≤ _ := by exact_mod_cast distance_filter_card_le G j.val (L+E+1)
  calc
    _ ≤ ∑ _j : Site G, (2*(L+E+1:ℝ)+1) := Finset.sum_le_sum (fun j _ => hlocal j)
    _ = _ := by simp [Site]; ring

/-- All local weights and the sparse baseline are separated from the full-value excess. -/
theorem weightedEdges_arithmetic_split (h : GoodGeometry C Y L E G)
    {a : ℝ} (ha : 0 < a) :
    weightedEdges h a ≤ 4*(G.card:ℝ)*(2*(L+E+1:ℝ)+1) +
      (edgeCount h + separatedExcess C L E G)/a := by
  have hw := weightedEdges_le_close_and_excess h ha
  have hc := closeEdgeCount_le h
  nlinarith

/-- The actual infinite-source comparison now uses the separated full-value excess. -/
theorem infinite_relation_comparison
    (h : GoodGeometry C Y L E G) (hY : 2*(L+E+2) ≤ Y)
    (A : SmallSample C Y → Prop)
    (hA : 0 < eventProbability (FinitePMF.uniform (SampleSpace C))
      (fun ω => A (restrictSmall C Y ω)))
    (hsolution : DirectionalSolutionBounds (rate L : Index G E → ℝ≥0)) :
    massTotalVariation (conditionalLaw C Y L E G A) (poissonFieldMass (rate L)) ≤
      (1/(2:ℝ)^L)^2 * ((G.card:ℝ) + edgeCount h +
        4*(G.card:ℝ)*(2*(L+E+1:ℝ)+1) +
        (edgeCount h + separatedExcess C L E G) /
          eventProbability (FinitePMF.uniform (SampleSpace C)) (fun ω => A (restrictSmall C Y ω))) := by
  have hi := infinite_arithmetic_comparison h hY A hA hsolution
  have hw := weightedEdges_arithmetic_split h hA
  apply hi.trans
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  linarith

end
end PaperC.Prel8.MicroscopicRelationExcess
