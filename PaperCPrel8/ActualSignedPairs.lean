import PaperCPrel8.MicroscopicFiniteLedger
import PaperCPrel8.SmallPrimeMixture
import PaperCV282.SignedMarkedSeparatedRelations

/-! # Actual conditional pair costs for the microscopic signed field

Local good windows admit the factor-four estimate on every small-prime fibre.
Separated full-value relation bounds are unconditional and pay one inverse
conditioning mass, rather than assuming that relation bounds hold on each atom.
-/
namespace PaperC.Prel8.ActualSignedPairs
open PaperC.Prel8.ActualSignedPalm PaperC.Prel8.OddPrimePivot
open PaperC.Prel8.FiniteConditioning PaperC.Prel8.SmallPrimeMixture
open PaperC.V282.ExactMarkedModel PaperC.V282.ExactMarkedLocalProbability
open PaperC.V282.SignedMarkedSeparatedRelations PaperC.V282.DictionaryMarginalCap
open PaperC.ConditionalStartProbability PaperC.ConditionalAGGInstantiation
open PaperC.ArratiaGoldsteinGordonInput PaperC.IndependentThinning
open PaperC.V282.SteinFiniteExpectation PaperC.V282.WindowValues
open scoped BigOperators NNReal
noncomputable section
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- Products of the actual zero-one counts equal the joint event indicator. -/
theorem indicator_pair_expectation {Ω : Type*} [Fintype Ω] (μ : FinitePMF Ω)
    (P Q : Ω → Prop) :
    finitePMFExpectation μ (fun ω => ((if P ω then 1 else 0 : ℕ) : ℝ) *
      (if Q ω then 1 else 0 : ℕ)) = eventProbability μ (fun ω => P ω ∧ Q ω) := by
  simp only [finitePMFExpectation, eventProbability]
  apply Finset.sum_congr rfl
  intro ω _
  split_ifs <;> simp_all

variable {C Y L E : ℕ} {G : Finset ℕ}

/-- Every vertex of a retained maximal window is nondefective in the baseline model. -/
theorem maximal_nondefective (h : GoodGeometry C Y L E G) (j : {j // j ∈ G})
    (a : Fin (L+E+2)) :
    ¬PaperC.DefectivePredicate.HDefective Y (vertex (j.val+1) (L+E+2) a) := by
  rw [← largestOddPrime_le_iff h.cutoff_pos]
  simpa only [vertex, Nat.add_sub_cancel] using not_le.mpr (h.good j.val j.property a)

/-- The sharp local pair ceiling survives every positive small-prime event. -/
theorem local_pair_bound (h : GoodGeometry C Y L E G) (hY : 2*(L+E+2) ≤ Y)
    (A : SmallSample C Y → Prop)
    (hA : 0 < eventProbability (FinitePMF.uniform (SampleSpace C))
      (fun ω => A (restrictSmall C Y ω))) (i k : Index G E)
    (hik : i.1.val < k.1.val) (hd : k.1.val-i.1.val ≤ L+E+1) :
    finitePMFExpectation (sourceLaw A hA)
      (fun ω => (field C L E G ω i : ℝ) * field C L E G ω k) ≤
      4*(rate L i : ℝ)*rate L k := by
  apply conditional_fiber_bound C Y A hA
  intro σ
  have heq : i.1.val+1+(k.1.val-i.1.val)=k.1.val+1 := by omega
  have hp := conditioned_signed_pair_le_four
    (by have := h.start_pos i.1.val i.1.property; omega : 2 ≤ i.1.val+1)
    h.length_pos (Nat.le_of_lt_succ i.2.1.isLt) (Nat.le_of_lt_succ k.2.1.isLt)
    (Nat.sub_pos_of_lt hik) hd
    (by rw [heq]; simpa using h.cylinder_le k.1.val k.1.property) hY
    (maximal_nondefective h i.1)
    (by rw [heq]; exact maximal_nondefective h k.1) i.2.2 k.2.2 σ
  simp only [heq] at hp
  simp only [field, signedMarkValue, indicator_pair_expectation]
  exact hp

/-- The local bound is symmetric in the two retained sites. -/
theorem local_pair_bound_dist (h : GoodGeometry C Y L E G) (hY : 2*(L+E+2) ≤ Y)
    (A : SmallSample C Y → Prop)
    (hA : 0 < eventProbability (FinitePMF.uniform (SampleSpace C))
      (fun ω => A (restrictSmall C Y ω))) (i k : Index G E)
    (hne : i.1.val ≠ k.1.val) (hd : Nat.dist i.1.val k.1.val ≤ L+E+1) :
    finitePMFExpectation (sourceLaw A hA)
      (fun ω => (field C L E G ω i : ℝ) * field C L E G ω k) ≤
      4*(rate L i : ℝ)*rate L k := by
  rcases lt_or_gt_of_ne hne with hik | hki
  · apply local_pair_bound h hY A hA i k hik
    simpa only [Nat.dist_eq_sub_of_le hik.le] using hd
  · have hh := local_pair_bound h hY A hA k i hki
      (by simpa only [Nat.dist_eq_sub_of_le_right hki.le] using hd)
    have he : finitePMFExpectation (sourceLaw A hA)
        (fun ω => (field C L E G ω i : ℝ) * field C L E G ω k) =
        finitePMFExpectation (sourceLaw A hA)
        (fun ω => (field C L E G ω k : ℝ) * field C L E G ω i) :=
      expectation_congr _ (fun _ => mul_comm _ _)
    rw [he]
    nlinarith

/-- The actual full-value relation rank controls a pair before conditioning. -/
theorem unconditional_pair_bound (hL : 1 ≤ L) (i k : Index G E) :
    finitePMFExpectation (FinitePMF.uniform (SampleSpace C))
      (fun ω => (field C L E G ω i : ℝ) * field C L E G ω k) ≤
      (rate L i : ℝ)*rate L k * (2:ℝ) ^ PaperC.Affine.relationRho
        (jointValueSystem C (i.1.val+1) (k.1.val+1) (L+E+2)) := by
  simp only [field, signedMarkValue, indicator_pair_expectation]
  exact signed_joint_probability_le_full_value_weight (by omega) (by omega) hL
    (Nat.le_of_lt_succ i.2.1.isLt) (Nat.le_of_lt_succ k.2.1.isLt) i.2.2 k.2.2

/-- Only one inverse event mass is paid for the unconditional relation estimate. -/
theorem conditional_relation_bound (hL : 1 ≤ L) (A : SmallSample C Y → Prop)
    (hA : 0 < eventProbability (FinitePMF.uniform (SampleSpace C))
      (fun ω => A (restrictSmall C Y ω))) (i k : Index G E) :
    finitePMFExpectation (sourceLaw A hA)
      (fun ω => (field C L E G ω i : ℝ) * field C L E G ω k) ≤
      ((rate L i : ℝ)*rate L k * (2:ℝ) ^ PaperC.Affine.relationRho
        (jointValueSystem C (i.1.val+1) (k.1.val+1) (L+E+2))) /
      eventProbability (FinitePMF.uniform (SampleSpace C)) (fun ω => A (restrictSmall C Y ω)) := by
  apply (expectation_conditional_le _ _ hA _ (fun _ => by positivity)).trans
  exact div_le_div_of_nonneg_right (unconditional_pair_bound hL i k) hA.le

end
end PaperC.Prel8.ActualSignedPairs
