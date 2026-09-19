import PaperCPrel8.ActualSignedPairs
import PaperCPrel8.ActualSignedConditionalLaw
import PaperCPrel8.MicroscopicRelationExcess
import PaperCPrel8.RegularTargetPresence

/-! # Absolute conditional covariance, with exact zero for regular two-block plants

A simple positive-mass majorant on the exceptional pairs suffices for the
final pair bound. Exact zero is used before enlarging that exceptional set.
-/
namespace PaperC.Prel8.ActualSignedCovariance
open Finset ActualSignedPalm ActualSignedPairs ActualSignedConditionalLaw CategoricalPalm
open MicroscopicRelationExcess RegularTargetPresence RoughKernelRegularity
open ConditionalStartProbability ArratiaGoldsteinGordonInput IndependentThinning V282.SteinFiniteExpectation
open V282.ExactMarkedModel V282.DictionaryMarginalCap
noncomputable section
open scoped NNReal
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P
variable {C Y L E : ℕ} {G : Finset ℕ}

def covariance (mu : FinitePMF (SampleSpace C)) (i k : Index G E) : ℝ :=
  finitePMFExpectation mu (fun w ↦ (field C L E G w i:ℝ)*field C L E G w k)-
    finitePMFExpectation mu (fun w ↦ (field C L E G w i:ℝ))*
      finitePMFExpectation mu (fun w ↦ (field C L E G w k:ℝ))

theorem probability_le_one {Ω : Type*} [Fintype Ω] (mu : FinitePMF Ω) (P : Ω → Prop) :
    eventProbability mu P≤1 := by
  unfold eventProbability
  apply (sum_le_sum (fun w _ ↦ ?_)).trans_eq mu.sum_prob
  split_ifs
  · exact le_refl _
  · exact mu.nonneg w

theorem covariance_eq (h : GoodGeometry C Y L E G) (A : SmallSample C Y → Prop)
    (hA : 0<eventProbability (FinitePMF.uniform (SampleSpace C)) (fun w ↦ A (restrictSmall C Y w)))
    (i k : Index G E) :
    covariance (L:=L) (sourceLaw A hA) i k=
      finitePMFExpectation (sourceLaw A hA) (fun w ↦ (field C L E G w i:ℝ)*field C L E G w k)-
        (rate L i:ℝ)*rate L k := by
  unfold covariance
  rw [mean_of_palm _ _ _ _ (actual_palm_law h A hA) i,mean_of_palm _ _ _ _ (actual_palm_law h A hA) k]

/-- Private-prime regularity gives exact conditional pair independence for every event A. -/
theorem regular_covariance_zero (h : GoodGeometry C Y L E G) (A : SmallSample C Y → Prop)
    (hA : 0<eventProbability (FinitePMF.uniform (SampleSpace C)) (fun w ↦ A (restrictSmall C Y w)))
    (i k : Index G E) (hr : Regular (L+E+1) Y ![i.1.val,k.1.val]) :
    covariance (L:=L) (sourceLaw A hA) i k=0 := by
  have hj : ∀ a : Fin 2, 0<(![i.1.val,k.1.val] a) := by
    intro a; fin_cases a
    · exact h.start_pos _ i.1.property
    · exact h.start_pos _ k.1.property
  have he : ∀ a : Fin 2, (![i.2.1.val,k.2.1.val] a)≤E := by
    intro a; fin_cases a <;> simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
    · exact Nat.le_of_lt_succ i.2.1.isLt
    · exact Nat.le_of_lt_succ k.2.1.isLt
  have hC : ∀ a : Fin 2, (![i.1.val,k.1.val] a)+(L+E+1)≤C := by
    intro a; fin_cases a
    · have := h.cylinder_le _ i.1.property; simp; omega
    · have := h.cylinder_le _ k.1.property; simp; omega
  have hp := regular_presence h.length_pos ![i.1.val,k.1.val] ![i.2.1.val,k.2.1.val]
    ![i.2.2,k.2.2] hj he hC hr A hA
  rw [covariance_eq h A hA]
  simp only [field,signedMarkValue,indicator_pair_expectation]
  have heq : eventProbability (sourceLaw A hA) (fun w ↦
      SignedExactMark (valueBit w) (i.1.val+1) L i.2.1.val i.2.2 ∧
      SignedExactMark (valueBit w) (k.1.val+1) L k.2.1.val k.2.2)=
        (rate L i:ℝ)*rate L k := by
    simpa [Fin.forall_fin_two,Fin.prod_univ_two,sourceLaw,rate] using hp
  rw [heq,sub_self]

/-- The sharp local pair ceiling also bounds the absolute covariance. -/
theorem local_covariance_le (h : GoodGeometry C Y L E G) (hY : 2*(L+E+2)≤Y)
    (A : SmallSample C Y → Prop)
    (hA : 0<eventProbability (FinitePMF.uniform (SampleSpace C)) (fun w ↦ A (restrictSmall C Y w)))
    (i k : Index G E) (hne : i.1.val≠k.1.val) (hd : Nat.dist i.1.val k.1.val≤L+E+1) :
    |covariance (L:=L) (sourceLaw A hA) i k|≤4*(rate L i:ℝ)*rate L k := by
  rw [covariance_eq h A hA]
  have hb := local_pair_bound_dist h hY A hA i k hne hd
  have hn : 0≤finitePMFExpectation (sourceLaw A hA)
      (fun w ↦ (field C L E G w i:ℝ)*field C L E G w k) := expectation_nonneg _ (fun _ ↦ by positivity)
  have hr : 0≤(rate L i:ℝ)*rate L k := by positivity
  exact abs_le.mpr ⟨by nlinarith,by nlinarith⟩

/-- Outside exact regularity only one inverse conditioning mass is charged. -/
theorem covariance_exception_bound (h : GoodGeometry C Y L E G) (A : SmallSample C Y → Prop)
    (hA : 0<eventProbability (FinitePMF.uniform (SampleSpace C)) (fun w ↦ A (restrictSmall C Y w)))
    (i k : Index G E) :
    |covariance (L:=L) (sourceLaw A hA) i k|≤
      (rate L i:ℝ)*rate L k*(valueExcess C L E i.1.val k.1.val+
        2*(if Regular (L+E+1) Y ![i.1.val,k.1.val] then 0 else 1))/
          eventProbability (FinitePMF.uniform (SampleSpace C)) (fun w ↦ A (restrictSmall C Y w)) := by
  by_cases hr : Regular (L+E+1) Y ![i.1.val,k.1.val]
  · rw [regular_covariance_zero h A hA i k hr,abs_zero,if_pos hr]
    have := valueExcess_nonneg C L E i.1.val k.1.val
    positivity
  · rw [if_neg hr,covariance_eq h A hA]
    have hb := (le_div_iff₀ hA).mp (conditional_relation_bound h.length_pos A hA i k)
    have hprob := probability_le_one (FinitePMF.uniform (SampleSpace C))
      (fun w ↦ A (restrictSmall C Y w))
    have he : 0≤finitePMFExpectation (sourceLaw A hA)
        (fun w ↦ (field C L E G w i:ℝ)*field C L E G w k) := expectation_nonneg _ (fun _ ↦ by positivity)
    have hr0 : 0≤(rate L i:ℝ)*rate L k := by positivity
    have hab : |finitePMFExpectation (sourceLaw A hA)
      (fun w ↦ (field C L E G w i:ℝ)*field C L E G w k) - (rate L i:ℝ)*rate L k| ≤
        finitePMFExpectation (sourceLaw A hA)
          (fun w ↦ (field C L E G w i:ℝ)*field C L E G w k) + (rate L i:ℝ)*rate L k :=
      abs_le.mpr ⟨by linarith, by linarith⟩
    have hh := mul_le_mul_of_nonneg_right hab hA.le
    have hp := mul_le_mul_of_nonneg_left hprob hr0
    apply (le_div_iff₀ hA).mpr
    unfold valueExcess
    nlinarith

end
end PaperC.Prel8.ActualSignedCovariance
