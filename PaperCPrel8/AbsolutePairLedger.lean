import PaperCPrel8.ActualSignedCovariance
import PaperCPrel8.TwoBlockRegularity

/-! # The absolute pair ledger after summing all low marks first -/
namespace PaperC.Prel8.AbsolutePairLedger
open Finset ActualSignedPalm ActualSignedCovariance MicroscopicFiniteLedger MicroscopicRelationExcess
open MicroscopicFootprintLedger RoughKernelRegularity TwoBlockRegularity
open ConditionalStartProbability ArratiaGoldsteinGordonInput IndependentThinning V282.ExactMarkedModel
noncomputable section
open scoped NNReal
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P
variable {C Y L E : ℕ} {G : Finset ℕ}

def pairWeight (C Y L E : ℕ) (j k : ℕ) : ℝ :=
  4*(if Nat.dist j k≤L+E+1 then 1 else 0)+
    (if L+E+1<Nat.dist j k then valueExcess C L E j k else 0)+
      2*(if Regular (L+E+1) Y ![j,k] then 0 else 1)

def activity (mu : FinitePMF (SampleSpace C)) (L E : ℕ) (G : Finset ℕ) : ℝ :=
  ∑ j : Site G, ∑ k : Site G, if j=k then 0 else
    ∑ a : Fin (E+1)×F₂, ∑ b : Fin (E+1)×F₂, |covariance (L:=L) mu (j,a) (k,b)|

theorem pairWeight_nonneg (j k : ℕ) : 0≤pairWeight C Y L E j k := by
  have := valueExcess_nonneg C L E j k
  unfold pairWeight
  split_ifs <;> positivity

/-- A category-wise covariance bound with one inverse event probability. -/
theorem covariance_le_weight (h : GoodGeometry C Y L E G) (hY : 2*(L+E+2)≤Y)
    (A : SmallSample C Y → Prop)
    (hA : 0<eventProbability (FinitePMF.uniform (SampleSpace C)) (fun w ↦ A (restrictSmall C Y w)))
    (i k : Index G E) (hne : i.1.val≠k.1.val) :
    |covariance (L:=L) (sourceLaw A hA) i k|≤
      (rate L i:ℝ)*rate L k*pairWeight C Y L E i.1.val k.1.val/
        eventProbability (FinitePMF.uniform (SampleSpace C)) (fun w ↦ A (restrictSmall C Y w)) := by
  by_cases hd : Nat.dist i.1.val k.1.val≤L+E+1
  · apply (local_covariance_le h hY A hA i k hne hd).trans
    apply (le_div_iff₀ hA).mpr
    have hp := probability_le_one (FinitePMF.uniform (SampleSpace C)) (fun w ↦ A (restrictSmall C Y w))
    have hw : 4≤pairWeight C Y L E i.1.val k.1.val := by
      unfold pairWeight
      simp only [hd,Nat.not_lt.mpr hd,ite_true,ite_false,mul_one,add_zero]
      split_ifs <;> norm_num
    have hr : 0≤(rate L i:ℝ)*rate L k := by positivity
    have hh := mul_le_mul_of_nonneg_left hp (show 0≤4*((rate L i:ℝ)*rate L k) by positivity)
    have hh' := mul_le_mul_of_nonneg_left hw hr
    nlinarith
  · have hh := covariance_exception_bound h A hA i k
    simpa only [pairWeight,hd,Nat.lt_of_not_ge hd,ite_false,ite_true,mul_zero,zero_add] using hh

/-- Low sign/excess categories sum to at most the square of the base rate. -/
theorem site_pair_bound (h : GoodGeometry C Y L E G) (hY : 2*(L+E+2)≤Y)
    (A : SmallSample C Y → Prop)
    (hA : 0<eventProbability (FinitePMF.uniform (SampleSpace C)) (fun w ↦ A (restrictSmall C Y w)))
    (j k : Site G) (hne : j≠k) :
    (∑ a : Fin (E+1)×F₂, ∑ b : Fin (E+1)×F₂, |covariance (L:=L) (sourceLaw A hA) (j,a) (k,b)|)≤
      (1/(2:ℝ)^L)^2*pairWeight C Y L E j.val k.val/
        eventProbability (FinitePMF.uniform (SampleSpace C)) (fun w ↦ A (restrictSmall C Y w)) := by
  have hs := sum_le_sum (s:=univ) (fun (a:Fin (E+1)×F₂) _ ↦
    sum_le_sum (s:=univ) (fun (b:Fin (E+1)×F₂) _ ↦
      covariance_le_weight h hY A hA (j,a) (k,b) (fun he ↦ hne (Subtype.ext he))))
  have he : (∑ a : Fin (E+1)×F₂, ∑ b : Fin (E+1)×F₂,
      (rate L (j,a):ℝ)*rate L (k,b)*pairWeight C Y L E j.val k.val/
        eventProbability (FinitePMF.uniform (SampleSpace C)) (fun w ↦ A (restrictSmall C Y w)))=
      (retainedRate L E)^2*pairWeight C Y L E j.val k.val/
        eventProbability (FinitePMF.uniform (SampleSpace C)) (fun w ↦ A (restrictSmall C Y w)) := by
    simp only [rate,retainedRate,pow_two,sum_mul,mul_sum,sum_div]
    exact sum_comm
  rw [he] at hs
  apply hs.trans
  have hr := retainedRate_le_base L E
  apply div_le_div_of_nonneg_right _ hA.le
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr.1 hr.2 2) (pairWeight_nonneg j.val k.val)

/-- The ordered covariance sum, before the geometric counts are substituted. -/
theorem activity_le_weights (h : GoodGeometry C Y L E G) (hY : 2*(L+E+2)≤Y)
    (A : SmallSample C Y → Prop)
    (hA : 0<eventProbability (FinitePMF.uniform (SampleSpace C)) (fun w ↦ A (restrictSmall C Y w))) :
    activity (sourceLaw A hA) L E G≤
      (1/(2:ℝ)^L)^2*(∑ j : Site G, ∑ k : Site G, pairWeight C Y L E j.val k.val)/
        eventProbability (FinitePMF.uniform (SampleSpace C)) (fun w ↦ A (restrictSmall C Y w)) := by
  unfold activity
  rw [mul_sum,sum_div]
  apply sum_le_sum
  intro j hj
  rw [mul_sum,sum_div]
  apply sum_le_sum
  intro k hk
  by_cases he : j=k
  · simp only [he,ite_true]
    have := pairWeight_nonneg (C:=C) (Y:=Y) (L:=L) (E:=E) k.val k.val
    positivity
  · simp only [he,ite_false]
    exact site_pair_bound h hY A hA j k he

end
end PaperC.Prel8.AbsolutePairLedger
