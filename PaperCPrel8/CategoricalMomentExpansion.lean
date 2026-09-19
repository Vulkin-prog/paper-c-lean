import PaperCPrel8.CategoricalTransversals

/-! # Exact signed tensor expansion of an actual categorical law -/
namespace PaperC.Prel8.CategoricalMomentExpansion
open Finset CategoricalTransversals FiniteCumulantEnvelope
open IndependentThinning ArratiaGoldsteinGordonInput V282.SteinFiniteExpectation
noncomputable section
variable {ι α Ω : Type*} [Fintype ι] [Fintype α] [Fintype Ω] [DecidableEq ι] [DecidableEq α]
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

def delta (v y : Option α) : ℝ := if v=y then 1 else 0

def direction (a : α) (y : Option α) : ℝ := delta (some a) y-delta none y

def marginal (mu : FinitePMF Ω) (Y : ι → Ω → Option α) (i : ι) (y : Option α) : ℝ :=
  eventProbability mu (fun w ↦ Y i w=y)

def indicator (Y : ι → Ω → Option α) (a : ι×α) (w : Ω) : ℝ := delta (Y a.1 w) (some a.2)

def tensor (nu : ι → Option α → ℝ) (S : Finset (ι×α)) (y : ι → Option α) : ℝ :=
  ∏ i, match choice S i with | none => nu i (y i) | some a => direction a (y i)

theorem marginal_sum (mu : FinitePMF Ω) (Y : ι → Ω → Option α) (i : ι) :
    (∑ y, marginal mu Y i y)=1 := by
  unfold marginal eventProbability
  rw [sum_comm]
  apply Eq.trans _ mu.sum_prob
  apply sum_congr rfl
  intro w hw
  rw [sum_eq_single (Y i w)]
  · simp
  · intro y hy hn
    simp [Ne.symm hn]
  · simp

theorem indicator_mean (mu : FinitePMF Ω) (Y : ι → Ω → Option α) (a : ι×α) :
    finitePMFExpectation mu (indicator Y a)=marginal mu Y a.1 (some a.2) := by
  unfold indicator delta marginal
  unfold finitePMFExpectation eventProbability
  apply sum_congr rfl
  intro w hw
  by_cases h : Y a.1 w=some a.2 <;> simp [h]

/-- The centered signed-category identity at a single site, including the cemetery value. -/
theorem site_identity (p : Option α → ℝ) (hp : ∑ y, p y=1) (v y : Option α) :
    delta v y=p y+∑ a, (delta v (some a)-p (some a))*direction a y := by
  cases y with
  | some b => simp [delta,direction]
  | none =>
    have hp' := hp
    rw [Fintype.sum_option] at hp'
    simp only [direction,delta,reduceCtorEq,ite_false,ite_true,zero_sub,mul_neg_one,sum_neg_distrib,sum_sub_distrib]
    cases v <;> simp_all [delta]
    <;> linarith

theorem product_expansion (mu : FinitePMF Ω) (Y : ι → Ω → Option α)
    (w : Ω) (y : ι → Option α) :
    (∏ i, delta (Y i w) (y i))=
      ∑ S∈transversals, (∏ a∈S, (indicator Y a w-finitePMFExpectation mu (indicator Y a)))*
        tensor (marginal mu Y) S y := by
  have he (i : ι) : delta (Y i w) (y i)=∑ a : Option α, match a with
      | none => marginal mu Y i (y i)
      | some a => (indicator Y (i,a) w-finitePMFExpectation mu (indicator Y (i,a)))*direction a (y i) := by
    rw [Fintype.sum_option,site_identity _ (marginal_sum mu Y i)]
    simp only [indicator_mean,indicator]
  simp_rw [he]
  rw [Fintype.prod_sum,← sum_graph]
  apply sum_congr rfl
  intro f hf
  simp only [tensor,choice_graph]
  rw [prod_graph,← prod_mul_distrib]
  apply prod_congr rfl
  intro i hi
  cases f i <;> simp

/-- The actual joint mass has exactly the centered-moment tensor coefficients. -/
theorem source_expansion (mu : FinitePMF Ω) (Y : ι → Ω → Option α) (y : ι → Option α) :
    eventProbability mu (fun w ↦ (fun i ↦ Y i w)=y)=
      ∑ S∈transversals, centeredMoment mu (indicator Y) S*tensor (marginal mu Y) S y := by
  rw [← finitePMFExpectation_indicator]
  have he (w : Ω) : (if (fun i ↦ Y i w)=y then (1:ℝ) else 0)=∏ i, delta (Y i w) (y i) := by
    by_cases h : (fun i ↦ Y i w)=y
    · have hh (i : ι) : Y i w=y i := congrFun h i
      simp [h,delta,hh]
    · simp only [if_neg h]
      symm
      obtain ⟨i,hi⟩ := not_forall.mp (fun hh ↦ h (funext hh))
      exact prod_eq_zero (mem_univ i) (by simp [delta,hi])
  have heE : finitePMFExpectation mu (fun w ↦ if (fun i ↦ Y i w)=y then (1:ℝ) else 0)=
      finitePMFExpectation mu (fun w ↦ ∏ i, delta (Y i w) (y i)) := by
    apply expectation_congr
    intro w
    exact he w
  convert heE.trans ?_ using 1
  · apply expectation_congr
    intro w
    by_cases h : (fun i ↦ Y i w)=y <;> simp [h]
  · simp_rw [product_expansion mu Y]
    rw [expectation_finset_sum]
    apply sum_congr rfl
    intro S hS
    exact expectation_mul_const _ _ _

theorem tensor_empty (nu : ι → Option α → ℝ) (y : ι → Option α) :
    tensor nu ∅ y=∏ i, nu i (y i) := by simp [tensor,choice]

theorem centered_source_expansion (mu : FinitePMF Ω) (Y : ι → Ω → Option α) (y : ι → Option α) :
    eventProbability mu (fun w ↦ (fun i ↦ Y i w)=y)-(∏ i, marginal mu Y i (y i))=
      ∑ S∈transversals.erase ∅, centeredMoment mu (indicator Y) S*tensor (marginal mu Y) S y := by
  rw [source_expansion,← sum_erase_add _ _ empty_mem,centeredMoment_empty,tensor_empty]
  ring

end
end PaperC.Prel8.CategoricalMomentExpansion
