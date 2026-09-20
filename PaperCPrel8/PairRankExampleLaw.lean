import PaperCPrel8.PairRankExample

/-! # Exact probabilities of the concrete two-rank example, for every prescribed raw word -/
namespace PaperC.Prel8.PairRankExampleLaw
open PairRankExample TwoRankPair _root_.PaperC.Affine V282.DictionaryMarginalCap
open ArratiaGoldsteinGordonInput IndependentThinning V282.SteinFiniteExpectation
noncomputable section
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem rough_probability (b : Rows) :
    eventProbability (FinitePMF.uniform Large) (fun x ↦ rough x=b)=
      if Compatible rough b then (1/128:ℝ) else 0 := by
  rw [eventProbability_affine_eq,uniformSolutionProbability_eq_ite]
  have hk : Module.finrank F₂ (LinearMap.ker rough)=0 := by
    have h := rough.finrank_range_add_finrank_ker
    rw [rough_rank] at h
    simp only [Module.finrank_fintype_fun_eq_card,Fintype.card_fin] at h
    omega
  split_ifs <;> norm_num [hk,Large]

theorem full_probability (b : Rows) :
    eventProbability (FinitePMF.uniform (SmallBits×Large)) (fun x ↦ full x=b)=(1/1024:ℝ) := by
  rw [eventProbability_affine_eq,uniformSolutionProbability_of_compatible full b
    (LinearMap.mem_range.mpr (full_surjective b))]
  have hk : Module.finrank F₂ (LinearMap.ker full)=1 := by
    have h := full.finrank_range_add_finrank_ker
    rw [full_rank] at h
    norm_num [SmallBits,Large,Module.finrank_prod] at h
    omega
  norm_num [hk,SmallBits,Large,Module.finrank_prod]

theorem conditional_probability (b : Rows) (e : SmallBits) :
    conditionalMass small rough b e=if Compatible rough (b-small e) then (1/128:ℝ) else 0 :=
  rough_probability _

theorem mean_probability (b : Rows) :
    finitePMFExpectation (FinitePMF.uniform SmallBits) (conditionalMass small rough b)=(1/1024:ℝ) := by
  rw [mean_conditional_mass]
  exact full_probability b

/-- Exactly one eighth of small-prime environments support the prescribed joint word. -/
theorem compatibility_probability (b : Rows) :
    eventProbability (FinitePMF.uniform SmallBits) (fun e ↦ Compatible rough (b-small e))=(1/8:ℝ) := by
  have h := mean_probability b
  have he : finitePMFExpectation (FinitePMF.uniform SmallBits) (conditionalMass small rough b)=
      (1/128:ℝ)*eventProbability (FinitePMF.uniform SmallBits) (fun e ↦ Compatible rough (b-small e)) := by
    unfold finitePMFExpectation eventProbability
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    rw [conditional_probability]
    split_ifs <;> ring
  rw [he] at h
  linarith

/-- The raw-word reference is the product of the two individual conditional masses. -/
theorem individual_probabilities (b : Fin 5 → F₂) :
    eventProbability (FinitePMF.uniform Large) (fun x ↦ first x=b)=(1/32:ℝ) ∧
    eventProbability (FinitePMF.uniform Large) (fun x ↦ second x=b)=(1/32:ℝ) := by
  have main (T : Large →ₗ[F₂] (Fin 5 → F₂)) (hr : Module.finrank F₂ T.range=5) :
      eventProbability (FinitePMF.uniform Large) (fun x ↦ T x=b)=(1/32:ℝ) := by
    have hs : T.range=⊤ := Submodule.eq_top_of_finrank_eq (by simpa using hr)
    have hk : Module.finrank F₂ T.ker=2 := by
      have h := T.finrank_range_add_finrank_ker
      rw [hr] at h
      norm_num [Large] at h
      omega
    rw [eventProbability_affine_eq,uniformSolutionProbability_of_compatible T b (by rw [Compatible,hs]; trivial)]
    norm_num [hk,Large]
  exact ⟨main first individual_ranks.1,main second individual_ranks.2⟩

/-- In particular the positive-positive exact-mark word has mean absolute covariance 7/4096. -/
theorem mean_absolute_covariance (b : Rows) :
    finitePMFExpectation (FinitePMF.uniform SmallBits)
      (fun e ↦ |conditionalMass small rough b e-(1/32:ℝ)*(1/32)|)=(7/4096:ℝ) := by
  have hp (e : SmallBits) : conditionalMass small rough b e=0 ∨ conditionalMass small rough b e=(1/128:ℝ) := by
    rw [conditional_probability]
    split_ifs <;> simp
  have he (e : SmallBits) := absolute_two_point (r:=1/1024) (c:=1/128)
    (by norm_num) (by norm_num) (by norm_num) (hp e)
  norm_num only [show (1/32:ℝ)*(1/32)=1/1024 by norm_num]
  simp_rw [he]
  rw [expectation_sub,expectation_add,expectation_const,expectation_const_mul,mean_probability]
  norm_num
end
end PaperC.Prel8.PairRankExampleLaw
