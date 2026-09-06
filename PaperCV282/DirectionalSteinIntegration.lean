import PaperCV282.DirectionalGradientGrowth
import PaperCV282.PoissonFilling
import PaperCV282.DirectionalGeneratorIdentity

/-! # Integration of the directional graph comparison

Every linearity step uses integrability proved from the Hessian bounds and
actual Poisson moments. The independent filling may have zero coordinates.
-/
namespace PaperC.V282.DirectionalSteinIntegration

open DirectionalGeneratorIdentity
open MeasureTheory DirectionalSteinInput DirectionalHessian DirectionalSteinComparison
open DirectionalGradientGrowth PoissonFilling PoissonFillingIdentity PoissonFieldMeasure
open ArratiaGoldsteinGordonInput IndependentThinning SteinFiniteExpectation
open scoped BigOperators NNReal

noncomputable section

variable {Ω ι κ : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The true category mean includes every retained indicator separately. -/
def categoryRate (mu : FinitePMF Ω) (X : ι → Ω → Bool) (kind : ι → κ) (j : κ) : ℝ≥0 :=
  ⟨∑ i, if kind i=j then marginal mu X i else 0,
    Finset.sum_nonneg (fun i _ => by split_ifs;exact marginal_nonneg mu X i;norm_num)⟩

omit [DecidableEq ι] in
theorem sum_categoryRate_mul (mu : FinitePMF Ω) (X : ι → Ω → Bool) (kind : ι → κ)
    (f : κ → ℝ) : (∑ j, (categoryRate mu X kind j : ℝ)*f j)=∑ i, marginal mu X i*f (kind i) := by
  change (∑ j, (∑ i, if kind i=j then marginal mu X i else 0)*f j)=_
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp [ite_mul]

theorem integrable_gradient (fill : κ → ℝ≥0) (g : (κ → ℕ) → ℝ)
    (hsecond : ∀ z i j, |secondDifference g i j z|≤1) (i : κ) (v : κ → ℕ) :
    Integrable (fun z => firstDifference g i (z+v)) (fieldMeasure fill) := by
  simpa only [add_comm] using integrable_firstDifference_shift fill g hsecond i v

theorem integrable_deathGradient (fill : κ → ℝ≥0) (g : (κ → ℕ) → ℝ)
    (hsecond : ∀ z i j, |secondDifference g i j z|≤1) (i : κ) (v : κ → ℕ) :
    Integrable (fun z => (z i : ℝ)*firstDifference g i (decrement i z+v)) (fieldMeasure fill) := by
  apply integrable_coordinate_firstDifference fill g hsecond i i v
    (fun z => decrement i z+v)
  intro z k
  change decrement i z k+v k≤v k+z k
  have h : decrement i z k≤z k := by
    by_cases hk : k=i
    · subst k;simp [decrement]
    · simp [decrement,Function.update_of_ne hk]
  omega

theorem integral_deathGradient (fill : κ → ℝ≥0) (g : (κ → ℕ) → ℝ)
    (i : κ) (v : κ → ℕ) :
    (∫ z, (z i : ℝ)*firstDifference g i (decrement i z+v) ∂fieldMeasure fill)=
      (fill i : ℝ)*∫ z, firstDifference g i (z+v) ∂fieldMeasure fill :=
  poisson_filling_integral fill i (fun z => firstDifference g i (z+v))

omit [DecidableEq κ] in
theorem integral_finiteExpectation (mu : FinitePMF Ω) (fill : κ → ℝ≥0)
    (f : Ω → (κ → ℕ) → ℝ) (hf : ∀ omega, Integrable (f omega) (fieldMeasure fill)) :
    (∫ z, finitePMFExpectation mu (fun omega => f omega z) ∂fieldMeasure fill)=
      finitePMFExpectation mu (fun omega => ∫ z, f omega z ∂fieldMeasure fill) := by
  unfold finitePMFExpectation
  rw [integral_finsetSum Finset.univ (fun omega _ => (hf omega).const_mul _)]
  simp only [integral_const_mul]

/-- Uniformity in the entire independent filling vector survives exact integration. -/
theorem integral_typed_error_le (mu : FinitePMF Ω) (X : ι → Ω → Bool) (kind : ι → κ)
    (G : SimpleGraph ι) (hdep : HasExactDependencyGraph mu X G)
    (f : κ → (κ → ℕ) → ℝ) (weight : κ → κ → ℝ)
    (hstep : ∀ i z j, |f i (addPoint z j)-f i z|≤weight i j) (fill : κ → ℝ≥0) :
    |∫ z, (∑ i, (marginal mu X i*finitePMFExpectation mu
      (fun omega => f (kind i) (z+typedSum X kind Finset.univ omega))-
      finitePMFExpectation mu (fun omega => (if X i omega=true then (1 : ℝ) else 0)*
        f (kind i) (z+typedSum X kind (Finset.univ.erase i) omega)))) ∂fieldMeasure fill|≤
      typedCost mu X kind G weight := by
  have hbound := typed_stein_error_le mu X kind G hdep f weight hstep
  have hi : Integrable (fun z => ∑ i, (marginal mu X i*finitePMFExpectation mu
      (fun omega => f (kind i) (z+typedSum X kind Finset.univ omega))-
      finitePMFExpectation mu (fun omega => (if X i omega=true then (1 : ℝ) else 0)*
        f (kind i) (z+typedSum X kind (Finset.univ.erase i) omega)))) (fieldMeasure fill) :=
    Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable _
      (Filter.Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs] using hbound z))
  apply abs_integral_le_integral_abs.trans
  have h := integral_mono hi.abs (integrable_const (typedCost mu X kind G weight)) hbound
  simpa only [integral_const,probReal_univ,one_smul] using h

/-- Poisson integration by parts removes exactly the independent filling rate. -/
theorem integral_filled_generator (mu : FinitePMF Ω) (X : ι → Ω → Bool) (kind : ι → κ)
    (fill t : κ → ℝ≥0) (hbalance : ∀ j, t j=fill j+categoryRate mu X kind j)
    (g : (κ → ℕ) → ℝ) (hsecond : ∀ z i j, |secondDifference g i j z|≤1) (omega : Ω) :
    (∫ z, steinGenerator t g (z+typedSum X kind Finset.univ omega) ∂fieldMeasure fill)=
      ∑ i, (marginal mu X i*∫ z, firstDifference g (kind i)
        (z+typedSum X kind Finset.univ omega) ∂fieldMeasure fill)-
      ∑ i, (if X i omega=true then (1 : ℝ) else 0)*∫ z,
        firstDifference g (kind i) (z+typedSum X kind (Finset.univ.erase i) omega) ∂fieldMeasure fill := by
  let v := typedSum X kind Finset.univ omega
  have hb (j : κ) := (integrable_gradient fill g hsecond j v).const_mul (t j : ℝ)
  have hd (j : κ) := integrable_deathGradient fill g hsecond j v
  have hr (i : ι) := (integrable_gradient fill g hsecond (kind i)
    (typedSum X kind (Finset.univ.erase i) omega)).const_mul
      (if X i omega=true then (1 : ℝ) else 0)
  dsimp only [v] at hb hd
  simp_rw [filled_steinGenerator_eq]
  have hs := integral_sub ((integrable_finsetSum Finset.univ (fun j _ => hb j)).sub
    (integrable_finsetSum Finset.univ (fun j _ => hd j)))
      (integrable_finsetSum Finset.univ (fun i _ => hr i))
  simp only [Pi.sub_apply] at hs
  rw [hs]
  rw [integral_sub (integrable_finsetSum Finset.univ (fun j _ => hb j))
      (integrable_finsetSum Finset.univ (fun j _ => hd j))]
  rw [integral_finsetSum Finset.univ (fun j _ => hb j),integral_finsetSum Finset.univ (fun j _ => hd j),
    integral_finsetSum Finset.univ (fun i _ => hr i)]
  simp only [integral_const_mul,integral_deathGradient]
  congr 1
  simp_rw [hbalance,NNReal.coe_add,add_mul]
  rw [Finset.sum_add_distrib,add_sub_cancel_left]
  exact sum_categoryRate_mul mu X kind _

/-- The expectation of the true filled generator is precisely the integrated graph error. -/
theorem average_integral_generator_eq_error (mu : FinitePMF Ω) (X : ι → Ω → Bool)
    (kind : ι → κ) (fill t : κ → ℝ≥0)
    (hbalance : ∀ j, t j=fill j+categoryRate mu X kind j)
    (g : (κ → ℕ) → ℝ) (hsecond : ∀ z i j, |secondDifference g i j z|≤1) :
    finitePMFExpectation mu (fun omega =>
      ∫ z, steinGenerator t g (z+typedSum X kind Finset.univ omega) ∂fieldMeasure fill)=
    ∫ z, (∑ i, (marginal mu X i*finitePMFExpectation mu
      (fun omega => firstDifference g (kind i) (z+typedSum X kind Finset.univ omega))-
      finitePMFExpectation mu (fun omega => (if X i omega=true then (1 : ℝ) else 0)*
        firstDifference g (kind i) (z+typedSum X kind (Finset.univ.erase i) omega)))) ∂fieldMeasure fill := by
  have hf (i : ι) (omega : Ω) := integrable_gradient fill g hsecond (kind i)
    (typedSum X kind Finset.univ omega)
  have hg (i : ι) (omega : Ω) := (integrable_gradient fill g hsecond (kind i)
    (typedSum X kind (Finset.univ.erase i) omega)).const_mul
      (if X i omega=true then (1 : ℝ) else 0)
  have hF (i : ι) : Integrable (fun z => finitePMFExpectation mu
      (fun omega => firstDifference g (kind i) (z+typedSum X kind Finset.univ omega))) (fieldMeasure fill) :=
    integrable_finsetSum Finset.univ (fun omega _ => (hf i omega).const_mul (mu.prob omega))
  have hG (i : ι) : Integrable (fun z => finitePMFExpectation mu
      (fun omega => (if X i omega=true then (1 : ℝ) else 0)*
        firstDifference g (kind i) (z+typedSum X kind (Finset.univ.erase i) omega))) (fieldMeasure fill) :=
    integrable_finsetSum Finset.univ (fun omega _ => (hg i omega).const_mul (mu.prob omega))
  simp_rw [integral_filled_generator mu X kind fill t hbalance g hsecond]
  rw [expectation_sub,expectation_finset_sum,expectation_finset_sum]
  have hs := integral_finsetSum Finset.univ
    (fun i _ => ((hF i).const_mul (marginal mu X i)).sub (hG i))
  simp only [Pi.sub_apply] at hs
  rw [hs]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_sub ((hF i).const_mul (marginal mu X i)) (hG i),integral_const_mul,
    integral_finiteExpectation mu fill _ (hf i),integral_finiteExpectation mu fill _ (hg i),
    expectation_const_mul]
  simp only [integral_const_mul]

end
end PaperC.V282.DirectionalSteinIntegration
