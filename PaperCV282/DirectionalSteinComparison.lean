import PaperCV282.DirectionalSteinInput
import PaperCV282.SteinFiniteExpectation

/-! # Category-valued dependency-graph telescoping

The offset vector is arbitrary and remains in the outside configuration.
This permits an independent Poisson filling after averaging, without any
lower bound on the retained population. All pair weights remain entrywise.
-/
namespace PaperC.V282.DirectionalSteinComparison

open DirectionalSteinInput ArratiaGoldsteinGordonInput IndependentThinning SteinFiniteExpectation
open scoped BigOperators

noncomputable section

variable {Ω ι κ : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι] [DecidableEq κ]

def typedSum (X : ι → Ω → Bool) (kind : ι → κ) (s : Finset ι) (omega : Ω) : κ → ℕ :=
  ∑ i ∈ s, if X i omega=true then Pi.single (kind i) 1 else 0

def typedBOne (mu : FinitePMF Ω) (X : ι → Ω → Bool) (kind : ι → κ)
    (G : SimpleGraph ι) (weight : κ → κ → ℝ) : ℝ :=
  ∑ i, ∑ j ∈ closedNeighborhood G i, weight (kind i) (kind j)*marginal mu X i*marginal mu X j

def typedBTwo (mu : FinitePMF Ω) (X : ι → Ω → Bool) (kind : ι → κ)
    (G : SimpleGraph ι) (weight : κ → κ → ℝ) : ℝ :=
  ∑ i, ∑ j ∈ (closedNeighborhood G i).erase i, weight (kind i) (kind j)*jointMarginal mu X i j

def typedCost (mu : FinitePMF Ω) (X : ι → Ω → Bool) (kind : ι → κ)
    (G : SimpleGraph ι) (weight : κ → κ → ℝ) : ℝ :=
  typedBOne mu X kind G weight+typedBTwo mu X kind G weight

omit [Fintype Ω] in
theorem typedSum_partition (X : ι → Ω → Bool) (kind : ι → κ) (s : Finset ι) (omega : Ω) :
    typedSum X kind s omega+typedSum X kind (Finset.univ \ s) omega=typedSum X kind Finset.univ omega := by
  unfold typedSum
  exact Finset.sum_add_sum_compl s _

omit [Fintype Ω] [Fintype ι] in
theorem typedSum_erase (X : ι → Ω → Bool) (kind : ι → κ) {s : Finset ι} {i : ι}
    (hi : i ∈ s) (omega : Ω) :
    typedSum X kind s omega=(if X i omega=true then Pi.single (kind i) 1 else 0)+typedSum X kind (s.erase i) omega := by
  unfold typedSum
  exact (Finset.add_sum_erase _ _ hi).symm

omit [Fintype Ω] in
theorem typedSum_erased_partition (X : ι → Ω → Bool) (kind : ι → κ) (G : SimpleGraph ι)
    (i : ι) (omega : Ω) :
    typedSum X kind (Finset.univ.erase i) omega =
      typedSum X kind ((closedNeighborhood G i).erase i) omega+
        typedSum X kind (Finset.univ \ closedNeighborhood G i) omega := by
  have h := typedSum_partition X kind (closedNeighborhood G i) omega
  rw [typedSum_erase X kind (self_mem_closedNeighborhood G i) omega,
    typedSum_erase X kind (Finset.mem_univ i) omega,add_assoc] at h
  exact (add_left_cancel h).symm

omit [Fintype Ω] [Fintype ι] [DecidableEq ι] in
/-- Telescoping along actual active categories, preserving their separate costs. -/
theorem typedSum_difference_le (X : ι → Ω → Bool) (kind : ι → κ) (s : Finset ι)
    (f : (κ → ℕ) → ℝ) (weight : κ → ℝ)
    (hstep : ∀ z j, |f (addPoint z j)-f z|≤weight j) (v : κ → ℕ) (omega : Ω) :
    |f (v+typedSum X kind s omega)-f v|≤∑ j ∈ s, if X j omega=true then weight (kind j) else 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [typedSum]
  | @insert j s hj ih =>
    simp only [typedSum,Finset.sum_insert hj] at ih ⊢
    by_cases hx : X j omega=true
    · simp only [hx,if_true]
      have h := hstep (v+∑ i ∈ s, if X i omega=true then Pi.single (kind i) 1 else 0) (kind j)
      have heq : v+(Pi.single (kind j) 1+∑ i ∈ s, if X i omega=true then Pi.single (kind i) 1 else 0)=
          addPoint (v+∑ i ∈ s, if X i omega=true then Pi.single (kind i) 1 else 0) (kind j) := by
        unfold addPoint
        ac_rfl
      rw [heq]
      exact (abs_sub_le _ _ _).trans (add_le_add h ih)
    · simpa [hx] using ih

/-- The complete outside vector, rather than just its total, is independent of the local bit. -/
theorem expectation_indicator_typed_outside (mu : FinitePMF Ω) (X : ι → Ω → Bool)
    (kind : ι → κ) (G : SimpleGraph ι) (hdep : HasExactDependencyGraph mu X G)
    (i : ι) (f : (κ → ℕ) → ℝ) (v : κ → ℕ) :
    finitePMFExpectation mu (fun omega => (if X i omega=true then (1 : ℝ) else 0)*
      f (v+typedSum X kind (Finset.univ \ closedNeighborhood G i) omega)) =
      marginal mu X i * finitePMFExpectation mu
        (fun omega => f (v+typedSum X kind (Finset.univ \ closedNeighborhood G i) omega)) := by
  classical
  letI : Finite (OutsideIndex G i) := Finite.of_injective Subtype.val Subtype.coe_injective
  letI : Fintype (OutsideIndex G i) := Fintype.ofFinite _
  let phi : (OutsideIndex G i → Bool) → ℝ := fun pattern =>
    f (v+∑ j : OutsideIndex G i, if pattern j=true then Pi.single (kind j.val) 1 else 0)
  have hv (omega : Ω) : phi (outsideVector X G i omega)=
      f (v+typedSum X kind (Finset.univ \ closedNeighborhood G i) omega) := by
    dsimp [phi,outsideVector,typedSum]
    congr 2
    exact (Finset.sum_subtype (Finset.univ \ closedNeighborhood G i)
      (fun j => by simp) (fun j => if X j omega=true then Pi.single (kind j) 1 else 0)).symm
  have hh := finitePMFExpectation_mul_of_hasExactDependencyGraph mu X G hdep i
    (fun b => if b=true then (1 : ℝ) else 0) phi
  simp_rw [hv] at hh
  rw [expectation_indicator_eq_marginal] at hh
  exact hh

omit [Fintype ι] [DecidableEq ι] in
/-- The expected weighted active sum is the sum of the true weighted marginals. -/
theorem expectation_weighted_bits (mu : FinitePMF Ω) (X : ι → Ω → Bool)
    (s : Finset ι) (w : ι → ℝ) :
    finitePMFExpectation mu (fun omega =>∑ j ∈ s, if X j omega=true then w j else 0) =
      ∑ j ∈ s, w j*marginal mu X j := by
  rw [expectation_finset_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have heq : (fun omega => if X j omega=true then w j else 0)=
      (fun omega => w j*(if X j omega=true then (1 : ℝ) else 0)) := by
    funext omega
    split_ifs <;> ring
  rw [heq,expectation_const_mul,expectation_indicator_eq_marginal]

omit [Fintype ι] [DecidableEq ι] in
theorem expectation_indicator_weighted_bits (mu : FinitePMF Ω) (X : ι → Ω → Bool)
    (i : ι) (s : Finset ι) (w : ι → ℝ) :
    finitePMFExpectation mu (fun omega => (if X i omega=true then (1 : ℝ) else 0)*
      ∑ j ∈ s, if X j omega=true then w j else 0) =
      ∑ j ∈ s, w j*jointMarginal mu X i j := by
  simp_rw [Finset.mul_sum]
  rw [expectation_finset_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have heq : (fun omega => (if X i omega=true then (1 : ℝ) else 0)*(if X j omega=true then w j else 0))=
      (fun omega => w j*((if X i omega=true then (1 : ℝ) else 0)*(if X j omega=true then (1 : ℝ) else 0))) := by
    funext omega
    split_ifs <;> ring
  rw [heq,expectation_const_mul,expectation_indicator_mul]

/-- A single retained indicator is compared with its complete outside category vector. -/
theorem local_typed_stein_error_le (mu : FinitePMF Ω) (X : ι → Ω → Bool) (kind : ι → κ)
    (G : SimpleGraph ι) (hdep : HasExactDependencyGraph mu X G) (i : ι)
    (f : (κ → ℕ) → ℝ) (weight : κ → ℝ)
    (hstep : ∀ z j, |f (addPoint z j)-f z|≤weight j) (v : κ → ℕ) :
    |marginal mu X i * finitePMFExpectation mu (fun omega => f (v+typedSum X kind Finset.univ omega)) -
      finitePMFExpectation mu (fun omega => (if X i omega=true then (1 : ℝ) else 0)*
        f (v+typedSum X kind (Finset.univ.erase i) omega))| ≤
      marginal mu X i*(∑ j ∈ closedNeighborhood G i, weight (kind j)*marginal mu X j)+
        ∑ j ∈ (closedNeighborhood G i).erase i, weight (kind j)*jointMarginal mu X i j := by
  classical
  let bit : Ω → ℝ := fun omega => if X i omega=true then 1 else 0
  let V : Ω → κ → ℕ := fun omega => v+typedSum X kind (Finset.univ \ closedNeighborhood G i) omega
  let W : Ω → κ → ℕ := fun omega => v+typedSum X kind Finset.univ omega
  let U : Ω → κ → ℕ := fun omega => v+typedSum X kind (Finset.univ.erase i) omega
  have hp : 0≤marginal mu X i := marginal_nonneg mu X i
  have hbit (omega : Ω) : 0≤bit omega := by dsimp [bit];split_ifs <;> norm_num
  have hfirst : |finitePMFExpectation mu (fun omega => f (W omega)-f (V omega))|≤
      ∑ j ∈ closedNeighborhood G i, weight (kind j)*marginal mu X j := by
    apply (abs_expectation_le mu _).trans
    rw [← expectation_weighted_bits mu X (closedNeighborhood G i) (fun j => weight (kind j))]
    apply expectation_mono
    intro omega
    have heq : W omega=V omega+typedSum X kind (closedNeighborhood G i) omega := by
      dsimp [W,V]
      rw [← typedSum_partition X kind (closedNeighborhood G i) omega]
      ac_rfl
    rw [heq]
    exact typedSum_difference_le X kind (closedNeighborhood G i) f weight hstep (V omega) omega
  have hsecond : |finitePMFExpectation mu (fun omega => bit omega*(f (V omega)-f (U omega)))|≤
      ∑ j ∈ (closedNeighborhood G i).erase i, weight (kind j)*jointMarginal mu X i j := by
    apply (abs_expectation_le mu _).trans
    rw [← expectation_indicator_weighted_bits mu X i ((closedNeighborhood G i).erase i) (fun j => weight (kind j))]
    apply expectation_mono
    intro omega
    rw [abs_mul,abs_of_nonneg (hbit omega),abs_sub_comm]
    have heq : U omega=V omega+typedSum X kind ((closedNeighborhood G i).erase i) omega := by
      dsimp [U,V]
      rw [typedSum_erased_partition X kind G i omega]
      ac_rfl
    rw [heq]
    exact mul_le_mul_of_nonneg_left
      (typedSum_difference_le X kind ((closedNeighborhood G i).erase i) f weight hstep (V omega) omega)
      (hbit omega)
  have hfactor := expectation_indicator_typed_outside mu X kind G hdep i f v
  have heq : marginal mu X i*finitePMFExpectation mu (fun omega => f (W omega))-
      finitePMFExpectation mu (fun omega => bit omega*f (U omega)) =
      marginal mu X i*finitePMFExpectation mu (fun omega => f (W omega)-f (V omega))+
        finitePMFExpectation mu (fun omega => bit omega*(f (V omega)-f (U omega))) := by
    rw [expectation_sub]
    simp_rw [mul_sub]
    rw [expectation_sub]
    change _ = _ + (finitePMFExpectation mu (fun omega =>
      (if X i omega=true then (1 : ℝ) else 0)*
      f (v+typedSum X kind (Finset.univ \ closedNeighborhood G i) omega))-_)
    rw [hfactor]
    dsimp [V]
    ring
  change |marginal mu X i*finitePMFExpectation mu (fun omega => f (W omega))-
    finitePMFExpectation mu (fun omega => bit omega*f (U omega))|≤_
  rw [heq]
  have hh := abs_add_le (marginal mu X i*finitePMFExpectation mu (fun omega => f (W omega)-f (V omega)))
    (finitePMFExpectation mu (fun omega => bit omega*(f (V omega)-f (U omega))))
  rw [abs_mul,abs_of_nonneg hp] at hh
  have hm := mul_le_mul_of_nonneg_left hfirst hp
  linarith

/-- The complete finite graph error, uniformly in the fixed outside filling vector. -/
theorem typed_stein_error_le (mu : FinitePMF Ω) (X : ι → Ω → Bool) (kind : ι → κ)
    (G : SimpleGraph ι) (hdep : HasExactDependencyGraph mu X G)
    (f : κ → (κ → ℕ) → ℝ) (weight : κ → κ → ℝ)
    (hstep : ∀ i z j, |f i (addPoint z j)-f i z|≤weight i j) (v : κ → ℕ) :
    |∑ i, (marginal mu X i*finitePMFExpectation mu
      (fun omega => f (kind i) (v+typedSum X kind Finset.univ omega))-
      finitePMFExpectation mu (fun omega => (if X i omega=true then (1 : ℝ) else 0)*
        f (kind i) (v+typedSum X kind (Finset.univ.erase i) omega)))|≤typedCost mu X kind G weight := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  have h := Finset.sum_le_sum (fun i (_hi : i ∈ (Finset.univ : Finset ι)) =>
    local_typed_stein_error_le mu X kind G hdep i (f (kind i)) (weight (kind i)) (hstep (kind i)) v)
  apply h.trans_eq
  unfold typedCost typedBOne typedBTwo
  simp only [Finset.sum_add_distrib,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

end
end PaperC.V282.DirectionalSteinComparison
