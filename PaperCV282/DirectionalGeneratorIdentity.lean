import PaperCV282.DirectionalSteinComparison
import PaperCV282.PoissonFillingIdentity

/-!
# Exact generator identity with independent Poisson filling

This is a pointwise identity on natural configurations, including empty
retained populations and boundary coordinates. It assumes no property of
the test solution and no probability law.
-/
namespace PaperC.V282.DirectionalGeneratorIdentity

open DirectionalSteinInput DirectionalSteinComparison PoissonFillingIdentity
open scoped BigOperators NNReal

noncomputable section

variable {Ω ι κ : Type*} [DecidableEq κ]

theorem addPoint_eq_increment (z : κ → ℕ) (i : κ) : addPoint z i=increment i z := by
  ext j
  by_cases h : j=i <;> simp [addPoint,increment,h]

theorem removePoint_eq_decrement (z : κ → ℕ) (i : κ) : removePoint z i=decrement i z := by
  ext j
  by_cases h : j=i <;> simp [removePoint,decrement,h]

theorem addPoint_decrement_add (z v : κ → ℕ) (i : κ) (hi : 0<z i) :
    addPoint (decrement i z+v) i=z+v := by
  ext j
  by_cases h : j=i
  · subst j
    simp only [addPoint,Pi.add_apply,Pi.single_eq_same,decrement,Function.update_self]
    omega
  · simp [addPoint,decrement,h]

theorem removePoint_add_left (z v : κ → ℕ) (i : κ) (hi : 0<z i) :
    removePoint (z+v) i=decrement i z+v := by
  ext j
  by_cases h : j=i
  · subst j
    simp only [removePoint,Pi.sub_apply,Pi.add_apply,Pi.single_eq_same,decrement,Function.update_self]
    omega
  · simp [removePoint,decrement,h]

/-- The filled-coordinate death term has its true predecessor, even at zero. -/
theorem filling_death_term (g : (κ → ℕ) → ℝ) (z v : κ → ℕ) (i : κ) :
    (z i : ℝ)*(g (removePoint (z+v) i)-g (z+v))=
      -(z i : ℝ)*firstDifference g i (decrement i z+v) := by
  by_cases hi : z i=0
  · simp [hi]
  · have hp : 0<z i := Nat.pos_of_ne_zero hi
    rw [firstDifference,removePoint_add_left z v i hp,addPoint_decrement_add z v i hp]
    ring

/-- Summing the category counts against an arbitrary function is summing the active labels. -/
theorem typedSum_weighted_duality [Fintype κ] (X : ι → Ω → Bool) (kind : ι → κ)
    (s : Finset ι) (omega : Ω) (f : κ → ℝ) :
    ∑ j, (typedSum X kind s omega j : ℝ)*f j =
      ∑ i ∈ s, if X i omega=true then f (kind i) else 0 := by
  classical
  unfold typedSum
  simp only [Finset.sum_apply,Nat.cast_sum]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : X i omega=true
  · simp [h,Pi.single_apply]
  · simp [h]

variable [Fintype ι] [DecidableEq ι]

theorem active_removed_configuration (X : ι → Ω → Bool) (kind : ι → κ)
    (omega : Ω) (i : ι) (hi : X i omega=true) (z : κ → ℕ) :
    removePoint (z+typedSum X kind Finset.univ omega) (kind i)=
      z+typedSum X kind (Finset.univ.erase i) omega := by
  classical
  rw [typedSum_erase X kind (Finset.mem_univ i) omega,if_pos hi]
  ext j
  by_cases h : j=kind i
  · subst j
    simp [removePoint]
    omega
  · simp [removePoint,h]

theorem active_added_configuration (X : ι → Ω → Bool) (kind : ι → κ)
    (omega : Ω) (i : ι) (hi : X i omega=true) (z : κ → ℕ) :
    addPoint (z+typedSum X kind (Finset.univ.erase i) omega) (kind i)=
      z+typedSum X kind Finset.univ omega := by
  classical
  rw [typedSum_erase X kind (Finset.mem_univ i) omega,if_pos hi]
  unfold addPoint
  ac_rfl

theorem active_death_sum [Fintype κ] (X : ι → Ω → Bool) (kind : ι → κ)
    (omega : Ω) (g : (κ → ℕ) → ℝ) (z : κ → ℕ) :
    (∑ j, (typedSum X kind Finset.univ omega j : ℝ)*
      (g (removePoint (z+typedSum X kind Finset.univ omega) j)-
        g (z+typedSum X kind Finset.univ omega))) =
    -(∑ i, (if X i omega=true then (1 : ℝ) else 0)*
      firstDifference g (kind i) (z+typedSum X kind (Finset.univ.erase i) omega)) := by
  classical
  rw [typedSum_weighted_duality,← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hx : X i omega=true
  · simp only [hx,if_true,one_mul,firstDifference,
      active_removed_configuration X kind omega i hx z,active_added_configuration X kind omega i hx z]
    ring
  · simp [hx]

/-- Exact immigration, filling death, and retained-label death decomposition. -/
theorem filled_steinGenerator_eq [Fintype κ] (t : κ → ℝ≥0) (g : (κ → ℕ) → ℝ)
    (X : ι → Ω → Bool) (kind : ι → κ) (omega : Ω) (z : κ → ℕ) :
    steinGenerator t g (z+typedSum X kind Finset.univ omega)=
      (∑ j, (t j : ℝ)*firstDifference g j (z+typedSum X kind Finset.univ omega))-
      (∑ j, (z j : ℝ)*firstDifference g j (decrement j z+typedSum X kind Finset.univ omega))-
      (∑ i, (if X i omega=true then (1 : ℝ) else 0)*
        firstDifference g (kind i) (z+typedSum X kind (Finset.univ.erase i) omega)) := by
  classical
  unfold steinGenerator
  simp only [Pi.add_apply,Nat.cast_add,add_mul,Finset.sum_add_distrib]
  simp_rw [filling_death_term,neg_mul]
  rw [Finset.sum_neg_distrib,active_death_sum]
  ring

end
end PaperC.V282.DirectionalGeneratorIdentity
