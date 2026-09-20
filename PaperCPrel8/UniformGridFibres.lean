import PaperCPrel8.RoughKernelAllocation

/-! # Exposing one coordinate of the actual uniform Cartesian grid -/
namespace PaperC.Prel8.UniformGridFibres
open Finset RoughKernelAllocation ArratiaGoldsteinGordonInput
noncomputable section
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- Exact probability on the independent uniform grid. -/
theorem probability_eq (n k : ℕ) (hn : 0<n) (P : (Fin k → ℕ) → Prop) :
    eventProbability (gridLaw n k hn) (fun J ↦ P J.val) =
      (((grid n k).filter P).card:ℝ)/(n:ℝ)^k := by
  let : Nonempty (grid n k) := ⟨⟨(fun _ ↦ 1),by simp [grid,Fintype.mem_piFinset]; omega⟩⟩
  change eventProbability (FinitePMF.uniform (grid n k)) _ = _
  rw [uniform_finset_probability (grid n k) P,grid_card,Nat.cast_pow]

/-- Deleting the exposed coordinate injects a fibre into the residual event. -/
theorem fibre_card_le (n h j : ℕ) (i : Fin (h+1))
    (P : (Fin (h+1) → ℕ) → Prop) (R : (Fin h → ℕ) → Prop)
    (hmap : ∀ J ∈ grid n (h+1), P J → J i=j → R (fun b ↦ J (i.succAbove b))) :
    (((grid n (h+1)).filter P).filter (fun J ↦ J i=j)).card ≤ ((grid n h).filter R).card := by
  apply card_le_card_of_injOn (fun J b ↦ J (i.succAbove b))
  · intro J hJ
    obtain ⟨hJ,hj⟩ := mem_filter.mp hJ
    obtain ⟨hg,hP⟩ := mem_filter.mp hJ
    apply mem_filter.mpr
    refine ⟨?_,hmap J hg hP hj⟩
    exact Fintype.mem_piFinset.mpr (fun b ↦ Fintype.mem_piFinset.mp hg (i.succAbove b))
  · intro J hJ K hK he
    have hj := (mem_filter.mp hJ).2
    have hk := (mem_filter.mp hK).2
    funext l
    by_cases hl : l=i
    · simpa only [hl] using hj.trans hk.symm
    · obtain ⟨b,rfl⟩ := Fin.exists_succAbove_eq hl
      exact congrFun he b

/-- A uniform conditional bound on every exposed fibre bounds the whole event. -/
theorem probability_le_of_fibres (n h : ℕ) (hn : 0<n) (i : Fin (h+1))
    (P : (Fin (h+1) → ℕ) → Prop) (R : ℕ → (Fin h → ℕ) → Prop) (B : ℝ)
    (hmap : ∀ j ∈ Icc 1 n, ∀ J ∈ grid n (h+1), P J → J i=j → R j (fun b ↦ J (i.succAbove b)))
    (hbound : ∀ j ∈ Icc 1 n, (((grid n h).filter (R j)).card:ℝ) ≤ (n:ℝ)^h*B) :
    eventProbability (gridLaw n (h+1) hn) (fun J ↦ P J.val) ≤ B := by
  have he : ((grid n (h+1)).filter P).card =
      ∑ j ∈ Icc 1 n, (((grid n (h+1)).filter P).filter (fun J ↦ J i=j)).card := by
    apply card_eq_sum_card_fiberwise
    intro J hJ
    exact Fintype.mem_piFinset.mp (mem_filter.mp hJ).1 i
  rw [probability_eq]
  apply (div_le_iff₀ (pow_pos (by exact_mod_cast hn : (0:ℝ)<n) _)).mpr
  rw [he,Nat.cast_sum]
  calc
    _ ≤ ∑ j ∈ Icc 1 n, (n:ℝ)^h*B := by
      apply sum_le_sum
      intro j hj
      have hc := fibre_card_le n h j i P (R j) (hmap j hj)
      exact (by exact_mod_cast hc : _ ≤ (((grid n h).filter (R j)).card:ℝ)).trans (hbound j hj)
    _ = _ := by simp [Nat.card_Icc,pow_succ]; ring

/-- Nonconstant fibre bounds retain their average over the exposed source index. -/
theorem probability_le_of_fibres_average (n h : ℕ) (hn : 0<n) (i : Fin (h+1))
    (P : (Fin (h+1) → ℕ) → Prop) (R : ℕ → (Fin h → ℕ) → Prop) (B : ℕ → ℝ)
    (hmap : ∀ j ∈ Icc 1 n, ∀ J ∈ grid n (h+1), P J → J i=j → R j (fun b ↦ J (i.succAbove b)))
    (hbound : ∀ j ∈ Icc 1 n, (((grid n h).filter (R j)).card:ℝ) ≤ (n:ℝ)^h*B j) :
    eventProbability (gridLaw n (h+1) hn) (fun J ↦ P J.val) ≤ (∑ j ∈ Icc 1 n, B j)/n := by
  have he : ((grid n (h+1)).filter P).card =
      ∑ j ∈ Icc 1 n, (((grid n (h+1)).filter P).filter (fun J ↦ J i=j)).card := by
    apply card_eq_sum_card_fiberwise
    intro J hJ
    exact Fintype.mem_piFinset.mp (mem_filter.mp hJ).1 i
  rw [probability_eq]
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  apply (div_le_iff₀ (pow_pos hn' _)).mpr
  rw [he,Nat.cast_sum]
  calc
    _ ≤ ∑ j ∈ Icc 1 n, (n:ℝ)^h*B j := by
      apply sum_le_sum
      intro j hj
      have hc := fibre_card_le n h j i P (R j) (hmap j hj)
      exact (by exact_mod_cast hc : _ ≤ (((grid n h).filter (R j)).card:ℝ)).trans (hbound j hj)
    _ = _ := by rw [← mul_sum,pow_succ]; field_simp

/-- One uniform coordinate hits a deleted set with probability at most its grid fraction. -/
theorem coordinate_deleted_le (n h : ℕ) (hn : 0<n) (i : Fin (h+1)) (G : Finset ℕ) :
    eventProbability (gridLaw n (h+1) hn) (fun J ↦ J.val i ∉ G) ≤
      (((Icc 1 n) \ G).card:ℝ)/n := by
  have hbound := probability_le_of_fibres_average n h hn i (fun J ↦ J i ∉ G)
    (fun j _ ↦ j ∉ G) (fun j ↦ if j ∉ G then (1:ℝ) else 0)
    (fun _ _ _ _ h hj ↦ by simpa only [← hj] using h)
    (fun j _ ↦ by by_cases hj : j ∈ G <;> simp [hj,grid_card])
  apply hbound.trans_eq
  congr 1
  rw [← sum_filter]
  simp only [sum_const,nsmul_eq_mul,mul_one]
  congr 2
  ext j
  simp

end
end PaperC.Prel8.UniformGridFibres
