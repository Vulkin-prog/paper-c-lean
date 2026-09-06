import PaperC.Probability.MarkedDetruncation
import PaperC.Probability.MarkedLocalGeometry

/-!
# Constant windows and their exact-run clusters

All windows are counted, without a left-maximality condition. The weighted
exact-run count agrees outside the two endpoint-window events. The proof is
deterministic: absence of the right endpoint window supplies the needed
finite right endpoint of every relevant run.
-/

namespace PaperC.V282.ConstantWindowClusters

open ExactLengthDecomposition MixedLengthAffine MarkedLocalGeometry
open SectionTwelveMoments
open scoped BigOperators

noncomputable section

@[reducible]
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

/-- A genuine constant length-L window starting at t. -/
def ConstantWindow (g : ℕ → F₂) (t L : ℕ) : Prop :=
  ∀ j : ℕ, j < L → g (t+j)=g t

/-- All constant windows with left endpoint in the dyadic block. -/
def constantWindowCount (g : ℕ → F₂) (N L : ℕ) : ℕ :=
  ∑ t ∈ dyadicBlock N, if ConstantWindow g t L then 1 else 0

/-- Windows contributed by all exact runs whose starts lie in the dyadic block. -/
def exactClusterCount (g : ℕ → F₂) (N L : ℕ) : ℕ :=
  ∑ x ∈ dyadicBlock N, ∑' e : ℕ,
    if ExactLengthEvent g x (excessRowCount L e) then e+1 else 0

/-- The windows inside this block assigned to a specified exact-run start. -/
def clusterWindows (g : ℕ → F₂) (N L x : ℕ) : Finset ℕ :=
  (dyadicBlock N).filter (fun t => ∃ e : ℕ,
    ExactLengthEvent g x (excessRowCount L e) ∧ x ≤ t ∧ t ≤ x+e)

theorem exact_constantWindow {g : ℕ → F₂} {x L e t : ℕ}
    (he : ExactLengthEvent g x (excessRowCount L e)) (hxt : x ≤ t) (hte : t ≤ x+e) :
    ConstantWindow g t L := by
  have hs : StartEvent g x (L+e) := exactLengthEvent_start (e := 0)
    (by simpa only [excessRowCount,Nat.add_zero] using he)
  intro j hj
  exact hs.eq_of_mem_run (by omega) (by omega) (by omega) (by omega)

/-- An absent later window forces a change somewhere after every earlier site. -/
theorem tailChangesAt_of_not_constantWindow {g : ℕ → F₂} {x r L : ℕ}
    (hxr : x ≤ r) (hr : ¬ConstantWindow g r L) : TailChangesAt g x := by
  by_contra hn
  apply hr
  have hsame : ∀ n : ℕ, x ≤ n → g n=g x := by
    intro n hxn
    by_contra hne
    exact hn ⟨n,hxn,hne⟩
  intro j hj
  exact (hsame (r+j) (by omega)).trans (hsame r hxr).symm

/-- Each interior window has an actual left-maximal start inside the block. -/
theorem exists_exact_cluster_of_constantWindow {g : ℕ → F₂} {N L t : ℕ}
    (hN : 1 ≤ N) (ht : t ∈ dyadicBlock N)
    (hw : ConstantWindow g t L)
    (hleft : ¬ConstantWindow g N L) (hright : ¬ConstantWindow g (2*N-1) L) :
    ∃ x ∈ dyadicBlock N, ∃ e : ℕ,
      ExactLengthEvent g x (excessRowCount L e) ∧ x ≤ t ∧ t ≤ x+e := by
  obtain ⟨hNt,htN⟩ := Finset.mem_Ico.mp ht
  let P : ℕ → Prop := fun x => N ≤ x ∧ x ≤ t ∧
    ∀ n : ℕ, x ≤ n → n < t+L → g n=g t
  have hp : ∃ x, P x := by
    refine ⟨t,hNt,le_rfl,?_⟩
    intro n htn hn
    simpa only [Nat.add_sub_of_le htn] using hw (n-t) (by omega)
  let x := Nat.find hp
  have hx : P x := Nat.find_spec hp
  have hxN : N < x := by
    have hge := hx.1
    by_contra hnot
    have heq : x=N := by omega
    apply hleft
    intro j hj
    have h1 := hx.2.2 (N+j) (by omega) (by omega)
    have h0 := hx.2.2 N (by omega) (by omega)
    exact h1.trans h0.symm
  have hxvalue : g x=g t := hx.2.2 x le_rfl (by
    have htL : 0 < L := by
      by_contra hz
      apply hleft
      intro j hj
      omega
    omega)
  have hchange : g (x-1) ≠ g x := by
    intro heq
    have hprev : P (x-1) := by
      refine ⟨by omega,by omega,?_⟩
      intro n hn hnt
      by_cases he : n=x-1
      · subst n
        exact heq.trans hxvalue
      · exact hx.2.2 n (by omega) hnt
    exact Nat.find_min hp (show x-1<x by omega) hprev
  have hs : StartEvent g x (L+(t-x)) := by
    refine ⟨(add_eq_one_iff_ne _ _).mpr hchange,?_⟩
    intro j hj
    exact (hx.2.2 (x+j) (by omega) (by omega)).trans hxvalue.symm
  have htail := tailChangesAt_of_not_constantWindow (x := x) (by omega) hright
  obtain ⟨f,hf⟩ := exists_exactLengthEvent_of_start_of_tailChangesAt hs htail
  refine ⟨x,Finset.mem_Ico.mpr ⟨hx.1,by omega⟩,(t-x)+f,?_,hx.2.1,by omega⟩
  simpa only [excessRowCount,Nat.add_assoc] using hf

/-- Two distinct left-maximal runs cannot own the same window. -/
theorem disjoint_clusterWindows {g : ℕ → F₂} {N L x y : ℕ}
    (hL : 1 ≤ L) (hxy : x ≠ y) :
    Disjoint (clusterWindows g N L x) (clusterWindows g N L y) := by
  apply Finset.disjoint_left.mpr
  intro t ht ht'
  obtain ⟨_,e,he,hxt,hte⟩ := Finset.mem_filter.mp ht
  obtain ⟨_,f,hf,hyt,htf⟩ := Finset.mem_filter.mp ht'
  rcases lt_or_gt_of_ne hxy with hxy | hyx
  · exact exactLengthEvents_excess_incompatible_of_left_overlap hxy (by omega) he hf
  · exact exactLengthEvents_excess_incompatible_of_left_overlap hyx (by omega) hf he

/-- The right endpoint event detects every cluster reaching outside the block. -/
theorem cluster_end_before_right {g : ℕ → F₂} {N L x e : ℕ}
    (hx : x ∈ dyadicBlock N)
    (he : ExactLengthEvent g x (excessRowCount L e))
    (hright : ¬ConstantWindow g (2*N-1) L) : x+e < 2*N-1 := by
  have hxb := Finset.mem_Ico.mp hx
  by_contra hn
  exact hright (exact_constantWindow he (by omega) (by omega))

/-- Each exact run contributes precisely e+1 windows when the right boundary is absent. -/
theorem clusterWindows_eq_Icc {g : ℕ → F₂} {N L x e : ℕ}
    (hL : 1 ≤ L) (hx : x ∈ dyadicBlock N)
    (he : ExactLengthEvent g x (excessRowCount L e))
    (hright : ¬ConstantWindow g (2*N-1) L) :
    clusterWindows g N L x = Finset.Icc x (x+e) := by
  have hend := cluster_end_before_right hx he hright
  have hxb := Finset.mem_Ico.mp hx
  ext t
  simp only [clusterWindows,Finset.mem_filter,Finset.mem_Icc]
  constructor
  · rintro ⟨_,f,hf,hxt,htf⟩
    have hfe := exactLengthEvent_excess_unique hL hf he
    subst f
    exact ⟨hxt,htf⟩
  · rintro ⟨hxt,hte⟩
    exact ⟨Finset.mem_Ico.mpr ⟨by omega,by omega⟩,e,he,hxt,hte⟩

/-- The weighted infinite mark sum is finite and equals the cluster's cardinality. -/
theorem card_clusterWindows_eq_weight {g : ℕ → F₂} {N L x : ℕ}
    (hL : 1 ≤ L) (hx : x ∈ dyadicBlock N)
    (hright : ¬ConstantWindow g (2*N-1) L) :
    (clusterWindows g N L x).card =
      ∑' e : ℕ, if ExactLengthEvent g x (excessRowCount L e) then e+1 else 0 := by
  by_cases h : ∃ e, ExactLengthEvent g x (excessRowCount L e)
  · obtain ⟨e,he⟩ := h
    rw [clusterWindows_eq_Icc hL hx he hright]
    rw [tsum_eq_single e]
    · simp only [Nat.card_Icc,if_pos he]
      omega
    · intro f hfe
      exact if_neg (fun hf => hfe (exactLengthEvent_excess_unique hL hf he))
  · have hempty : clusterWindows g N L x = ∅ := by
      ext t
      simp only [clusterWindows,Finset.mem_filter,Finset.notMem_empty,iff_false,not_and]
      intro ht hf
      exact h ⟨hf.choose,hf.choose_spec.1⟩
    rw [hempty,Finset.card_empty]
    have hz : ∀ e : ℕ, (if ExactLengthEvent g x (excessRowCount L e) then e+1 else 0)=0 :=
      fun e => if_neg (fun he => h ⟨e,he⟩)
    simp only [hz,tsum_zero]

/-- Every counted window belongs to exactly one actual run, except at the two boundaries. -/
theorem constantWindowCount_eq_exactClusterCount {g : ℕ → F₂} {N L : ℕ}
    (hN : 1 ≤ N) (hL : 1 ≤ L)
    (hleft : ¬ConstantWindow g N L) (hright : ¬ConstantWindow g (2*N-1) L) :
    constantWindowCount g N L = exactClusterCount g N L := by
  have hset : (dyadicBlock N).filter (fun t => ConstantWindow g t L) =
      (dyadicBlock N).biUnion (clusterWindows g N L) := by
    ext t
    simp only [Finset.mem_filter,Finset.mem_biUnion]
    constructor
    · rintro ⟨ht,hw⟩
      obtain ⟨x,hx,e,he,hxt,hte⟩ := exists_exact_cluster_of_constantWindow hN ht hw hleft hright
      exact ⟨x,hx,Finset.mem_filter.mpr ⟨ht,e,he,hxt,hte⟩⟩
    · rintro ⟨x,hx,ht⟩
      obtain ⟨ht,e,he,hxt,hte⟩ := Finset.mem_filter.mp ht
      exact ⟨ht,exact_constantWindow he hxt hte⟩
  unfold constantWindowCount exactClusterCount
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const,smul_eq_mul,mul_one]
  rw [hset,Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro x hx
    exact card_clusterWindows_eq_weight hL hx hright
  · intro x hx y hy hxy
    exact disjoint_clusterWindows hL hxy

end
end PaperC.V282.ConstantWindowClusters
