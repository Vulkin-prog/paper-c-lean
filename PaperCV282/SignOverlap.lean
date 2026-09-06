import PaperCV282.SignDictionary
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Compatible shifts up to a common sign

The common multiplicative sign is the additive bit in the binary encoding.
Every compatible proper shift contributes exactly two ordered sign choices.
-/

namespace PaperC.V282.SignOverlap

open SignDictionary WordOverlap WordOverlapSum Filter
open scoped BigOperators Topology

noncomputable section

/-- Compatibility after allowing a single common sign on the second word. -/
def CompatibleUpToSign {B : ℕ} (d : ℕ) (a : Fin B → F₂) : Prop :=
  Compatible d a a ∨ Compatible d a (oppositeWord a)

local instance instDecidableCompatibleUpToSign {B : ℕ} (d : ℕ) (a : Fin B → F₂) :
    Decidable (CompatibleUpToSign d a) := Classical.propDecidable _

/-- The genuine proper compatible shifts in equation (5.9). -/
def compatibleShifts {B : ℕ} (a : Fin B → F₂) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 (B-1)).filter (fun d => CompatibleUpToSign d a)

/-- Equation (5.9), including the empty set of proper shifts. -/
def theta {B : ℕ} (a : Fin B → F₂) : ℝ :=
  ∑ d ∈ compatibleShifts a, 1 / (2 : ℝ)^d

/-- The exceptional fallback B only applies when no proper shift is compatible. -/
def leastCompatibleShift {B : ℕ} (a : Fin B → F₂) : ℕ := by
  classical
  exact if h : (compatibleShifts a).Nonempty then (compatibleShifts a).min' h else B

theorem compatibleUpToSign_iff {B : ℕ} (d : ℕ) (a : Fin B → F₂) :
    CompatibleUpToSign d a ↔ ∃ e : F₂, ∀ j : Fin B, ∀ h : d+j.val < B,
      a ⟨d+j.val,h⟩ = e+a j := by
  constructor
  · rintro (h | h)
    · exact ⟨0,fun j hj => by simpa using h j hj⟩
    · exact ⟨1,h⟩
  · rintro ⟨e,h⟩
    have he : e=0 ∨ e=1 := by
      fin_cases e
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases he with rfl | rfl
    · exact Or.inl (fun j hj => by simpa using h j hj)
    · exact Or.inr h

theorem theta_nonneg {B : ℕ} (a : Fin B → F₂) : 0 ≤ theta a := by
  exact Finset.sum_nonneg fun d _ => by positivity

theorem directed_sign_pair_sum {B d : ℕ} (hd : d < B) (a : Fin B → F₂) :
    directedOverlapWeight d a a + directedOverlapWeight d a (oppositeWord a) =
      if CompatibleUpToSign d a then 1 / (2 : ℝ)^d else 0 := by
  classical
  have hn := not_compatible_both hd a
  unfold directedOverlapWeight CompatibleUpToSign
  split_ifs <;> simp_all

/-- The normalization by the two words cancels the two directed sign choices. -/
theorem overlapWeight_signDictionary {B : ℕ} (hB : 0 < B) (a : Fin B → F₂) :
    overlapWeight (signDictionary a) = theta a := by
  classical
  have hne := Ne.symm (oppositeWord_ne hB a)
  have hpp : ∀ d, directedOverlapWeight d (oppositeWord a) (oppositeWord a) =
      directedOverlapWeight d a a := by
    intro d
    simp only [directedOverlapWeight,compatible_opposites_iff]
  have hmp : ∀ d, directedOverlapWeight d (oppositeWord a) a =
      directedOverlapWeight d a (oppositeWord a) := by
    intro d
    simp only [directedOverlapWeight,compatible_opposite_left_iff]
  have hsum : (∑ d ∈ Finset.Icc 1 (B-1), directedOverlapWeight d a a) +
      (∑ d ∈ Finset.Icc 1 (B-1), directedOverlapWeight d a (oppositeWord a)) = theta a := by
    rw [← Finset.sum_add_distrib]
    unfold theta compatibleShifts
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d hd
    exact directed_sign_pair_sum (by have := Finset.mem_Icc.mp hd; omega) a
  unfold overlapWeight
  rw [card_signDictionary hB a]
  have hmem : a ∉ ({oppositeWord a} : Finset (Fin B → F₂)) := by simpa using hne
  simp only [signDictionary,Finset.sum_insert hmem,Finset.sum_singleton]
  simp_rw [hpp,hmp]
  norm_num only [Nat.cast_ofNat]
  linarith

/-- Any lower bound for the compatible shifts bounds the geometric tail. -/
theorem theta_le_geometric_tail {B : ℕ} (a : Fin B → F₂) (dstar : ℕ)
    (hstar : ∀ d ∈ compatibleShifts a, dstar ≤ d) :
    theta a ≤ 2 / (2 : ℝ)^dstar := by
  classical
  have hsub : compatibleShifts a ⊆ Finset.Ico dstar B := by
    intro d hd
    have hproper := (Finset.mem_filter.mp hd).1
    have := Finset.mem_Icc.mp hproper
    exact Finset.mem_Ico.mpr ⟨hstar d hd,by omega⟩
  have hsum : theta a ≤ ∑ d ∈ Finset.Ico dstar B, (1/(2 : ℝ))^d := by
    unfold theta
    simp only [one_div_pow]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
  have hgeom := geom_sum_Ico_le_of_lt_one (m := dstar) (n := B)
    (show (0 : ℝ) ≤ 1/2 by norm_num) (show (1 : ℝ)/2 < 1 by norm_num)
  have heq : ((1 : ℝ)/2)^dstar/(1-1/2) = 2/(2 : ℝ)^dstar := by
    simp only [div_pow,one_pow]
    ring
  exact hsum.trans (heq ▸ hgeom)

theorem theta_le_leastCompatibleShift {B : ℕ} (a : Fin B → F₂) :
    theta a ≤ 2 / (2 : ℝ)^(leastCompatibleShift a) := by
  classical
  apply theta_le_geometric_tail
  intro d hd
  have hn : (compatibleShifts a).Nonempty := ⟨d,hd⟩
  simp only [leastCompatibleShift,dif_pos hn]
  exact Finset.min'_le _ _ hd

/-- The one-letter terminal overlap always has a common sign. -/
theorem lastShift_compatible (L : ℕ) (a : Fin (L+1) → F₂) :
    CompatibleUpToSign L a := by
  apply (compatibleUpToSign_iff L a).mpr
  refine ⟨a ⟨L,by omega⟩ + a ⟨0,by omega⟩,?_⟩
  intro j hj
  rcases j with ⟨j,hjlt⟩
  have hj0 : j=0 := by change L+j<L+1 at hj; omega
  subst j
  simp only [add_zero,add_assoc,CharTwo.add_self_eq_zero]

/-- At length at least two, the minimum really is a member of the compatible shifts. -/
theorem leastCompatibleShift_mem {L : ℕ} (hL : 1 ≤ L) (a : Fin (L+1) → F₂) :
    leastCompatibleShift a ∈ compatibleShifts a := by
  classical
  have hn : (compatibleShifts a).Nonempty := by
    refine ⟨L,?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr (by omega),lastShift_compatible L a⟩
  simp only [leastCompatibleShift,dif_pos hn]
  exact Finset.min'_mem _ hn

/-- The manuscript's real-power notation for the same geometric tail. -/
theorem theta_le_two_rpow_leastCompatibleShift {B : ℕ} (a : Fin B → F₂) :
    theta a ≤ (2 : ℝ)^((1 : ℝ)-(leastCompatibleShift a : ℝ)) := by
  rw [Real.rpow_sub (by norm_num),Real.rpow_one,Real.rpow_natCast]
  exact theta_le_leastCompatibleShift a

/-- The precise convergence assertion following Corollary 5.5. -/
theorem theta_tendsto_zero_of_leastCompatibleShift
    (B : ℕ → ℕ) (a : ∀ n, Fin (B n) → F₂)
    (hshift : Tendsto (fun n => leastCompatibleShift (a n)) atTop atTop) :
    Tendsto (fun n => theta (a n)) atTop (𝓝 0) := by
  have hpow := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (show (0 : ℝ) ≤ 1/2 by norm_num) (show (1 : ℝ)/2 < 1 by norm_num)).comp hshift
  have hbound : Tendsto (fun n => 2/(2 : ℝ)^(leastCompatibleShift (a n))) atTop (𝓝 0) := by
    simpa only [Function.comp_def,mul_zero,div_pow,one_pow,mul_one_div] using hpow.const_mul 2
  exact squeeze_zero (fun n => theta_nonneg (a n))
    (fun n => theta_le_leastCompatibleShift (a n)) hbound

/-- The bit encoding of (-1,+1,...,+1). -/
def runStartWord (L : ℕ) : Fin (L+1) → F₂ := fun i => if i.val=0 then 1 else 0

theorem runStartWord_compatible_iff {L d : ℕ} (hdpos : 1 ≤ d) (hd : d ≤ L) :
    CompatibleUpToSign d (runStartWord L) ↔ d=L := by
  constructor
  · intro h
    obtain ⟨e,he⟩ := (compatibleUpToSign_iff d _).mp h
    by_contra hne
    have hdlt : d < L := by omega
    have h0 := he ⟨0,by omega⟩ (by simp only; omega)
    have h1 := he ⟨1,by omega⟩ (by simp only; omega)
    simp [runStartWord,show d≠0 by omega] at h0 h1
    have he0 : e=0 := h1.symm
    rw [he0,zero_add] at h0
    exact zero_ne_one h0
  · rintro rfl
    apply Or.inr
    intro j hj
    have hj0 : j.val=0 := by omega
    simp [runStartWord,oppositeWord,hj0,show d≠0 by omega,
      show (1 : F₂)+1=0 by decide]

theorem theta_runStartWord {L : ℕ} (hL : 1 ≤ L) :
    theta (runStartWord L) = 1/(2 : ℝ)^L := by
  classical
  have hset : compatibleShifts (runStartWord L) = {L} := by
    ext d
    simp only [compatibleShifts,Finset.mem_filter,Finset.mem_Icc,Finset.mem_singleton,
      Nat.add_sub_cancel]
    constructor
    · rintro ⟨⟨hdpos,hd⟩,hc⟩
      exact (runStartWord_compatible_iff hdpos hd).mp hc
    · rintro rfl
      exact ⟨⟨hL,le_rfl⟩,(runStartWord_compatible_iff hL le_rfl).mpr rfl⟩
  simp [theta,hset]

end
end PaperC.V282.SignOverlap
