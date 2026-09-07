import PaperCV282.SignedExactMarks

/-!
# The real value supports of signed exact marks

The shared value count is two at a common sign change, one at touching
boundaries, and zero after the two real supports separate.
-/
namespace PaperC.V282.ExactMarkedLocalGeometry

open ExactMarkedModel SignedExactMarks MixedLengthAffine MarkedLocalGeometry
open WindowValues WordOverlap

noncomputable section

/-- Actual marked support including both boundary values. -/
def markSupport (x L e : ℕ) : Finset ℕ := Finset.Icc (x-1) (x+(L+e))

/-- The prescribed absolute bit on the real support. -/
def markAssignment (x L e : ℕ) (s : F₂) (n : ℕ) : F₂ :=
  if n=x-1 ∨ n=x+(L+e) then 1+s else s

/-- Use the first prescription on the shared part of a support union. -/
def unionAssignment (x y L e f : ℕ) (s t : F₂) (n : ℕ) : F₂ :=
  if n ∈ markSupport x L e then markAssignment x L e s n else markAssignment y L f t n

def MarkCompatible (x y L e f : ℕ) (s t : F₂) : Prop :=
  ∀ n ∈ markSupport x L e ∩ markSupport y L f,
    markAssignment x L e s n = markAssignment y L f t n

theorem markAssignment_vertex {x L e : ℕ} (hx : 1 ≤ x) (s : F₂) (i : Fin (L+e+2)) :
    markAssignment x L e s (vertex x (L+e+2) i) = signedExactWord L e s i := by
  unfold markAssignment signedExactWord vertex
  congr 1
  apply propext
  have hi := i.isLt
  omega

theorem signedExactMark_iff_prescribed {g : ℕ → F₂} {x L e : ℕ}
    (hx : 1 ≤ x) (hL : 1 ≤ L) (s : F₂) :
    SignedExactMark g x L e s ↔ ∀ n ∈ markSupport x L e, g n = markAssignment x L e s n := by
  rw [signedExactMark_iff_occurs hx hL]
  constructor
  · intro hw n hn
    simp only [markSupport,Finset.mem_Icc] at hn
    let i : Fin (L+e+2) := ⟨n-(x-1),by omega⟩
    have hv : vertex x (L+e+2) i = n := by dsimp [vertex,i];omega
    rw [← hv,markAssignment_vertex hx]
    exact hw i
  · intro hw i
    rw [← markAssignment_vertex hx]
    apply hw
    simp only [markSupport,Finset.mem_Icc,vertex]
    have hi := i.isLt
    omega

theorem signed_pair_iff_union {g : ℕ → F₂} {x y L e f : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y) (hL : 1 ≤ L) (s t : F₂) :
    SignedExactMark g x L e s ∧ SignedExactMark g y L f t ↔
      MarkCompatible x y L e f s t ∧
      ∀ n ∈ markSupport x L e ∪ markSupport y L f, g n = unionAssignment x y L e f s t n := by
  rw [signedExactMark_iff_prescribed hx hL,signedExactMark_iff_prescribed hy hL]
  constructor
  · rintro ⟨hl,hr⟩
    constructor
    · intro n hn
      exact (hl n (Finset.mem_inter.mp hn).1).symm.trans (hr n (Finset.mem_inter.mp hn).2)
    · intro n hn
      by_cases hnx : n ∈ markSupport x L e
      · simpa [unionAssignment,hnx] using hl n hnx
      · simpa [unionAssignment,hnx] using hr n ((Finset.mem_union.mp hn).resolve_left hnx)
  · rintro ⟨hc,hu⟩
    constructor
    · intro n hn
      simpa [unionAssignment,hn] using hu n (Finset.mem_union_left _ hn)
    · intro n hn
      have hh := hu n (Finset.mem_union_right _ hn)
      by_cases hnx : n ∈ markSupport x L e
      · simpa only [unionAssignment,if_pos hnx,hc n (Finset.mem_inter.mpr ⟨hnx,hn⟩)] using hh
      · simpa [unionAssignment,hnx] using hh

theorem card_markSupport {x : ℕ} (hx : 1 ≤ x) (L e : ℕ) :
    (markSupport x L e).card = L+e+2 := by
  rw [markSupport,Nat.card_Icc]
  omega

theorem markSupport_inter_boundary {x L e f : ℕ} (hx : 1 ≤ x) (hL : 1 ≤ L) :
    markSupport x L e ∩ markSupport (x+(L+e)) L f = {x+(L+e)-1,x+(L+e)} := by
  ext n
  simp only [markSupport,Finset.mem_inter,Finset.mem_Icc,Finset.mem_insert,Finset.mem_singleton]
  omega

theorem markSupport_inter_touching {x L e f : ℕ} (hx : 1 ≤ x) (hL : 1 ≤ L) :
    markSupport x L e ∩ markSupport (x+(L+e+1)) L f = {x+(L+e)} := by
  ext n
  simp only [markSupport,Finset.mem_inter,Finset.mem_Icc,Finset.mem_singleton]
  omega

theorem markSupport_disjoint {x L e f d : ℕ} (hd : L+e+1 < d) :
    Disjoint (markSupport x L e) (markSupport (x+d) L f) := by
  rw [Finset.disjoint_left]
  intro n hn hm
  simp only [markSupport,Finset.mem_Icc] at hn hm
  omega

theorem card_markSupport_union_boundary {x L e f : ℕ} (hx : 1 ≤ x) (hL : 1 ≤ L) :
    (markSupport x L e ∪ markSupport (x+(L+e)) L f).card = (L+e)+(L+f)+2 := by
  have h := Finset.card_union_add_card_inter (markSupport x L e) (markSupport (x+(L+e)) L f)
  rw [card_markSupport hx,card_markSupport (by omega),markSupport_inter_boundary hx hL] at h
  have hn : x+(L+e)-1 ≠ x+(L+e) := by omega
  have hc : ({x+(L+e)-1,x+(L+e)} : Finset ℕ).card = 2 := by simp [hn]
  rw [hc] at h
  omega

theorem card_markSupport_union_touching {x L e f : ℕ} (hx : 1 ≤ x) (hL : 1 ≤ L) :
    (markSupport x L e ∪ markSupport (x+(L+e+1)) L f).card = (L+e)+(L+f)+3 := by
  have h := Finset.card_union_add_card_inter (markSupport x L e) (markSupport (x+(L+e+1)) L f)
  rw [card_markSupport hx,card_markSupport (by omega),markSupport_inter_touching hx hL,Finset.card_singleton] at h
  omega

theorem card_markSupport_union_separated {x L e f d : ℕ} (hx : 1 ≤ x) (hd : L+e+1 < d) :
    (markSupport x L e ∪ markSupport (x+d) L f).card = (L+e)+(L+f)+4 := by
  rw [Finset.card_union_of_disjoint (markSupport_disjoint hd),card_markSupport hx,card_markSupport (by omega)]
  omega

/-- Complementation in F2 is an involution. -/
theorem one_add_one_add (s : F₂) : 1+(1+s)=s := by revert s;decide

/-- At the shared two-value boundary, the following run has the opposite sign. -/
theorem markCompatible_boundary {x L e f : ℕ} (hx : 1 ≤ x) (hL : 1 ≤ L) (s t : F₂) :
    MarkCompatible x (x+(L+e)) L e f s t ↔ t=1+s := by
  rw [MarkCompatible,markSupport_inter_boundary hx hL]
  have hxa : x+(L+e) ≠ x-1 := by omega
  have hxp : x+(L+e)-1 ≠ x-1 := by omega
  have hpp : x+(L+e)-1 ≠ x+(L+e) := by omega
  have hyb : x+(L+e) ≠ x+(L+e)+(L+f) := by omega
  have hyp : x+(L+e)-1 ≠ x+(L+e)+(L+f) := by omega
  have heval : markAssignment x L e s (x+(L+e)) = 1+s ∧
      markAssignment (x+(L+e)) L f t (x+(L+e)) = t := by
    simp [markAssignment,hxa,Ne.symm hpp,show L ≠ 0 by omega]
  constructor
  · intro h
    have hh := h (x+(L+e)) (by simp)
    rw [heval.1,heval.2] at hh
    exact hh.symm
  · intro ht n hn
    rcases Finset.mem_insert.mp hn with rfl | hn
    · simp [markAssignment,hxp,hpp,hyp,ht,one_add_one_add]
    · have hn' : n=x+(L+e) := Finset.mem_singleton.mp hn
      subst n
      rw [heval.1,heval.2,ht]

/-- At the shared one-value boundary, the signs must agree. -/
theorem markCompatible_touching {x L e f : ℕ} (hx : 1 ≤ x) (hL : 1 ≤ L) (s t : F₂) :
    MarkCompatible x (x+(L+e+1)) L e f s t ↔ t=s := by
  rw [MarkCompatible,markSupport_inter_touching hx hL]
  have hp : x+(L+e+1)-1=x+(L+e) := by omega
  have heval : markAssignment x L e s (x+(L+e)) = 1+s ∧
      markAssignment (x+(L+e+1)) L f t (x+(L+e)) = 1+t := by simp [markAssignment,hp]
  simp only [Finset.mem_singleton,forall_eq,heval.1,heval.2]
  exact ⟨fun h => (add_left_cancel h).symm,fun h => by rw [h]⟩

theorem markCompatible_separated {x L e f d : ℕ} (hd : L+e+1 < d) (s t : F₂) :
    MarkCompatible x (x+d) L e f s t := by
  intro n hn
  exact False.elim (Finset.disjoint_left.mp (markSupport_disjoint hd)
    (Finset.mem_inter.mp hn).1 (Finset.mem_inter.mp hn).2)

end
end PaperC.V282.ExactMarkedLocalGeometry
