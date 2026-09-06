import PaperCV282.WordOverlapSum

/-!
# A word and its opposite sign

Opposite signs are encoded by adding the bit one. They are not represented
by additive negation in F₂, which would leave each bit unchanged.
-/

namespace PaperC.V282.SignDictionary

open WordOverlap WordOverlapProbability InfiniteWordTransfer

noncomputable section

/-- Flip every actual sign by adding one to each binary bit. -/
def oppositeWord {B : ℕ} (a : Fin B → F₂) : Fin B → F₂ := fun i => 1+a i

/-- The actual two-word dictionary, with distinct words whenever B is positive. -/
def signDictionary {B : ℕ} (a : Fin B → F₂) : Finset (Fin B → F₂) := by
  classical
  exact {a,oppositeWord a}

theorem oppositeWord_oppositeWord {B : ℕ} (a : Fin B → F₂) :
    oppositeWord (oppositeWord a) = a := by
  funext i
  simp only [oppositeWord,← add_assoc,show (1 : F₂)+1=0 by decide,zero_add]

theorem oppositeWord_ne {B : ℕ} (hB : 0 < B) (a : Fin B → F₂) : oppositeWord a ≠ a := by
  intro heq
  have h := congrFun heq ⟨0,hB⟩
  change 1+a ⟨0,hB⟩ = a ⟨0,hB⟩ at h
  exact one_ne_zero (add_right_cancel (h.trans (zero_add _).symm))

theorem card_signDictionary {B : ℕ} (hB : 0 < B) (a : Fin B → F₂) :
    (signDictionary a).card = 2 := by
  classical
  simp [signDictionary,Ne.symm (oppositeWord_ne hB a)]

theorem signDictionary_nonempty {B : ℕ} (a : Fin B → F₂) : (signDictionary a).Nonempty := by
  classical
  simp [signDictionary]

theorem mem_signDictionary {B : ℕ} (a b : Fin B → F₂) :
    b ∈ signDictionary a ↔ b=a ∨ b=oppositeWord a := by
  classical
  simp [signDictionary]

/-- The two actual source events are disjoint. -/
theorem sign_events_disjoint {B : ℕ} (hB : 0 < B) (x : ℕ) (a : Fin B → F₂) :
    Disjoint (infiniteWordEvent x B a) (infiniteWordEvent x B (oppositeWord a)) :=
  infiniteWordEvent_disjoint_same_site x B a (oppositeWord a) (Ne.symm (oppositeWord_ne hB a))

/-- Flipping both words preserves directed compatibility. -/
theorem compatible_opposites_iff {B : ℕ} (d : ℕ) (a b : Fin B → F₂) :
    Compatible d (oppositeWord a) (oppositeWord b) ↔ Compatible d a b := by
  constructor <;> intro h j hj
  · exact add_left_cancel (h j hj)
  · exact congrArg (fun z : F₂ => 1+z) (h j hj)

/-- Flipping the first word is equivalent to flipping the second. -/
theorem compatible_opposite_left_iff {B : ℕ} (d : ℕ) (a b : Fin B → F₂) :
    Compatible d (oppositeWord a) b ↔ Compatible d a (oppositeWord b) := by
  simpa only [oppositeWord_oppositeWord] using
    (compatible_opposites_iff d a (oppositeWord b))

/-- On a nonempty overlap, its common sign is unique. -/
theorem not_compatible_both {B d : ℕ} (hd : d < B) (a : Fin B → F₂) :
    ¬ (Compatible d a a ∧ Compatible d a (oppositeWord a)) := by
  rintro ⟨hpos,hneg⟩
  have h0 : 0 < B := by omega
  have h1 := hpos ⟨0,h0⟩ (by simpa using hd)
  have h2 := hneg ⟨0,h0⟩ (by simpa using hd)
  have heq : 1+a ⟨0,h0⟩ = a ⟨0,h0⟩ := h2.symm.trans h1
  exact one_ne_zero (add_right_cancel (heq.trans (zero_add _).symm))

end
end PaperC.V282.SignDictionary
