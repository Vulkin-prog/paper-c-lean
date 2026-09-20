import PaperC.Probability.MarkedLocalGeometry
import PaperCV282.DictionaryFieldModel

/-!
# Exact marked source events with a freely chosen prime cylinder

The excess e has q=L+e+1 relative equations and q+1 actual values.
The signed label is the value at x. All labels remain in the fields.
-/
namespace PaperC.V282.ExactMarkedModel

open MixedLengthAffine ExactLengthDecomposition SectionTwelveMoments
open ConditionalStartProbability ArratiaGoldsteinGordonInput
open scoped BigOperators NNReal

noncomputable section

@[reducible]
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

@[reducible]
def ExactMarkIndex (N E : ℕ) := {x : ℕ // x ∈ dyadicBlock N} × Fin (E+1)

@[reducible]
def SignedMarkIndex (N E : ℕ) := {x : ℕ // x ∈ dyadicBlock N} × (Fin (E+1) × F₂)

/-- The sign is read at the first site of the run, not at its left boundary. -/
def SignedExactMark (g : ℕ → F₂) (x L e : ℕ) (s : F₂) : Prop :=
  ExactLengthEvent g x (excessRowCount L e) ∧ g x = s

def exactMarkValue (g : ℕ → F₂) (x L e : ℕ) : ℕ :=
  if ExactLengthEvent g x (excessRowCount L e) then 1 else 0

def signedMarkValue (g : ℕ → F₂) (x L e : ℕ) (s : F₂) : ℕ :=
  if SignedExactMark g x L e s then 1 else 0

def baseStartValue (g : ℕ → F₂) (x L : ℕ) : ℕ := if StartEvent g x L then 1 else 0

def exactMarkedIndicator (C N L E : ℕ) (i : ExactMarkIndex N E) (omega : SampleSpace C) : Bool :=
  decide (exactLengthAt omega i.1.val (excessRowCount L i.2.val))

def signedMarkedIndicator (C N L E : ℕ) (i : SignedMarkIndex N E) (omega : SampleSpace C) : Bool :=
  decide (SignedExactMark (valueBit omega) i.1.val L i.2.1.val i.2.2)

def conditionedSignedMarkedIndicator (C N L E Y : ℕ) (sigma : SmallSample C Y)
    (i : SignedMarkIndex N E) (eta : LargeSample C Y) : Bool :=
  signedMarkedIndicator C N L E i (assemble C Y sigma eta)

def exactMarkRate (L e : ℕ) : ℝ≥0 := ⟨1/(2 : ℝ)^(L+e+1), by positivity⟩

def signedMarkRate (L e : ℕ) : ℝ≥0 := ⟨1/(2 : ℝ)^(L+e+2), by positivity⟩

theorem exactMarkRate_coe (L e : ℕ) : (exactMarkRate L e : ℝ) = 1/(2 : ℝ)^(L+e+1) := rfl

theorem signedMarkRate_coe (L e : ℕ) : (signedMarkRate L e : ℝ) = 1/(2 : ℝ)^(L+e+2) := rfl

theorem exactMarkedIndicator_eq_true (C N L E : ℕ) (i : ExactMarkIndex N E) (omega : SampleSpace C) :
    exactMarkedIndicator C N L E i omega = true ↔
      ExactLengthEvent (valueBit omega) i.1.val (excessRowCount L i.2.val) := by
  simp only [exactMarkedIndicator, decide_eq_true_eq]
  rfl

theorem signedMarkedIndicator_eq_true (C N L E : ℕ) (i : SignedMarkIndex N E) (omega : SampleSpace C) :
    signedMarkedIndicator C N L E i omega = true ↔
      SignedExactMark (valueBit omega) i.1.val L i.2.1.val i.2.2 := by
  simp [signedMarkedIndicator]

/-- One and only one sign is present whenever the unsigned exact event occurs. -/
theorem sum_signedMarkValue (g : ℕ → F₂) (x L e : ℕ) :
    (∑ s : F₂, signedMarkValue g x L e s) = exactMarkValue g x L e := by
  rw [Finset.sum_eq_single (g x)]
  · simp [signedMarkValue,SignedExactMark,exactMarkValue]
  · intro s _ hs
    simp [signedMarkValue,SignedExactMark,Ne.symm hs]
  · simp

/-- Distinct exact mark-sign labels at one site are mutually exclusive. -/
theorem signedExactMark_unique {g : ℕ → F₂} {x L e f : ℕ} {s t : F₂}
    (hL : 1 ≤ L) (he : SignedExactMark g x L e s) (hf : SignedExactMark g x L f t) :
    e = f ∧ s = t :=
  ⟨exactLengthEvent_excess_unique hL he.1 hf.1,he.2.symm.trans hf.2⟩

/-- Every finite collection of exact excesses is dominated by the base start. -/
theorem sum_exactMarkValue_le_base (g : ℕ → F₂) (x L E : ℕ) (hL : 1 ≤ L) :
    (∑ e : Fin (E+1), exactMarkValue g x L e.val) ≤ baseStartValue g x L := by
  by_cases hex : ∃ e : Fin (E+1), ExactLengthEvent g x (excessRowCount L e.val)
  · obtain ⟨e,he⟩ := hex
    rw [Finset.sum_eq_single e]
    · simp [exactMarkValue,he,baseStartValue,exactLengthEvent_start he]
    · intro f _ hfe
      have hf : ¬ExactLengthEvent g x (excessRowCount L f.val) := by
        intro hf
        exact hfe (Fin.ext (exactLengthEvent_excess_unique hL hf he))
      simp [exactMarkValue,hf]
    · simp
  · push Not at hex
    simp [exactMarkValue,hex]

/-- Signs and excesses are removed before taking any expectation or arithmetic bound. -/
theorem sum_signedMarkValue_le_base (g : ℕ → F₂) (x L E : ℕ) (hL : 1 ≤ L) :
    (∑ e : Fin (E+1), ∑ s : F₂, signedMarkValue g x L e.val s) ≤ baseStartValue g x L := by
  simp only [sum_signedMarkValue]
  exact sum_exactMarkValue_le_base g x L E hL

/-- The same lossless domination for pairs, with no factor depending on E. -/
theorem sum_signedMarkValue_pair_le_base (g : ℕ → F₂) (x y L E : ℕ) (hL : 1 ≤ L) :
    (∑ e : Fin (E+1), ∑ s : F₂, ∑ f : Fin (E+1), ∑ t : F₂,
      signedMarkValue g x L e.val s * signedMarkValue g y L f.val t) ≤
        baseStartValue g x L * baseStartValue g y L := by
  have h := Nat.mul_le_mul (sum_signedMarkValue_le_base g x L E hL)
    (sum_signedMarkValue_le_base g y L E hL)
  simp_rw [Finset.sum_mul] at h
  simp_rw [Finset.mul_sum] at h
  exact h

theorem sum_exactMarkValue_pair_le_base (g : ℕ → F₂) (x y L E : ℕ) (hL : 1 ≤ L) :
    (∑ e : Fin (E+1), ∑ f : Fin (E+1), exactMarkValue g x L e.val * exactMarkValue g y L f.val) ≤
      baseStartValue g x L * baseStartValue g y L := by
  have h := Nat.mul_le_mul (sum_exactMarkValue_le_base g x L E hL)
    (sum_exactMarkValue_le_base g y L E hL)
  simp_rw [Finset.sum_mul] at h
  simp_rw [Finset.mul_sum] at h
  exact h

/-- Exact geometric sum of the unsigned marginal rates. -/
theorem sum_range_exactMarkRate (L n : ℕ) :
    (∑ e ∈ Finset.range n, (exactMarkRate L e : ℝ)) =
      (1-1/(2 : ℝ)^n)/(2 : ℝ)^L := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ,ih,exactMarkRate_coe]
    simp only [pow_add,pow_succ]
    field_simp
    ring

theorem sum_exactMarkRate (L E : ℕ) :
    (∑ e : Fin (E+1), (exactMarkRate L e.val : ℝ)) =
      (1-1/(2 : ℝ)^(E+1))/(2 : ℝ)^L := by
  simpa only [Finset.sum_range] using sum_range_exactMarkRate L (E+1)

theorem sum_exactMarkRate_le_base (L E : ℕ) :
    (∑ e : Fin (E+1), (exactMarkRate L e.val : ℝ)) ≤ 1/(2 : ℝ)^L := by
  rw [sum_exactMarkRate]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have h : 0 ≤ 1/(2 : ℝ)^(E+1) := by positivity
  linarith

theorem sum_signedMarkRate (L e : ℕ) :
    (∑ _s : F₂, (signedMarkRate L e : ℝ)) = (exactMarkRate L e : ℝ) := by
  simp only [Finset.sum_const,Finset.card_univ,ZMod.card,nsmul_eq_mul,signedMarkRate_coe,exactMarkRate_coe]
  have hp : L+e+2 = L+e+1+1 := by omega
  rw [hp,pow_succ]
  norm_num
  field_simp

theorem sum_all_signedMarkRate_le_base (L E : ℕ) :
    (∑ e : Fin (E+1), ∑ _s : F₂, (signedMarkRate L e.val : ℝ)) ≤ 1/(2 : ℝ)^L := by
  simp only [sum_signedMarkRate]
  exact sum_exactMarkRate_le_base L E

end
end PaperC.V282.ExactMarkedModel
