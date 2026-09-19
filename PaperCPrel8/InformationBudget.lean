import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith

/-!
# Exact optimization of the information-dependent graph budget

Algebraic part of 3PREL8 §6.2. `D w` represents the deletion exponent at
cutoff log-height `w`. These lemmas do not assume that a conditioning event
is measurable at a smaller cutoff; the admissible lower endpoint is explicit.
The uniform arithmetic estimates and saddle asymptotics remain separate.
-/
namespace PaperC.Prel8.InformationBudget

noncomputable section

def budget (D : ℝ → ℝ) (I w : ℝ) : ℝ := min (D w-I) ((w-I)/2)

theorem budget_at_crossing (D : ℝ → ℝ) (I s : ℝ) (h : 2*D s=s+I) :
    budget D I s = (s-I)/2 := by
  unfold budget
  have he : D s-I=(s-I)/2 := by linarith
  rw [he, min_self]

/-- Every admissible cutoff has budget at most that of the crossing. -/
theorem crossing_maximizes {D : ℝ → ℝ} {I lo hi s w : ℝ}
    (hD : AntitoneOn D (Set.Icc lo hi)) (hs : s ∈ Set.Icc lo hi)
    (hw : w ∈ Set.Icc lo hi) (hcross : 2*D s=s+I) :
    budget D I w ≤ budget D I s := by
  rw [budget_at_crossing D I s hcross]
  by_cases h : w ≤ s
  · exact (min_le_right _ _).trans (by linarith)
  · have hd := hD hs hw (le_of_not_ge h)
    exact (min_le_left _ _).trans (by linarith)

/-- The crossing is unique even when deletion is merely nonincreasing. -/
theorem crossing_unique {D : ℝ → ℝ} {I lo hi s t : ℝ}
    (hD : AntitoneOn D (Set.Icc lo hi)) (hs : s ∈ Set.Icc lo hi)
    (ht : t ∈ Set.Icc lo hi) (hcs : 2*D s=s+I) (hct : 2*D t=t+I) : s=t := by
  rcases le_total s t with h | h
  · have hd := hD hs ht h
    linarith
  · have hd := hD ht hs h
    linarith

/-- If only cutoffs above `floor` are allowed, use `max floor s`. -/
theorem admissible_cutoff_maximizes {D : ℝ → ℝ} {I lo hi s floor w : ℝ}
    (hD : AntitoneOn D (Set.Icc lo hi)) (hs : s ∈ Set.Icc lo hi)
    (hf : floor ∈ Set.Icc lo hi) (hw : w ∈ Set.Icc lo hi)
    (hfw : floor ≤ w) (hcross : 2*D s=s+I) :
    budget D I w ≤ budget D I (max floor s) := by
  by_cases h : floor ≤ s
  · rw [max_eq_right h]
    exact crossing_maximizes hD hs hw hcross
  · have hsf : s ≤ floor := le_of_not_ge h
    rw [max_eq_left hsf]
    have hd := hD hs hf hsf
    have hmin : budget D I floor = D floor-I := by
      unfold budget
      rw [min_eq_left (by linarith)]
    rw [hmin]
    have hdw := hD hf hw hfw
    exact (min_le_left _ _).trans (by linarith)

/-- The exact crossing converts one margin into both required exponential margins. -/
theorem two_error_margins {deletion I w ell c nu : ℝ}
    (hcross : 2*deletion=w+I) (hbudget : ell ≤ (w-I)/2-c*nu) :
    I+ell-deletion ≤ -c*nu ∧ I+2*ell-w ≤ -2*c*nu := by
  constructor <;> linarith

/-- A strict smaller margin absorbs a controlled deterministic remainder. -/
theorem absorb_remainder {exponent remainder c c' nu : ℝ}
    (hexponent : exponent ≤ -c*nu) (hremainder : remainder ≤ (c-c')*nu) :
    exponent+remainder ≤ -c'*nu := by
  nlinarith

end
end PaperC.Prel8.InformationBudget
