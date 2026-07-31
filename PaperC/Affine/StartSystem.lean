import PaperC.Affine.System
import PaperC.Model.FiniteRademacher

/-!
# The affine system of a run start

A start of length `L > 0` at `x` is encoded by `L` affine equations over
`𝔽₂`.  Row zero is the left-boundary equation

`Y_(x - 1) + Y_x = 1`,

and row `j`, for `0 < j < L`, is the constancy equation

`Y_x + Y_(x + j) = 0`.

This is the finite-cylinder version of the affine formulation in Section 2 of
Paper C.
-/

namespace PaperC.Affine

/-- In `𝔽₂`, a sum vanishes exactly when its two summands are equal. -/
@[simp]
theorem add_eq_zero_iff_eq (a b : F₂) : a + b = 0 ↔ a = b := by
  revert a b
  decide

/-- The linear functional occurring in row `i` of the start system. -/
noncomputable def startRow (M x L : ℕ) (i : Fin L) :
    SampleSpace M →ₗ[F₂] F₂ :=
  if i.1 = 0 then
    valueLinear M (x - 1) + valueLinear M x
  else
    valueLinear M x + valueLinear M (x + i.1)

/-- The linear map collecting all rows of the start system. -/
noncomputable def startSystem (M x L : ℕ) :
    SampleSpace M →ₗ[F₂] (Fin L → F₂) :=
  LinearMap.pi (startRow M x L)

/-- The right-hand side: one on the boundary row and zero elsewhere. -/
def startRhs (L : ℕ) : Fin L → F₂ :=
  fun i => if i.1 = 0 then 1 else 0

@[simp]
theorem startSystem_apply (M x L : ℕ) (ω : SampleSpace M) (i : Fin L) :
    startSystem M x L ω i =
      if i.1 = 0 then
        valueBit ω (x - 1) + valueBit ω x
      else
        valueBit ω x + valueBit ω (x + i.1) := by
  change (startRow M x L i) ω = _
  by_cases hi : i.1 = 0
  · rw [startRow, if_pos hi, LinearMap.add_apply, valueLinear_apply, valueLinear_apply,
      if_pos hi]
  · rw [startRow, if_neg hi, LinearMap.add_apply, valueLinear_apply, valueLinear_apply,
      if_neg hi]

@[simp]
theorem startRhs_apply (L : ℕ) (i : Fin L) :
    startRhs L i = if i.1 = 0 then 1 else 0 :=
  rfl

/--
For positive `L`, solving the finite affine system is exactly the deterministic
start event for the bit-valued multiplicative function.
-/
theorem startSystem_eq_startRhs_iff
    {M x L : ℕ} (ω : SampleSpace M) (hL : 0 < L) :
    startSystem M x L ω = startRhs L ↔
      StartEvent (valueBit ω) x L := by
  constructor
  · intro h
    constructor
    · have hzero := congrFun h (⟨0, hL⟩ : Fin L)
      simpa using hzero
    · intro j hj
      by_cases hj0 : j = 0
      · subst j
        simp
      · have hrow := congrFun h (⟨j, hj⟩ : Fin L)
        have hsum :
            valueBit ω x + valueBit ω (x + j) = 0 := by
          simpa [hj0] using hrow
        exact (add_eq_zero_iff_eq _ _).mp hsum |>.symm
  · intro h
    funext i
    by_cases hi : i.1 = 0
    · simpa [hi] using h.1
    · have hsum :
          valueBit ω x + valueBit ω (x + i.1) = 0 :=
        (add_eq_zero_iff_eq _ _).mpr (h.2 i.1 i.2).symm
      simpa [hi] using hsum

/-- Set-membership form of `startSystem_eq_startRhs_iff`. -/
theorem mem_startSolutionSet_iff
    {M x L : ℕ} (ω : SampleSpace M) (hL : 0 < L) :
    ω ∈ solutionSet (startSystem M x L) (startRhs L) ↔
      StartEvent (valueBit ω) x L := by
  simpa only [mem_solutionSet_iff] using
    startSystem_eq_startRhs_iff ω hL

/-- The same equivalence expressed using the finite-model predicate `startAt`. -/
theorem startSystem_eq_startRhs_iff_startAt
    {M x L : ℕ} (ω : SampleSpace M) (hL : 0 < L) :
    startSystem M x L ω = startRhs L ↔ startAt ω x L := by
  simpa only [startAt] using startSystem_eq_startRhs_iff ω hL

/-- Solution-set membership expressed using `startAt`. -/
theorem mem_startSolutionSet_iff_startAt
    {M x L : ℕ} (ω : SampleSpace M) (hL : 0 < L) :
    ω ∈ solutionSet (startSystem M x L) (startRhs L) ↔ startAt ω x L := by
  simpa only [mem_solutionSet_iff] using
    startSystem_eq_startRhs_iff_startAt ω hL

end PaperC.Affine
