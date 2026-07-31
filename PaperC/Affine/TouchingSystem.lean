import PaperC.Affine.StartSystem

/-!
# The affine system of two touching starts

Two starts of the same positive length `L`, based at `x` and `x + L`,
are encoded by a single system with row type `Sum (Fin L) (Fin L)`.
The left summand contains the rows of the start at `x`, and the right
summand those of the start at `x + L`.
-/

namespace PaperC
namespace Affine

noncomputable section

/-- A row of the joint system of starts at `x` and `x + L`. -/
def touchingRow (M x L : ℕ) :
    Sum (Fin L) (Fin L) → SampleSpace M →ₗ[F₂] F₂
  | Sum.inl i => startRow M x L i
  | Sum.inr i => startRow M (x + L) L i

/-- The joint linear system of two touching starts. -/
def touchingSystem (M x L : ℕ) :
    SampleSpace M →ₗ[F₂] (Sum (Fin L) (Fin L) → F₂) :=
  LinearMap.pi (touchingRow M x L)

/-- The joint right-hand side: one boundary equation in each start block. -/
def touchingRhs (L : ℕ) : Sum (Fin L) (Fin L) → F₂
  | Sum.inl i => startRhs L i
  | Sum.inr i => startRhs L i

@[simp]
theorem touchingSystem_apply_inl
    (M x L : ℕ) (ω : SampleSpace M) (i : Fin L) :
    touchingSystem M x L ω (Sum.inl i) =
      startSystem M x L ω i := by
  rfl

@[simp]
theorem touchingSystem_apply_inr
    (M x L : ℕ) (ω : SampleSpace M) (i : Fin L) :
    touchingSystem M x L ω (Sum.inr i) =
      startSystem M (x + L) L ω i := by
  rfl

@[simp]
theorem touchingRhs_apply_inl (L : ℕ) (i : Fin L) :
    touchingRhs L (Sum.inl i) = startRhs L i :=
  rfl

@[simp]
theorem touchingRhs_apply_inr (L : ℕ) (i : Fin L) :
    touchingRhs L (Sum.inr i) = startRhs L i :=
  rfl

/--
Solving the joint affine system is equivalent to simultaneous starts at
`x` and `x + L`.
-/
theorem touchingSystem_eq_touchingRhs_iff
    {M x L : ℕ} (ω : SampleSpace M) (hL : 0 < L) :
    touchingSystem M x L ω = touchingRhs L ↔
      StartEvent (valueBit ω) x L ∧
        StartEvent (valueBit ω) (x + L) L := by
  rw [← startSystem_eq_startRhs_iff ω hL,
    ← startSystem_eq_startRhs_iff ω hL]
  constructor
  · intro h
    constructor
    · funext i
      exact congrFun h (Sum.inl i)
    · funext i
      exact congrFun h (Sum.inr i)
  · rintro ⟨hleft, hright⟩
    funext i
    cases i with
    | inl i => exact congrFun hleft i
    | inr i => exact congrFun hright i

/--
Every integer vertex used by the two touching starts is below the cylinder
cutoff `dyadicCutoff N (2 * L)`.
-/
theorem touchingWindow_le_dyadicCutoff
    {N L x j : ℕ} (hx : x ∈ dyadicBlock N) (hj : j < 2 * L) :
    x + j ≤ dyadicCutoff N (2 * L) := by
  have hxUpper :
      x < 2 * N :=
    (Finset.mem_Ico.mp (by simpa [dyadicBlock] using hx)).2
  unfold dyadicCutoff
  omega

/-- The omitted root `x - 1` is covered by the same touching cylinder. -/
theorem touchingRoot_le_dyadicCutoff
    {N L x : ℕ} (hx : x ∈ dyadicBlock N) :
    x - 1 ≤ dyadicCutoff N (2 * L) := by
  have hxUpper :
      x < 2 * N :=
    (Finset.mem_Ico.mp (by simpa [dyadicBlock] using hx)).2
  unfold dyadicCutoff
  omega

end

end Affine
end PaperC
