import Challenge

/-!
# Paper C external-audit challenge: infinite-product transfer

This second trust boundary states the exact identity between the source
infinite Rademacher law and the finite cylinder used in `Challenge.lean`.
It is intentionally a separate Comparator target: success of the finite
theorem alone does not establish this identity.

Reference: Paper C, model discussion in §§1–2 and formalization discussion in
§18. Audit bridge: none; this is an internally proved, exact cylinder identity.
Relation: the infinite product assigns one uniform `ZMod 2` bit to each prime,
and the count observes only finitely many such coordinates.
-/

open scoped BigOperators ENNReal
open MeasureTheory Set

namespace PaperCAudit
namespace InfiniteRademacher

/-- Discrete measurable structure on one sign coordinate.
Reference: Paper C, §§1–2. Bridge: none. Relation: the exact discrete
measurable structure on the paper's two-point coordinate. -/
local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

/-- Infinite assignments of independent prime bits.
Reference: Paper C, §§1–2. Bridge: none. Relation: exact source model. -/
abbrev InfiniteSample := ℕ → F₂

/-- Uniform law of one Rademacher bit.
Reference: Paper C, §§1–2. Bridge: none. Relation: exact coordinate law. -/
noncomputable def coordinateMeasure : Measure F₂ :=
  (PMF.uniformOfFintype F₂).toMeasure

/-- Probability normalization of the coordinate law.
Reference: Paper C, §§1–2. Bridge: none. Relation: exact normalization of
the uniform Rademacher coordinate law. -/
noncomputable instance instIsProbabilityMeasureCoordinateMeasure :
    IsProbabilityMeasure coordinateMeasure := by
  unfold coordinateMeasure
  infer_instance

/-- Infinite product law of the prime bits.
Reference: Paper C, §§1–2. Bridge: none. Relation: exact unrestricted model. -/
noncomputable def infiniteRademacherMeasure : Measure InfiniteSample :=
  Measure.infinitePi (fun _ : ℕ => coordinateMeasure)

/-- Infinite-model parity functional.
Reference: Paper C, §2. Bridge: none. Relation: coordinate `k` is assigned to
the `k`-th prime and paired with the exact factorization parity. -/
noncomputable def infiniteValueBit (ω : InfiniteSample) (n : ℕ) : F₂ :=
  (parityVec n).sum fun p e => ω (Nat.primeCounting' p) * e

end InfiniteRademacher

namespace InfiniteStartProbabilityTransfer

open InfiniteRademacher

/-- Discrete measurable structure reused for the start-count observable.
Reference: Paper C, §§1–2. Bridge: none. Relation: the exact discrete
measurable structure on each bit coordinate. -/
local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

/-- Dyadic start count evaluated directly on the infinite product.
Reference: Paper C, Theorem 1.1, p. 3. Bridge: none. Relation: same finite
family of start events as `dyadicCount`, before restriction to a cylinder. -/
noncomputable def infiniteDyadicStartCount
    (N L : ℕ) (ω : InfiniteSample) : ℕ := by
  classical
  exact ∑ x ∈ dyadicBlock N,
    if StartEvent (infiniteValueBit ω) x L then 1 else 0

/-- Atom of the infinite-product start count.
Reference: Paper C, Theorem 1.1, p. 3. Bridge: none. Relation: exact. -/
def infiniteDyadicStartCountEvent
    (N L k : ℕ) : Set InfiniteSample :=
  {ω | infiniteDyadicStartCount N L ω = k}

/-- Mass function of the infinite-product start count.
Reference: Paper C, Theorem 1.1, p. 3. Bridge: none. Relation: exact law of
the source-model observable. -/
noncomputable def infiniteDyadicStartLaw
    (N L k : ℕ) : ℝ :=
  (infiniteRademacherMeasure
    (infiniteDyadicStartCountEvent N L k)).toReal

end InfiniteStartProbabilityTransfer
end PaperCAudit

/-- Exact transfer from the infinite product to the finite cylinder.
Reference: Paper C, Theorem 1.1, p. 3, and §18. Audit bridge: none.
Relation: equality of mass functions, not merely asymptotic equivalence. -/
theorem paper_c_theorem_one_one_infinite_finite_law_identity
    (N L : ℕ) :
    PaperCAudit.InfiniteStartProbabilityTransfer.infiniteDyadicStartLaw N L =
      PaperCAudit.SectionThirteenCouplings.fullDyadicStartLaw N L := by sorry
