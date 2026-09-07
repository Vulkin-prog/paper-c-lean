import PaperCV282.CrossoverMarkedTarget
import PaperCV282.CrossoverPrimeClockLaw

/-! # The common border-or-one-point comparison observable -/
namespace PaperC.V282.CrossoverMarkedCandidate

open MeasureTheory ProbabilityTheory InfiniteRademacher BulkMarkedTypes BulkMarkedSource BulkMarkedTarget
open CrossoverMarkedModel CrossoverBulkOnePoint CrossoverBulkAtoms CrossoverPrimeClockStable
open CrossoverMarkedTarget BulkMarkedGeometry

noncomputable section

@[reducible]
def CandidateSample (sites : Finset ℕ) := (Bool × ℕ) × SpatialMarkedConfig sites

/-- Only the prime clock is capped; all bulk marks remain present in this comparison. -/
def capBorder (K : ℕ) : Record → Record
  | some (Sum.inl G) => borderLabel (min G K)
  | r => r

def candidate (sites : Finset ℕ) (z : CandidateSample sites) : Record :=
  if z.1.1=true then borderLabel z.1.2
  else (selectPoint sites z.2).map (fun j => Sum.inr (j.1.val,j.2))

def rareEvent (sites : Finset ℕ) : Set (CandidateSample sites) :=
  {z | z.1.1=true ∨ totalSize sites z.2≠0}

def sourceJoint (M L K : ℕ) (delta : ℝ) : Measure (CandidateSample (bulkStarts M L delta)) :=
  infiniteRademacherMeasure.map (fun omega =>
    (actualClockRecord L K omega,spatialMarkedSource (bulkStarts M L delta) L omega))

def productJoint (sites : Finset ℕ) (L K : ℕ) : Measure (CandidateSample sites) :=
  (infiniteRademacherMeasure.map (actualClockRecord L K)).prod (spatialTargetMeasure sites L)

theorem candidate_on_border (sites : Finset ℕ) (z : CandidateSample sites) (hz : z.1.1=true) :
    candidate sites z=borderLabel z.1.2 := by simp only [candidate,hz,ite_true]

theorem candidate_on_single (sites : Finset ℕ) (j : SpatialMarkedIndex sites) (v : Bool × ℕ)
    (hv : v.1=false) : candidate sites (v,Finsupp.single j 1)=bulkLabel sites j := by
  have hs := (selectPoint_eq_some sites (Finsupp.single j 1) j).mpr rfl
  simp [candidate,hv,hs,bulkLabel]

theorem capBorder_idempotent (K : ℕ) (r : Record) : capBorder K (capBorder K r)=capBorder K r := by
  cases r with
  | none => rfl
  | some r => cases r <;> simp [capBorder,borderLabel]

theorem capBorder_macroPosition (M K : ℕ) (r : Record) :
    macroPosition M (capBorder K r)=macroPosition M r := by
  cases r with
  | none => rfl
  | some r => cases r <;> rfl

end
end PaperC.V282.CrossoverMarkedCandidate
