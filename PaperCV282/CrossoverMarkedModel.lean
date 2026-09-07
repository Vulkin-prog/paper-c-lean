import PaperCV282.CrossoverBulkOnePoint
import PaperCV282.CrossoverPrimeClockStable
import PaperCV282.RarePrefixGeometry

/-! # The actual source-labelled rare crossover record

`some (Sum.inl G)` records the border at position one with positive sign.
`some (Sum.inr (x,(e,s)))` records a bulk start, its excess and its sign.
`none` is the cemetery mark. Maximal bulk lengths remain uncensored.
-/
namespace PaperC.V282.CrossoverMarkedModel

open MeasureTheory ProbabilityTheory InfiniteRademacher BulkMarkedTypes BulkMarkedSource
open BulkMarkedGeometry CrossoverBulkOnePoint CrossoverBulkAtoms RarePrefixGeometry
open PrimeClockDistribution MicroscopicBorderEvents

noncomputable section
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P
local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

@[reducible]
def Record := Option (Sum ℕ (ℕ × (ℕ × F₂)))

instance instMeasurableRecord : MeasurableSpace Record := ⊤
instance instMeasurableSingletonRecord : MeasurableSingletonClass Record := by infer_instance

def borderLabel (G : ℕ) : Record := some (Sum.inl G)
def bulkLabel (sites : Finset ℕ) (j : SpatialMarkedIndex sites) : Record :=
  some (Sum.inr (j.1.val,j.2))

/-- Choose the unique active exact mark at a specified actual start, if present. -/
def pointAtSite (sites : Finset ℕ) (x : ℕ) (c : SpatialMarkedConfig sites) : Option (SpatialMarkedIndex sites) :=
  if h : ∃ j, j.1.val=x ∧ c j≠0 then some h.choose else none

theorem pointAtSite_some_property {sites : Finset ℕ} {x : ℕ} {c : SpatialMarkedConfig sites}
    {j : SpatialMarkedIndex sites} (h : pointAtSite sites x c=some j) : j.1.val=x ∧ c j≠0 := by
  unfold pointAtSite at h
  split_ifs at h with he
  · exact Option.some.inj h ▸ he.choose_spec

theorem pointAtSite_single (sites : Finset ℕ) (j : SpatialMarkedIndex sites) :
    pointAtSite sites j.1.val (Finsupp.single j 1)=some j := by
  have hex : ∃ k : SpatialMarkedIndex sites,
      k.1.val=j.1.val ∧ (Finsupp.single j 1 : SpatialMarkedConfig sites) k≠0 := ⟨j,rfl,by simp⟩
  rw [pointAtSite,dif_pos hex]
  congr 1
  by_contra hn
  exact hex.choose_spec.2 (Finsupp.single_eq_of_ne hn)

def recordFromValues (sites : Finset ℕ) (x G : ℕ) (c : SpatialMarkedConfig sites) : Record :=
  if x=1 then borderLabel G else (pointAtSite sites x c).map (fun j => Sum.inr (j.1.val,j.2))

/-- Gamma reads the least genuine contained start; no desired distribution is built into it. -/
def gamma (M L : ℕ) (delta : ℝ) (omega : InfiniteSample) : Record :=
  recordFromValues (bulkStarts M L delta) (firstStart M L omega) (primeOvershoot L omega)
    (spatialMarkedSource (bulkStarts M L delta) L omega)

theorem measurable_gamma (M L : ℕ) (delta : ℝ) : Measurable (gamma M L delta) := by
  exact (measurable_of_countable (fun z : ℕ × (ℕ × SpatialMarkedConfig (bulkStarts M L delta)) =>
    recordFromValues _ z.1 z.2.1 z.2.2)).comp
      ((measurable_firstStart M L).prodMk ((measurable_primeOvershoot L).prodMk
        (measurable_spatialMarkedSource _ _)))

theorem gamma_on_border {M L : ℕ} {delta : ℝ} (hLM : L ≤ M)
    {omega : InfiniteSample} (hb : omega ∈ borderEvent L) :
    gamma M L delta omega=borderLabel (primeOvershoot L omega) := by
  have hx := (firstStart_eq_one_iff hLM omega).mpr hb
  simp only [gamma,recordFromValues,hx,ite_true]

theorem gamma_of_unique {M L : ℕ} {delta : ℝ} {omega : InfiniteSample}
    (j : SpatialMarkedIndex (bulkStarts M L delta)) (hj : j.1.val≠1)
    (hx : firstStart M L omega=j.1.val)
    (hc : spatialMarkedSource (bulkStarts M L delta) L omega=Finsupp.single j 1) :
    gamma M L delta omega=bulkLabel _ j := by
  simp only [gamma,recordFromValues,hx,hj,ite_false,hc,pointAtSite_single,Option.map_some,bulkLabel]

theorem gamma_bulk_position {M L : ℕ} {delta : ℝ} {omega : InfiniteSample} {x e : ℕ} {s : F₂}
    (hg : gamma M L delta omega=some (Sum.inr (x,(e,s)))) : firstStart M L omega=x := by
  unfold gamma recordFromValues at hg
  split_ifs at hg with hx
  · simp [borderLabel] at hg
  · cases hp : pointAtSite (bulkStarts M L delta) (firstStart M L omega)
        (spatialMarkedSource (bulkStarts M L delta) L omega) with
    | none => simp [hp] at hg
    | some j =>
      have hj := pointAtSite_some_property hp
      simp only [hp,Option.map_some,Option.some.injEq,Sum.inr.injEq,Prod.mk.injEq] at hg
      exact hj.1.symm.trans hg.1

/-- The bulk test uses the integer clock; the border is located at the microscopic endpoint. -/
def macroPosition (M : ℕ) : Record → ℝ
  | some (Sum.inr (x,_)) => (x : ℝ)/M
  | _ => 0

/-- A source-labelled projection retains the two different spatial clocks. -/
def twoClockPosition (M L : ℕ) : Record → Bool × ℝ
  | some (Sum.inl _) => (false,1/(L : ℝ)^2)
  | some (Sum.inr (x,_)) => (true,(x : ℝ)/M)
  | none => (false,0)

def truncateRecord (K : ℕ) : Record → Record
  | some (Sum.inl G) => borderLabel (min G K)
  | some (Sum.inr (x,(e,s))) => some (Sum.inr (x,(min e K,s)))
  | none => none

theorem truncateRecord_macroPosition (M K : ℕ) (r : Record) :
    macroPosition M (truncateRecord K r)=macroPosition M r := by
  cases r with
  | none => rfl
  | some r => cases r <;> rfl

end
end PaperC.V282.CrossoverMarkedModel
