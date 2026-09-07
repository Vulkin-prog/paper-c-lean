import PaperCV282.CrossoverMarkedModel

/-! # The moving discrete crossover target, with its actual site population -/
namespace PaperC.V282.CrossoverMarkedTarget

open MeasureTheory ProbabilityTheory CrossoverMarkedModel CrossoverBulkOnePoint CrossoverBulkAtoms
open GeometricClusterTarget SpatialDiffuseMarks BulkMarkedTypes
open scoped NNReal ENNReal

noncomputable section
local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

def borderRate (L : ℕ) : ℝ≥0 := 1/2^(Nat.primeCounting L)
def borderWeight (sites : Finset ℕ) (L : ℕ) : ℝ≥0 := borderRate L/(borderRate L+totalRate sites L)
def bulkWeight (sites : Finset ℕ) (L : ℕ) : ℝ≥0 := totalRate sites L/(borderRate L+totalRate sites L)

theorem borderRate_pos (L : ℕ) : 0 < borderRate L := by unfold borderRate; positivity

theorem weights_sum (sites : Finset ℕ) (L : ℕ) : borderWeight sites L+bulkWeight sites L=1 := by
  unfold borderWeight bulkWeight
  rw [← add_div,div_self (ne_of_gt (add_pos_of_pos_of_nonneg (borderRate_pos L) (by positivity)))]

def borderLaw : Measure Record := (geometricMeasure halfSuccess).map borderLabel
def bulkLaw (sites : Finset ℕ) (hs : sites.Nonempty) : Measure Record :=
  (labelMeasure sites hs).map (bulkLabel sites)

instance instProbabilityBorderLaw : IsProbabilityMeasure borderLaw :=
  Measure.isProbabilityMeasure_map (measurable_of_countable borderLabel).aemeasurable

instance instProbabilityBulkLaw (sites : Finset ℕ) (hs : sites.Nonempty) :
    IsProbabilityMeasure (bulkLaw sites hs) :=
  Measure.isProbabilityMeasure_map (measurable_of_countable (bulkLabel sites)).aemeasurable

/-- Both mixture weights may move or oscillate with the prefix size. -/
def mixedLaw (sites : Finset ℕ) (hs : sites.Nonempty) (L : ℕ) : Measure Record :=
  (borderWeight sites L : ℝ≥0∞) • borderLaw + (bulkWeight sites L : ℝ≥0∞) • bulkLaw sites hs

instance instProbabilityMixedLaw (sites : Finset ℕ) (hs : sites.Nonempty) (L : ℕ) :
    IsProbabilityMeasure (mixedLaw sites hs L) := by
  constructor
  simp only [mixedLaw,Measure.add_apply,Measure.smul_apply,smul_eq_mul,measure_univ,mul_one]
  exact_mod_cast weights_sum sites L

theorem mixedLaw_real (sites : Finset ℕ) (hs : sites.Nonempty) (L : ℕ) (A : Set Record) :
    (mixedLaw sites hs L).real A =
      (borderWeight sites L : ℝ)*borderLaw.real A+(bulkWeight sites L : ℝ)*(bulkLaw sites hs).real A := by
  unfold mixedLaw
  rw [measureReal_add_apply
    (by simpa only [Measure.smul_apply,smul_eq_mul] using
      ENNReal.mul_ne_top ENNReal.coe_ne_top (measure_ne_top borderLaw A))
    (by simpa only [Measure.smul_apply,smul_eq_mul] using
      ENNReal.mul_ne_top ENNReal.coe_ne_top (measure_ne_top (bulkLaw sites hs) A))]
  simp only [measureReal_ennreal_smul_apply,ENNReal.coe_toReal]

theorem borderLaw_singleton (G : ℕ) : borderLaw.real {borderLabel G}=1/(2 : ℝ)^(G+1) := by
  rw [borderLaw,Measure.real,Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  have he : borderLabel ⁻¹' {borderLabel G}={G} := by ext k; simp [borderLabel]
  rw [he]
  exact geometric_excess_real G

theorem bulkLaw_border_zero (sites : Finset ℕ) (hs : sites.Nonempty) (G : ℕ) :
    (bulkLaw sites hs).real {borderLabel G}=0 := by
  rw [bulkLaw,Measure.real,Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  have he : bulkLabel sites ⁻¹' {borderLabel G}=∅ := by ext k; simp [bulkLabel,borderLabel]
  simp [he]

theorem mixedLaw_border_singleton (sites : Finset ℕ) (hs : sites.Nonempty) (L G : ℕ) :
    (mixedLaw sites hs L).real {borderLabel G}=(borderWeight sites L : ℝ)/(2 : ℝ)^(G+1) := by
  rw [mixedLaw_real,borderLaw_singleton,bulkLaw_border_zero]
  ring

theorem mixedLaw_cemetery_zero (sites : Finset ℕ) (hs : sites.Nonempty) (L : ℕ) :
    (mixedLaw sites hs L).real {none}=0 := by
  rw [mixedLaw_real]
  have hb : borderLaw.real {none}=0 := by
    rw [borderLaw,Measure.real,Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
    have he : borderLabel ⁻¹' {none}=∅ := by ext k; simp [borderLabel]
    simp [he]
  have hc : (bulkLaw sites hs).real {none}=0 := by
    rw [bulkLaw,Measure.real,Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
    have he : bulkLabel sites ⁻¹' {none}=∅ := by ext k; simp [bulkLabel]
    simp [he]
  simp [hb,hc]

/-- Positive is zero in the additive F₂ coordinate used by the source model. -/
def positiveSign : Record → Bool
  | some (Sum.inl _) => true
  | some (Sum.inr (_,(_,s))) => if s=0 then true else false
  | none => false

theorem borderLaw_positive : borderLaw.real {r | positiveSign r=true}=1 := by
  rw [borderLaw,Measure.real,Measure.map_apply (measurable_of_countable _) (Set.to_countable _).measurableSet]
  have he : borderLabel ⁻¹' {r | positiveSign r=true}=Set.univ := by ext k; simp [borderLabel,positiveSign]
  simp [he]

theorem bulkLaw_positive (sites : Finset ℕ) (hs : sites.Nonempty) :
    (bulkLaw sites hs).real {r | positiveSign r=true}=1/2 := by
  rw [bulkLaw,Measure.real,Measure.map_apply (measurable_of_countable _) (Set.to_countable _).measurableSet]
  have he : bulkLabel sites ⁻¹' {r | positiveSign r=true}=
      Set.univ ×ˢ (Set.univ ×ˢ ({0} : Set F₂)) := by
    ext j
    simp [bulkLabel,positiveSign]
  change (labelMeasure sites hs).real (bulkLabel sites ⁻¹' {r | positiveSign r=true})=_
  rw [he,labelMeasure,measureReal_prod_prod,measureReal_prod_prod,probReal_univ,probReal_univ,
    signMeasure_real_singleton]
  ring

/-- The sign-bias expression is exact for the target; transferring it needs the actual-source TV theorem. -/
theorem mixedLaw_positive (sites : Finset ℕ) (hs : sites.Nonempty) (L : ℕ) :
    (mixedLaw sites hs L).real {r | positiveSign r=true}=
      ((borderRate L : ℝ)+(totalRate sites L : ℝ)/2)/((borderRate L : ℝ)+(totalRate sites L : ℝ)) := by
  rw [mixedLaw_real,borderLaw_positive,bulkLaw_positive]
  simp only [borderWeight,bulkWeight,NNReal.coe_div,NNReal.coe_add]
  ring

end
end PaperC.V282.CrossoverMarkedTarget
