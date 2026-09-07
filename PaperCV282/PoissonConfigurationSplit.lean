import PaperCV282.PoissonResolvedTarget

/-! # A finite lower segment is independent of the complete geometric future -/
namespace PaperC.V282.PoissonConfigurationSplit

open MeasureTheory ProbabilityTheory GeometricMarkedConfiguration GeometricClusterTruncation
open PoissonFieldMeasure PoissonResolvedTarget
open scoped NNReal ENNReal

noncomputable section

def shiftedConfiguration (k : ℕ) (c : ℕ →₀ ℕ) : ℕ →₀ ℕ :=
  c.comapDomain (fun e => k+e) (fun _ _ _ _ h => Nat.add_left_cancel h)

theorem shiftedConfiguration_apply (k : ℕ) (c : ℕ →₀ ℕ) (e : ℕ) :
    shiftedConfiguration k c e = c (k+e) := rfl

def splitConfiguration (k : ℕ) (c : ℕ →₀ ℕ) : (Fin k → ℕ) × (ℕ →₀ ℕ) :=
  (fun i => c i.val, shiftedConfiguration k c)

def lowerRates (rate : ℝ≥0) (k : ℕ) (i : Fin k) : ℝ≥0 := rate / 2^(i.val+1)

def splitVector (k d : ℕ) (v : Fin (k+d) → ℕ) : (Fin k → ℕ) × (Fin d → ℕ) :=
  (fun i => v (Fin.castAdd d i), fun i => v (Fin.natAdd k i))

theorem splitVector_preimage (k d : ℕ) (a : Fin k → ℕ) (b : Fin d → ℕ) :
    splitVector k d ⁻¹' {(a,b)} = {Fin.addCases a b} := by
  ext v
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro h
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa [splitVector] using congrFun (congrArg Prod.fst h) j
    · intro j
      simpa [splitVector] using congrFun (congrArg Prod.snd h) j
  · rintro rfl
    simp [splitVector]

theorem hasLaw_splitVector (k d : ℕ) (rates : Fin (k+d) → ℝ≥0) :
    HasLaw (splitVector k d)
      ((fieldMeasure (fun i => rates (Fin.castAdd d i))).prod
        (fieldMeasure (fun i => rates (Fin.natAdd k i)))) (fieldMeasure rates) := by
  refine ⟨(measurable_of_countable _).aemeasurable, ?_⟩
  apply Measure.ext_of_singleton
  rintro ⟨a,b⟩
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _),
    splitVector_preimage]
  rw [show ({(a,b)} : Set ((Fin k → ℕ) × (Fin d → ℕ))) = {a} ×ˢ {b} by ext z; simp]
  simp only [fieldMeasure, Measure.prod_prod, Measure.pi_singleton, Fin.prod_univ_add]
  simp

def splitProjection (k E : ℕ) (p : (Fin k → ℕ) × (ℕ →₀ ℕ)) :
    (Fin k → ℕ) × (Fin (E+1) → ℕ) := (p.1, fun i => p.2 i.val)

theorem hasLaw_split_projection (rate : ℝ≥0) (k E : ℕ) :
    HasLaw (splitProjection k E ∘ splitConfiguration k)
      ((fieldMeasure (lowerRates rate k)).prod
        (fieldMeasure (geometricCoordinateRates (rate / 2^k) E))) (configurationMeasure rate) := by
  have hbase : HasLaw (fun c : ℕ →₀ ℕ => fun i : Fin (k+(E+1)) => c i.val)
      (fieldMeasure (fun i : Fin (k+(E+1)) => rate / 2^(i.val+1)))
      (configurationMeasure rate) := by
    have h := hasLaw_finite_configuration rate (k+E)
    change HasLaw (fun c : ℕ →₀ ℕ => fun i : Fin (k+E+1) => c i.val)
      (fieldMeasure (fun i : Fin (k+E+1) => rate / 2^(i.val+1))) _ at h
    rw [show k+(E+1)=k+E+1 by omega]
    exact h
  have h := (hasLaw_splitVector k (E+1) (fun i => rate / 2^(i.val+1))).fun_comp hbase
  have hr : (fun i : Fin (E+1) => rate / 2^((Fin.natAdd k i).val+1)) =
      geometricCoordinateRates (rate / 2^k) E := by
    funext i
    simp only [Fin.val_natAdd, geometricCoordinateRates, Nat.add_assoc, pow_add]
    rw [div_div]
  rw [hr] at h
  exact h

/-- Finite measures on a lower vector and a whole configuration are identified by all finite projections. -/
theorem splitMeasure_ext (k : ℕ) (μ ν : Measure ((Fin k → ℕ) × (ℕ →₀ ℕ)))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ E, μ.map (splitProjection k E) = ν.map (splitProjection k E)) : μ=ν := by
  apply Measure.ext_of_singleton
  intro target
  let S : ℕ → Set ((Fin k → ℕ) × (ℕ →₀ ℕ)) :=
    fun E => {p | splitProjection k E p = splitProjection k E target}
  have hanti : Antitone S := by
    intro E F hEF p hp
    change splitProjection k F p = splitProjection k F target at hp
    have hfirst := congrArg Prod.fst hp
    change p.1 = target.1 at hfirst
    change splitProjection k E p = splitProjection k E target
    apply Prod.ext
    · exact hfirst
    · funext i
      exact congrFun (congrArg Prod.snd hp) ⟨i.val, by omega⟩
  have hinter : {target} = ⋂ E, S E := by
    ext p
    simp only [Set.mem_singleton_iff, Set.mem_iInter]
    constructor
    · rintro rfl E
      rfl
    · intro hp
      have hp0 := hp 0
      change splitProjection k 0 p = splitProjection k 0 target at hp0
      have hfirst := congrArg Prod.fst hp0
      change p.1 = target.1 at hfirst
      apply Prod.ext
      · exact hfirst
      · ext e
        exact congrFun (congrArg Prod.snd (hp e)) ⟨e, by omega⟩
  rw [hinter, hanti.measure_iInter (fun E => (Set.to_countable (S E)).measurableSet.nullMeasurableSet)
      ⟨0, measure_ne_top _ _⟩,
    hanti.measure_iInter (fun E => (Set.to_countable (S E)).measurableSet.nullMeasurableSet)
      ⟨0, measure_ne_top _ _⟩]
  congr 1
  funext E
  have he := congrArg (fun m : Measure ((Fin k → ℕ) × (Fin (E+1) → ℕ)) =>
    m {splitProjection k E target}) (h E)
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _),
    Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)] at he
  have hS : splitProjection k E ⁻¹' {splitProjection k E target} = S E := by
    ext p
    simp [S]
  rwa [hS] at he

/-- Independent Poisson lower coordinates and a genuinely independent entire future configuration. -/
theorem hasLaw_split_configuration (rate : ℝ≥0) (k : ℕ) :
    HasLaw (splitConfiguration k)
      ((fieldMeasure (lowerRates rate k)).prod (configurationMeasure (rate / 2^k)))
      (configurationMeasure rate) := by
  refine ⟨(measurable_of_countable _).aemeasurable, ?_⟩
  apply splitMeasure_ext k
  intro E
  rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  rw [(hasLaw_split_projection rate k E).map_eq]
  change _ = ((fieldMeasure (lowerRates rate k)).prod (configurationMeasure (rate / 2^k))).map
    (Prod.map id (fun c : ℕ →₀ ℕ => fun i : Fin (E+1) => c i.val))
  rw [← Measure.map_prod_map _ _ measurable_id (measurable_of_countable _), Measure.map_id,
    (hasLaw_finite_configuration (rate / 2^k) E).map_eq]

end
end PaperC.V282.PoissonConfigurationSplit
