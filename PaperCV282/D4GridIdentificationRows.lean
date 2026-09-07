import PaperCV282.D4ClosurePointLaws
import PaperCV282.SpatialMarkedPoissonIdentification
import PaperCV282.SpatialDiffuseMarks

/-! # Independent spatial counts in every exact row of the integer-level target -/
namespace PaperC.V282.D4GridIdentificationRows

open MeasureTheory ProbabilityTheory GeneralPoissonMarking UniformSpatialGrid
open D4ClosurePointMeasure D4ClosurePointLaws D4ClosureIntegerLevels PoissonFieldMeasure
open SpatialMarkedTypes ExactMarkedModel SpatialMarkedPoissonIdentification ConditionalStartProbability
open scoped BigOperators NNReal ENNReal

noncomputable section

instance instMeasurableRowCategory (N : ℕ) : MeasurableSpace (Option (Fin N × F₂)) := ⊤
instance instSingletonRowCategory (N : ℕ) : MeasurableSingletonClass (Option (Fin N × F₂)) := by
  infer_instance

def rowCategory (N : ℕ) (hN : 0<N) (u : unitInterval) : Option (Fin N × F₂) :=
  some (gridSite N hN u,0)

theorem measurable_rowCategory (N : ℕ) (hN : 0<N) : Measurable (rowCategory N hN) :=
  (measurable_of_countable (fun x : Fin N => some (x,(0 : F₂)))).comp (measurable_gridSite N hN)

def rowCounts (N : ℕ) (hN : 0<N) (sample : ℕ × (ℕ→unitInterval)) : Fin N × F₂ → ℕ :=
  categoryCounts (rowCategory N hN) sample

theorem measurable_rowCounts (N : ℕ) (hN : 0<N) : Measurable (rowCounts N hN) :=
  measurable_categoryCounts _ (measurable_rowCategory N hN)

def rowRates (N : ℕ) (hN : 0<N) (rate : ℝ≥0) : Fin N × F₂ → ℝ≥0 :=
  categoryRates rate unitIntervalUniformMeasure (rowCategory N hN)

theorem hasLaw_rowCounts (N : ℕ) (hN : 0<N) (rate : ℝ≥0) :
    HasLaw (rowCounts N hN) (fieldMeasure (rowRates N hN rate))
      (markSampleMeasure rate unitIntervalUniformMeasure) :=
  hasLaw_categoryCounts _ _ _ (measurable_rowCategory N hN)

theorem rowRates_coe (N : ℕ) (hN : 0<N) (rate : ℝ≥0) (i : Fin N × F₂) :
    (rowRates N hN rate i : ℝ)=if i.2=0 then (rate : ℝ)/N else 0 := by
  classical
  rw [rowRates,categoryRates_coe]
  by_cases hi : i.2=0
  · rw [if_pos hi]
    have hs : {u | rowCategory N hN u=some i}={u | gridSite N hN u=i.1} := by
      ext u
      simp [rowCategory,Prod.ext_iff,hi]
    rw [hs,measureReal_def,grid_cell_probability,ENNReal.toReal_inv,ENNReal.toReal_natCast]
    rfl
  · rw [if_neg hi]
    have hs : {u | rowCategory N hN u=some i}=∅ := by
      ext u
      simp [rowCategory,Prod.ext_iff,Ne.symm hi]
    rw [hs,measureReal_empty,mul_zero]

/-- The full vector of spatial cells within each level is a genuine product-Poisson vector. -/
theorem hasLaw_spatialRowCounts (N : ℕ) (hN : 0<N) (theta : ℝ) (r : ℤ) :
    HasLaw (fun sample : IntegerSpatialSample => rowCounts N hN (sample r))
      (fieldMeasure (rowRates N hN (integerLevelRate theta r)))
      (integerSpatialSampleMeasure theta) :=
  (hasLaw_rowCounts N hN _).fun_comp (hasLaw_spatialLevelSample theta r)

theorem independent_spatialRowCells (N : ℕ) (hN : 0<N) (theta : ℝ) (r : ℤ) :
    iIndepFun (fun i (sample : IntegerSpatialSample) => rowCounts N hN (sample r) i)
      (integerSpatialSampleMeasure theta) := by
  apply (iIndepFun_iff_hasLaw_pi_pi (fun i =>
    (hasLaw_coordinate _ i).fun_comp (hasLaw_spatialRowCounts N hN theta r))).2
  exact hasLaw_spatialRowCounts N hN theta r

/-- All spatial cells at all exact levels are jointly independent, not just marginally Poisson. -/
theorem independent_allSpatialCells (N : ℕ) (hN : 0<N) (theta : ℝ) :
    iIndepFun (fun p : ℤ × (Fin N × F₂) => fun sample : IntegerSpatialSample =>
      rowCounts N hN (sample p.1) p.2) (integerSpatialSampleMeasure theta) := by
  refine iIndepFun_uncurry' (X := fun r i (sample : IntegerSpatialSample) => rowCounts N hN (sample r) i) ?_ ?_ ?_
  · intro r i
    exact (measurable_pi_apply i).comp ((measurable_rowCounts N hN).comp (measurable_pi_apply r))
  · exact (independent_spatialLevelSamples theta).comp
      (fun _ => rowCounts N hN) (fun _ => measurable_rowCounts N hN)
  · exact independent_spatialRowCells N hN theta

/-- The entire finite joint projection on the standard signed carrier. -/
theorem hasLaw_finiteSpatialCells (N : ℕ) (hN : 0<N) (theta : ℝ) (m : ℤ) (E : ℕ) :
    HasLaw (fun sample : IntegerSpatialSample => fun i : SignedMarkIndex N E =>
      rowCounts N hN (sample (m+(i.2.1.val : ℤ))) ((dyadicSiteEquiv N).symm i.1,i.2.2))
      (fieldMeasure (fun i : SignedMarkIndex N E =>
        rowRates N hN (integerLevelRate theta (m+(i.2.1.val : ℤ)))
          ((dyadicSiteEquiv N).symm i.1,i.2.2)))
      (integerSpatialSampleMeasure theta) := by
  let f : SignedMarkIndex N E → ℤ × (Fin N × F₂) :=
    fun i => (m+(i.2.1.val : ℤ),((dyadicSiteEquiv N).symm i.1,i.2.2))
  have hf : Function.Injective f := by
    intro i j h
    have he : i.2.1=j.2.1 := by
      apply Fin.ext
      exact_mod_cast add_left_cancel (congrArg Prod.fst h)
    have hx : i.1=j.1 := (dyadicSiteEquiv N).symm.injective (congrArg (fun p => p.2.1) h)
    have hs : i.2.2=j.2.2 := congrArg (fun p => p.2.2) h
    exact Prod.ext hx (Prod.ext he hs)
  have hind := (independent_allSpatialCells N hN theta).precomp hf
  exact hind.hasLaw_pi (fun i => (hasLaw_coordinate _ _).fun_comp
    (hasLaw_spatialRowCounts N hN theta (m+(i.2.1.val : ℤ))))

end
end PaperC.V282.D4GridIdentificationRows
