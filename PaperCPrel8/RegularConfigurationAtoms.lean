import PaperCPrel8.RegularTargetCloud
import PaperCV282.CrossoverBulkAtoms

/-! # Exact masses of simple marked plants under the complete target law

Rows may be empty or contain one exact excess. No finite mark truncation or
unproved Poisson point-process atom formula is used.
-/
namespace PaperC.Prel8.RegularConfigurationAtoms
open Finset MeasureTheory ProbabilityTheory
open V282.BulkMarkedTypes V282.BulkMarkedTarget V282.CrossoverBulkAtoms
open V282.CrossoverConfigurationAtoms V282.GeometricMarkedConfiguration
open V282.SpatialMarkedTarget (signedSiteRate)
open V282.ExactMarkedModel
open scoped NNReal
noncomputable section

def rowConfiguration : Option ℕ → (ℕ →₀ ℕ)
  | none => 0
  | some e => Finsupp.single e 1

def rowWeight (L : ℕ) : Option ℕ → ℝ
  | none => 1
  | some e => signedMarkRate L e

def plantConfiguration (sites : Finset ℕ) (plant : sites × F₂ → Option ℕ) : SpatialMarkedConfig sites :=
  flattenRows sites (fun i ↦ rowConfiguration (plant i))

def plantWeight (sites : Finset ℕ) (L : ℕ) (plant : sites × F₂ → Option ℕ) : ℝ :=
  ∏ i, rowWeight L (plant i)

/-- Each occupied row has the exact elementary signed-mark intensity. -/
theorem row_mass (L : ℕ) (r : Option ℕ) :
    (configurationMeasure (signedSiteRate L)).real {rowConfiguration r} =
      Real.exp (-(signedSiteRate L:ℝ))*rowWeight L r := by
  cases r with
  | none => simpa [rowConfiguration,rowWeight] using configuration_zero_mass (signedSiteRate L)
  | some e =>
    rw [rowConfiguration,configuration_single_mass _ (by change (0:ℝ)<1/(2:ℝ)^(L+1); positivity),rowWeight]
    change Real.exp (-(signedSiteRate L:ℝ))*(1/(2:ℝ)^(L+1))/(2:ℝ)^(e+1)=
      Real.exp (-(signedSiteRate L:ℝ))*(1/(2:ℝ)^(L+e+2))
    rw [show L+e+2=(L+1)+(e+1) by omega,pow_add]
    ring

/-- The actual complete target mass is exp(-mu) times the product of planted
signed-mark intensities, with all empty rows retained in the void factor. -/
theorem plant_mass (sites : Finset ℕ) (L : ℕ) (plant : sites × F₂ → Option ℕ) :
    (spatialTargetMeasure sites L).real {plantConfiguration sites plant} =
      Real.exp (-(totalRate sites L:ℝ))*plantWeight sites L plant := by
  rw [plantConfiguration,spatial_atom_eq_rows]
  simp_rw [row_mass]
  rw [prod_mul_distrib]
  have hzero := spatial_zero_mass sites L
  rw [← flattenRows_zero sites,spatial_atom_eq_rows] at hzero
  simp_rw [configuration_zero_mass] at hzero
  rw [hzero]
  rfl

/-- Empty and singleton rows are represented without losing multiplicity or excess. -/
theorem rowConfiguration_injective : Function.Injective rowConfiguration := by
  intro a b h
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some e =>
      have he := congrArg (fun c : ℕ →₀ ℕ ↦ c e) h
      simp [rowConfiguration] at he
  | some e =>
    cases b with
    | none =>
      have he := congrArg (fun c : ℕ →₀ ℕ ↦ c e) h
      simp [rowConfiguration] at he
    | some f =>
      have he : e=f := Finsupp.single_left_injective (by decide : (1:ℕ)≠0) h
      exact congrArg some he

/-- Distinct simple row plants correspond to distinct full target configurations. -/
theorem plantConfiguration_injective (sites : Finset ℕ) : Function.Injective (plantConfiguration sites) := by
  intro a b h
  have hh := flattenRows_injective sites h
  funext i
  exact rowConfiguration_injective (congrFun hh i)

/-- Every plant has strictly positive elementary mass. -/
theorem plantWeight_pos (sites : Finset ℕ) (L : ℕ) (plant : sites × F₂ → Option ℕ) :
    0<plantWeight sites L plant := by
  apply prod_pos
  intro i hi
  cases plant i <;> simp only [rowWeight]
  · norm_num
  · change 0<1/(2:ℝ)^_
    positivity

end
end PaperC.Prel8.RegularConfigurationAtoms
