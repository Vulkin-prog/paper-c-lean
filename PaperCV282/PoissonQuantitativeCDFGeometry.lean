import PaperCV282.PoissonQuantitativeCells
import PaperCV282.PoissonQuantitativeMoments

/-! # Central cells and true distribution-function events -/
namespace PaperC.V282.PoissonQuantitativeCDFGeometry

open MeasureTheory ProbabilityTheory Real Set PoissonQuantitativeLocal PoissonQuantitativeLattice

noncomputable section

local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

def centralCDFAtoms (rate t : ℝ) : Finset ℕ :=
  (Finset.range (⌈2*rate⌉₊+1)).filter (fun n => |(n : ℝ)-rate|≤rate/2 ∧ latticePoint rate n≤t)

def centralCDFCells (rate t : ℝ) : Set ℝ := ⋃ n∈centralCDFAtoms rate t,latticeCell rate n

theorem mem_centralCDFAtoms {rate t : ℝ} (hr : 0≤rate) (n : ℕ) :
    n∈centralCDFAtoms rate t ↔ |(n : ℝ)-rate|≤rate/2 ∧ latticePoint rate n≤t := by
  simp only [centralCDFAtoms,Finset.mem_filter,Finset.mem_range,and_iff_right_iff_imp]
  intro hn
  have hb : (n : ℝ)≤2*rate := by have h := le_abs_self ((n : ℝ)-rate);linarith [hn.1]
  have hc := hb.trans (Nat.le_ceil (2*rate))
  have hnat : n≤⌈2*rate⌉₊ := by exact_mod_cast hc
  omega

theorem central_cell_contains {rate x : ℝ} (hr : 16≤rate) (hx : |x|<sqrt rate/4) :
    ∃ n : ℕ, |(n : ℝ)-rate|≤rate/2 ∧ x∈latticeCell rate n := by
  have hp : 0<sqrt rate := by positivity
  have hsq := sq_sqrt (by linarith : 0≤rate)
  have hl : -sqrt rate/4<x := by have h := neg_abs_le x;linarith
  have hu : x<sqrt rate/4 := (le_abs_self x).trans_lt hx
  have hmulL := mul_lt_mul_of_pos_left hl hp
  have hmulU := mul_lt_mul_of_pos_left hu hp
  have hy : 0≤rate+sqrt rate*x := by nlinarith
  let n : ℕ := ⌊rate+sqrt rate*x⌋₊
  have hnL : (n : ℝ)≤rate+sqrt rate*x := Nat.floor_le hy
  have hnU : rate+sqrt rate*x<(n : ℝ)+1 := Nat.lt_floor_add_one _
  refine ⟨n,?_,?_⟩
  · rw [abs_le]
    constructor <;> nlinarith
  · constructor
    · unfold latticePoint
      exact (div_le_iff₀ hp).mpr (by nlinarith)
    · unfold latticePoint
      rw [← add_div]
      exact (lt_div_iff₀ hp).mpr (by nlinarith)

theorem centralCDFCells_subsets {rate t : ℝ} (hr : 16≤rate) :
    centralCDFCells rate t ⊆ Iic t ∪ Ioc t (t+1/sqrt rate) ∧
    Iic t ⊆ centralCDFCells rate t ∪ {x : ℝ | sqrt rate/4≤|x|} := by
  constructor
  · intro x hx
    obtain ⟨n,hn,hx⟩ := mem_iUnion₂.mp hx
    have ht := ((mem_centralCDFAtoms (by linarith : 0≤rate) n).mp hn).2
    by_cases hxt : x≤t
    · exact Or.inl hxt
    · exact Or.inr ⟨lt_of_not_ge hxt,by have hh := hx.2;linarith⟩
  · intro x hx
    by_cases houter : sqrt rate/4≤|x|
    · exact Or.inr houter
    obtain ⟨n,hc,hn⟩ := central_cell_contains hr (lt_of_not_ge houter)
    exact Or.inl (mem_iUnion₂.mpr ⟨n,(mem_centralCDFAtoms (by linarith : 0≤rate) n).mpr ⟨hc,hn.1.trans hx⟩,hn⟩)

theorem probability_difference_le_errors {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (A B E F : Set α)
    (hAB : A⊆B∪E) (hBA : B⊆A∪F) :
    |μ.real A-μ.real B|≤μ.real E+μ.real F := by
  have h1 := (measureReal_mono (μ := μ) hAB).trans (measureReal_union_le B E)
  have h2 := (measureReal_mono (μ := μ) hBA).trans (measureReal_union_le A F)
  exact abs_le.mpr ⟨by linarith [measureReal_nonneg (μ := μ) (s := E)],by linarith [measureReal_nonneg (μ := μ) (s := F)]⟩

theorem gaussian_real_eq_integral (s : Set ℝ) :
    (gaussianReal 0 1).real s=∫ x in s,gaussianPDFReal 0 1 x := by
  rw [measureReal_def,gaussianReal_apply_eq_integral 0 one_ne_zero,
    ENNReal.toReal_ofReal (integral_nonneg fun x => gaussianPDFReal_nonneg 0 1 x)]

theorem gaussian_interval_mass_le {a b : ℝ} (hab : a≤b) :
    (gaussianReal 0 1).real (Ioc a b)≤b-a := by
  rw [gaussian_real_eq_integral]
  have hi := integrable_gaussianPDFReal (μ := 0) (v := 1)
  have hc : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc a b) :=
    integrableOn_const (by rw [volume_Ioc];exact ENNReal.ofReal_ne_top)
  have h := setIntegral_mono_on hi.integrableOn hc measurableSet_Ioc (fun x _ => by
    have hpi : 1≤sqrt (2*π) := one_le_sqrt.mpr (by have hh := pi_gt_three;linarith)
    have hp := inv_le_one_of_one_le₀ hpi
    have he : exp (-x^2/2)≤1 := exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])
    simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero]
    exact mul_le_one₀ hp (exp_pos _).le he)
  simpa only [setIntegral_const,smul_eq_mul,mul_one,measureReal_def,volume_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hab)] using h

theorem gaussian_CDF_cell_error {rate t : ℝ} (hr : 16≤rate) :
    |(gaussianReal 0 1).real (centralCDFCells rate t)-(gaussianReal 0 1).real (Iic t)|≤
      1/sqrt rate+16/rate := by
  obtain ⟨h1,h2⟩ := centralCDFCells_subsets (t := t) hr
  have h := probability_difference_le_errors (gaussianReal 0 1) (centralCDFCells rate t) (Iic t)
    (Ioc t (t+1/sqrt rate)) {x : ℝ | sqrt rate/4≤|x|} h1 h2
  have hi := gaussian_interval_mass_le (a := t) (b := t+1/sqrt rate) (le_add_of_nonneg_right (by positivity))
  have ho := PoissonQuantitativeMoments.gaussian_outer_tail (sqrt rate/4) (by positivity)
  have he : 1/(sqrt rate/4)^2=16/rate := by rw [div_pow,sq_sqrt (by linarith : 0≤rate)];ring
  rw [he] at ho
  exact h.trans (add_le_add (by simpa using hi) ho)

end
end PaperC.V282.PoissonQuantitativeCDFGeometry
