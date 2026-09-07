import PaperCV282.PoissonQuantitativeTailCells

/-! # The exact central cutoff and the integer rounding of a moderate tail -/
namespace PaperC.V282.PoissonQuantitativeTailCutoff

open MeasureTheory ProbabilityTheory Real Set
open PoissonQuantitativeLattice PoissonQuantitativeTailCells PoissonQuantitativeCDFGeometry

noncomputable section

def centralTailTop (rate : ℝ) : ℕ := ⌊3*rate/2⌋₊

def moderateTailAtoms (rate t : ℝ) : Finset ℕ :=
  Finset.Icc ⌈rate+sqrt rate*t⌉₊ (centralTailTop rate)

theorem centralTailTop_bounds {rate : ℝ} (hr : 16≤rate) :
    0<centralTailTop rate ∧ sqrt rate/4≤latticePoint rate (centralTailTop rate) ∧
      latticePoint rate (centralTailTop rate)≤sqrt rate/2 ∧ rate/(centralTailTop rate+1)≤2/3 := by
  have hp : 0<sqrt rate := by positivity
  have hs := sq_sqrt (by linarith : 0≤rate)
  have hlo : 3*rate/2<(centralTailTop rate : ℝ)+1 := Nat.lt_floor_add_one _
  have hhi : (centralTailTop rate : ℝ)≤3*rate/2 := Nat.floor_le (by linarith)
  have hn : (0 : ℝ)<centralTailTop rate := by linarith
  refine ⟨by exact_mod_cast hn,?_,?_,?_⟩
  · unfold latticePoint
    exact (le_div_iff₀ hp).mpr (by nlinarith)
  · unfold latticePoint
    exact (div_le_iff₀ hp).mpr (by nlinarith)
  · exact (div_le_iff₀ (by positivity)).mpr (by linarith)

theorem moderate_parameter_bound {rate t : ℝ} (hr : 4096≤rate) (ht : 0≤t)
    (hcubic : t^3/sqrt rate≤1) : t≤sqrt rate/8 := by
  have hp : 0<sqrt rate := by positivity
  have ht0 := ht
  have hs : 64≤sqrt rate := by nlinarith [sq_sqrt (by linarith : 0≤rate)]
  have hc : t^3≤sqrt rate := (div_le_one hp).mp hcubic
  by_contra hn
  have ht' : sqrt rate/8<t := lt_of_not_ge hn
  have hpow := pow_lt_pow_left₀ ht' (by positivity : 0≤sqrt rate/8) (by norm_num : (3 : ℕ)≠0)
  have hcube := mul_nonneg (show 0≤(sqrt rate)^2-512 by nlinarith) hp.le
  nlinarith

theorem mem_moderateTailAtoms {rate t : ℝ} (hr : 16≤rate) (ht : 0≤t)
    {n : ℕ} (hn : n∈moderateTailAtoms rate t) :
    t≤latticePoint rate n ∧ latticePoint rate n≤sqrt rate/2 := by
  have hp : 0<sqrt rate := by positivity
  have ht0 := ht
  have hm := Finset.mem_Icc.mp hn
  have h1 : rate+sqrt rate*t≤n := (Nat.le_ceil _).trans (by exact_mod_cast hm.1)
  have h2 : (n : ℝ)≤centralTailTop rate := by exact_mod_cast hm.2
  constructor
  · unfold latticePoint
    exact (le_div_iff₀ hp).mpr (by nlinarith)
  · exact (div_le_div_of_nonneg_right (sub_le_sub_right h2 rate) hp.le).trans (centralTailTop_bounds hr).2.2.1

theorem lattice_cell_of_floor {rate x : ℝ} (hr : 0<rate) (hx : 0≤x) :
    x∈latticeCell rate ⌊rate+sqrt rate*x⌋₊ := by
  have hp : 0<sqrt rate := sqrt_pos.mpr hr
  have hlo := Nat.floor_le (show 0≤rate+sqrt rate*x by positivity)
  have hhi := Nat.lt_floor_add_one (rate+sqrt rate*x)
  constructor
  · unfold latticePoint
    exact (div_le_iff₀ hp).mpr (by nlinarith)
  · unfold latticePoint
    rw [← add_div]
    exact (lt_div_iff₀ hp).mpr (by nlinarith)

theorem moderate_cells_cover {rate t : ℝ} (hr : 16≤rate) (ht : 0≤t) :
    (⋃n∈moderateTailAtoms rate t,latticeCell rate n)⊆Ici t ∧
    Ici t⊆(⋃n∈moderateTailAtoms rate t,latticeCell rate n)∪
      (Ico t (t+1/sqrt rate)∪Ici (latticePoint rate (centralTailTop rate))) := by
  have hp : 0<sqrt rate := by positivity
  constructor
  · intro x hx
    obtain ⟨n,hn,hx⟩ := mem_iUnion₂.mp hx
    exact (mem_moderateTailAtoms hr ht hn).1.trans hx.1
  · intro x hx
    by_cases hleft : x<t+1/sqrt rate
    · exact Or.inr (Or.inl ⟨hx,hleft⟩)
    by_cases hright : latticePoint rate (centralTailTop rate)≤x
    · exact Or.inr (Or.inr hright)
    let n : ℕ := ⌊rate+sqrt rate*x⌋₊
    have hncell : x∈latticeCell rate n := lattice_cell_of_floor (by linarith) (ht.trans hx)
    have hnlo : ⌈rate+sqrt rate*t⌉₊≤n := by
      apply Nat.ceil_le.mpr
      have hf : rate+sqrt rate*x<(n : ℝ)+1 := Nat.lt_floor_add_one _
      have hg := mul_le_mul_of_nonneg_left (le_of_not_gt hleft) hp.le
      have he : sqrt rate*(1/sqrt rate)=1 := by field_simp
      rw [mul_add,he] at hg
      nlinarith
    have hnhi : n≤centralTailTop rate := by
      have hf : (n : ℝ)≤rate+sqrt rate*x := Nat.floor_le (by have hx0 : 0≤x := ht.trans hx; positivity)
      have hg := (lt_div_iff₀ hp).mp (lt_of_not_ge hright)
      have hh : (n : ℝ)<centralTailTop rate := by nlinarith
      exact le_of_lt (by exact_mod_cast hh)
    exact Or.inl (mem_iUnion₂.mpr ⟨n,Finset.mem_Icc.mpr ⟨hnlo,hnhi⟩,hncell⟩)

theorem gaussian_threshold_rounding_le {rate t : ℝ} (hr : 0<rate) (ht : 0≤t) :
    (gaussianReal 0 1).real (Ico t (t+1/sqrt rate))≤(1/sqrt rate)*exp (-t^2/2) := by
  rw [gaussian_real_eq_integral]
  have hi := integrable_gaussianPDFReal (μ := 0) (v := 1)
  have hc : IntegrableOn (fun _ : ℝ => gaussianPDFReal 0 1 t) (Ico t (t+1/sqrt rate)) :=
    integrableOn_const (by rw [volume_Ico];exact ENNReal.ofReal_ne_top)
  have h := setIntegral_mono_on hi.integrableOn hc measurableSet_Ico
    (fun x hx => gaussianPDF_antitone_nonneg ht hx.1)
  rw [setIntegral_const,measureReal_def,volume_Ico] at h
  simp only [add_sub_cancel_left,ENNReal.toReal_ofReal (by positivity : 0≤1/sqrt rate),smul_eq_mul] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hpi : 1≤sqrt (2*π) := one_le_sqrt.mpr (by have hh := pi_gt_three;linarith)
  simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero]
  exact mul_le_of_le_one_left (exp_pos _).le (inv_le_one_of_one_le₀ hpi)

end
end PaperC.V282.PoissonQuantitativeTailCutoff
