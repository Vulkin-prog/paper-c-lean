import PaperCV282.FiniteFieldTotalVariation

/-! # The overlap and residual masses of two countable probability laws -/
namespace PaperC.V282.MaximalCouplingMass

open FiniteFieldTotalVariation

noncomputable section

variable {α : Type*}

def overlap (p q : α → ℝ) (x : α) : ℝ := min (p x) (q x)

def residual (p q : α → ℝ) (x : α) : ℝ := p x-overlap p q x

theorem overlap_nonneg {p q : α → ℝ} (hp0 : ∀ x,0≤p x) (hq0 : ∀ x,0≤q x) (x : α) :
    0≤overlap p q x := le_min (hp0 x) (hq0 x)

theorem residual_nonneg (p q : α → ℝ) (x : α) : 0≤residual p q x :=
  sub_nonneg.mpr (min_le_left _ _)

theorem summable_overlap {p q : α → ℝ} (hp : Summable p)
    (hp0 : ∀ x,0≤p x) (hq0 : ∀ x,0≤q x) : Summable (overlap p q) :=
  hp.of_nonneg_of_le (overlap_nonneg hp0 hq0) (fun _ => min_le_left _ _)

theorem variation_eq_one_sub_overlap {p q : α → ℝ} (hp : HasSum p 1) (hq : HasSum q 1)
    (hp0 : ∀ x,0≤p x) (hq0 : ∀ x,0≤q x) :
    massTotalVariation p q=1-∑' x,overlap p q x := by
  have ho := summable_overlap hp.summable hp0 hq0
  have hpoint (x : α) : |p x-q x|=p x+q x-2*overlap p q x := by
    unfold overlap
    rcases le_total (p x) (q x) with h|h
    · rw [min_eq_left h,abs_of_nonpos (sub_nonpos.mpr h)]
      ring
    · rw [min_eq_right h,abs_of_nonneg (sub_nonneg.mpr h)]
      ring
  unfold massTotalVariation
  simp_rw [hpoint]
  rw [(hp.summable.add hq.summable).tsum_sub (ho.mul_left 2),
    hp.summable.tsum_add hq.summable,tsum_mul_left,hp.tsum_eq,hq.tsum_eq]
  ring

theorem hasSum_residual {p q : α → ℝ} (hp : HasSum p 1) (hq : HasSum q 1)
    (hp0 : ∀ x,0≤p x) (hq0 : ∀ x,0≤q x) :
    HasSum (residual p q) (massTotalVariation p q) := by
  rw [variation_eq_one_sub_overlap hp hq hp0 hq0]
  exact hp.sub (summable_overlap hp.summable hp0 hq0).hasSum

theorem residual_eq_zero_of_variation_zero {p q : α → ℝ} (hp : HasSum p 1) (hq : HasSum q 1)
    (hp0 : ∀ x,0≤p x) (hq0 : ∀ x,0≤q x) (hzero : massTotalVariation p q=0) (x : α) :
    residual p q x=0 := by
  have hs := hasSum_residual hp hq hp0 hq0
  have hle := hs.summable.le_tsum x (fun j _ => residual_nonneg p q j)
  rw [hs.tsum_eq,hzero] at hle
  exact le_antisymm hle (residual_nonneg p q x)

theorem residual_product_self (p q : α → ℝ) (x : α) : residual p q x*residual q p x=0 := by
  unfold residual overlap
  rcases le_total (p x) (q x) with h|h
  · simp [min_eq_left h,min_eq_right h]
  · simp [min_eq_right h,min_eq_left h]

/-- The usual diagonal overlap plus the independent product of the disjoint residuals. -/
def couplingMass (p q : α → ℝ) (z : α × α) : ℝ := by
  classical
  exact (if z.1=z.2 then overlap p q z.1 else 0)+
    residual p q z.1*residual q p z.2/massTotalVariation p q

theorem couplingMass_nonneg {p q : α → ℝ} (hp0 : ∀ x,0≤p x) (hq0 : ∀ x,0≤q x)
    (z : α × α) : 0≤couplingMass p q z := by
  classical
  unfold couplingMass
  apply add_nonneg
  · split_ifs
    · exact overlap_nonneg hp0 hq0 _
    · exact le_rfl
  · exact div_nonneg (mul_nonneg (residual_nonneg _ _ _) (residual_nonneg _ _ _))
      (massTotalVariation_nonneg _ _)

theorem couplingMass_diagonal (p q : α → ℝ) (x : α) :
    couplingMass p q (x,x)=overlap p q x := by
  classical
  simp [couplingMass,residual_product_self]

/-- Its first marginal is exactly p, including the case of identical laws. -/
theorem hasSum_couplingMass_row {p q : α → ℝ} (hp : HasSum p 1) (hq : HasSum q 1)
    (hp0 : ∀ x,0≤p x) (hq0 : ∀ x,0≤q x) (x : α) :
    HasSum (fun y => couplingMass p q (x,y)) (p x) := by
  classical
  have hr := hasSum_residual hq hp hq0 hp0
  rw [massTotalVariation_comm q p] at hr
  have hd : HasSum (fun y => if x=y then overlap p q x else 0) (overlap p q x) := by
    simpa only [eq_comm] using (hasSum_ite_eq x (overlap p q x))
  have hs := hd.add ((hr.mul_left (residual p q x)).div_const (massTotalVariation p q))
  have he : overlap p q x+residual p q x*massTotalVariation p q/massTotalVariation p q=p x := by
    by_cases hz : massTotalVariation p q=0
    · have hx := residual_eq_zero_of_variation_zero hp hq hp0 hq0 hz x
      simp only [hz,mul_zero,div_zero,add_zero]
      unfold residual at hx
      linarith
    · rw [mul_div_cancel_right₀ _ hz]
      unfold residual
      ring
  rw [he] at hs
  exact hs

theorem couplingMass_swap (p q : α → ℝ) (x y : α) :
    couplingMass p q (x,y)=couplingMass q p (y,x) := by
  classical
  unfold couplingMass overlap
  rw [massTotalVariation_comm q p]
  by_cases h : x=y
  · subst y
    simp [min_comm,mul_comm]
  · simp [h,Ne.symm h,mul_comm]

theorem hasSum_couplingMass_column {p q : α → ℝ} (hp : HasSum p 1) (hq : HasSum q 1)
    (hp0 : ∀ x,0≤p x) (hq0 : ∀ x,0≤q x) (y : α) :
    HasSum (fun x => couplingMass p q (x,y)) (q y) := by
  simp_rw [couplingMass_swap p q]
  exact hasSum_couplingMass_row hq hp hq0 hp0 y

/-- A genuine probability mass on the countable product space. -/
theorem hasSum_couplingMass {p q : α → ℝ} (hp : HasSum p 1) (hq : HasSum q 1)
    (hp0 : ∀ x,0≤p x) (hq0 : ∀ x,0≤q x) : HasSum (couplingMass p q) 1 := by
  have hs : Summable (couplingMass p q) := (summable_prod_of_nonneg (couplingMass_nonneg hp0 hq0)).mpr
    ⟨fun x => (hasSum_couplingMass_row hp hq hp0 hq0 x).summable,
      by simpa only [(hasSum_couplingMass_row hp hq hp0 hq0 _).tsum_eq] using hp.summable⟩
  have ht : (∑' z,couplingMass p q z)=1 := by
    rw [hs.tsum_prod]
    simp_rw [(hasSum_couplingMass_row hp hq hp0 hq0 _).tsum_eq]
    exact hp.tsum_eq
  exact ht ▸ hs.hasSum

end
end PaperC.V282.MaximalCouplingMass
