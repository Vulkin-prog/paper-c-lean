import PaperCV282.RarePrefixMass
import PaperCV282.CrossoverSparseWeights

/-! # The common rare scale: exact border mass plus exact contained bulk intensity -/
namespace PaperC.V282.CrossoverRareScale

open Filter Topology MeasureTheory InfiniteRademacher AllStartSoftPoisson
open BulkPopulation BulkMarkedGeometry CrossoverMarkedTarget CrossoverBulkAtoms
open MicroscopicNonvacancy MicroscopicBoundaryDominance CrossoverClockRecordMass
open PrimeEulerPNT LaishramUniformInput PostQuadraticLiterature

noncomputable section

/-- The denominator uses the actual finite bulk population, with both endpoints retained. -/
def rareScale (M L : ℕ) (delta : ℝ) : ℝ :=
  (borderRate L : ℝ)+(totalRate (bulkStarts M L delta) L : ℝ)

theorem borderRate_coe (L : ℕ) :
    (borderRate L : ℝ)=((2 : ℝ)⁻¹)^Nat.primeCounting L := by
  simp [borderRate,one_div,inv_pow]

theorem totalRate_bulk_eq (M L : ℕ) (delta : ℝ) :
    totalRate (bulkStarts M L delta) L=bulkRate M L delta := rfl

theorem rareScale_pos (M L : ℕ) (delta : ℝ) : 0<rareScale M L delta := by
  unfold rareScale
  exact add_pos_of_pos_of_nonneg (by exact_mod_cast borderRate_pos L) (by positivity)

/-- Relative errors of positive summands control their sum even when the mixture weights oscillate. -/
theorem sum_ratio_error_le {a b c d : ℝ} (hc : 0<c) (hd : 0<d) :
    |(a+b)/(c+d)-1|≤|a/c-1|+|b/d-1| := by
  have hs : 0<c+d := by positivity
  have he (x y : ℝ) (hy : 0<y) : |x/y-1|=|x-y|/y := by
    rw [show x/y-1=(x-y)/y by field_simp,abs_div,abs_of_pos hy]
  rw [he _ _ hs,he _ _ hc,he _ _ hd]
  have ht : |a+b-(c+d)|≤|a-c|+|b-d| := by
    rw [show a+b-(c+d)=(a-c)+(b-d) by ring]
    exact abs_add_le (a-c) (b-d)
  calc
    _ ≤ (|a-c|+|b-d|)/(c+d) := div_le_div_of_nonneg_right ht hs.le
    _ = |a-c|/(c+d)+|b-d|/(c+d) := add_div _ _ _
    _ ≤ _ := add_le_add
      (div_le_div_of_nonneg_left (abs_nonneg _) hc (by linarith))
      (div_le_div_of_nonneg_left (abs_nonneg _) hd (by linarith))

theorem sum_ratio_tendsto_one {a b c d : ℕ → ℝ}
    (hc : ∀ᶠ n in atTop,0<c n) (hd : ∀ᶠ n in atTop,0<d n)
    (ha : Tendsto (fun n=>a n/c n) atTop (𝓝 1))
    (hb : Tendsto (fun n=>b n/d n) atTop (𝓝 1)) :
    Tendsto (fun n=>(a n+b n)/(c n+d n)) atTop (𝓝 1) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _=>norm_nonneg _) ?_
    (by simpa using ((ha.sub_const 1).abs.add ((hb.sub_const 1).abs)))
  filter_upwards [hc,hd] with n hcn hdn
  simpa only [Real.norm_eq_abs] using sum_ratio_error_le (a:=a n) (b:=b n) hcn hdn

/-- A vanishing error relative to lambda remains negligible when the new denominator is at least lambda/2. -/
theorem relative_zero_of_half_le {u lambda d : ℕ → ℝ}
    (hu : ∀ᶠ n in atTop,0≤u n) (hl : ∀ᶠ n in atTop,0<lambda n)
    (hd : ∀ᶠ n in atTop,lambda n/2≤d n)
    (ht : Tendsto (fun n=>u n/lambda n) atTop (𝓝 0)) :
    Tendsto (fun n=>u n/d n) atTop (𝓝 0) := by
  apply squeeze_zero' ?_ ?_ (by simpa using ht.const_mul 2)
  · filter_upwards [hu,hl,hd] with n hn hln hdn
    exact div_nonneg hn (by linarith)
  · filter_upwards [hu,hl,hd] with n hn hln hdn
    have hdp : 0<d n := by linarith
    calc
      _ ≤ u n/(lambda n/2) := div_le_div_of_nonneg_left hn (by positivity) hdn
      _ = 2*(u n/lambda n) := by ring

theorem bulk_rate_tendsto_zero
    (sizes lengths : ℕ → ℕ) (hsizes : Tendsto sizes atTop atTop)
    (beta delta : ℝ) (hdelta : 0<delta) (hdeltaOne : delta<1)
    (hupper : ∀ᶠ n in atTop,(lengths n : ℝ)≤beta*Real.log (sizes n))
    (hpositive : ∀ᶠ n in atTop,1≤lengths n)
    (hrare : Tendsto (fun n=>(fullRate (sizes n) (lengths n) : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n=>(totalRate (bulkStarts (sizes n) (lengths n) delta) (lengths n) : ℝ))
      atTop (𝓝 0) := by
  have hr := bulkRate_ratio_tendsto_one sizes lengths hsizes beta delta hdelta hdeltaOne hupper hpositive
  have ht := hr.mul hrare
  simp only [mul_zero] at ht
  apply ht.congr'
  filter_upwards [hsizes.eventually (eventually_ge_atTop 1)] with n hn
  have hp : (fullRate (sizes n) (lengths n) : ℝ)≠0 := by
    change (sizes n : ℝ)/(2 : ℝ)^lengths n≠0
    positivity
  exact div_mul_cancel₀ _ hp

theorem full_rate_half_le_eventually
    (sizes lengths : ℕ → ℕ) (hsizes : Tendsto sizes atTop atTop)
    (beta delta : ℝ) (hdelta : 0<delta) (hdeltaOne : delta<1)
    (hupper : ∀ᶠ n in atTop,(lengths n : ℝ)≤beta*Real.log (sizes n))
    (hpositive : ∀ᶠ n in atTop,1≤lengths n) :
    ∀ᶠ n in atTop,(fullRate (sizes n) (lengths n) : ℝ)/2≤rareScale (sizes n) (lengths n) delta := by
  have hr := bulkRate_ratio_tendsto_one sizes lengths hsizes beta delta hdelta hdeltaOne hupper hpositive
  filter_upwards [hr.eventually (lt_mem_nhds (by norm_num : (1/2 : ℝ)<1)),
    hsizes.eventually (eventually_ge_atTop 1)] with n hn hs
  have hp : 0<(fullRate (sizes n) (lengths n) : ℝ) := by
    change 0<(sizes n : ℝ)/(2 : ℝ)^lengths n
    positivity
  have hb := (lt_div_iff₀ hp).mp hn
  have ha : 0≤(borderRate (lengths n) : ℝ) := by positivity
  change _≤(borderRate (lengths n) : ℝ)+(bulkRate (sizes n) (lengths n) delta : ℝ)
  linarith

theorem denominator_ratio_tendsto_one
    (hLS : UniformPrimeDivisorStatement) (hShorey : ShoreySquareProductStatement)
    (hPNT : PrimeNumberTheoremRemainder)
    (sizes lengths : ℕ → ℕ) (hsizes : Tendsto sizes atTop atTop)
    (hlengths : Tendsto lengths atTop atTop)
    (beta delta : ℝ) (hdelta : 0<delta) (hdeltaOne : delta<1)
    (hupper : ∀ᶠ n in atTop,(lengths n : ℝ)≤beta*Real.log (sizes n)) :
    Tendsto (fun n=>(microscopicProbability (lengths n)+(fullRate (sizes n) (lengths n) : ℝ))/
      rareScale (sizes n) (lengths n) delta) atTop (𝓝 1) := by
  have hq := (microscopic_probability_ratio_tendsto_one hLS hShorey hPNT).comp hlengths
  have hr := bulkRate_ratio_tendsto_one sizes lengths hsizes beta delta hdelta hdeltaOne hupper
    (hlengths.eventually (eventually_ge_atTop 1))
  have hb : Tendsto (fun n=>(fullRate (sizes n) (lengths n) : ℝ)/
      (bulkRate (sizes n) (lengths n) delta : ℝ)) atTop (𝓝 1) := by
    simpa only [inv_one,inv_div] using hr.inv₀ (by norm_num : (1 : ℝ)≠0)
  apply sum_ratio_tendsto_one (Eventually.of_forall fun n=>by exact_mod_cast borderRate_pos (lengths n)) ?_
    (by simpa only [borderRate_coe,Function.comp_def] using hq) hb
  filter_upwards [hr.eventually (lt_mem_nhds (by norm_num : (0 : ℝ)<1)),
    hsizes.eventually (eventually_ge_atTop 1)] with n hn hs
  have hp : 0<(fullRate (sizes n) (lengths n) : ℝ) := by
    change 0<(sizes n : ℝ)/(2 : ℝ)^lengths n
    positivity
  exact (div_pos_iff.mp hn).elim (fun h=>h.1) (fun h=>by linarith [h.2])

end
end PaperC.V282.CrossoverRareScale
