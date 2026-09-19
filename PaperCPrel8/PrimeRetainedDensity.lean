import PaperCPrel8.PrimeWindowGeometry
import PaperCPrel8.ArithmeticLowMarginals

/-! # The G.9 omission hypothesis for both named retained sets -/
namespace PaperC.Prel8.PrimeRetainedDensity
open Finset Filter Topology PrimeWindowScales PrimeWindowErrors PrimeWindowBudget PrimeWindowGeometry
open StrongerDeletionTheorem RoughKernelDeletion RoughKernelGoodSet RoughKernelDeletionLimits
open MicroscopicGoodField ArithmeticLowMarginals ActualSignedPalm
open V282.PrimeEulerPNT V282.SaddleParameters V282.SaddleScales
noncomputable section

def retained (q : ℕ) (theta : ℝ) : Finset ℕ := strongerGood (window q) (q-1) 0 theta
def original (q : ℕ) : Finset ℕ := originalGood (window q) (q-1) 0

theorem retained_subset_original (q : ℕ) (theta : ℝ) : retained q theta⊆original q :=
  strongGood_subset _ _ _ _

theorem original_subset (q : ℕ) : original q⊆Icc 1 (window q-(q-1)) := goodSites_subset _ _ _ _ _

theorem retained_subset (q : ℕ) (theta : ℝ) : retained q theta⊆Icc 1 (window q-(q-1)) :=
  (retained_subset_original q theta).trans (original_subset q)

theorem retained_geometry (theta : ℝ) : ∀ᶠ q : ℕ in atTop,
    GoodGeometry (cylinder q) (MicroscopicActualGeometry.primeCutoff (window q)) (q-1) (excess q)
      (retained q theta) := by
  filter_upwards [original_geometry] with q hq
  exact geometry_subset hq (retained_subset_original q theta)

/-- Passing from the physical interior interval to [1,M] adds exactly the final L sites. -/
theorem full_omission_eq {M L : ℕ} (hL : L≤M) {G : Finset ℕ} (hG : G⊆Icc 1 (M-L)) :
    ((Icc 1 M)\G).card=((Icc 1 (M-L))\G).card+L := by
  have hgM : G⊆Icc 1 M := hG.trans (Icc_subset_Icc_right (Nat.sub_le _ _))
  have hgcard := card_le_card hG
  rw [card_sdiff_of_subset hgM,card_sdiff_of_subset hG]
  simp only [Nat.card_Icc] at hgcard ⊢
  omega

/-- Literal G_theta omissions are o(M/log M), including the terminal L sites. -/
theorem retained_density (hPNT : PrimeNumberTheoremRemainder) {theta : ℝ} (htheta : 0≤theta) :
    Tendsto (fun q ↦ (((Icc 1 (window q))\retained q theta).card:ℝ)*
      Real.log (window q)/(window q:ℝ)) atTop (𝓝 0) := by
  obtain ⟨M0,hM⟩ := paper_counts hPNT betaMin betaMax theta (theta+1)
    band_constants.1 band_constants.2 htheta (by linarith)
  have he := ((shallow_density_tendsto.comp window_tendsto).add
    ((height_exponential_tendsto (theta+1)).comp log_window_atTop)).add log_mul_prime_div_window
  apply squeeze_zero' (Eventually.of_forall (fun q ↦ by
    apply div_nonneg _ (by positivity)
    exact mul_nonneg (by positivity) (Real.log_nonneg (by exact_mod_cast (window_pos q))))) _
    (show Tendsto (fun q ↦ (⌈Real.sqrt (window q)⌉₊:ℝ)/(window q:ℝ)*Real.log (window q)+
      Real.log (window q)*Real.exp (-saddleCutoff 1 (Real.log (window q))+
        (theta+1)*saddleNu 1 (Real.log (window q)))+
      Real.log (window q)*(q:ℝ)/(window q:ℝ)) atTop (𝓝 0) by simpa only [Function.comp_def,add_zero] using he)
  filter_upwards [scalar_regime (theta+1),window_tendsto.eventually (eventually_ge_atTop M0),
    eventually_ge_atTop 1] with q hq hM0 hq1
  have hc := (hM (window q) hM0 (q-1) 0 (by exact_mod_cast hq.1) (by exact_mod_cast hq.2.1)
    hq.2.2.1 hq.2.2.2.1 hq.2.2.2.2).2
  have heq := full_omission_eq ((Nat.sub_le q 1).trans (prime_le_window hq1)) (retained_subset q theta)
  have hcount : (((Icc 1 (window q))\retained q theta).card:ℝ)≤
      (⌈Real.sqrt (window q)⌉₊:ℝ)+(window q:ℝ)*Real.exp
        (-saddleCutoff 1 (Real.log (window q))+(theta+1)*saddleNu 1 (Real.log (window q)))+q := by
    rw [heq,Nat.cast_add]
    have hlen : ((q-1:ℕ):ℝ)≤q := by exact_mod_cast Nat.sub_le q 1
    change (((Icc 1 (window q-(q-1)))\retained q theta).card:ℝ) ≤ _ at hc
    linarith
  have hH : 0≤Real.log (window q) := Real.log_nonneg (by exact_mod_cast (window_pos q))
  have hw : (window q:ℝ)≠0 := by exact_mod_cast (window_pos q).ne'
  have hh := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcount hH)
    (show (0:ℝ)≤window q by positivity)
  convert hh using 1
  field_simp

/-- G0 omits no more sites than any stronger G_theta. -/
theorem original_density (hPNT : PrimeNumberTheoremRemainder) :
    Tendsto (fun q ↦ (((Icc 1 (window q))\original q).card:ℝ)*
      Real.log (window q)/(window q:ℝ)) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun q ↦ by
    apply div_nonneg _ (by positivity)
    exact mul_nonneg (by positivity) (Real.log_nonneg (by exact_mod_cast (window_pos q))))) _
      (retained_density hPNT (theta:=0) (by norm_num))
  apply Eventually.of_forall
  intro q
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (Real.log_nonneg (by exact_mod_cast (window_pos q)))
  have hs : (Icc 1 (window q))\original q⊆(Icc 1 (window q))\retained q 0 := by
    intro j hj
    exact mem_sdiff.mpr ⟨(mem_sdiff.mp hj).1,fun ht ↦ (mem_sdiff.mp hj).2 (retained_subset_original q 0 ht)⟩
  exact_mod_cast card_le_card hs

end
end PaperC.Prel8.PrimeRetainedDensity
