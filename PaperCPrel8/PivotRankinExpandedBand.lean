import PaperCPrel8.PivotRankinUniform
import PaperCV282.PrimeEulerSaddle

/-! # F.3 on the literal expanded band, uniformly in nearby population ceilings -/
namespace PaperC.Prel8.PivotRankinExpandedBand
open PaperC.Prel8.PivotRankinUniform PaperC.Prel8.OddPrimePivot
open PaperC.V282.SaddleParameters PaperC.V282.SaddleScales
open PaperC.V282.PrimeEulerSaddle PaperC.V282.SaddleCutoffAdmissibility
open PaperC.V282.PrimeEulerPNT
open Set Filter Topology
noncomputable section

/-- Population monotonicity of the actual odd-pivot counting set. -/
theorem pivotValues_mono_population {X Z Y : ℕ} (hXZ : X ≤ Z) :
    pivotValues X Y ⊆ pivotValues Z Y := by
  intro m hm
  simp only [pivotValues, Finset.mem_filter, Finset.mem_Icc] at hm ⊢
  exact ⟨⟨hm.1.1, hm.1.2.trans hXZ⟩, hm.2⟩

/-- The paper's `V-2..3V+2` band and all ceilings with `M≤2X`, with a uniform second-scale error. -/
theorem expanded_band_count (hPNT : PrimeNumberTheoremRemainder)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ X : ℕ, M ≤ 2*X → ∀ w : ℝ,
      saddleCutoff 1 (Real.log M)-2 ≤ w → w ≤ 3*saddleCutoff 1 (Real.log M)+2 →
      ((pivotValues X ⌊Real.exp w⌋₊).card : ℝ) ≤
        X * Real.exp (-saddleCost (Real.log M/w)+epsilon*saddleNu 1 (Real.log M)) := by
  obtain ⟨c,K,hc,hK,Hband,hband⟩ := saddleCutoff_sqrt_log_band_eventually (by norm_num : (0:ℝ)<1)
  obtain ⟨Mcount,hcount⟩ := enlarged_population_rankin hPNT (c/2) (4*K) (epsilon/4)
    (by positivity) (by positivity) (by positivity)
  have hnatlog : Tendsto (fun M : ℕ => Real.log M) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hevent : ∀ᶠ M : ℕ in atTop, ∀ X : ℕ, M ≤ 2*X → ∀ w : ℝ,
      saddleCutoff 1 (Real.log M)-2 ≤ w → w ≤ 3*saddleCutoff 1 (Real.log M)+2 →
      ((pivotValues X ⌊Real.exp w⌋₊).card : ℝ) ≤
        X * Real.exp (-saddleCost (Real.log M/w)+epsilon*saddleNu 1 (Real.log M)) := by
    filter_upwards [eventually_ge_atTop (max Mcount 2),
      hnatlog.eventually (eventually_ge_atTop Hband),
      hnatlog.eventually ((tendsto_saddleCutoff_atTop (by norm_num : (0:ℝ)<1)).eventually
        (eventually_ge_atTop (4:ℝ))),
      hnatlog.eventually ((tendsto_saddleNu_atTop (by norm_num : (0:ℝ)<1)).eventually
        (eventually_ge_atTop (2*Real.log 2/epsilon)))] with M hM hH hV hnu
    intro X hMX w hwlo hwhi
    obtain ⟨hVlo,hVhi⟩ := hband (Real.log M) hH
    have hw : 0 < w := by linarith
    have hVp : 0 < saddleCutoff 1 (Real.log M) := by linarith
    have hhalf : saddleCutoff 1 (Real.log M)/2 ≤ w := by linarith
    have hfour : w ≤ 4*saddleCutoff 1 (Real.log M) := by linarith
    have hlo : c/2*Real.sqrt (Real.log M*Real.log (Real.log M)) ≤ w := by nlinarith
    have hhi : w ≤ (4*K)*Real.sqrt (Real.log M*Real.log (Real.log M)) := by nlinarith
    have hr := hcount M (by omega) (max M X) (le_max_left _ _) w hlo hhi
    have hmaxpos : (0:ℝ) < (max M X : ℕ) := by exact_mod_cast (show 0 < max M X by omega)
    have hraw := (div_le_iff₀ hmaxpos).mp hr
    have hratio : Real.log M/w ≤ 2*saddleNu 1 (Real.log M) := by
      have hlog : 0 ≤ Real.log M := Real.log_nonneg (by exact_mod_cast (show 1≤M by omega))
      have hh := div_le_div_of_nonneg_left hlog (by positivity : 0<saddleCutoff 1 (Real.log M)/2) hhalf
      convert hh using 1
      unfold saddleNu
      ring
    have hlog2 : Real.log 2 ≤ (epsilon/2)*saddleNu 1 (Real.log M) := by
      have hh := (div_le_iff₀ hepsilon).mp hnu
      nlinarith
    have hmono : ((pivotValues X ⌊Real.exp w⌋₊).card : ℝ) ≤
        ((pivotValues (max M X) ⌊Real.exp w⌋₊).card : ℝ) := by
      exact_mod_cast Finset.card_le_card (pivotValues_mono_population (le_max_right M X))
    have hpop : ((max M X : ℕ) : ℝ) ≤ 2*X := by
      exact_mod_cast (show max M X ≤ 2*X by omega)
    calc
      _ ≤ _ := hmono
      _ ≤ Real.exp (-saddleCost (Real.log M/w)+(epsilon/4)*(Real.log M/w)) * (max M X : ℕ) := hraw
      _ ≤ Real.exp (-saddleCost (Real.log M/w)+(epsilon/4)*(Real.log M/w)) * (2*X) := by gcongr
      _ = (X:ℝ) * Real.exp (Real.log 2 + (-saddleCost (Real.log M/w)+(epsilon/4)*(Real.log M/w))) := by
        simp only [Real.exp_add, Real.exp_log (by norm_num : (0:ℝ)<2)]
        ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg X)
        apply Real.exp_le_exp.mpr
        nlinarith
  exact eventually_atTop.mp hevent

end
end PaperC.Prel8.PivotRankinExpandedBand
