import PaperCPrel8.ReciprocalPivotShells
import PaperCPrel8.PivotRankinUniform

/-! # Reciprocal pivots at the actual hard saddle

A deterministic epsilon bound at scale nu=log M/V, uniform for every population
X≥M. The ordinary PNT remainder is the only literature input. No reciprocal
estimate, comparison theorem, or asymptotic remainder is assumed.
-/
namespace PaperC.Prel8.ReciprocalPivotAsymptotics
open PaperC.Prel8.ReciprocalPivotShells PaperC.Prel8.DirectedFootprint
open PaperC.Prel8.PivotRankinUniform PaperC.Prel8.OddPrimePivot PaperC.Prel8.SaddleEnvelope
open PaperC.V282.SaddleParameters PaperC.V282.SaddleScales
open PaperC.V282.PrimeEulerSaddle PaperC.V282.SaddleCutoffAdmissibility
open PaperC.V282.PrimeEulerPNT
open Set Filter Topology
noncomputable section

/-- The number of logarithmic shells costs little-o of the second scale in its logarithm. -/
theorem shell_prefactor_tendsto_zero :
    Tendsto (fun H => (Real.log (4*H)+1)/saddleNu 1 H) atTop (𝓝 0) := by
  have h := ((tendsto_const_nhds (x := Real.log 4+1)).div_atTop
    (tendsto_saddleNu_atTop (by norm_num : (0 : ℝ)<1))).add
    (tendsto_log_div_saddleNu (by norm_num : (0 : ℝ)<1))
  apply (show Tendsto (fun H => (Real.log 4+1)/saddleNu 1 H+Real.log H/saddleNu 1 H)
      atTop (𝓝 0) by simpa using h).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with H hH
  rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hH.ne']
  ring

/-- The shell prefactor is absorbed with any fixed positive second-scale margin. -/
theorem shell_prefactor_eventually (delta : ℝ) (hdelta : 0<delta) :
    ∃ Hzero : ℝ, ∀ H ≥ Hzero, Real.log (4*H)+1 ≤ delta*saddleNu 1 H := by
  have hh := shell_prefactor_tendsto_zero.eventually (gt_mem_nhds hdelta)
  have he : ∀ᶠ H : ℝ in atTop, Real.log (4*H)+1 ≤ delta*saddleNu 1 H := by
    filter_upwards [hh, (tendsto_saddleNu_atTop (by norm_num : (0 : ℝ)<1)).eventually
      (eventually_gt_atTop (0 : ℝ))] with H h hnu
    exact (div_le_iff₀ hnu).mp h.le
  exact eventually_atTop.mp he

/-- The shell band is eventually positive and entirely on the upper saddle branch. -/
theorem hard_shell_domain_eventually :
    ∃ Hzero : ℝ, ∀ H ≥ Hzero,
      1≤H ∧ 1≤saddleCutoff 1 H ∧ saddleCutoff 1 H≤H ∧
      ∀ w : ℝ, saddleCutoff 1 H ≤ w → w ≤ 4*saddleCutoff 1 H →
        0<w ∧ Real.exp 1 ≤ H/w := by
  have hsmall := (tendsto_saddleCutoff_div_height (by norm_num : (0 : ℝ)<1)).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ)<1))
  have he : ∀ᶠ H : ℝ in atTop,
      1≤H ∧ 1≤saddleCutoff 1 H ∧ saddleCutoff 1 H≤H ∧
      ∀ w : ℝ, saddleCutoff 1 H ≤ w → w ≤ 4*saddleCutoff 1 H →
        0<w ∧ Real.exp 1 ≤ H/w := by
    filter_upwards [eventually_ge_atTop (1 : ℝ), hsmall,
      (tendsto_saddleCutoff_atTop (by norm_num : (0 : ℝ)<1)).eventually (eventually_ge_atTop (1 : ℝ)),
      (tendsto_saddleNu_atTop (by norm_num : (0 : ℝ)<1)).eventually (eventually_ge_atTop (4*Real.exp 1))]
      with H hH hsmall hV hnu
    have hVp : 0<saddleCutoff 1 H := by linarith
    have hVH : saddleCutoff 1 H≤H := by
      have h := (div_le_iff₀ (by linarith : 0<H)).mp hsmall.le
      simpa using h
    refine ⟨hH,hV,hVH,?_⟩
    intro w hwlo hwhi
    have hw : 0<w := hVp.trans_le hwlo
    refine ⟨hw, (le_div_iff₀ hw).mpr ?_⟩
    have hnu' := (le_div_iff₀ hVp).mp hnu
    have hp := mul_le_mul_of_nonneg_left hwhi (Real.exp_pos 1).le
    nlinarith
  exact eventually_atTop.mp he

/-- Explicit absorption of a finite shell sum and its large-pivot tail. -/
theorem absorb_shell_bound {S H V nu epsilon : ℝ} {X K : ℕ}
    (hH : 0<H) (_hV : 0≤V) (hnu : 0≤nu) (hepsilon : 0≤epsilon)
    (hKlo : 2*V≤K) (hKhi : (K : ℝ)+1≤4*H)
    (hprefactor : Real.log (4*H)+1≤(epsilon/2)*nu)
    (hS : S≤X*((K : ℝ)*Real.exp (1-2*V+(epsilon/2)*nu)+Real.exp (-(V+K)))) :
    S≤X*Real.exp (-2*V+epsilon*nu) := by
  have htail : Real.exp (-(V+K)) ≤ Real.exp (1-2*V+(epsilon/2)*nu) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hepsilon hnu]
  calc
    _ ≤ _ := hS
    _ ≤ X*(((K : ℝ)+1)*Real.exp (1-2*V+(epsilon/2)*nu)) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg X)
      nlinarith
    _ ≤ X*((4*H)*Real.exp (1-2*V+(epsilon/2)*nu)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hKhi (Real.exp_pos _).le) (Nat.cast_nonneg X)
    _ = X*Real.exp (Real.log (4*H)+(1-2*V+(epsilon/2)*nu)) := by
      simp only [Real.exp_add, Real.exp_log (by positivity : 0<4*H)]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (Nat.cast_nonneg X)

/-- F.5 for the actual enlarged support, uniformly for every X≥M and every positive error margin. -/
theorem reciprocal_pivots_hard_bound (hPNT : PrimeNumberTheoremRemainder)
    (epsilon : ℝ) (hepsilon : 0<epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ X ≥ M,
      reciprocalPivots X ⌊Real.exp (saddleCutoff 1 (Real.log M))⌋₊ ≤
        X*Real.exp (-2*saddleCutoff 1 (Real.log M)+epsilon*saddleNu 1 (Real.log M)) := by
  obtain ⟨Mcount,hcount⟩ := hard_band_count hPNT (epsilon/4) (by positivity)
  obtain ⟨Henv,henv⟩ := hard_envelope_eventually (epsilon/4) (by positivity)
  obtain ⟨Hdomain,hdomain⟩ := hard_shell_domain_eventually
  obtain ⟨Hprefactor,hprefactor⟩ := shell_prefactor_eventually (epsilon/2) (by positivity)
  have hnatlog : Tendsto (fun M : ℕ => Real.log M) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hevent : ∀ᶠ M : ℕ in atTop, ∀ X ≥ M,
      reciprocalPivots X ⌊Real.exp (saddleCutoff 1 (Real.log M))⌋₊ ≤
        X*Real.exp (-2*saddleCutoff 1 (Real.log M)+epsilon*saddleNu 1 (Real.log M)) := by
    filter_upwards [eventually_ge_atTop Mcount,
      hnatlog.eventually (eventually_ge_atTop (max Henv (max Hdomain Hprefactor)))] with M hM hH
    intro X hMX
    let H := Real.log M
    let V := saddleCutoff 1 H
    let nu := saddleNu 1 H
    let K := ⌈2*V⌉₊
    obtain ⟨hHone,hVone,hVH,hdom⟩ := hdomain H (by dsimp [H]; order)
    have hVp : 0<V := by dsimp [V]; linarith
    have hnup : 0<nu := div_pos (by linarith : 0<H) hVp
    have hKlo : 2*V≤(K : ℝ) := Nat.le_ceil _
    have hKhi : (K : ℝ)<2*V+1 := Nat.ceil_lt_add_one (by positivity : 0≤2*V)
    have hband (i : ℕ) (hi : i ∈ Finset.range K) : V≤V+i+1 ∧ V+i+1≤4*V := by
      have hiK : (i : ℝ)+1≤K := by exact_mod_cast Nat.succ_le_iff.mpr (Finset.mem_range.mp hi)
      have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg _
      dsimp [V] at *
      constructor <;> linarith
    have hs := reciprocalTail_of_uniform_bounds X K V H nu (epsilon/4) (epsilon/4)
      (fun i hi => hcount M hM X hMX (V+i+1) (hband i hi).1 (hband i hi).2)
      (fun i hi => henv H (by dsimp [H]; order) (V+i+1)
        (hdom _ (hband i hi).1 (hband i hi).2).1
        (hdom _ (hband i hi).1 (hband i hi).2).2)
    have hs' : reciprocalPivots X ⌊Real.exp V⌋₊ ≤
        X*((K : ℝ)*Real.exp (1-2*V+(epsilon/2)*nu)+Real.exp (-(V+K))) := by
      have heps : epsilon/4+epsilon/4=epsilon/2 := by ring
      simpa only [heps] using hs
    exact absorb_shell_bound (by linarith) hVp.le hnup.le hepsilon.le hKlo
      (by dsimp [V] at *; linarith) (hprefactor H (by dsimp [H]; order)) hs'
  exact eventually_atTop.mp hevent

/-- Enlarging the counted population can only increase its actual reciprocal tail. -/
theorem reciprocalPivots_mono_population {X Z Y : ℕ} (hXZ : X≤Z) :
    reciprocalPivots X Y ≤ reciprocalPivots Z Y := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro m hm
    obtain ⟨hm,hy⟩ := Finset.mem_filter.mp hm
    have hm := Finset.mem_Icc.mp hm
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hm.1,hm.2.trans hXZ⟩,hy⟩
  · intro m _ _
    positivity

/-- Full nearby-ceiling form of F.5; the uniform range 2X≥M includes X=M+O(log M). -/
theorem reciprocal_pivots_nearby_bound (hPNT : PrimeNumberTheoremRemainder)
    (epsilon : ℝ) (hepsilon : 0<epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ X : ℕ, M≤2*X →
      reciprocalPivots X ⌊Real.exp (saddleCutoff 1 (Real.log M))⌋₊ ≤
        X*Real.exp (-2*saddleCutoff 1 (Real.log M)+epsilon*saddleNu 1 (Real.log M)) := by
  obtain ⟨Mcount,hcount⟩ := reciprocal_pivots_hard_bound hPNT (epsilon/2) (by positivity)
  have hnatlog : Tendsto (fun M : ℕ => Real.log M) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hgrowth := ((tendsto_saddleNu_atTop (by norm_num : (0 : ℝ)<1)).const_mul_atTop
    (by positivity : 0<epsilon/2)).comp hnatlog
  have hevent : ∀ᶠ M : ℕ in atTop, ∀ X : ℕ, M≤2*X →
      reciprocalPivots X ⌊Real.exp (saddleCutoff 1 (Real.log M))⌋₊ ≤
        X*Real.exp (-2*saddleCutoff 1 (Real.log M)+epsilon*saddleNu 1 (Real.log M)) := by
    filter_upwards [eventually_ge_atTop Mcount, hgrowth.eventually (eventually_ge_atTop (Real.log 2))]
      with M hM hfactor
    intro X hMX
    let V := saddleCutoff 1 (Real.log M)
    let nu := saddleNu 1 (Real.log M)
    have htwo : (2 : ℝ)≤Real.exp ((epsilon/2)*nu) := by
      calc
        2 = Real.exp (Real.log 2) := (Real.exp_log (by norm_num : (0 : ℝ)<2)).symm
        _ ≤ _ := Real.exp_le_exp.mpr hfactor
    have hmax : ((max M X : ℕ) : ℝ)≤2*X := by
      exact_mod_cast (show max M X≤2*X by omega)
    calc
      _ ≤ reciprocalPivots (max M X) ⌊Real.exp V⌋₊ := reciprocalPivots_mono_population (le_max_right _ _)
      _ ≤ (max M X : ℕ)*Real.exp (-2*V+(epsilon/2)*nu) := hcount M hM _ (le_max_left _ _)
      _ ≤ (2*X)*Real.exp (-2*V+(epsilon/2)*nu) := mul_le_mul_of_nonneg_right hmax (Real.exp_pos _).le
      _ = X*(2*Real.exp (-2*V+(epsilon/2)*nu)) := by ring
      _ ≤ X*(Real.exp ((epsilon/2)*nu)*Real.exp (-2*V+(epsilon/2)*nu)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le) (Nat.cast_nonneg X)
      _ = _ := by rw [← Real.exp_add]; congr 2; ring
  exact eventually_atTop.mp hevent

/-- The actual directed footprint now inherits the proved reciprocal exponential estimate. -/
theorem directed_footprint_hard_bound (hPNT : PrimeNumberTheoremRemainder)
    (epsilon : ℝ) (hepsilon : 0<epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ C n Q : ℕ, M≤2*(n+Q) →
      ∀ (G : Finset ℕ) (q : ℕ → Fin (Q+1) → PrimeUpTo C),
      G ⊆ Finset.Icc 1 n →
      (∀ j ∈ G, ∀ a : Fin (Q+1), (q j a).val.val=largestOddPrime (j+a.val)) →
      (∀ j ∈ G, ∀ a : Fin (Q+1), ⌊Real.exp (saddleCutoff 1 (Real.log M))⌋₊<largestOddPrime (j+a.val)) →
      (∑ j ∈ G, ((PrimeForcing.directedFootprint G Q (q j)).card : ℝ)) ≤
        (n : ℝ)*(Q+1 : ℝ)^2*(1+(n+Q : ℕ)*
          Real.exp (-2*saddleCutoff 1 (Real.log M)+epsilon*saddleNu 1 (Real.log M))) := by
  obtain ⟨Mzero,h⟩ := reciprocal_pivots_nearby_bound hPNT epsilon hepsilon
  refine ⟨Mzero, ?_⟩
  intro M hM C n Q hpop G q hG hq hgood
  have hfinite := total_footprint_le G n Q ⌊Real.exp (saddleCutoff 1 (Real.log M))⌋₊ q hG hq hgood
  exact hfinite.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl (h M hM (n+Q) hpop)) (by positivity))

end
end PaperC.Prel8.ReciprocalPivotAsymptotics
