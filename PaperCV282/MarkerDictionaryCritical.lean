import PaperCV282.MarkerDictionaryAsymptotics
import PaperCV282.DictionaryCriticalWindow

/-!
# Marker capacity in the literal growing-dictionary critical window

The threshold precedes the requested cardinality and word length. The
window is centered at log_2(N*m), exactly as in (5.3).
-/

namespace PaperC.V282.MarkerDictionaryCritical

open Filter Topology CriticalRunWindow DictionaryCriticalWindow
open MarkerDictionaryAsymptotics WordOverlapSum

noncomputable section

/-- At critical length, the explicit family has room for every requested m up to sqrt N. -/
theorem marker_capacity_critical_eventually (C : ℝ) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ m : ℝ, 1 ≤ m → m ≤ (N : ℝ)^(1/(2 : ℝ)) →
      ∀ B : ℕ, |(B : ℝ) - Real.log ((N : ℝ)*m) / Real.log 2| ≤ C →
        8 ≤ B ∧ m ≤ (2 : ℝ)^B / (32*(B : ℝ)) := by
  let K : ℝ := Real.exp (C*Real.log 2)
  have hK : 0 < K := Real.exp_pos _
  have hupper : 0 < upperConstant := lowerConstant_pos.trans lowerConstant_lt_upperConstant
  obtain ⟨Nband,hband⟩ := dictionary_critical_log_band_eventually C
  have hnatlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨Nlarge,hlarge⟩ := eventually_atTop.1
    (hnatlog.eventually (eventually_ge_atTop (8/lowerConstant)))
  have hratio : Tendsto (fun N : ℕ => Real.log N / (N : ℝ)) atTop (𝓝 0) := by
    simpa only [pow_one, one_mul, add_zero, Function.comp_def] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
        tendsto_natCast_atTop_atTop
  have hsmallLimit : Tendsto
      (fun N : ℕ => (32*K*upperConstant)*(Real.log N/(N : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using hratio.const_mul (32*K*upperConstant)
  obtain ⟨Nsmall,hsmall⟩ := eventually_atTop.1
    (hsmallLimit.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)))
  refine ⟨max Nband (max Nlarge (max Nsmall 1)), ?_⟩
  intro N hN m hm hmN B hwindow
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hmpos : 0 < m := by linarith
  obtain ⟨hBlo,hBhi⟩ := hband N (by omega) m hm hmN B hwindow
  have hlogbig := (div_le_iff₀ lowerConstant_pos).mp (hlarge N (by omega))
  have hBreal : (8 : ℝ) ≤ B := by nlinarith
  have hB : 8 ≤ B := by exact_mod_cast hBreal
  have hratioN : (32*K*upperConstant*Real.log N)/(N : ℝ) < 1 := by
    simpa only [div_eq_mul_inv, mul_assoc] using hsmall N (by omega)
  have hNK : 32*K*upperConstant*Real.log N < N := by
    simpa only [one_mul] using (div_lt_iff₀ hn).mp hratioN
  have hBK : 32*(B : ℝ)*K ≤ N := by
    have hmul := mul_le_mul_of_nonneg_left hBhi (by positivity : (0 : ℝ) ≤ 32*K)
    nlinarith
  have hrate := (dictionary_intensity_bounds hn hmpos hwindow).2
  have hrate' : (N : ℝ)*m ≤ K*(2 : ℝ)^B :=
    (div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ)^B)).mp hrate
  have hcapacity : 32*(B : ℝ)*m ≤ (2 : ℝ)^B := by
    apply (mul_le_mul_iff_right₀ hK).mp
    calc
      _ = (32*(B : ℝ)*K)*m := by ring
      _ ≤ (N : ℝ)*m := mul_le_mul_of_nonneg_right hBK hmpos.le
      _ ≤ _ := by simpa only [mul_comm K] using hrate'
  refine ⟨hB, ?_⟩
  exact (le_div_iff₀ (by positivity : (0 : ℝ) < 32*(B : ℝ))).mpr (by nlinarith)

/-- The final existence clause of Corollary 5.4 throughout the range (5.3). -/
theorem critical_subdictionary_exists_eventually (C delta : ℝ) (hdelta : 0 < delta) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ m : ℕ, 1 ≤ m →
      (m : ℝ) ≤ (N : ℝ)^((1 : ℝ)/2-delta) → ∀ B : ℕ,
      |(B : ℝ) - Real.log ((N : ℝ)*(m : ℝ)) / Real.log 2| ≤ C →
      ∃ W : Finset (Fin B → F₂), W ⊆ explicitDictionary B ∧ W.card = m ∧
        overlapWeight W = 0 := by
  obtain ⟨Nzero,hzero⟩ := marker_capacity_critical_eventually C
  refine ⟨max Nzero 1, ?_⟩
  intro N hN m hm hcard B hwindow
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hmReal : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hcard' : (m : ℝ) ≤ (N : ℝ)^(1/(2 : ℝ)) :=
    hcard.trans (Real.rpow_le_rpow_of_exponent_le hn (by linarith))
  obtain ⟨hB,hcapacity⟩ := hzero N (by omega) m hmReal hcard' B hwindow
  exact exists_subdictionary_of_card_bound hB hcapacity

end
end PaperC.V282.MarkerDictionaryCritical
