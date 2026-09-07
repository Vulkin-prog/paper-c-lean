import PaperCV282.MacroTransportModel
import PaperCV282.MacroscopicRetentionBounds
import PaperCV282.LogarithmicWordPowers

/-! # Density of the actual base-contained macroscopic retained population -/
namespace PaperC.V282.MacroAggregateGeometry

open Filter Topology BulkMarkedGeometry LogarithmicWordPowers

noncomputable section

/-- Both the lower spatial cutoff and the omitted terminal base window are paid explicitly. -/
theorem card_bulkStarts_ge_half_eventually (betaMax delta : ℝ)
    (hbeta : 0≤betaMax) (hdelta : delta<1) :
    ∃ Mzero : ℕ, ∀ M≥Mzero, ∀ L : ℕ,
      (L+1 : ℝ)≤betaMax*Real.log M → (M : ℝ)/2≤(bulkStarts M L delta).card := by
  have hp : Tendsto (fun M : ℕ => (M : ℝ)^(-(1-delta))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by linarith : 0<1-delta)).comp tendsto_natCast_atTop_atTop
  obtain ⟨Np,hp⟩ := eventually_atTop.1 (hp.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1/8)))
  obtain ⟨Nl,hl⟩ := polynomial_factor_le_rpow_eventually betaMax hbeta 4 1 (1/2) (by norm_num)
  refine ⟨max Np (max Nl 8),?_⟩
  intro M hM L hL
  have hMr : (8 : ℝ)≤M := by exact_mod_cast (show 8≤M by omega)
  have hpos : (0 : ℝ)<M := by positivity
  have hpow : (M : ℝ)^delta/M≤1/8 := by
    calc
      _ = (M : ℝ)^(-(1-delta)) := by rw [neg_sub,Real.rpow_sub hpos,Real.rpow_one]
      _ ≤ _ := (hp M (by omega)).le
  have hpow' := (div_le_iff₀ hpos).mp hpow
  have hceil := Nat.ceil_lt_add_one (Real.rpow_nonneg hpos.le delta)
  have hceilquarter : (⌈(M : ℝ)^delta⌉₊ : ℝ)≤(M : ℝ)/4 := by linarith
  have hlength := hl M (by omega) L (by simpa using hL)
  simp only [pow_one,abs_of_nonneg (by positivity : 0≤4*(L+1 : ℝ))] at hlength
  have hroot : (M : ℝ)^(1/2 : ℝ)≤M := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ)≤M) (by norm_num : (1/2 : ℝ)≤1)
  have hLquarter : (L : ℝ)≤(M : ℝ)/4 := by linarith
  have hLM : L≤M := by exact_mod_cast (show (L : ℝ)≤M by linarith)
  have hs : ⌈(M : ℝ)^delta⌉₊+L≤M := by
    exact_mod_cast (show (⌈(M : ℝ)^delta⌉₊ : ℝ)+(L : ℝ)≤M by linarith)
  have hsub : ⌈(M : ℝ)^delta⌉₊≤M-L+1+1 := by omega
  simp only [bulkStarts,Nat.card_Icc,Nat.cast_sub hsub,Nat.cast_add,Nat.cast_sub hLM,Nat.cast_one]
  linarith

end
end PaperC.V282.MacroAggregateGeometry
