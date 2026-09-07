import PaperCV282.MacroscopicAlignedRunge

/-!
# Hamming budgets at every fixed positive component density

The same radius works for m >= B/D for every fixed positive D. Only
the eventual threshold changes. This removes the historical one-sixteenth
restriction without assuming a short kernel word.
-/

namespace PaperC.V282.DensityHammingBudget

open TheoremEightHammingBudget MacroscopicAlignedRunge

noncomputable section

/-- The radius times log B has arbitrarily small fixed linear density. -/
theorem radius_mul_log_density {B D : ℕ}
    (hbase : 16384 ≤ Nat.log 2 (Nat.log 2 B))
    (hscale : 65 * D ≤ Nat.log 2 (Nat.log 2 B)) :
    D * (componentHammingRadius B * Nat.log 2 B) ≤ B := by
  have hellpos : 0 < Nat.log 2 (Nat.log 2 B) := by omega
  have hLpos : 0 < Nat.log 2 B := by
    have := (Nat.log_pos_iff.mp hellpos).1
    omega
  have hden : (0 : ℝ) < (Nat.log 2 B : ℝ) * (Nat.log 2 (Nat.log 2 B) : ℝ) := by
    exact mul_pos (by exact_mod_cast hLpos) (by exact_mod_cast hellpos)
  have h := (le_div_iff₀ hden).mp (componentHammingRadius_cast_le hbase)
  have hs : (65 : ℝ) * D ≤ (Nat.log 2 (Nat.log 2 B) : ℝ) := by exact_mod_cast hscale
  have hmul := mul_le_mul_of_nonneg_left hs
    (show 0 ≤ (componentHammingRadius B : ℝ) * (Nat.log 2 B : ℝ) by positivity)
  have hr : (D : ℝ) * ((componentHammingRadius B : ℝ) * (Nat.log 2 B : ℝ)) ≤ B := by
    nlinarith
  exact_mod_cast hr

/-- An explicit Hamming volume estimate independent of the desired density. -/
theorem volume_le_radius_log {B : ℕ}
    (hbase : 16384 ≤ Nat.log 2 (Nat.log 2 B)) :
    2 * componentHammingRadius B *
        2 ^ ((PrimesUpTo.count B + 2) / componentHammingRadius B + 1) ≤
      8 * (componentHammingRadius B * Nat.log 2 B) := by
  let t := componentHammingRadius B
  let ell := Nat.log 2 (Nat.log 2 B)
  have ht : 64 ≤ t := sixty_four_le_componentHammingRadius hbase
  have hr := primeRows_le_radius_mul_loglog hbase
  have hplus : PrimesUpTo.count B + 2 ≤ t * (ell + 1) := by
    dsimp [t, ell] at *
    nlinarith
  have hdiv : (PrimesUpTo.count B + 2) / t ≤ ell + 1 :=
    Nat.div_le_of_le_mul (by simpa [Nat.mul_comm] using hplus)
  have hLne : Nat.log 2 B ≠ 0 := by
    intro h
    simp [h] at hbase
  have hpow : 2 ^ ((PrimesUpTo.count B + 2) / t + 1) ≤ 4 * Nat.log 2 B := by
    calc
      _ ≤ 2 ^ (ell + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 4 * 2 ^ ell := by rw [pow_add]; norm_num; ring
      _ ≤ _ := Nat.mul_le_mul_left 4 (Nat.pow_log_le_self 2 hLne)
  calc
    _ ≤ 2 * t * (4 * Nat.log 2 B) := Nat.mul_le_mul_left (2 * t) hpow
    _ = _ := by dsimp [t]; ring

/-- A Hamming volume bound also pays its own row and radius conditions. -/
theorem rows_le_hamming_volume (r t : ℕ) (ht : 0 < t) :
    r ≤ 2 * t * 2 ^ (r / t + 1) := by
  calc
    r ≤ (r / t + 1) * t := by simpa [Nat.mul_comm] using (Nat.lt_mul_div_succ r ht).le
    _ ≤ 2 ^ (r / t + 1) * t :=
      Nat.mul_le_mul_right t (Nat.lt_two_pow_self.le)
    _ = t * 2 ^ (r / t + 1) := Nat.mul_comm _ _
    _ ≤ 2 * (t * 2 ^ (r / t + 1)) := by omega
    _ = _ := by ring

/-- All finite Hamming hypotheses for any fixed positive denominator. -/
theorem conditions_of_loglog {B D m : ℕ} (hD : 0 < D)
    (hbase : 16384 ≤ Nat.log 2 (Nat.log 2 B))
    (hscale : 520 * D ≤ Nat.log 2 (Nat.log 2 B)) (hm : B / D ≤ m) :
    1 ≤ componentHammingRadius B ∧ 2 * componentHammingRadius B ≤ m ∧
      PrimesUpTo.count B + 2 ≤ m ∧
      2 * componentHammingRadius B *
        2 ^ ((PrimesUpTo.count B + 2) / componentHammingRadius B + 1) ≤ m := by
  have ht := sixty_four_le_componentHammingRadius hbase
  have hb := radius_mul_log_density (D := 8 * D) hbase (by convert hscale using 1; ring)
  have hv := volume_le_radius_log hbase
  have hlarge : 2 * componentHammingRadius B *
      2 ^ ((PrimesUpTo.count B + 2) / componentHammingRadius B + 1) ≤ m := by
    apply le_trans _ hm
    apply (Nat.le_div_iff_mul_le hD).mpr
    calc
      _ ≤ (8 * (componentHammingRadius B * Nat.log 2 B)) * D :=
        Nat.mul_le_mul_right D hv
      _ = (8 * D) * (componentHammingRadius B * Nat.log 2 B) := by ring
      _ ≤ _ := hb
  have htwo : 2 * componentHammingRadius B ≤ m :=
    (Nat.le_mul_of_pos_right _ (by positivity)).trans hlarge
  exact ⟨by omega, htwo,
    (rows_le_hamming_volume (PrimesUpTo.count B + 2) _ (by omega)).trans hlarge,
    hlarge⟩

/-- Every positive logarithmic band reaches the density-dependent threshold. -/
theorem conditions_eventually (D : ℕ) (hD : 0 < D) (betaMin : ℝ) (hmin : 0 < betaMin) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ B : ℕ,
      betaMin * Real.log M ≤ (B : ℝ) →
      64 ≤ B ∧
      (componentHammingRadius B : ℝ) ≤
        65 * (B : ℝ) / (Real.log B * Real.log (Real.log B)) ∧
      ∀ m : ℕ, B / D ≤ m →
        1 ≤ componentHammingRadius B ∧ 2 * componentHammingRadius B ≤ m ∧
        PrimesUpTo.count B + 2 ≤ m ∧
        2 * componentHammingRadius B *
          2 ^ ((PrimesUpTo.count B + 2) / componentHammingRadius B + 1) ≤ m := by
  let T := max 16384 (520 * D)
  obtain ⟨Mzero, hheight⟩ := height_ge_eventually betaMin hmin (max 64 (2 ^ (2 ^ T)))
  refine ⟨Mzero, ?_⟩
  intro M hM B hB
  have hh := hheight M hM B hB
  have hpow : 2 ^ (2 ^ T) ≤ B := (le_max_right _ _).trans hh
  have hlog := Nat.le_log_of_pow_le Nat.one_lt_two hpow
  have hll : T ≤ Nat.log 2 (Nat.log 2 B) :=
    Nat.le_log_of_pow_le Nat.one_lt_two hlog
  have hbase : 16384 ≤ Nat.log 2 (Nat.log 2 B) := (le_max_left _ _).trans hll
  have hscale : 520 * D ≤ Nat.log 2 (Nat.log 2 B) := (le_max_right _ _).trans hll
  exact ⟨(le_max_left _ _).trans hh,
    TheoremEightAlignedClosure.componentHammingRadius_cast_le_real_log hbase,
    fun m hm => conditions_of_loglog hD hbase hscale hm⟩

end
end PaperC.V282.DensityHammingBudget
