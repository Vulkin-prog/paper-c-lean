import PaperCV282.DeepStartEvents
import PaperCV282.PostQuadraticDecay

/-! # Mesoscopic cutoffs with an artificial upper ambient scale -/
namespace PaperC.V282.MesoscopicCutoff

open Filter MeasureTheory InfiniteRademacher InfiniteStartProbabilityTransfer
open DeepStartEvents PostQuadraticLiterature BalasubramanianShoreyInput PostQuadraticDecay
open scoped Topology

noncomputable section

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

local instance instProbabilityInfiniteRademacher : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

/-- Equation (7.9), with the stronger single-box exceptional term.
No dyadic lower endpoint is required to be comparable with 2^L. -/
theorem equation_seven_nine (hShorey : ShoreySquareProductStatement)
    (hPNT : PrimeEulerPNT.PrimeNumberTheoremRemainder)
    (hNR : PellInput.NicolasRobinDivisorLogBoundStatement) :
    ∃ theta K : ℝ, 0 ≤ K ∧ ∃ Lzero : ℕ, ∀ L ≥ Lzero, ∀ T : ℕ, T ≤ 2 ^ L →
      infiniteRademacherMeasure.real (⋃ x ∈ Finset.Ioc (2 * L ^ 2) T, infiniteStartEvent x L) ≤
        (T : ℝ) / (2 : ℝ) ^ L +
        Real.exp (K * ((L : ℝ) / Real.log L)) * (2 : ℝ) ^ (-gap (L + 1) theta) := by
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  obtain ⟨theta, K, hK, Mzero, h⟩ := integer_cutoff_bound_eventually
    (1 / (2 * Real.log 2)) (2 / Real.log 2) (by positivity)
    (by apply (div_lt_div_iff₀ (by positivity) hlog).mpr; nlinarith)
    hShorey hPNT hNR
  refine ⟨theta, K, hK, max Mzero 1, ?_⟩
  intro L hL T hT
  have hLM : L ≤ 2 ^ L := (Nat.lt_two_pow_self).le
  have hlogM : Real.log ((2 ^ L : ℕ) : ℝ) = (L : ℝ) * Real.log 2 := by
    simp only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  have hlow : 1 / (2 * Real.log 2) * Real.log ((2 ^ L : ℕ) : ℝ) ≤ (L + 1 : ℕ) := by
    rw [hlogM]
    have he : 1 / (2 * Real.log 2) * ((L : ℝ) * Real.log 2) = (L : ℝ) / 2 := by field_simp
    rw [he]
    push_cast
    linarith [show 0 ≤ (L : ℝ) by positivity]
  have hupper : ((L + 1 : ℕ) : ℝ) ≤ 2 / Real.log 2 * Real.log ((2 ^ L : ℕ) : ℝ) := by
    rw [hlogM]
    have he : 2 / Real.log 2 * ((L : ℝ) * Real.log 2) = 2 * (L : ℝ) := by field_simp
    rw [he]
    exact_mod_cast (show L + 1 ≤ 2 * L by omega)
  exact h (2 ^ L) (by omega) L hlow hupper T (by omega)

/-- The real critical cutoff scale is exactly 2^L times the border probability. -/
theorem cutoff_scale_eq (L : ℕ) :
    (2 : ℝ) ^ ((L : ℝ) - (Nat.primeCounting L : ℝ)) =
      (2 : ℝ) ^ L * ((2 : ℝ)⁻¹) ^ Nat.primeCounting L := by
  rw [Real.rpow_sub (by norm_num), Real.rpow_natCast, Real.rpow_natCast, inv_pow, div_eq_mul_inv]

/-- The additional-start probability is negligible relative to the exact border mass
whenever the free integer cutoff is o(2^(L-pi(L))). -/
theorem cutoff_probability_negligible (hShorey : ShoreySquareProductStatement)
    (hPNT : PrimeEulerPNT.PrimeNumberTheoremRemainder)
    (hNR : PellInput.NicolasRobinDivisorLogBoundStatement)
    (cutoffs : ℕ → ℕ)
    (hcutoff : ∀ᶠ L : ℕ in atTop, cutoffs L ≤ 2 ^ L)
    (hsmall : Tendsto (fun L : ℕ => (cutoffs L : ℝ) /
      (2 : ℝ) ^ ((L : ℝ) - (Nat.primeCounting L : ℝ))) atTop (𝓝 0)) :
    Tendsto (fun L : ℕ =>
      infiniteRademacherMeasure.real (⋃ x ∈ Finset.Ioc (2 * L ^ 2) (cutoffs L),
        infiniteStartEvent x L) / ((2 : ℝ)⁻¹) ^ Nat.primeCounting L) atTop (𝓝 0) := by
  obtain ⟨theta, K, hK, Lzero, h⟩ := equation_seven_nine hShorey hPNT hNR
  have htail := exceptional_relative_to_border_tendsto_zero hPNT theta K hK
  have hsum := hsmall.add htail
  apply squeeze_zero' (Eventually.of_forall (fun L => by positivity)) _ (by simpa only [add_zero] using hsum)
  filter_upwards [hcutoff, eventually_ge_atTop Lzero] with L hT hL
  have hb : 0 < ((2 : ℝ)⁻¹) ^ Nat.primeCounting L := by positivity
  have hp := div_le_div_of_nonneg_right (h L hL (cutoffs L) hT) hb.le
  rw [add_div, div_div] at hp
  rw [cutoff_scale_eq]
  exact hp

end
end PaperC.V282.MesoscopicCutoff
