import PaperCV282.MicroscopicIncidenceRank
import PaperCV282.MediumIncidenceAsymptotics
import PaperCV282.LaishramUniformInput

/-! # The full quadratic microscopic rank surplus

The only premises are the published uniform prime-divisor input and the
already declared PNT remainder. Arithmetic matrix geometry, the quotient,
incidence counting, and the constant-direction loss are all discharged.
-/

namespace PaperC.V282.MicroscopicQuadraticAsymptotics

open Filter MicroscopicIncidenceRank MediumIncidenceAsymptotics LaishramUniformInput
open HarmonicIncidenceSurplus MicroscopicValuationMatrix PrimeEulerPNT
open PostQuadraticPrimeBounds PointwiseStartBounds
open scoped Topology

noncomputable section

/-- The exact harmonic arithmetic behind the published surplus. -/
theorem harmonic_budget_identity (epsilon : ℝ) :
    11 * (1 - epsilon) + ((harmonic 11 : ℝ) - 1 - epsilon) =
      12 * (1 + (surplus 11 : ℝ) - epsilon) := by
  rw [harmonic_eleven_eq,surplus_eleven_eq]
  push_cast
  ring

/-- Complete-value rank is uniformly at least (1+delta_star-epsilon)pi(B). -/
theorem quadratic_value_rank_lower (hLS : UniformPrimeDivisorStatement)
    (hPNT : PrimeNumberTheoremRemainder) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ Bzero : ℕ, 1332 ≤ Bzero ∧ ∀ B : ℕ, Bzero ≤ B → ∀ lo M : ℕ,
      B < lo → lo + B ≤ B ^ 2 + B + 1 → lo + B ≤ M + 1 →
      (1 + (surplus 11 : ℝ) - epsilon) * PrimesUpTo.count B ≤
        ((valuationMatrix M (lo + 1) B).rank : ℝ) := by
  obtain ⟨N,hN⟩ := uniform_large_prime_species hLS hepsilon
  obtain ⟨P,hPmin,hP⟩ := odd_incidence_lower_eventually hPNT hepsilon
  refine ⟨max N P,hPmin.trans (le_max_right _ _),fun B hB lo M hlo htop hcut => ?_⟩
  have hBmin : 1332 ≤ B := hPmin.trans ((le_max_right _ _).trans hB)
  have ht := hN B ((le_max_left _ _).trans hB) (by omega) lo hlo
  have he := hP B ((le_max_right _ _).trans hB) lo (by omega) htop
  have hr := microscopic_rank_medium_primes (M := M) (by omega : 0 < lo) hBmin htop hcut
  have hid := harmonic_budget_identity epsilon
  have hid' := congrArg (fun z : ℝ => z * PrimesUpTo.count B) hid
  nlinarith

/-- Every fixed surplus below delta_star holds for actual quadratic affine starts. -/
theorem quadratic_affine_probability_eventually (hLS : UniformPrimeDivisorStatement)
    (hPNT : PrimeNumberTheoremRemainder) {delta : ℝ} (hdelta : delta < (surplus 11 : ℝ)) :
    ∃ Lzero : ℕ, ∀ L : ℕ, Lzero ≤ L → ∀ x : ℕ,
      L + 3 ≤ x → x ≤ (L + 1) ^ 2 + 2 → ∀ b : Fin L → F₂,
      infiniteAffineStartProbability x L b ≤
        (2 : ℝ) ^ (-(1 + delta) * PrimesUpTo.count (L + 1)) := by
  let epsilon : ℝ := ((surplus 11 : ℝ) - delta) / 2
  have hepsilon : 0 < epsilon := by dsimp [epsilon]; linarith
  obtain ⟨N,hNmin,hN⟩ := quadratic_value_rank_lower hLS hPNT hepsilon
  have hlarge : ∀ᶠ B : ℕ in atTop, 1 / epsilon ≤ (PrimesUpTo.count B : ℝ) :=
    prime_count_tendsto_atTop.eventually_ge_atTop _
  obtain ⟨P,hP⟩ := eventually_atTop.mp hlarge
  refine ⟨max N P,fun L hL x hxlo hxhi b => ?_⟩
  have hBN : N ≤ L + 1 := by omega
  have hBP : P ≤ L + 1 := by omega
  have hr := hN (L + 1) hBN (x - 1) (x + L) (by omega) (by omega) (by omega)
  have hx : 1 ≤ x := by omega
  rw [Nat.sub_add_cancel hx] at hr
  have hmargin : 1 ≤ epsilon * (PrimesUpTo.count (L + 1) : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left (hP (L + 1) hBP) hepsilon.le
    have hid : epsilon * (1 / epsilon) = 1 := by field_simp
    rwa [hid] at hh
  have hreal : (1 + delta) * PrimesUpTo.count (L + 1) + 1 ≤
      ((valuationMatrix (x + L) x (L + 1)).rank : ℝ) := by
    dsimp [epsilon] at hr hmargin
    nlinarith
  have hp := infinite_probability_le_real_value_rank hx (le_refl _) hreal b
  simpa only [neg_mul] using hp

end
end PaperC.V282.MicroscopicQuadraticAsymptotics
