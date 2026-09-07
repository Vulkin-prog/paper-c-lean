import PaperCV282.FixedMediumAsymptotics
import PaperCV282.MicroscopicQuadraticAsymptotics

/-! # The full fixed-K family of quadratic rank lower bounds

The already proved optimal K=11 arithmetic rank bound dominates every
member of the printed family. This avoids repeating the same private-row
geometry for suboptimal cutoffs; the incidence estimate itself is separately
proved for each K in FixedMediumAsymptotics.
-/
namespace PaperC.V282.FixedMediumRank

open Filter HarmonicIncidenceSurplus MicroscopicQuadraticAsymptotics
open MicroscopicValuationMatrix LaishramUniformInput PrimeEulerPNT
open scoped Topology

noncomputable section

theorem surplus_real (K : ℕ) :
    (surplus K : ℝ)=((harmonic K : ℝ)-2)/((K : ℝ)+1) := by
  simp [surplus]

/-- The threshold can even precede K, because the optimal member has already
been proved arithmetically and the whole harmonic family is bounded by it. -/
theorem equation_E_four_values (hLS : UniformPrimeDivisorStatement)
    (hPNT : PrimeNumberTheoremRemainder) {epsilon : ℝ} (hepsilon : 0<epsilon) :
    ∃ Bzero : ℕ, 1332≤Bzero ∧ ∀ B : ℕ, Bzero≤B → ∀ K lo M : ℕ,
      B<lo → lo+B≤B^2+B+1 → lo+B≤M+1 →
      (1+((harmonic K : ℝ)-2)/((K : ℝ)+1)-epsilon)*PrimesUpTo.count B≤
        ((valuationMatrix M (lo+1) B).rank : ℝ) := by
  obtain ⟨Bzero,hmin,h⟩ := quadratic_value_rank_lower hLS hPNT hepsilon
  refine ⟨Bzero,hmin,fun B hB K lo M hlo htop hcut => ?_⟩
  have hq : (surplus K : ℝ)≤(surplus 11 : ℝ) := by exact_mod_cast surplus_le_eleven K
  rw [← surplus_real K]
  exact (mul_le_mul_of_nonneg_right (by linarith :
    1+(surplus K : ℝ)-epsilon≤1+(surplus 11 : ℝ)-epsilon) (Nat.cast_nonneg _)).trans
      (h B hB lo M hlo htop hcut)

/-- Companion E.4 for the literal start matrix, including its lost constant
direction and the uniform choice of the quadratic window and cylinder. -/
theorem equation_E_four_start (hLS : UniformPrimeDivisorStatement)
    (hPNT : PrimeNumberTheoremRemainder) {epsilon : ℝ} (hepsilon : 0<epsilon) :
    ∃ Bzero : ℕ, 1332≤Bzero ∧ ∀ B : ℕ, Bzero≤B → ∀ K lo M : ℕ,
      B<lo → lo+B≤B^2+B+1 → lo+B≤M+1 →
      (1+((harmonic K : ℝ)-2)/((K : ℝ)+1)-epsilon)*PrimesUpTo.count B≤
        ((startMatrix M (lo+1) (B-1)).rank : ℝ) := by
  obtain ⟨N,hmin,h⟩ := equation_E_four_values hLS hPNT (half_pos hepsilon)
  obtain ⟨P,hP⟩ := eventually_atTop.mp
    (MediumIncidenceAsymptotics.prime_count_tendsto_atTop.eventually_ge_atTop (2/epsilon))
  refine ⟨max N P,hmin.trans (le_max_left _ _),fun B hB K lo M hlo htop hcut => ?_⟩
  have hNB : N≤B := (le_max_left _ _).trans hB
  have hPB : P≤B := (le_max_right _ _).trans hB
  have hBpos : 1≤B := by omega
  have hv := h B hNB K lo M hlo htop hcut
  have hs := valuation_rank_le_start_rank_add_one (M := M) (x := lo+1) (L := B-1) (by omega)
  rw [Nat.sub_add_cancel hBpos] at hs
  have hsR : ((valuationMatrix M (lo+1) B).rank : ℝ)≤
      ((startMatrix M (lo+1) (B-1)).rank : ℝ)+1 := by exact_mod_cast hs
  have hmargin : 1≤(epsilon/2)*(PrimesUpTo.count B : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left (hP B hPB) (half_pos hepsilon).le
    have he : (epsilon/2)*(2/epsilon)=1 := by field_simp
    rwa [he] at hh
  linarith

end
end PaperC.V282.FixedMediumRank
