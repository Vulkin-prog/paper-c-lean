import PaperCPrel8.PrimeActivityLower
import PaperCPrel8.PrimeWindowErrors

/-! # The normalized G.9 obstruction on the literal prime windows

The limit-inferior assertion is expressed as its epsilon/eventual lower-bound
form. This remains meaningful if the normalized activity itself is unbounded.
-/
namespace PaperC.Prel8.PrimeActivityAsymptotics
open Finset Filter Topology PrimeWindowScales PrimeWindowErrors PrimeActivityLower
open PrimeWitnessCountBounds PrimeWitnessRetention ArithmeticLowCategory ConditionalStartProbability
open CategoricalOccupancyEnvelope CategoricalCumulantBound ArratiaGoldsteinGordonInput IndependentThinning
open V282.PrimeEulerPNT
noncomputable section

def lowerEnvelope (q Q : ℕ) (D B : ℝ) : ℝ :=
  ((Real.log (window q)/(q:ℝ)-3*Real.log (window q)/(window q:ℝ)-
      2*Real.log (window q)/(q:ℝ)^2-D*Real.log (window q)/(window q:ℝ))*Real.log 3-
    (Nat.primeCounting (window q+Q):ℝ)*Real.log (window q)/(window q:ℝ)*Real.log 2-
      4*B*Real.log (window q)/(window q:ℝ))/2

/-- Pointwise link to the original arithmetic law, including every rounding and deletion error. -/
theorem normalized_lower {q Q E : ℕ} (hq : q.Prime) (G : Finset ℕ) {r : ℝ}
    (hr : 0≤r) (hrq : r≤1/4)
    (hmean : ∀ i : G, finitePMFExpectation (FinitePMF.uniform (SampleSpace (window q+Q)))
      (occupancy (retainedCategory (window q+Q) (q-1) E G) i)=r) :
    lowerEnvelope q Q (((Icc 1 (window q))\G).card:ℝ) ((G.card:ℝ)*r) ≤
      Real.log (window q)/(window q:ℝ)*
        activity (FinitePMF.uniform (SampleSpace (window q+Q)))
          (retainedCategory (window q+Q) (q-1) E G) := by
  let p : PrimeUpTo (window q+Q) := ⟨⟨q,by have := prime_le_window hq.one_le; omega⟩,hq⟩
  have ha := arithmetic_linear_lower (M:=window q) hq p rfl G hr hrq hmean
  have hc := retained_count_lower (M:=window q) hq.two_le G
  have hh : (0:ℝ)≤Real.log (window q)/(window q:ℝ) := by
    apply div_nonneg _ (by positivity)
    exact Real.log_nonneg (by exact_mod_cast (window_pos q))
  have hb := mul_le_mul_of_nonneg_right hc (show 0≤Real.log 3 by positivity)
  have hw : (window q:ℝ)≠0 := by exact_mod_cast (window_pos q).ne'
  have hqr : (q:ℝ)≠0 := by exact_mod_cast hq.ne_zero
  have hbase : (((window q:ℝ)/q-3-2*(window q:ℝ)/(q:ℝ)^2-
      (((Icc 1 (window q))\G).card:ℝ))*Real.log 3-
      (Nat.primeCounting (window q+Q):ℝ)*Real.log 2-4*(G.card:ℝ)*r)/2 ≤
      activity (FinitePMF.uniform (SampleSpace (window q+Q)))
        (retainedCategory (window q+Q) (q-1) E G) := by linarith
  apply (mul_le_mul_of_nonneg_left hbase hh).trans_eq'
  unfold lowerEnvelope
  field_simp

/-- The three stated small errors suffice for exactly the paper's leading constant. -/
theorem lowerEnvelope_tendsto (hPNT : PrimeNumberTheoremRemainder)
    (Q : ℕ → ℕ) (D B : ℕ → ℝ)
    (hQ : Tendsto (fun q ↦ (Q q:ℝ)/(window q:ℝ)) atTop (𝓝 0))
    (hD : Tendsto (fun q ↦ D q*Real.log (window q)/(window q:ℝ)) atTop (𝓝 0))
    (hB : Tendsto (fun q ↦ B q*Real.log (window q)/(window q:ℝ)) atTop (𝓝 0)) :
    Tendsto (fun q ↦ lowerEnvelope q (Q q) (D q) (B q)) atTop (𝓝 obstructionConstant) := by
  have hp := ShiftedCylinderPNT.prime_count_shifted hPNT window Q window_tendsto hQ
  have hh := (((((log_ratio.sub (log_div_window.const_mul 3)).sub
    (log_div_prime_square.const_mul 2)).sub hD).mul_const (Real.log 3)).sub
      (hp.mul_const (Real.log 2))).sub (hB.const_mul 4)
  have hh' := hh.div_const 2
  convert hh' using 1
  · ext q
    unfold lowerEnvelope
    ring
  · congr 1
    unfold obstructionConstant
    ring

/-- G.9's lower-limit conclusion for any retained sets with the stated exact marginals.
Only primality at the evaluated q is needed; the parameters are defined for all naturals. -/
theorem arithmetic_obstruction (hPNT : PrimeNumberTheoremRemainder)
    (Q E : ℕ → ℕ) (G : ℕ → Finset ℕ) (r : ℕ → ℝ)
    (hQ : Tendsto (fun q ↦ (Q q:ℝ)/(window q:ℝ)) atTop (𝓝 0))
    (hD : Tendsto (fun q ↦ (((Icc 1 (window q))\G q).card:ℝ)*
      Real.log (window q)/(window q:ℝ)) atTop (𝓝 0))
    (hB : Tendsto (fun q ↦ (G q).card*r q*Real.log (window q)/(window q:ℝ)) atTop (𝓝 0))
    (hmean : ∀ᶠ q : ℕ in atTop, q.Prime → 0≤r q ∧ r q≤1/4 ∧
      ∀ i : G q, finitePMFExpectation (FinitePMF.uniform (SampleSpace (window q+Q q)))
        (occupancy (retainedCategory (window q+Q q) (q-1) (E q) (G q)) i)=r q)
    {epsilon : ℝ} (hepsilon : 0<epsilon) :
    ∀ᶠ q : ℕ in atTop, q.Prime → obstructionConstant-epsilon ≤
      Real.log (window q)/(window q:ℝ)*
        activity (FinitePMF.uniform (SampleSpace (window q+Q q)))
          (retainedCategory (window q+Q q) (q-1) (E q) (G q)) := by
  have ht := lowerEnvelope_tendsto hPNT Q
    (fun q ↦ (((Icc 1 (window q))\G q).card:ℝ)) (fun q ↦ (G q).card*r q) hQ hD hB
  have he := ht.eventually (eventually_gt_nhds (show obstructionConstant-epsilon<obstructionConstant by linarith))
  filter_upwards [he,hmean] with q hq hm hp
  exact hq.le.trans (normalized_lower hp (G q) (hm hp).1 (hm hp).2.1 (hm hp).2.2)

end
end PaperC.Prel8.PrimeActivityAsymptotics
