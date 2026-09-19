import PaperCPrel8.WeightedActivityWitness
import PaperCPrel8.PrimeCumulantObstruction

/-! # The arithmetic prime witness for every fixed positive polynomial weight -/
namespace PaperC.Prel8.PrimeWeightedWitness
open Finset Filter Topology WeightedActivityWitness CategoricalActivityWitness
open ArithmeticLowCategory PrimeWitnessRetention PrimeWitnessCountBounds PrimeWindowScales
open PrimeWindowErrors PrimeWindowGeometry PrimeRetainedDensity PrimeWindowIntensity
open ConditionalStartProbability CategoricalOccupancyEnvelope
open ArratiaGoldsteinGordonInput IndependentThinning V282.PrimeEulerPNT
noncomputable section

theorem arithmetic_log_lower {C q M E : ℕ} (hq : q.Prime) (p : PrimeUpTo C) (hp : p.val.val=q)
    (G : Finset ℕ) {r t : ℝ} (ht : 0≤t) (hr : 0≤r) (htr : t*r≤1/2)
    (hmean : ∀ i : G, finitePMFExpectation (FinitePMF.uniform (SampleSpace C))
      (occupancy (retainedCategory C (q-1) E G) i)=r) :
    ((((certifiedSites q M).card-((Icc 1 M)\G).card:ℕ):ℝ)*Real.log (1+t)-
      (Nat.primeCounting C:ℝ)*Real.log 2-2*t*(G.card:ℝ)*r)≤
        Real.log (polynomial (FinitePMF.uniform (SampleSpace C)) (retainedCategory C (q-1) E G) t) := by
  have hP : 0<eventProbability (FinitePMF.uniform (SampleSpace C)) (fun w ↦ w=Pi.single p 1) := by
    rw [witness_probability]; positivity
  have hh := witness_log_lower (FinitePMF.uniform (SampleSpace C)) (retainedCategory C (q-1) E G)
    ht (by linarith) hmean (fun w ↦ w=Pi.single p 1) hP
    ((certifiedSites q M).card-((Icc 1 M)\G).card) (fun w hw ↦ by
      subst w; exact (retained_count hq.two_le G).trans (certified_occupied hq p hp G))
  rw [witness_probability,Real.log_div (by norm_num) (by positivity),Real.log_one,Real.log_pow] at hh
  have hb := mul_le_mul_of_nonneg_left (baseline_log_lower ht hr htr) (show (0:ℝ)≤G.card by positivity)
  have ho := mul_le_mul_of_nonneg_left (occupied_log_lower ht hr (by linarith))
    (show (0:ℝ)≤(((certifiedSites q M).card-((Icc 1 M)\G).card:ℕ):ℝ) by positivity)
  simp only [Fintype.card_coe] at hh
  nlinarith only [hh,hb,ho]

def lowerEnvelope (t : ℝ) (q Q : ℕ) (D B : ℝ) : ℝ :=
  (Real.log (window q)/(q:ℝ)-3*Real.log (window q)/(window q:ℝ)-
    2*Real.log (window q)/(q:ℝ)^2-D*Real.log (window q)/(window q:ℝ))*Real.log (1+t)-
      (Nat.primeCounting (window q+Q):ℝ)*Real.log (window q)/(window q:ℝ)*Real.log 2-
        2*t*B*Real.log (window q)/(window q:ℝ)

theorem normalized_lower {q Q E : ℕ} (hq : q.Prime) (G : Finset ℕ) {r t : ℝ}
    (ht : 0≤t) (hr : 0≤r) (htr : t*r≤1/2)
    (hmean : ∀ i : G, finitePMFExpectation (FinitePMF.uniform (SampleSpace (window q+Q)))
      (occupancy (retainedCategory (window q+Q) (q-1) E G) i)=r) :
    lowerEnvelope t q Q (((Icc 1 (window q))\G).card:ℝ) ((G.card:ℝ)*r)≤
      Real.log (window q)/(window q:ℝ)*Real.log (polynomial (FinitePMF.uniform (SampleSpace (window q+Q)))
        (retainedCategory (window q+Q) (q-1) E G) t) := by
  let p : PrimeUpTo (window q+Q) := ⟨⟨q,by have := prime_le_window hq.one_le; omega⟩,hq⟩
  have ha := arithmetic_log_lower (M:=window q) hq p rfl G ht hr htr hmean
  have hc := retained_count_lower (M:=window q) hq.two_le G
  have hh : (0:ℝ)≤Real.log (window q)/(window q:ℝ) :=
    div_nonneg (Real.log_nonneg (by exact_mod_cast window_pos q)) (by positivity)
  have hb := mul_le_mul_of_nonneg_right hc (Real.log_nonneg (by linarith : 1≤1+t))
  have hw : (window q:ℝ)≠0 := by exact_mod_cast (window_pos q).ne'
  have hqr : (q:ℝ)≠0 := by exact_mod_cast hq.ne_zero
  have hbase : (((window q:ℝ)/q-3-2*(window q:ℝ)/(q:ℝ)^2-
      (((Icc 1 (window q))\G).card:ℝ))*Real.log (1+t)-
      (Nat.primeCounting (window q+Q):ℝ)*Real.log 2-2*t*(G.card:ℝ)*r)≤
      Real.log (polynomial (FinitePMF.uniform (SampleSpace (window q+Q)))
        (retainedCategory (window q+Q) (q-1) E G) t) := by linarith
  apply (mul_le_mul_of_nonneg_left hbase hh).trans_eq'
  unfold lowerEnvelope
  field_simp

theorem lowerEnvelope_tendsto (hPNT : PrimeNumberTheoremRemainder)
    (t : ℝ) (Q : ℕ → ℕ) (D B : ℕ → ℝ)
    (hQ : Tendsto (fun q ↦ (Q q:ℝ)/(window q:ℝ)) atTop (𝓝 0))
    (hD : Tendsto (fun q ↦ D q*Real.log (window q)/(window q:ℝ)) atTop (𝓝 0))
    (hB : Tendsto (fun q ↦ B q*Real.log (window q)/(window q:ℝ)) atTop (𝓝 0)) :
    Tendsto (fun q ↦ lowerEnvelope t q (Q q) (D q) (B q)) atTop
      (𝓝 (Real.log 2*(Real.log (1+t)-1))) := by
  have hp := ShiftedCylinderPNT.prime_count_shifted hPNT window Q window_tendsto hQ
  have hh := (((((log_ratio.sub (log_div_window.const_mul 3)).sub
    (log_div_prime_square.const_mul 2)).sub hD).mul_const (Real.log (1+t))).sub
      (hp.mul_const (Real.log 2))).sub (hB.const_mul (2*t))
  convert hh using 1
  · ext q; unfold lowerEnvelope; ring
  · congr 1; ring

end
end PaperC.Prel8.PrimeWeightedWitness
