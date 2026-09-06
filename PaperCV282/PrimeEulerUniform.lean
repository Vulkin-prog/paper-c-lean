import PaperCV282.PrimeEulerLowerSplit
import PaperCV282.SaddleAsymptotics

/-!
# Uniform weighted-prime asymptotics from a source-form PNT

The sole arithmetic input is an explicit error estimate for the ordinary
prime-counting function relative to Li. The moving weight and cutoff are not
assumed to satisfy a weighted-prime estimate. Their hypotheses are scalar
scale conditions: nu and w grow, zeta tends to zero, and |log zeta| = o(nu).
The link zeta*w=u(nu) selects the actual upper saddle branch.
-/

namespace PaperC.V282.PrimeEulerUniform

open Set Filter Topology PrimeEulerPNT PrimeEulerLowerSplit PrimeEulerRankin
open SaddleBranch SaddleAsymptotics ExponentialIntegral

noncomputable section

/-- Ei(u(nu))/nu tends to one for the actual upper branch. -/
theorem tendsto_Ei_upperSaddleBranch_div :
    Tendsto (fun nu => exponentialIntegral (upperSaddleBranch nu) / nu) atTop (𝓝 1) := by
  apply (tendsto_normalizedExponentialIntegral.comp tendsto_upperSaddleBranch_atTop).congr'
  filter_upwards [eventually_ge_atTop (Real.exp 1)] with nu hnu
  dsimp [normalizedExponentialIntegral]
  rw [exp_upperSaddleBranch hnu]
  field_simp [ne_of_gt (upperSaddleBranch_pos hnu)]

/-- A convenient absolute bound for the fixed lower Ei term. -/
theorem abs_Ei_lower_le {A zeta : ℝ} (hA : 1 < A) (hzeta : 0 < zeta)
    (hzetaOne : zeta ≤ 1) (hlow : zeta * Real.log A ≤ 1) :
    |exponentialIntegral (zeta * Real.log A)| ≤
      2 * A + |Real.log zeta| + |Real.log (Real.log A)| + |exponentialIntegral 1| + Real.exp 1 := by
  have hsplit := abs_lower_split_le hA hzeta hzetaOne hlow
  have hsum : 0 ≤ rankinPrimeSum ⌊A⌋₊ zeta := Finset.sum_nonneg (fun _ _ => by positivity)
  have hsumupper := (rankinPrimeSum_le_cutoff ⌊A⌋₊ hzetaOne).trans
    (Nat.floor_le (by linarith : 0 ≤ A))
  have h := abs_add_le
    (exponentialIntegral (zeta * Real.log A) - rankinPrimeSum ⌊A⌋₊ zeta)
    (rankinPrimeSum ⌊A⌋₊ zeta)
  rw [sub_add_cancel, abs_sub_comm, abs_of_nonneg hsum] at h
  linarith

/-- The weighted prime sum has an o(nu) error uniformly along every admissible
moving-cutoff family. The hypothesis concerns ordinary prime counting only. -/
theorem weighted_prime_sum_normalized_error_of_pnt
    (hPNT : PrimeNumberTheoremRemainder)
    {alpha : Type*} {l : Filter alpha} {w nu zeta : alpha → ℝ}
    (hw : Tendsto w l atTop) (hnu : Tendsto nu l atTop)
    (hzeta : Tendsto zeta l (𝓝 0))
    (hzetaPos : ∀ᶠ i in l, 0 < zeta i)
    (hlog : Tendsto (fun i => |Real.log (zeta i)| / nu i) l (𝓝 0))
    (hlink : ∀ᶠ i in l, zeta i * w i = upperSaddleBranch (nu i)) :
    Tendsto (fun i =>
      (rankinPrimeSum ⌊Real.exp (w i)⌋₊ (zeta i) -
        exponentialIntegral (upperSaddleBranch (nu i))) / nu i) l (𝓝 0) := by
  apply Metric.tendsto_nhds.2
  intro epsilon hepsilon
  let eta := epsilon / 4
  have heta : 0 < eta := by dsimp [eta]; positivity
  obtain ⟨A, hAtwo, hR⟩ := hPNT eta heta
  have hA : 1 < A := by linarith
  let C : ℝ := A + |Real.log (Real.log A)| + |exponentialIntegral 1| + Real.exp 1
  let K : alpha → ℝ := fun i => C + |Real.log (zeta i)|
  have hK : Tendsto (fun i => K i / nu i) l (𝓝 0) := by
    have h := (tendsto_const_nhds (x := C)).div_atTop hnu
    simpa only [K, add_div, add_zero] using h.add hlog
  have hKA : Tendsto (fun i => (K i + A) / nu i) l (𝓝 0) := by
    simpa only [add_div, add_zero] using hK.add ((tendsto_const_nhds (x := A)).div_atTop hnu)
  have hrpow : Tendsto (fun i => A ^ zeta i / Real.log A) l (𝓝 (1 / Real.log A)) := by
    have harg : Tendsto (fun i => Real.log A * zeta i) l (𝓝 0) := by
      simpa only [mul_zero] using hzeta.const_mul (Real.log A)
    have hexp := (Real.continuous_exp.tendsto 0).comp harg
    simpa only [Real.rpow_def_of_pos (by linarith : 0 < A), mul_zero,
      Real.exp_zero, Function.comp_def] using hexp.div_const (Real.log A)
  have hboundary : Tendsto (fun i => (A ^ zeta i / Real.log A) / nu i) l (𝓝 0) :=
    hrpow.div_atTop hnu
  have hei : Tendsto (fun i => |exponentialIntegral (upperSaddleBranch (nu i))| / nu i)
      l (𝓝 1) := by
    apply (show Tendsto (fun i => |exponentialIntegral (upperSaddleBranch (nu i)) / nu i|)
      l (𝓝 1) by
        simpa only [abs_one, Function.comp_def] using (tendsto_Ei_upperSaddleBranch_div.comp hnu).abs).congr'
    filter_upwards [hnu.eventually (eventually_gt_atTop (0 : ℝ))] with i hi
    rw [abs_div, abs_of_pos hi]
  let bound : alpha → ℝ := fun i => eta *
    (zeta i + (A ^ zeta i / Real.log A) / nu i +
      |exponentialIntegral (upperSaddleBranch (nu i))| / nu i + (K i + A) / nu i) + K i / nu i
  have hbound : Tendsto bound l (𝓝 eta) := by
    simpa only [bound, zero_add, add_zero, mul_one] using
      (((hzeta.add hboundary).add hei).add hKA).const_mul eta |>.add hK
  have hsmall := hbound.eventually (gt_mem_nhds (show eta < epsilon by dsimp [eta]; linarith))
  have hupper := hzeta.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  have hlowercutoff := (Real.tendsto_exp_atTop.comp hw).eventually (eventually_ge_atTop A)
  have harg : Tendsto (fun i => Real.log A * zeta i) l (𝓝 0) := by
    simpa only [mul_zero] using hzeta.const_mul (Real.log A)
  have hlow := harg.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [hsmall, hupper, hlowercutoff, hlow, hzetaPos, hlink,
    hw.eventually (eventually_gt_atTop (0 : ℝ)),
    hnu.eventually (eventually_ge_atTop (Real.exp 1))] with i hsmall hupper hcut hlow hzpos hlink hwpos hn
  have hnpos : 0 < nu i := (Real.exp_pos 1).trans_le hn
  have hKval : K i = A + |Real.log (zeta i)| + |Real.log (Real.log A)| +
      |exponentialIntegral 1| + Real.exp 1 := by dsimp [K, C]; ring
  have hfull := weighted_prime_full_error_le hA hcut hzpos hupper.le
    (by simpa only [mul_comm] using hlow.le)
    (fun t ht => hR t ht.1)
  have hlowEi := abs_Ei_lower_le hA hzpos hupper.le
    (by simpa only [mul_comm] using hlow.le)
  have hlowEi' : |exponentialIntegral (zeta i * Real.log A)| ≤ K i + A := by
    rw [hKval]
    linarith
  have hdelta : (1 - zeta i) *
      (exponentialIntegral (upperSaddleBranch (nu i)) - exponentialIntegral (zeta i * Real.log A)) ≤
      |exponentialIntegral (upperSaddleBranch (nu i))| + K i + A := by
    have habs := abs_sub (exponentialIntegral (upperSaddleBranch (nu i)))
      (exponentialIntegral (zeta i * Real.log A))
    have hfactor : 0 ≤ 1 - zeta i ∧ 1 - zeta i ≤ 1 := ⟨by linarith, by linarith⟩
    calc
      _ ≤ (1 - zeta i) * (|exponentialIntegral (upperSaddleBranch (nu i))| +
          |exponentialIntegral (zeta i * Real.log A)|) :=
        mul_le_mul_of_nonneg_left ((le_abs_self _).trans habs) hfactor.1
      _ ≤ |exponentialIntegral (upperSaddleBranch (nu i))| +
          |exponentialIntegral (zeta i * Real.log A)| := by
        nlinarith [abs_nonneg (exponentialIntegral (upperSaddleBranch (nu i))),
          abs_nonneg (exponentialIntegral (zeta i * Real.log A))]
      _ ≤ _ := by linarith
  have hboundaryEq : (Real.exp (w i)) ^ zeta i / w i = zeta i * nu i := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, mul_comm (w i), hlink,
      exp_upperSaddleBranch hn]
    have hu : upperSaddleBranch (nu i) = zeta i * w i := hlink.symm
    rw [hu]
    field_simp [hwpos.ne']
  simp only [Function.comp_def, Real.log_exp, hlink] at hfull
  rw [← hKval, hboundaryEq] at hfull
  have herr : |rankinPrimeSum ⌊Real.exp (w i)⌋₊ (zeta i) -
      exponentialIntegral (upperSaddleBranch (nu i))| / nu i ≤ bound i := by
    have hfull' : |rankinPrimeSum ⌊Real.exp (w i)⌋₊ (zeta i) -
        exponentialIntegral (upperSaddleBranch (nu i))| ≤ eta *
        (zeta i * nu i + A ^ zeta i / Real.log A +
          |exponentialIntegral (upperSaddleBranch (nu i))| + K i + A) + K i := by
      nlinarith
    calc
      _ ≤ (eta * (zeta i * nu i + A ^ zeta i / Real.log A +
          |exponentialIntegral (upperSaddleBranch (nu i))| + K i + A) + K i) / nu i :=
        div_le_div_of_nonneg_right hfull' hnpos.le
      _ = _ := by dsimp [bound]; field_simp [hnpos.ne']; ring
  simpa only [Real.dist_eq, sub_zero, abs_div, abs_of_pos hnpos] using herr.trans_lt hsmall

/-- The exact logarithm of the Euler product has the same normalized limit;
its difference from the weighted prime sum is uniformly bounded by two. -/
theorem log_euler_normalized_error_of_pnt
    (hPNT : PrimeNumberTheoremRemainder)
    {alpha : Type*} {l : Filter alpha} {w nu zeta : alpha → ℝ}
    (hw : Tendsto w l atTop) (hnu : Tendsto nu l atTop)
    (hzeta : Tendsto zeta l (𝓝 0))
    (hzetaPos : ∀ᶠ i in l, 0 < zeta i)
    (hlog : Tendsto (fun i => |Real.log (zeta i)| / nu i) l (𝓝 0))
    (hlink : ∀ᶠ i in l, zeta i * w i = upperSaddleBranch (nu i)) :
    Tendsto (fun i =>
      (rankinLogSum ⌊Real.exp (w i)⌋₊ (zeta i) -
        exponentialIntegral (upperSaddleBranch (nu i))) / nu i) l (𝓝 0) := by
  have hdiff : Tendsto (fun i =>
      (rankinLogSum ⌊Real.exp (w i)⌋₊ (zeta i) - rankinPrimeSum ⌊Real.exp (w i)⌋₊ (zeta i)) / nu i)
      l (𝓝 0) := by
    apply squeeze_zero_norm' _ ((tendsto_const_nhds (x := (2 : ℝ))).div_atTop hnu)
    filter_upwards [hzeta.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4)),
      hnu.eventually (eventually_gt_atTop (0 : ℝ))] with i hi hn
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hn]
    exact div_le_div_of_nonneg_right
      (abs_logSum_sub_primeSum_le_two _ hi.le) hn.le
  have hmain := weighted_prime_sum_normalized_error_of_pnt hPNT hw hnu hzeta hzetaPos hlog hlink
  have h := hdiff.add hmain
  simp only [add_zero] at h
  apply h.congr
  intro i
  ring

end
end PaperC.V282.PrimeEulerUniform
