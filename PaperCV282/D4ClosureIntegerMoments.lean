import PaperCV282.D4ClosureCoherence
import PaperCV282.D4ClosureCovariance

/-! # The literal sum and covariance identities on the common integer-level law -/
namespace PaperC.V282.D4ClosureIntegerMoments

open MeasureTheory ProbabilityTheory
open D4ClosureHalfLines D4ClosureCoherence D4ClosureIntegerLevels D4ClosureCovariance
open GeometricMarkedConfiguration GeometricConfigurationCounts ThresholdPathEquivalence
open scoped BigOperators NNReal

noncomputable section

theorem ae_integerThreshold_eq_tsum (theta : ℝ) (m : ℤ) :
    ∀ᵐ counts ∂integerCountMeasure theta,
      integerThreshold m counts = ∑' e : ℕ, counts (m+e) := by
  filter_upwards [ae_halfLineConfiguration_coordinates theta m] with counts hc
  have hsum : (∑' e : ℕ, (halfLineConfiguration m counts) e) =
      ∑ e ∈ (halfLineConfiguration m counts).support, (halfLineConfiguration m counts) e :=
    tsum_eq_sum (fun e he => Finsupp.notMem_support_iff.mp he)
  rw [← (tsum_congr hc)]
  exact hsum.symm

theorem integerHalfRate_shift (theta : ℝ) (m : ℤ) (k : ℕ) :
    (integerHalfRate theta (m+k) : ℝ) = (integerHalfRate theta m : ℝ)/(2 : ℝ)^k := by
  change (2 : ℝ)^(theta-(m+k : ℤ)) = (2 : ℝ)^(theta-m)/(2 : ℝ)^k
  rw [← Real.rpow_natCast, ← Real.rpow_sub (by norm_num : (0 : ℝ)<2)]
  congr 1
  push_cast
  ring

theorem covariance_congr_ae {Ω : Type*} [MeasurableSpace Ω] (mu : Measure Ω)
    {f g f' g' : Ω → ℝ} (hf : f =ᵐ[mu] f') (hg : g =ᵐ[mu] g') :
    covariance f g mu = covariance f' g' mu := by
  unfold covariance
  rw [integral_congr_ae hf, integral_congr_ae hg]
  apply integral_congr_ae
  filter_upwards [hf,hg] with x hx hy
  rw [hx,hy]

/-- The two thresholds live on the same two-sided Poisson probability space. -/
theorem integer_threshold_covariance (theta : ℝ) (m n : ℤ) :
    covariance (fun counts => (integerThreshold m counts : ℝ))
      (fun counts => (integerThreshold n counts : ℝ)) (integerCountMeasure theta) =
        (2 : ℝ)^(theta-(max m n : ℝ)) := by
  let b : ℤ := min m n
  let i : ℕ := (m-b).toNat
  let j : ℕ := (n-b).toNat
  have hi : b+i=m := by dsimp [b,i]; omega
  have hj : b+j=n := by dsimp [b,j]; omega
  have hm := ae_integerThreshold_shift theta b i
  have hn := ae_integerThreshold_shift theta b j
  rw [hi] at hm
  rw [hj] at hn
  have he := covariance_congr_ae (integerCountMeasure theta)
    (hm.mono (fun _ h => congrArg (fun k : ℕ => (k : ℝ)) h))
    (hn.mono (fun _ h => congrArg (fun k : ℕ => (k : ℝ)) h))
  rw [he]
  have hlaw := hasLaw_halfLineConfiguration theta b
  have hcov := covariance_map_fun
    (μ := integerCountMeasure theta) (Z := halfLineConfiguration b)
    (measurable_of_countable (fun c : ℕ→₀ℕ => (tailCount c i : ℝ))).aestronglyMeasurable
    (measurable_of_countable (fun c : ℕ→₀ℕ => (tailCount c j : ℝ))).aestronglyMeasurable
    hlaw.aemeasurable
  rw [hlaw.map_eq] at hcov
  rw [← hcov,threshold_covariance,← integerHalfRate_shift]
  have hij : b+(max i j : ℕ)=max m n := by omega
  rw [hij]
  change (2 : ℝ)^(theta-((max m n : ℤ) : ℝ)) = _
  rw [Int.cast_max]

end
end PaperC.V282.D4ClosureIntegerMoments
