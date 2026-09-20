import PaperCPrel8.AffineDictionaryTheorem
import PaperCPrel8.TypicalDictionaryUniform

/-! # One deterministic rate with a uniform o(nu) remainder

The supremum is over the actual admissible means, not over dictionaries
inside a distance. It is bounded by one and includes zero if the regime
is empty. Arbitrary fixed slack is converted into the literal paper form.
-/
namespace PaperC.Prel8.AffineDictionaryUniform
open Filter Topology
open PaperC.SectionTwelveMoments PaperC.SectionThirteenFiniteBound PaperC.ConditionalAGGAverage
open PaperC.ConditionalStartProbability PaperC.ConditionalAGGInstantiation
open PaperC.V282.RandomDictionary PaperC.V282.DictionaryFieldInfinite
open PaperC.V282.DictionaryFieldModel PaperC.V282.DictionaryFieldTransfer
open PaperC.V282.FiniteFieldTotalVariation PaperC.V282.FiniteFieldPoissonCoupling
open PaperC.V282.PrimeEulerPNT PaperC.V282.ProcessAGGInput PaperC.V282.HardPoissonRates
open PaperC.V282.SaddleParameters PaperC.V282.SaddleScales
open PaperC.Prel8.DictionaryAverage PaperC.Prel8.TypicalDictionaryTheorem
open PaperC.Prel8.UniformExponentialEnvelope
open PaperC.Prel8.AffineDictionarySample PaperC.Prel8.AffineDictionaryInclusion
open PaperC.Prel8.AffineDictionaryMoments
noncomputable section

/-- The fixed band and bounded-intensity regime; a lower intensity bound is unnecessary. -/
def Regime (betaMin betaMax K : ℝ) (N L r : ℕ) : Prop :=
  betaMin*Real.log N ≤ (L+1:ℝ) ∧ (L+1:ℝ) ≤ betaMax*Real.log N ∧
  r ≤ L+1 ∧ (N:ℝ)*(((2^(L+1-r):ℕ):ℝ)/(2:ℝ)^(L+1)) ≤ K

def meanErrors (betaMin betaMax K : ℝ) (N : ℕ) : Set ℝ :=
  {r | r=0 ∨ ∃ L k, Regime betaMin betaMax K N L k ∧
    r=affineAverage (L+1) k (dictionaryConditionalDistance N L (hardCutoff N))}

def uniformRate (betaMin betaMax K : ℝ) (N : ℕ) : ℝ := sSup (meanErrors betaMin betaMax K N)

theorem meanErrors_bounded (betaMin betaMax K : ℝ) (N : ℕ) : BddAbove (meanErrors betaMin betaMax K N) := by
  refine ⟨1,?_⟩
  intro r hr
  rcases hr with rfl | ⟨L,k,hreg,rfl⟩
  · norm_num
  · have h := affine_mono hreg.2.2.1 (f := dictionaryConditionalDistance N L (hardCutoff N)) (g := fun _ => 1) (fun s => PaperC.Prel8.TypicalDictionaryUniform.conditional_distance_le_one N L (hardCutoff N) (dictionary s))
    simpa only [affine_const hreg.2.2.1] using h

/-- The uniform rate majorizes every admissible actual mean, with no chosen dictionary. -/
theorem mean_le_uniformRate {betaMin betaMax K : ℝ} {N L k : ℕ} (hreg : Regime betaMin betaMax K N L k) :
    affineAverage (L+1) k (dictionaryConditionalDistance N L (hardCutoff N)) ≤ uniformRate betaMin betaMax K N :=
  le_csSup (meanErrors_bounded betaMin betaMax K N) (Or.inr ⟨L,k,hreg,rfl⟩)

theorem uniformRate_nonneg (betaMin betaMax K : ℝ) (N : ℕ) : 0 ≤ uniformRate betaMin betaMax K N :=
  le_csSup (meanErrors_bounded betaMin betaMax K N) (Or.inl rfl)

/-- The threshold is uniform over the band and every admissible cardinality. -/
theorem uniformRate_le_eventually (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax K epsilon eta : ℝ) (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax)
    (hK : 0 ≤ K) (hepsilon : 0 < epsilon) (heta : 0 < eta) :
    ∀ᶠ N in atTop, uniformRate betaMin betaMax K N ≤ rate K epsilon eta N := by
  obtain ⟨Nz,hz⟩ := PaperC.Prel8.AffineDictionaryTheorem.mean_rate_eventually hAGG hPNT betaMin betaMax K epsilon eta hbetaMin hbeta hK hepsilon heta
  filter_upwards [eventually_ge_atTop Nz] with N hN
  change sSup (meanErrors betaMin betaMax K N) ≤ rate K epsilon eta N
  apply csSup_le (show (meanErrors betaMin betaMax K N).Nonempty from ⟨0,Or.inl rfl⟩)
  intro r hr
  rcases hr with rfl | ⟨L,k,hreg,rfl⟩
  · exact rate_nonneg hK epsilon eta N
  · have h := hz N hN L (2^(L+1-k)) k hreg.1 hreg.2.1
      (sample_size_bounds hreg.2.2.1).1 (sample_size_bounds hreg.2.2.1).2 hreg.2.2.1 rfl hreg.2.2.2 (dyadicBlock N) (Finset.Subset.refl _)
    have he : PaperC.Prel8.TypicalDictionaryTransfer.maskedDistance N L (hardCutoff N) (dyadicBlock N) =
        dictionaryConditionalDistance N L (hardCutoff N) :=
      funext (full_mask_distance_eq N L (hardCutoff N))
    rw [he] at h
    exact h

/-- The deterministic uniform rate tends to zero throughout the paper's regime. -/
theorem uniformRate_tendsto_zero (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax K : ℝ) (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax) (hK : 0 ≤ K) :
    Tendsto (uniformRate betaMin betaMax K) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (uniformRate_nonneg betaMin betaMax K))
    (uniformRate_le_eventually hAGG hPNT betaMin betaMax K (1/6) 1 hbetaMin hbeta hK (by norm_num) (by norm_num))
  exact rate_tendsto_zero K (1/6) 1 (by norm_num)

/-- The displayed uniform little-oh error is obtained from proved estimates, not assumed. -/
theorem uniform_littleOh_rate (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax K epsilon : ℝ) (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax)
    (hK : 0 ≤ K) (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∃ delta : ℕ → ℝ,
      (∀ N, 0 ≤ delta N) ∧
      Tendsto (fun N => delta N/saddleNu 1 (Real.log N)) atTop (𝓝 0) ∧
      ∀ N, uniformRate betaMin betaMax K N ≤
        C*(Real.exp (-saddleCutoff 1 (Real.log N)+delta N)+(N:ℝ)^(-(1/(3:ℝ))+epsilon)) := by
  let C : ℝ := 1+(2*K+6*K^2)+(10*K^2+2*K)
  have hC : 0 < C := by dsimp [C]; positivity
  let V : ℕ → ℝ := fun N => saddleCutoff 1 (Real.log N)
  let nu : ℕ → ℝ := fun N => saddleNu 1 (Real.log N)
  let P : ℕ → ℝ := fun N => (N:ℝ)^(-(1/(3:ℝ))+epsilon)
  let R := uniformRate betaMin betaMax K
  have hnu : Tendsto nu atTop atTop := (tendsto_saddleNu_atTop (by norm_num : (0:ℝ)<1)).comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hb : ∀ eta : ℝ, 0 < eta → ∀ᶠ N in atTop, R N ≤ C*(Real.exp (-V N+eta*nu N)+P N) := by
    intro eta heta
    filter_upwards [uniformRate_le_eventually hAGG hPNT betaMin betaMax K epsilon eta hbetaMin hbeta hK hepsilon heta] with N hN
    apply hN.trans
    unfold rate
    dsimp [C,V,nu,P]
    have hE := Real.exp_nonneg (-saddleCutoff 1 (Real.log N)+eta*saddleNu 1 (Real.log N))
    have hP := Real.rpow_nonneg (Nat.cast_nonneg N) (-(1/(3:ℝ))+epsilon)
    nlinarith [mul_nonneg (show 0 ≤ 10*K^2+2*K by positivity) hE,
      mul_nonneg (show 0 ≤ 2*K+6*K^2 by positivity) hP]
  exact ⟨C,hC,remainder V P R C,remainder_nonneg V P R C,
    remainder_div_tendsto_zero V nu P R hC hnu hb,remainder_bound V P R hC⟩

end
end PaperC.Prel8.AffineDictionaryUniform
