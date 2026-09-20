import PaperCPrel8.MicroscopicRelationExcess
import PaperCV282.MacroAggregateValueProfile

/-! # Arithmetic profile of the actual microscopic full-value excess

Left boundaries are translated to start coordinates before applying the
previously proved full-value profile. The prime cylinder and enlarged length
remain explicit, as does the square-root lower edge of the retained set.
-/
namespace PaperC.Prel8.MicroscopicValueProfile
open PaperC.Prel8.MicroscopicRelationExcess PaperC.Prel8.MicroscopicFiniteLedger
open PaperC.Prel8.MicroscopicGoodField PaperC.Prel8.ActualSignedPalm
open PaperC.V282.DictionaryMarginalCap PaperC.V282.TwoWindowParity
open PaperC.V282.RelationProfileRestriction PaperC.V282.ProfileMonomials
open PaperC.V282.MacroAggregateValueProfile
open PaperC.Prel8.MicroscopicInfiniteField PaperC.ConditionalStartProbability
open PaperC.ArratiaGoldsteinGordonInput PaperC.V282.DirectionalSteinInput
open PaperC.V282.FiniteFieldTotalVariation PaperC.V282.FiniteFieldPoissonCoupling
open scoped NNReal
noncomputable section
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- Actual starts corresponding to retained left boundaries. -/
def retainedStarts (G : Finset ℕ) : Finset ℕ := G.image (fun j => j+1)

/-- Full-value weights coincide exactly, including the natural-to-real subtraction. -/
theorem valueExcess_eq_weight (C L E j k : ℕ) :
    valueExcess C L E j k =
      ((2 ^ PaperC.Affine.relationRho (twoValueSystem C (j+1) (k+1) (L+E+1)) - 1 : ℕ):ℝ) := by
  unfold valueExcess
  rw [PaperC.V282.SignedMarkedSeparatedRelations.maximal_jointValueSystem_eq_twoValueSystem
    (by omega : 1 ≤ j+1) (by omega : 1 ≤ k+1)]
  rw [Nat.cast_sub (one_le_pow₀ (by norm_num : 1 ≤ (2:ℕ))), Nat.cast_pow]
  norm_num

/-- The full separated site sum is the established arithmetic mass on the shifted mask. -/
theorem separatedExcess_eq_valueWeightMass (C L E : ℕ) (G : Finset ℕ) :
    separatedExcess C L E G =
      (valueWeightMass C (L+E+1) (separatedPairs (retainedStarts G) (L+E+1)):ℝ) := by
  unfold separatedExcess valueWeightMass separatedPairs retainedStarts
  rw [Nat.cast_sum]
  simp only [Finset.sum_filter, Finset.sum_product]
  rw [Finset.sum_image (fun j _ k _ hjk => Nat.add_right_cancel hjk)]
  simp_rw [Finset.sum_image (fun j _ k _ hjk => Nat.add_right_cancel hjk)]
  rw [← Finset.sum_subtype G (fun _ => Iff.rfl)
    (fun j => ∑ k : Site G, if L+E+1 < Nat.dist j k.val then valueExcess C L E j k.val else 0)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Finset.sum_subtype G (fun _ => Iff.rfl)
    (fun k => if L+E+1 < Nat.dist j k then valueExcess C L E j k else 0)]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Nat.dist_add_add_right, valueExcess_eq_weight]

/-- The actual G0 starts lie in the closed square-root macroscopic interval. -/
theorem retained_goodStarts_subset {M n L E Y : ℕ} (hn : n+1 ≤ M) :
    retainedStarts (goodSites M n L E Y) ⊆ Finset.Icc ⌈(M:ℝ)^(1/(2:ℝ))⌉₊ M := by
  intro x hx
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hx
  have hcut := (Finset.mem_filter.mp hj).2.1
  have hupper := (Finset.mem_Icc.mp (goodSites_subset M n L E Y hj)).2
  rw [← Real.sqrt_eq_rpow]
  exact Finset.mem_Icc.mpr ⟨hcut,by omega⟩

/-- The actual retained full-value excess satisfies the coarse arithmetic profile. -/
theorem separatedExcess_good_le_eventually
    (betaMin betaMax epsilon : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ n L E Y C : ℕ,
      betaMin*Real.log M ≤ (L+E+2:ℝ) → (L+E+2:ℝ) ≤ betaMax*Real.log M →
      n+1 ≤ M → M+(L+E+1) ≤ C →
      separatedExcess C L E (goodSites M n L E Y) ≤
        (M:ℝ)^epsilon * coarseProfile M ((2:ℝ)^(L+E+2)) := by
  obtain ⟨Mzero,h⟩ := valueWeightMass_mask_le_coarse_eventually
    betaMin betaMax (1/2) epsilon hbetaMin hbeta (by norm_num) hepsilon
  refine ⟨Mzero, ?_⟩
  intro M hM n L E Y C hlo hhi hn hC
  rw [separatedExcess_eq_valueWeightMass]
  convert h M hM (L+E+1) (by push_cast; linarith) (by push_cast; linarith)
    C hC _ (retained_goodStarts_subset hn) _ (Finset.Subset.refl _) using 1

/-- The normalized enlarged profile keeps the exact excess-length cost explicit. -/
theorem normalized_separatedExcess_good_le_eventually
    (betaMin betaMax epsilon : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ n L E Y C : ℕ,
      betaMin*Real.log M ≤ (L+E+2:ℝ) → (L+E+2:ℝ) ≤ betaMax*Real.log M →
      n+1 ≤ M → M+(L+E+1) ≤ C →
      (1/(2:ℝ)^L)^2 * separatedExcess C L E (goodSites M n L E Y) ≤
        (2:ℝ)^(2*E+2)*(M:ℝ)^(-(1/(3:ℝ))+epsilon)*
          ((PaperC.V282.AllStartSoftPoisson.fullRate M L:ℝ)^2+
            2*(PaperC.V282.AllStartSoftPoisson.fullRate M L:ℝ)) := by
  obtain ⟨Mzero,h⟩ := enlarged_valueWeightMass_le_eventually
    betaMin betaMax (1/2) epsilon hbetaMin hbeta (by norm_num) hepsilon
  refine ⟨Mzero, ?_⟩
  intro M hM n L E Y C hlo hhi hn hC
  rw [separatedExcess_eq_valueWeightMass]
  exact h M hM L E hlo hhi C hC _ (retained_goodStarts_subset hn)

/-- The actual infinite conditional comparison with its arithmetic excess profile discharged. -/
theorem infinite_profile_comparison_eventually
    (betaMin betaMax epsilon : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ n L E Y C : ℕ,
      betaMin*Real.log M ≤ (L+E+2:ℝ) → (L+E+2:ℝ) ≤ betaMax*Real.log M →
      n+1 ≤ M → M+(L+E+1) ≤ C →
      ∀ h : GoodGeometry C Y L E (goodSites M n L E Y), 2*(L+E+2) ≤ Y →
      ∀ A : SmallSample C Y → Prop,
      ∀ _hA : 0 < eventProbability (FinitePMF.uniform (SampleSpace C))
        (fun ω => A (restrictSmall C Y ω)),
      DirectionalSolutionBounds (rate L : Index (goodSites M n L E Y) E → ℝ≥0) →
      massTotalVariation (conditionalLaw C Y L E (goodSites M n L E Y) A)
        (poissonFieldMass (rate L)) ≤
      (1/(2:ℝ)^L)^2 * (((goodSites M n L E Y).card:ℝ) + edgeCount h +
        4*((goodSites M n L E Y).card:ℝ)*(2*(L+E+1:ℝ)+1) +
        (edgeCount h + (M:ℝ)^epsilon * coarseProfile M ((2:ℝ)^(L+E+2))) /
          eventProbability (FinitePMF.uniform (SampleSpace C)) (fun ω => A (restrictSmall C Y ω))) := by
  obtain ⟨Mzero,hp⟩ := separatedExcess_good_le_eventually betaMin betaMax epsilon hbetaMin hbeta hepsilon
  refine ⟨Mzero, ?_⟩
  intro M hM n L E Y C hlo hhi hn hC h hY A hA hs
  apply (infinite_relation_comparison h hY A hA hs).trans
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  apply add_le_add le_rfl
  apply div_le_div_of_nonneg_right _ hA.le
  exact add_le_add le_rfl (hp M hM n L E Y C hlo hhi hn hC)

end
end PaperC.Prel8.MicroscopicValueProfile
