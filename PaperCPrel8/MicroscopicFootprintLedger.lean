import PaperCPrel8.MicroscopicPairLedger
import PaperCPrel8.DirectedFootprintAsymptotics

/-! # Actual marked-field product costs controlled by the odd-pivot footprint -/
namespace PaperC.Prel8.MicroscopicFootprintLedger
open PaperC.Prel8.ActualSignedPalm PaperC.Prel8.MicroscopicGoodField
open PaperC.Prel8.MicroscopicFiniteLedger PaperC.Prel8.PrimeForcing
open PaperC.Prel8.DirectedFootprintAsymptotics PaperC.Prel8.OddPrimePivot
open PaperC.V282.SaddleParameters PaperC.V282.SaddleScales PaperC.V282.PrimeEulerPNT
open scoped BigOperators
noncomputable section
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P
variable {C Y L E : ℕ} {G : Finset ℕ}

/-- Counting members of a subset through the ambient site index introduces no multiplicity. -/
theorem count_subtype_members (D : Finset ℕ) (hD : D ⊆ G) :
    (∑ k : Site G, if k.val ∈ D then (1:ℝ) else 0) = D.card := by
  rw [← Finset.sum_subtype G (fun _ => Iff.rfl) (fun k => if k ∈ D then (1:ℝ) else 0),
    ← Finset.sum_filter]
  have he : G.filter (fun k => k ∈ D) = D := Finset.filter_mem_eq_inter |>.trans (Finset.inter_eq_right.mpr hD)
  rw [he]
  simp

/-- Excluding a source's own site can only reduce its directed footprint. -/
theorem edgeCount_le_footprints (h : GoodGeometry C Y L E G) :
    edgeCount h ≤ ∑ j : Site G, ((directedFootprint G (L+E+1) (maximalPivots h j)).card : ℝ) := by
  classical
  apply Finset.sum_le_sum
  intro j _
  calc
    _ ≤ ∑ k : Site G, if k.val ∈ directedFootprint G (L+E+1) (maximalPivots h j) then (1:ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro k _
      unfold edge
      split_ifs <;> simp_all
    _ = _ := by
      apply count_subtype_members
      intro k hk
      simp only [directedFootprint, Finset.mem_filter] at hk
      exact hk.1

/-- The proved reciprocal-pivot estimate applies to the actual maximal marked-word pivots. -/
theorem actual_footprint_bound (hPNT : PrimeNumberTheoremRemainder)
    (beta epsilon : ℝ) (hbeta : 0<beta) (hepsilon : 0<epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ C n L E : ℕ,
      M≤2*(n+(L+E+1)) → L+E+1≤n → (L+E+1:ℝ)≤beta*Real.log M →
      ∀ G : Finset ℕ, G ⊆ Finset.Icc 1 n →
      ∀ h : GoodGeometry C ⌊Real.exp (saddleCutoff 1 (Real.log M))⌋₊ L E G,
      (∑ j : Site G, ((directedFootprint G (L+E+1) (maximalPivots h j)).card : ℝ)) ≤
        (n:ℝ)^2*Real.exp (-2*saddleCutoff 1 (Real.log M)+epsilon*saddleNu 1 (Real.log M)) +
          (n:ℝ)*(L+E+2:ℝ)^2 := by
  obtain ⟨Mzero, hz⟩ := directed_footprint_final_bound hPNT beta epsilon hbeta hepsilon
  refine ⟨Mzero, ?_⟩
  intro M hM C n L E hpop hQn hlog G hG h
  by_cases hempty : G.Nonempty
  · obtain ⟨j0,hj0⟩ := hempty
    let q : ℕ → Fin (L+E+2) → PrimeUpTo C := fun j =>
      if hj : j ∈ G then maximalPivots h ⟨j,hj⟩ else maximalPivots h ⟨j0,hj0⟩
    have hq (j : ℕ) (hj : j ∈ G) : q j = maximalPivots h ⟨j,hj⟩ := by simp [q,hj]
    have hh := hz M hM C n (L+E+1) hpop hQn (by exact_mod_cast hlog) G q hG
      (fun j hj a => by rw [hq j hj]; rfl) (fun j hj a => h.good j hj a)
    have he : (∑ j ∈ G, ((directedFootprint G (L+E+1) (q j)).card : ℝ)) =
        ∑ j : Site G, ((directedFootprint G (L+E+1) (maximalPivots h j)).card : ℝ) := by
      rw [Finset.sum_subtype G (fun _ => Iff.rfl)]
      apply Finset.sum_congr rfl
      intro j _
      rw [hq j.val j.property]
    rw [he] at hh
    convert hh using 1
    push_cast
    ring
  · have he : G = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
    subst G
    simp only [Site, Finset.univ_eq_attach, Finset.attach_empty, Finset.sum_empty]
    positivity

/-- The product-of-means edge count inherits the same actual asymptotic footprint bound. -/
theorem actual_edgeCount_bound (hPNT : PrimeNumberTheoremRemainder)
    (beta epsilon : ℝ) (hbeta : 0<beta) (hepsilon : 0<epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ C n L E : ℕ,
      M≤2*(n+(L+E+1)) → L+E+1≤n → (L+E+1:ℝ)≤beta*Real.log M →
      ∀ G : Finset ℕ, G ⊆ Finset.Icc 1 n →
      ∀ h : GoodGeometry C ⌊Real.exp (saddleCutoff 1 (Real.log M))⌋₊ L E G,
      edgeCount h ≤ (n:ℝ)^2*Real.exp (-2*saddleCutoff 1 (Real.log M)+epsilon*saddleNu 1 (Real.log M)) +
          (n:ℝ)*(L+E+2:ℝ)^2 := by
  obtain ⟨Mzero,hz⟩ := actual_footprint_bound hPNT beta epsilon hbeta hepsilon
  refine ⟨Mzero, ?_⟩
  intro M hM C n L E hpop hQn hlog G hG h
  exact (edgeCount_le_footprints h).trans (hz M hM C n L E hpop hQn hlog G hG h)

end
end PaperC.Prel8.MicroscopicFootprintLedger
