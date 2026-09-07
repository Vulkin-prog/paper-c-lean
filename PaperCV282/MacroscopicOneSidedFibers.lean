import PaperCV282.PolynomialSplitProducts
import PaperC.Asymptotics.BoundedRatioComponentHosts

/-!
# One-sided offset fibres without an Evertse--Silverman input

The historical natural-root fibre injects into its start coordinate.
Its signed offset convention is exactly the complete window `x-1,...,x+L-1`.
The unconditional split-product count applies to every fixed degree at
least two, uniformly over all shapes of bounded degree.
-/

namespace PaperC.V282.MacroscopicOneSidedFibers

open Affine BoundedRatioComponentHosts PolynomialSplitProducts PellInput
open scoped BigOperators

noncomputable section

/-- A nonnegative square root is uniquely determined by its start in the true offset fibre. -/
theorem fst_injective_on_offsetProductNatFiber
    {L e Y : ℕ} (offsets : Finset (Fin (L + 1))) (he : 0 < e)
    (s : Finset (ℕ × ℕ)) (hs : ∀ p ∈ s, offsetProductNatFiber offsets e Y p) :
    Set.InjOn (fun p : ℕ × ℕ => (p.1 : ℤ)) (s : Set (ℕ × ℕ)) := by
  intro p hp q hq hpq
  change (p.1 : ℤ) = (q.1 : ℤ) at hpq
  have hfirst : p.1 = q.1 := by exact_mod_cast hpq
  have hpEq := (hs p hp).2.2
  have hqEq := (hs q hq).2.2
  rw [hfirst] at hpEq
  have hsquare : p.2 ^ 2 = q.2 ^ 2 := Nat.eq_of_mul_eq_mul_left he (hpEq.symm.trans hqEq)
  exact Prod.ext hfirst ((Nat.pow_left_inj (by omega : 2 ≠ 0)).mp hsquare)

/-- Every enumerated signed shift is bounded by the full block length. -/
theorem offsetShiftOfCard_natAbs_le
    {L d : ℕ} (offsets : Finset (Fin (L + 1))) (hcard : offsets.card = d)
    (i : Fin d) : (offsetShiftOfCard offsets hcard i).natAbs ≤ L + 1 := by
  unfold offsetShiftOfCard offsetShift RationalChannelCode.channelVertexOffset
  have hval := ((offsetEnumeration offsets (Fin.cast hcard.symm i)).1).2
  omega

/-- The canonical shift enumeration preserves positivity of every complete-window factor. -/
theorem offsetShiftOfCard_add_pos
    {L d x : ℕ} (offsets : Finset (Fin (L + 1))) (hcard : offsets.card = d)
    (hx : 2 ≤ x) (i : Fin d) : 0 < (x : ℤ) + offsetShiftOfCard offsets hcard i := by
  unfold offsetShiftOfCard offsetShift
  rw [← RationalChannelCode.startCompleteVertexLabel_cast (by omega : 1 ≤ x)]
  exact_mod_cast RationalChannelCode.startCompleteVertexLabel_pos hx _

/-- A true natural-root fibre is a family of split-product starts, with exactly the signed offsets. -/
theorem offsetProductNatFiber_maps_to_splitProductStart
    {L d e Y H : ℕ} (offsets : Finset (Fin (L + 1))) (hcard : offsets.card = d)
    (hY : Y ≤ H) {p : ℕ × ℕ} (hp : offsetProductNatFiber offsets e Y p) :
    splitProductStart (offsetShiftOfCard offsets hcard) e H (p.1 : ℤ) := by
  refine ⟨by simpa only [Int.natAbs_natCast] using hp.2.1.trans hY,
    offsetShiftOfCard_add_pos offsets hcard hp.1, (p.2 : ℤ), ?_⟩
  change EvertseSilvermanInput.shiftedProduct (offsetShiftOfCard offsets hcard) (p.1 : ℤ) = _
  rw [shiftedProduct_offsetShiftOfCard, shiftedProduct_offsetShift (by have := hp.1; omega : 1 ≤ p.1)]
  exact_mod_cast hp.2.2

/-- Every fixed degree at least two has an unconditional uniform polynomial-height count. -/
theorem offsetProductNatFiber_fixed_degree_atMost_rpow_eventually
    (K d : ℕ) (hd : 2 ≤ d) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L e Y : ℕ,
      ∀ offsets : Finset (Fin (L + 1)), offsets.card = d →
      0 < e → e ≤ M ^ K → Y ≤ M ^ K → L + 1 ≤ M ^ K →
      HasAtMostSolutionsReal (offsetProductNatFiber offsets e Y) ((M : ℝ) ^ epsilon) := by
  classical
  obtain ⟨Mzero, hcount⟩ := splitProductStart_atMost_rpow_eventually K d hd epsilon hepsilon
  refine ⟨Mzero, ?_⟩
  intro M hM L e Y offsets hcard he heM hYM hLM s hs
  have hsplit := hcount M hM (offsetShiftOfCard offsets hcard) e
    (offsetShiftOfCard_injective offsets hcard) he heM
    (fun i => (offsetShiftOfCard_natAbs_le offsets hcard i).trans hLM)
  have himage : ∀ X ∈ s.image (fun p : ℕ × ℕ => (p.1 : ℤ)),
      splitProductStart (offsetShiftOfCard offsets hcard) e (M ^ K) X := by
    intro X hX
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hX
    exact offsetProductNatFiber_maps_to_splitProductStart offsets hcard hYM (hs p hp)
  have hcard := hsplit _ himage
  rwa [Finset.card_image_of_injOn (fst_injective_on_offsetProductNatFiber offsets he s hs)] at hcard

/-- One common threshold covers all mobile degrees between two and a fixed upper bound. -/
theorem offsetProductNatFiber_atMost_rpow_eventually
    (K D : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L e Y : ℕ,
      ∀ offsets : Finset (Fin (L + 1)), 2 ≤ offsets.card → offsets.card ≤ D →
      0 < e → e ≤ M ^ K → Y ≤ M ^ K → L + 1 ≤ M ^ K →
      HasAtMostSolutionsReal (offsetProductNatFiber offsets e Y) ((M : ℝ) ^ epsilon) := by
  classical
  have hdegree : ∀ d : Fin (D + 1), ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L e Y : ℕ,
      ∀ offsets : Finset (Fin (L + 1)), offsets.card = d.1 → 2 ≤ offsets.card →
      0 < e → e ≤ M ^ K → Y ≤ M ^ K → L + 1 ≤ M ^ K →
      HasAtMostSolutionsReal (offsetProductNatFiber offsets e Y) ((M : ℝ) ^ epsilon) := by
    intro d
    by_cases hd : 2 ≤ d.1
    · obtain ⟨Mzero, hMzero⟩ := offsetProductNatFiber_fixed_degree_atMost_rpow_eventually
        K d.1 hd epsilon hepsilon
      refine ⟨Mzero, ?_⟩
      intro M hM L e Y offsets hcard htwo
      exact hMzero M hM L e Y offsets hcard
    · refine ⟨0, ?_⟩
      intro M hM L e Y offsets hcard htwo
      omega
  choose threshold hthreshold using hdegree
  refine ⟨Finset.univ.sup threshold, ?_⟩
  intro M hM L e Y offsets htwo hdegree he heM hYM hLM
  let d : Fin (D + 1) := ⟨offsets.card, by omega⟩
  have hdM : threshold d ≤ M := (Finset.le_sup (f := threshold) (Finset.mem_univ d)).trans hM
  exact hthreshold d M hdM L e Y offsets rfl htwo he heM hYM hLM

end
end PaperC.V282.MacroscopicOneSidedFibers
