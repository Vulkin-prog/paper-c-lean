import PaperCV282.OrderedPairCounting

/-!
# Counting windows and ordered pairs from literal kernel energy

A window containing at least two small kernels contributes at least one
to the binomial energy. Larger-endpoint normalization then combines this
count with any uniform partner bound, retaining both orientations.
-/

namespace PaperC.V282.KernelEnergyCounting

open KernelWindowEnergy OrderedPairCounting
open scoped BigOperators

noncomputable section

/-- The literal energy dominates every selected set of windows with two small kernels. -/
theorem card_le_windowEnergy {B T L : ℕ} (starts selected : Finset ℕ)
    (hsub : selected ⊆ starts)
    (hsmall : ∀ x ∈ selected, 2 ≤ (smallKernelOffsets B T L x).card) :
    selected.card ≤ windowEnergy B T L starts := by
  calc
    selected.card = ∑ _x ∈ selected, 1 := by simp
    _ ≤ ∑ x ∈ selected, (smallKernelOffsets B T L x).card.choose 2 := by
      exact Finset.sum_le_sum fun x hx => Nat.choose_pos (hsmall x hx)
    _ ≤ windowEnergy B T L starts := Finset.sum_le_sum_of_subset hsub

/-- The same incidence bound in the real-valued asymptotic interface. -/
theorem card_cast_le_windowEnergy {B T L : ℕ} (starts selected : Finset ℕ)
    (hsub : selected ⊆ starts)
    (hsmall : ∀ x ∈ selected, 2 ≤ (smallKernelOffsets B T L x).card) :
    (selected.card : ℝ) ≤ (windowEnergy B T L starts : ℝ) := by
  exact_mod_cast card_le_windowEnergy starts selected hsub hsmall

/-- A pair mask with two small kernels at its larger endpoint costs energy times partners. -/
theorem card_pairs_le_two_energy_mul {B T L : ℕ} (starts : Finset ℕ)
    (s : Finset (ℕ × ℕ)) {R : ℝ} (hR : 0 ≤ R)
    (hstarts : largerStarts s ⊆ starts)
    (hsmall : ∀ x ∈ largerStarts s, 2 ≤ (smallKernelOffsets B T L x).card)
    (hpartners : ∀ x ∈ largerStarts s, ((smallerPartners s x).card : ℝ) ≤ R) :
    (s.card : ℝ) ≤ 2 * (windowEnergy B T L starts : ℝ) * R := by
  refine (card_le_two_mul_largerStarts_mul s R hpartners).trans ?_
  gcongr
  exact card_le_windowEnergy starts (largerStarts s) hstarts hsmall

end
end PaperC.V282.KernelEnergyCounting
