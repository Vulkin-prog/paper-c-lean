import PaperCV282.ShiftedKernelRangeCount
import Mathlib.Data.Finset.Powerset

/-!
# Exact shifted-pair double counting for kernel window energy

The actual values in a start window are `x-1+i`, for `i` in `range(L+1)`.
An unordered pair of offsets has a unique positive shift. Counting all
such pairs in the windows equals counting their placements over shifted
value pairs. Each shifted pair has at most `L+1` placements at positive
starts. This is a finite identity and inequality, with no energy estimate
supplied as a premise.
-/

namespace PaperC.V282.KernelWindowEnergy

open LargeOddKernel
open scoped BigOperators

noncomputable section

/-- Ordered increasing representatives of unordered pairs in a finite set. -/
def increasingPairs (s : Finset ℕ) : Finset (ℕ × ℕ) :=
  (s ×ˢ s).filter fun ij => ij.1 < ij.2

theorem mem_increasingPairs {s : Finset ℕ} {ij : ℕ × ℕ} :
    ij ∈ increasingPairs s ↔ ij.1 ∈ s ∧ ij.2 ∈ s ∧ ij.1 < ij.2 := by
  simp [increasingPairs, and_assoc]

/-- Choosing two elements is exactly counting their increasing representatives. -/
theorem card_increasingPairs (s : Finset ℕ) :
    (increasingPairs s).card = s.card.choose 2 := by
  rw [← Finset.card_powersetCard]
  apply Finset.card_bij (fun ij _ => ({ij.1, ij.2} : Finset ℕ))
  · intro ij hij
    obtain ⟨hi, hj, hij⟩ := mem_increasingPairs.mp hij
    apply Finset.mem_powersetCard.mpr
    refine ⟨?_, by simp [ne_of_lt hij]⟩
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl <;> assumption
  · intro ij hij uv huv heq
    have hijlt := (mem_increasingPairs.mp hij).2.2
    have huvlt := (mem_increasingPairs.mp huv).2.2
    have hi : ij.1 ∈ ({uv.1, uv.2} : Finset ℕ) := heq ▸ (by simp)
    have hj : ij.2 ∈ ({uv.1, uv.2} : Finset ℕ) := heq ▸ (by simp)
    have hu : uv.1 ∈ ({ij.1, ij.2} : Finset ℕ) := heq.symm ▸ (by simp)
    have hv : uv.2 ∈ ({ij.1, ij.2} : Finset ℕ) := heq.symm ▸ (by simp)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hu hv
    apply Prod.ext <;> omega
  · intro t ht
    obtain ⟨hts, htcard⟩ := Finset.mem_powersetCard.mp ht
    obtain ⟨i, j, hne, rfl⟩ := Finset.card_eq_two.mp htcard
    have hi : i ∈ s := hts (by simp)
    have hj : j ∈ s := hts (by simp)
    rcases lt_or_gt_of_ne hne with hij | hji
    · exact ⟨(i, j), mem_increasingPairs.mpr ⟨hi, hj, hij⟩, rfl⟩
    · exact ⟨(j, i), mem_increasingPairs.mpr ⟨hj, hi, hji⟩, by simp [Finset.pair_comm]⟩

/-- Offsets whose actual window values have small large-odd kernel. -/
def smallKernelOffsets (B T L x : ℕ) : Finset ℕ :=
  (Finset.range (L + 1)).filter fun i => largeOddKernel B (x - 1 + i) ≤ T

/-- The literal sum of binomial second moments over the chosen starts. -/
def windowEnergy (B T L : ℕ) (starts : Finset ℕ) : ℕ :=
  ∑ x ∈ starts, (smallKernelOffsets B T L x).card.choose 2

/-- Each increasing pair is retained with its original start. -/
def windowIncidences (B T L : ℕ) (starts : Finset ℕ) : Finset (Σ _x : ℕ, ℕ × ℕ) :=
  starts.sigma fun x => increasingPairs (smallKernelOffsets B T L x)

theorem card_windowIncidences (B T L : ℕ) (starts : Finset ℕ) :
    (windowIncidences B T L starts).card = windowEnergy B T L starts := by
  simp only [windowIncidences, Finset.card_sigma, card_increasingPairs, windowEnergy]

/-- First values of shifted small-kernel pairs in an explicit half-open interval. -/
def shiftedKernelValues (B T a b h : ℕ) : Finset ℕ :=
  (Finset.Ico a b).filter fun n =>
    largeOddKernel B n ≤ T ∧ largeOddKernel B (n + h) ≤ T

/-- Placements of a shifted value pair into the actual offset convention. -/
def windowPlacements (starts : Finset ℕ) (L h n : ℕ) : Finset (ℕ × ℕ) :=
  (starts ×ˢ Finset.range (L + 1)).filter fun xi =>
    n = xi.1 - 1 + xi.2 ∧ xi.2 + h < L + 1

/-- Shift, first value, and placement form the alternative incidence coordinates. -/
def shiftedWindowIncidences (B T L a b : ℕ) (starts : Finset ℕ) :
    Finset (Σ _h : ℕ, Σ _n : ℕ, ℕ × ℕ) :=
  (Finset.Icc 1 L).sigma fun h =>
    (shiftedKernelValues B T a b h).sigma fun n => windowPlacements starts L h n

/-- The two incidence descriptions are equinumerous with no unmentioned boundary convention. -/
theorem card_windowIncidences_eq_shifted
    (B T L a b : ℕ) (starts : Finset ℕ)
    (hcover : ∀ x ∈ starts, ∀ i ∈ Finset.range (L + 1), a ≤ x - 1 + i ∧ x - 1 + i < b) :
    (windowIncidences B T L starts).card = (shiftedWindowIncidences B T L a b starts).card := by
  apply Finset.card_bij
    (fun t _ => (⟨t.2.2 - t.2.1, ⟨t.1 - 1 + t.2.1, (t.1, t.2.1)⟩⟩ : Σ _h : ℕ, Σ _n : ℕ, ℕ × ℕ))
  · rintro ⟨x, i, j⟩ ht
    dsimp only at *
    obtain ⟨hx, hij⟩ := Finset.mem_sigma.mp ht
    obtain ⟨hi, hj, hlt⟩ := mem_increasingPairs.mp hij
    dsimp only at hi hj hlt
    obtain ⟨hirange, hik⟩ := Finset.mem_filter.mp hi
    obtain ⟨hjrange, hjk⟩ := Finset.mem_filter.mp hj
    have hiL := Finset.mem_range.mp hirange
    have hjL := Finset.mem_range.mp hjrange
    apply Finset.mem_sigma.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨by dsimp only; omega, by dsimp only; omega⟩, Finset.mem_sigma.mpr ?_⟩
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr (hcover x hx i hirange), hik, ?_⟩, ?_⟩
    · simpa only [show x - 1 + i + (j - i) = x - 1 + j by omega] using hjk
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_product.mpr ⟨hx, hirange⟩, rfl, by dsimp only; omega⟩
  · rintro ⟨x, i, j⟩ ht ⟨y, k, l⟩ hu heq
    have hx : x = y := congrArg (fun t : Σ _h : ℕ, Σ _n : ℕ, ℕ × ℕ => t.2.2.1) heq
    have hi : i = k := congrArg (fun t : Σ _h : ℕ, Σ _n : ℕ, ℕ × ℕ => t.2.2.2) heq
    have hdiff : j - i = l - k := congrArg Sigma.fst heq
    have hij := (mem_increasingPairs.mp (Finset.mem_sigma.mp ht).2).2.2
    have hkl := (mem_increasingPairs.mp (Finset.mem_sigma.mp hu).2).2.2
    dsimp only at *
    have hj : j = l := by omega
    subst y k l
    rfl
  · rintro ⟨h, n, x, i⟩ ht
    obtain ⟨hh, ht⟩ := Finset.mem_sigma.mp ht
    obtain ⟨hn, hplace⟩ := Finset.mem_sigma.mp ht
    obtain ⟨_, hnleft, hnright⟩ := Finset.mem_filter.mp hn
    obtain ⟨hxi, hnvalue, hibound⟩ := Finset.mem_filter.mp hplace
    obtain ⟨hx, hi⟩ := Finset.mem_product.mp hxi
    have hhpos := (Finset.mem_Icc.mp hh).1
    dsimp only at *
    refine ⟨⟨x, (i, i + h)⟩, Finset.mem_sigma.mpr ⟨hx, ?_⟩, ?_⟩
    · apply mem_increasingPairs.mpr
      refine ⟨Finset.mem_filter.mpr ⟨hi, ?_⟩, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hibound, ?_⟩,
        by dsimp only; omega⟩
      · simpa only [hnvalue] using hnleft
      · simpa only [hnvalue, Nat.add_assoc] using hnright
    · simp only [Nat.add_sub_cancel_left]
      congr 2
      exact hnvalue.symm

/-- Exact shifted-pair double counting of the literal binomial energy. -/
theorem windowEnergy_eq_sum_shifted
    (B T L a b : ℕ) (starts : Finset ℕ)
    (hcover : ∀ x ∈ starts, ∀ i ∈ Finset.range (L + 1), a ≤ x - 1 + i ∧ x - 1 + i < b) :
    windowEnergy B T L starts =
      ∑ h ∈ Finset.Icc 1 L, ∑ n ∈ shiftedKernelValues B T a b h,
        (windowPlacements starts L h n).card := by
  rw [← card_windowIncidences, card_windowIncidences_eq_shifted B T L a b starts hcover]
  simp only [shiftedWindowIncidences, Finset.card_sigma]

/-- At positive starts, one left offset determines the entire placement. -/
theorem card_windowPlacements_le (starts : Finset ℕ) (L h n : ℕ)
    (hpos : ∀ x ∈ starts, 1 ≤ x) :
    (windowPlacements starts L h n).card ≤ L + 1 := by
  calc
    _ ≤ (Finset.range (L + 1)).card := by
      apply Finset.card_le_card_of_injOn Prod.snd
      · intro xi hxi
        exact (Finset.mem_product.mp (Finset.mem_filter.mp hxi).1).2
      · intro xi hxi yj hyj heq
        obtain ⟨hxiprod, hnxi, _⟩ := Finset.mem_filter.mp hxi
        obtain ⟨hyjprod, hnyj, _⟩ := Finset.mem_filter.mp hyj
        have hxpos := hpos xi.1 (Finset.mem_product.mp hxiprod).1
        have hypos := hpos yj.1 (Finset.mem_product.mp hyjprod).1
        exact Prod.ext (by omega) heq
    _ = _ := Finset.card_range _

/-- The finite energy costs at most one window length per shifted pair. -/
theorem windowEnergy_le_length_mul_sum_shifted
    (B T L a b : ℕ) (starts : Finset ℕ)
    (hpos : ∀ x ∈ starts, 1 ≤ x)
    (hcover : ∀ x ∈ starts, ∀ i ∈ Finset.range (L + 1), a ≤ x - 1 + i ∧ x - 1 + i < b) :
    windowEnergy B T L starts ≤ (L + 1) *
      ∑ h ∈ Finset.Icc 1 L, (shiftedKernelValues B T a b h).card := by
  rw [windowEnergy_eq_sum_shifted B T L a b starts hcover]
  calc
    _ ≤ ∑ h ∈ Finset.Icc 1 L, ∑ _n ∈ shiftedKernelValues B T a b h, (L + 1) := by
      apply Finset.sum_le_sum
      intro h _
      exact Finset.sum_le_sum fun n _ => card_windowPlacements_le starts L h n hpos
    _ = _ := by simp [Finset.mul_sum, mul_comm]

/-- The dyadic start block uses the enlarged value interval beginning at `X-1`. -/
theorem dyadic_windowEnergy_eq_sum_shifted
    (B T L X : ℕ) (hX : 1 ≤ X) :
    windowEnergy B T L (Finset.Ico X (2 * X)) =
      ∑ h ∈ Finset.Icc 1 L, ∑ n ∈ shiftedKernelValues B T (X - 1) (2 * X + L) h,
        (windowPlacements (Finset.Ico X (2 * X)) L h n).card := by
  apply windowEnergy_eq_sum_shifted
  intro x hx i hi
  have hxrange := Finset.mem_Ico.mp hx
  have hirange := Finset.mem_range.mp hi
  constructor <;> omega

/-- The one-length multiplicity bound on the genuine dyadic window geometry. -/
theorem dyadic_windowEnergy_le_length_mul_sum_shifted
    (B T L X : ℕ) (hX : 1 ≤ X) :
    windowEnergy B T L (Finset.Ico X (2 * X)) ≤ (L + 1) *
      ∑ h ∈ Finset.Icc 1 L, (shiftedKernelValues B T (X - 1) (2 * X + L) h).card := by
  apply windowEnergy_le_length_mul_sum_shifted
  · intro x hx
    exact hX.trans (Finset.mem_Ico.mp hx).1
  · intro x hx i hi
    have hxrange := Finset.mem_Ico.mp hx
    have hirange := Finset.mem_range.mp hi
    constructor <;> omega

end
end PaperC.V282.KernelWindowEnergy
