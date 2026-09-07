import PaperCV282.MacroscopicMaskGeometry
import PaperCV282.CutoffGraphFreeCutoff

/-! # Actual large-prime graph bounds on all positive sites up to M -/
namespace PaperC.V282.MacroscopicGraphBounds

open LargeOddKernel LargePrimeDependencyGraph MaskedPairGeometry CutoffGraphDegree
open MacroscopicMaskGeometry
open scoped BigOperators

noncomputable section

def boundedStartsUsingPrime (M L Y p : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 2 M).filter fun x => p ∈ largePrimeCoordinates x L Y

theorem mem_boundedStartsUsingPrime {M L Y p x : ℕ} :
    x ∈ boundedStartsUsingPrime M L Y p ↔
      x ∈ Finset.Icc 2 M ∧ p ∈ largePrimeCoordinates x L Y := by
  classical
  simp [boundedStartsUsingPrime]

theorem card_divisible_offset_le {M p j : ℕ} (hM : 1 ≤ M) (hp : 0 < p) (hj : j ≤ p + 1) :
    (((Finset.Icc 2 M).filter fun x => p ∣ x - 1 + j).card : ℝ) ≤ (M : ℝ) / p + 1 := by
  have hs : (Finset.Icc 2 M).filter (fun x => p ∣ x - 1 + j) ⊆
      (Finset.Ico 1 (M + 1)).filter (fun x => x ≡ p + 1 - j [MOD p]) := by
    intro x hx
    obtain ⟨hxr, hd⟩ := Finset.mem_filter.mp hx
    have hxr := Finset.mem_Icc.mp hxr
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩,
      (dvd_sub_one_add_iff_modEq (by omega) hj).mp hd⟩
  have hc := card_nat_Ico_modEq_cast_le_div_add_one 1 (M + 1) (p + 1 - j) p hp (by omega)
  have hc' : (((Finset.Ico 1 (M + 1)).filter fun x => x ≡ p + 1 - j [MOD p]).card : ℝ) ≤
      (M : ℝ) / p + 1 := by
    have hh := (Rat.cast_le (K := ℝ)).mpr hc
    push_cast at hh
    simpa using hh
  exact (show (((Finset.Icc 2 M).filter fun x => p ∣ x - 1 + j).card : ℝ) ≤
    (((Finset.Ico 1 (M + 1)).filter fun x => x ≡ p + 1 - j [MOD p]).card : ℝ) by
      exact_mod_cast Finset.card_le_card hs).trans hc'

theorem boundedStartsUsingPrime_subset_offsetUnion {M L Y p : ℕ} :
    boundedStartsUsingPrime M L Y p ⊆ (Finset.range (L + 1)).biUnion
      fun i => (Finset.Icc 2 M).filter fun x => p ∣ x - 1 + i := by
  intro x hx
  obtain ⟨hxm, hc⟩ := mem_boundedStartsUsingPrime.mp hx
  obtain ⟨n, hn, hp⟩ := mem_largePrimeCoordinates.mp hc
  have hdvd := Nat.dvd_of_mem_primeFactors (largeOddPrimeSupport_subset_primeFactors Y n hp)
  have hxr := Finset.mem_Icc.mp hxm
  obtain ⟨i, hi, heq⟩ := BadStartRankin.tree_vertex_eq_complete_offset (by omega) hn
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_range.mpr hi,
    Finset.mem_filter.mpr ⟨hxm, heq ▸ hdvd⟩⟩

theorem card_boundedStartsUsingPrime_le {M L Y p : ℕ}
    (hM : 1 ≤ M) (hLY : L ≤ Y) (hpY : Y < p) :
    ((boundedStartsUsingPrime M L Y p).card : ℝ) ≤ (L + 1 : ℝ) * ((M : ℝ) / p + 1) := by
  have hp : 0 < p := by omega
  calc
    _ ≤ (((Finset.range (L + 1)).biUnion
        fun i => (Finset.Icc 2 M).filter fun x => p ∣ x - 1 + i).card : ℝ) := by
      exact_mod_cast Finset.card_le_card boundedStartsUsingPrime_subset_offsetUnion
    _ ≤ ∑ i ∈ Finset.range (L + 1), (((Finset.Icc 2 M).filter fun x => p ∣ x - 1 + i).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ Finset.range (L + 1), ((M : ℝ) / p + 1) := by
      apply Finset.sum_le_sum
      intro i hi
      apply card_divisible_offset_le hM hp
      have := Finset.mem_range.mp hi
      omega
    _ = _ := by simp; ring

theorem card_largePrimeCoordinates_le {N L Y x : ℕ} (hN : 2 ≤ N) (hL : L ≤ N)
    (hY : 1 < Y) (hx : x ∈ Finset.Icc 2 N) :
    ((largePrimeCoordinates x L Y).card : ℝ) ≤
      (L + 1 : ℝ) * (Real.log (3 * N : ℕ) / Real.log Y) := by
  have hlogY : 0 < Real.log Y := Real.log_pos (by exact_mod_cast hY)
  have hlog3N : 0 ≤ Real.log (3 * N : ℕ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ 3 * N by omega))
  calc
    _ ≤ ∑ n ∈ startTreeSupport x L, ((largeOddPrimeSupport Y n).card : ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le : (largePrimeCoordinates x L Y).card ≤ _)
    _ ≤ ∑ _n ∈ startTreeSupport x L, Real.log (3 * N : ℕ) / Real.log Y := by
      apply Finset.sum_le_sum
      intro n hn
      obtain ⟨hnpos, hnupper⟩ := MacroscopicMaskGeometry.tree_vertex_bounds hL hx hn
      apply (le_div_iff₀ hlogY).mpr
      exact (card_largeOddPrimeSupport_mul_log_le hnpos hY).trans
        (Real.log_le_log (by exact_mod_cast hnpos) (by exact_mod_cast hnupper))
    _ = ((startTreeSupport x L).card : ℝ) * (Real.log (3 * N : ℕ) / Real.log Y) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast card_startTreeSupport_le x L) (div_nonneg hlog3N hlogY.le)

theorem cutoffNeighbors_subset_prime_cover {N L Y x : ℕ} {mask : Finset ℕ}
    (hmask : mask ⊆ Finset.Icc 2 N) :
    cutoffNeighbors L Y mask x ⊆ (largePrimeCoordinates x L Y).biUnion
      fun p => boundedStartsUsingPrime N L Y p := by
  intro y hy
  obtain ⟨hymask, _, p, hp⟩ := mem_cutoffNeighbors.mp hy
  obtain ⟨hpx, hpy⟩ := Finset.mem_inter.mp hp
  exact Finset.mem_biUnion.mpr ⟨p, hpx, mem_boundedStartsUsingPrime.mpr ⟨hmask hymask, hpy⟩⟩

theorem card_cutoffNeighbors_le {N L Y x : ℕ} (hN : 2 ≤ N) (hL : L ≤ N)
    (hLY : L ≤ Y) (hY : 1 < Y) {mask : Finset ℕ} (hmask : mask ⊆ Finset.Icc 2 N)
    (hx : x ∈ Finset.Icc 2 N) :
    ((cutoffNeighbors L Y mask x).card : ℝ) ≤
      (L + 1 : ℝ) ^ 2 * (Real.log (3 * N : ℕ) / Real.log Y) * ((N : ℝ) / Y + 1) := by
  have hYpos : (0 : ℝ) < Y := by exact_mod_cast (show 0 < Y by omega)
  have hper := card_largePrimeCoordinates_le hN hL hY hx
  have hcount : ((cutoffNeighbors L Y mask x).card : ℝ) ≤
      ((largePrimeCoordinates x L Y).card : ℝ) * ((L + 1 : ℝ) * ((N : ℝ) / Y + 1)) := by
    calc
      _ ≤ (((largePrimeCoordinates x L Y).biUnion fun p => boundedStartsUsingPrime N L Y p).card : ℝ) := by
        exact_mod_cast Finset.card_le_card (cutoffNeighbors_subset_prime_cover hmask)
      _ ≤ ∑ p ∈ largePrimeCoordinates x L Y, ((boundedStartsUsingPrime N L Y p).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _p ∈ largePrimeCoordinates x L Y, (L + 1 : ℝ) * ((N : ℝ) / Y + 1) := by
        apply Finset.sum_le_sum
        intro p hp
        obtain ⟨n, _, hpn⟩ := mem_largePrimeCoordinates.mp hp
        have hpY := (prime_and_large_of_mem_largeOddPrimeSupport hpn).2
        exact (card_boundedStartsUsingPrime_le (by omega) hLY hpY).trans (by
          gcongr)
      _ = _ := by simp
  calc
    _ ≤ _ := hcount
    _ ≤ ((L + 1 : ℝ) * (Real.log (3 * N : ℕ) / Real.log Y)) *
        ((L + 1 : ℝ) * ((N : ℝ) / Y + 1)) := mul_le_mul_of_nonneg_right hper (by positivity)
    _ = _ := by ring

theorem cutoffMaxDegree_le {N L Y : ℕ} (hN : 2 ≤ N) (hL : L ≤ N)
    (hLY : L ≤ Y) (hY : 1 < Y) {mask : Finset ℕ} (hmask : mask ⊆ Finset.Icc 2 N) :
    (cutoffMaxDegree L Y mask : ℝ) ≤
      (L + 1 : ℝ) ^ 2 * (Real.log (3 * N : ℕ) / Real.log Y) * ((N : ℝ) / Y + 1) := by
  by_cases hm : mask.Nonempty
  · obtain ⟨x, hx, hsup⟩ := Finset.exists_mem_eq_sup mask hm (fun x => (cutoffNeighbors L Y mask x).card)
    change ((mask.sup (fun x => (cutoffNeighbors L Y mask x).card) : ℕ) : ℝ) ≤ _
    rw [hsup]
    exact card_cutoffNeighbors_le hN hL hLY hY hmask (hmask hx)
  · have hempty : mask = ∅ := Finset.not_nonempty_iff_eq_empty.mp hm
    have hz : cutoffMaxDegree L Y mask = 0 := by simp [hempty, cutoffMaxDegree]
    rw [hz, Nat.cast_zero]
    have hlogN : 0 ≤ Real.log (3 * N : ℕ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ 3 * N by omega))
    have hlogY : 0 < Real.log Y := Real.log_pos (by exact_mod_cast hY)
    positivity

theorem normalized_cutoffMaxDegree_le {N L Y : ℕ} (hN : 2 ≤ N) (hL : L ≤ N)
    (hLY : L ≤ Y) (hY : 1 < Y) {mask : Finset ℕ} (hmask : mask ⊆ Finset.Icc 2 N) :
    (cutoffMaxDegree L Y mask : ℝ) / N ≤
      (L + 1 : ℝ) ^ 2 * (Real.log (3 * N : ℕ) / Real.log Y) * (1 / (Y : ℝ) + 1 / N) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  calc
    _ ≤ ((L + 1 : ℝ) ^ 2 * (Real.log (3 * N : ℕ) / Real.log Y) * ((N : ℝ) / Y + 1)) / N :=
      div_le_div_of_nonneg_right (cutoffMaxDegree_le hN hL hLY hY hmask) hNr.le
    _ = _ := by field_simp

theorem normalized_maskedSupportEdges_le {N L Y : ℕ} (hN : 2 ≤ N) (hL : L ≤ N)
    (hLY : L ≤ Y) (hY : 1 < Y) {mask : Finset ℕ} (hmask : mask ⊆ Finset.Icc 2 N) :
    ((maskedSupportEdges L Y mask).card : ℝ) / (N : ℝ) ^ 2 ≤
      (L + 1 : ℝ) ^ 2 * (Real.log (3 * N : ℕ) / Real.log Y) * (1 / (Y : ℝ) + 1 / N) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hcard : mask.card ≤ N := by
    exact MacroscopicMaskGeometry.card_mask_le hmask
  have hedges : ((maskedSupportEdges L Y mask).card : ℝ) ≤ (N : ℝ) * cutoffMaxDegree L Y mask := by
    exact_mod_cast (card_maskedSupportEdges_le_card_mul_maxDegree L Y mask).trans
      (Nat.mul_le_mul_right _ hcard)
  calc
    _ ≤ ((N : ℝ) * cutoffMaxDegree L Y mask) / (N : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hedges (by positivity)
    _ = (cutoffMaxDegree L Y mask : ℝ) / N := by field_simp
    _ ≤ _ := normalized_cutoffMaxDegree_le hN hL hLY hY hmask

end
end PaperC.V282.MacroscopicGraphBounds
