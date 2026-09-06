import PaperCV282.MaskedPairGeometry
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Finite cutoff degree bounds on all starts

Every actual large-prime coordinate is counted, including coordinates of
bad starts. The complete tree has B vertices, each using at most
log(3N)/log(Y) large primes. A prime meets at most B(N/p+1) dyadic starts.
Their composition gives the explicit finite version of companion (B.3).
-/

namespace PaperC.V282.CutoffGraphDegree

open LargeOddKernel LargePrimeDependencyGraph MaskedPairGeometry

noncomputable section

/-- All dyadic starts using a prescribed large-prime coordinate, without a good-site filter. -/
def allStartsUsingPrime (N L Y p : ℕ) : Finset ℕ := by
  classical
  exact (dyadicBlock N).filter fun x => p ∈ largePrimeCoordinates x L Y

/-- Open neighbors in the graph induced by an arbitrary deterministic mask. -/
def cutoffNeighbors (L Y : ℕ) (mask : Finset ℕ) (x : ℕ) : Finset ℕ := by
  classical
  exact mask.filter fun y => LargePrimeAdjacent L Y x y

/-- The actual maximum degree on the mask, zero when the mask is empty. -/
def cutoffMaxDegree (L Y : ℕ) (mask : Finset ℕ) : ℕ :=
  mask.sup fun x => (cutoffNeighbors L Y mask x).card

theorem mem_allStartsUsingPrime {N L Y p x : ℕ} :
    x ∈ allStartsUsingPrime N L Y p ↔ x ∈ dyadicBlock N ∧ p ∈ largePrimeCoordinates x L Y := by
  classical
  simp [allStartsUsingPrime]

theorem mem_cutoffNeighbors {L Y x y : ℕ} {mask : Finset ℕ} :
    y ∈ cutoffNeighbors L Y mask x ↔ y ∈ mask ∧ LargePrimeAdjacent L Y x y := by
  classical
  simp [cutoffNeighbors]

/-- The logarithm of the actual prime product bounds the number of large coordinates. -/
theorem card_largeOddPrimeSupport_mul_log_le {n Y : ℕ} (hn : 0 < n) (hY : 1 < Y) :
    ((largeOddPrimeSupport Y n).card : ℝ) * Real.log Y ≤ Real.log n := by
  have hYpos : (0 : ℝ) < Y := by exact_mod_cast (show 0 < Y by omega)
  have hsum : ((largeOddPrimeSupport Y n).card : ℝ) * Real.log Y ≤
      ∑ p ∈ largeOddPrimeSupport Y n, Real.log p := by
    calc
      _ = ∑ _p ∈ largeOddPrimeSupport Y n, Real.log Y := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro p hp
        exact Real.log_le_log hYpos (by exact_mod_cast (prime_and_large_of_mem_largeOddPrimeSupport hp).2.le)
  have hlogprod : Real.log (largeOddKernel Y n) = ∑ p ∈ largeOddPrimeSupport Y n, Real.log p := by
    unfold largeOddKernel
    rw [Nat.cast_prod]
    exact Real.log_prod (fun p hp => by exact_mod_cast (prime_and_large_of_mem_largeOddPrimeSupport hp).1.ne_zero)
  rw [← hlogprod] at hsum
  exact hsum.trans (Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero (largeOddKernel_ne_zero Y n))
    (by exact_mod_cast largeOddKernel_le hn))

/-- Every complete-tree value stays in the positive interval [1,3N]. -/
theorem tree_vertex_bounds {N L x n : ℕ} (hN : 2 ≤ N) (hL : L ≤ N)
    (hx : x ∈ dyadicBlock N) (hn : n ∈ startTreeSupport x L) : 0 < n ∧ n ≤ 3 * N := by
  obtain ⟨hxN, hx2N⟩ := Finset.mem_Ico.mp hx
  rcases mem_startTreeSupport.mp hn with hr | ⟨j, hj, heq⟩ <;> constructor <;> omega

/-- The set of complete vertices has at most B elements even without injectivity arguments. -/
theorem card_startTreeSupport_le (x L : ℕ) : (startTreeSupport x L).card ≤ L + 1 := by
  calc
    _ ≤ (startRunSupport x L).card + 1 := Finset.card_insert_le _ _
    _ ≤ L + 1 := Nat.add_le_add_right ((Finset.card_image_le).trans_eq (Finset.card_range L)) 1

/-- The large-coordinate count is valid for all dyadic starts, including bad starts. -/
theorem card_largePrimeCoordinates_le {N L Y x : ℕ} (hN : 2 ≤ N) (hL : L ≤ N)
    (hY : 1 < Y) (hx : x ∈ dyadicBlock N) :
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
      obtain ⟨hnpos, hnupper⟩ := tree_vertex_bounds hN hL hx hn
      apply (le_div_iff₀ hlogY).mpr
      exact (card_largeOddPrimeSupport_mul_log_le hnpos hY).trans
        (Real.log_le_log (by exact_mod_cast hnpos) (by exact_mod_cast hnupper))
    _ = ((startTreeSupport x L).card : ℝ) * (Real.log (3 * N : ℕ) / Real.log Y) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast card_startTreeSupport_le x L) (div_nonneg hlog3N hlogY.le)

/-- Every start using p has one of the B complete offsets divisible by p. -/
theorem allStartsUsingPrime_subset_offsetUnion {N L Y p : ℕ} (hN : 1 ≤ N) :
    allStartsUsingPrime N L Y p ⊆ (Finset.range (L + 1)).biUnion
      fun i => startsWithDivisibleOffset N p i := by
  intro x hx
  obtain ⟨hxblock, hcoord⟩ := mem_allStartsUsingPrime.mp hx
  obtain ⟨n, hn, hp⟩ := mem_largePrimeCoordinates.mp hcoord
  have hdvd : p ∣ n := Nat.dvd_of_mem_primeFactors (largeOddPrimeSupport_subset_primeFactors Y n hp)
  have hxpos : 1 ≤ x := hN.trans (Finset.mem_Ico.mp hxblock).1
  rcases mem_startTreeSupport.mp hn with hr | ⟨j, hj, heq⟩
  · exact Finset.mem_biUnion.mpr ⟨0, by simp,
      mem_startsWithDivisibleOffset.mpr ⟨hxblock, by simpa [hr] using hdvd⟩⟩
  · have heq' : x - 1 + (j + 1) = n := by omega
    exact Finset.mem_biUnion.mpr ⟨j + 1, Finset.mem_range.mpr (by omega),
      mem_startsWithDivisibleOffset.mpr ⟨hxblock, heq' ▸ hdvd⟩⟩

/-- The finite one-prime start count, with no deletion of exceptional sites. -/
theorem card_allStartsUsingPrime_le {N L Y p : ℕ} (hN : 1 ≤ N) (hLY : L ≤ Y) (hpY : Y < p) :
    ((allStartsUsingPrime N L Y p).card : ℝ) ≤ (L + 1 : ℝ) * ((N : ℝ) / p + 1) := by
  have hp : 0 < p := by omega
  calc
    _ ≤ (((Finset.range (L + 1)).biUnion fun i => startsWithDivisibleOffset N p i).card : ℝ) := by
      exact_mod_cast Finset.card_le_card (allStartsUsingPrime_subset_offsetUnion hN)
    _ ≤ ∑ i ∈ Finset.range (L + 1), ((startsWithDivisibleOffset N p i).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ Finset.range (L + 1), ((N : ℝ) / p + 1) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ p + 1 := by have := Finset.mem_range.mp hi; omega
      have hcast := (Rat.cast_le (K := ℝ)).mpr (card_startsWithDivisibleOffset_cast_le hN hp hi')
      simpa only [Rat.cast_natCast, Rat.cast_add, Rat.cast_div, Rat.cast_one] using hcast
    _ = _ := by simp; ring

/-- Exact neighbor cover by the large-prime coordinates of the chosen start. -/
theorem cutoffNeighbors_subset_prime_cover {N L Y x : ℕ} {mask : Finset ℕ}
    (hmask : mask ⊆ dyadicBlock N) :
    cutoffNeighbors L Y mask x ⊆ (largePrimeCoordinates x L Y).biUnion
      fun p => allStartsUsingPrime N L Y p := by
  intro y hy
  obtain ⟨hymask, _, p, hp⟩ := mem_cutoffNeighbors.mp hy
  obtain ⟨hpx, hpy⟩ := Finset.mem_inter.mp hp
  exact Finset.mem_biUnion.mpr ⟨p, hpx, mem_allStartsUsingPrime.mpr ⟨hmask hymask, hpy⟩⟩

/-- Finite version of (B.3), uniformly at every site, not only at good ones. -/
theorem card_cutoffNeighbors_le {N L Y x : ℕ} (hN : 2 ≤ N) (hL : L ≤ N)
    (hLY : L ≤ Y) (hY : 1 < Y) {mask : Finset ℕ} (hmask : mask ⊆ dyadicBlock N)
    (hx : x ∈ dyadicBlock N) :
    ((cutoffNeighbors L Y mask x).card : ℝ) ≤
      (L + 1 : ℝ) ^ 2 * (Real.log (3 * N : ℕ) / Real.log Y) * ((N : ℝ) / Y + 1) := by
  have hYpos : (0 : ℝ) < Y := by exact_mod_cast (show 0 < Y by omega)
  have hper := card_largePrimeCoordinates_le hN hL hY hx
  have hcount : ((cutoffNeighbors L Y mask x).card : ℝ) ≤
      ((largePrimeCoordinates x L Y).card : ℝ) * ((L + 1 : ℝ) * ((N : ℝ) / Y + 1)) := by
    calc
      _ ≤ (((largePrimeCoordinates x L Y).biUnion fun p => allStartsUsingPrime N L Y p).card : ℝ) := by
        exact_mod_cast Finset.card_le_card (cutoffNeighbors_subset_prime_cover hmask)
      _ ≤ ∑ p ∈ largePrimeCoordinates x L Y, ((allStartsUsingPrime N L Y p).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _p ∈ largePrimeCoordinates x L Y, (L + 1 : ℝ) * ((N : ℝ) / Y + 1) := by
        apply Finset.sum_le_sum
        intro p hp
        obtain ⟨n, _, hpn⟩ := mem_largePrimeCoordinates.mp hp
        have hpY := (prime_and_large_of_mem_largeOddPrimeSupport hpn).2
        exact (card_allStartsUsingPrime_le (by omega) hLY hpY).trans (by
          gcongr)
      _ = _ := by simp
  calc
    _ ≤ _ := hcount
    _ ≤ ((L + 1 : ℝ) * (Real.log (3 * N : ℕ) / Real.log Y)) *
        ((L + 1 : ℝ) * ((N : ℝ) / Y + 1)) := mul_le_mul_of_nonneg_right hper (by positivity)
    _ = _ := by ring

/-- The actual maximum degree obeys the same bound on every mask. -/
theorem cutoffMaxDegree_le {N L Y : ℕ} (hN : 2 ≤ N) (hL : L ≤ N)
    (hLY : L ≤ Y) (hY : 1 < Y) {mask : Finset ℕ} (hmask : mask ⊆ dyadicBlock N) :
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

/-- The ordered edge count is bounded by the number of sites times the actual maximum degree. -/
theorem card_maskedSupportEdges_le_card_mul_maxDegree (L Y : ℕ) (mask : Finset ℕ) :
    (maskedSupportEdges L Y mask).card ≤ mask.card * cutoffMaxDegree L Y mask := by
  have hcover : maskedSupportEdges L Y mask ⊆ mask.biUnion
      (fun x => (cutoffNeighbors L Y mask x).image fun y => (x, y)) := by
    intro p hp
    obtain ⟨hx, hy, ha⟩ := mem_maskedSupportEdges.mp hp
    exact Finset.mem_biUnion.mpr ⟨p.1, hx,
      Finset.mem_image.mpr ⟨p.2, mem_cutoffNeighbors.mpr ⟨hy, ha⟩, rfl⟩⟩
  calc
    _ ≤ (mask.biUnion (fun x => (cutoffNeighbors L Y mask x).image fun y => (x, y))).card :=
      Finset.card_le_card hcover
    _ ≤ ∑ x ∈ mask, ((cutoffNeighbors L Y mask x).image fun y => (x, y)).card := Finset.card_biUnion_le
    _ ≤ ∑ x ∈ mask, (cutoffNeighbors L Y mask x).card := Finset.sum_le_sum fun _ _ => Finset.card_image_le
    _ ≤ ∑ _x ∈ mask, cutoffMaxDegree L Y mask := by
      apply Finset.sum_le_sum
      intro x hx
      exact Finset.le_sup (f := fun x => (cutoffNeighbors L Y mask x).card) hx
    _ = _ := by simp

/-- Normalized maximum-degree bound, with the two cutoff contributions explicit. -/
theorem normalized_cutoffMaxDegree_le {N L Y : ℕ} (hN : 2 ≤ N) (hL : L ≤ N)
    (hLY : L ≤ Y) (hY : 1 < Y) {mask : Finset ℕ} (hmask : mask ⊆ dyadicBlock N) :
    (cutoffMaxDegree L Y mask : ℝ) / N ≤
      (L + 1 : ℝ) ^ 2 * (Real.log (3 * N : ℕ) / Real.log Y) * (1 / (Y : ℝ) + 1 / N) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  calc
    _ ≤ ((L + 1 : ℝ) ^ 2 * (Real.log (3 * N : ℕ) / Real.log Y) * ((N : ℝ) / Y + 1)) / N :=
      div_le_div_of_nonneg_right (cutoffMaxDegree_le hN hL hLY hY hmask) hNr.le
    _ = _ := by field_simp

/-- An unconditional normalized edge envelope on the full mask, including bad sites. -/
theorem normalized_maskedSupportEdges_le {N L Y : ℕ} (hN : 2 ≤ N) (hL : L ≤ N)
    (hLY : L ≤ Y) (hY : 1 < Y) {mask : Finset ℕ} (hmask : mask ⊆ dyadicBlock N) :
    ((maskedSupportEdges L Y mask).card : ℝ) / (N : ℝ) ^ 2 ≤
      (L + 1 : ℝ) ^ 2 * (Real.log (3 * N : ℕ) / Real.log Y) * (1 / (Y : ℝ) + 1 / N) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hcard : mask.card ≤ N := by
    exact (Finset.card_le_card hmask).trans_eq (by simp [dyadicBlock]; omega)
  have hedges : ((maskedSupportEdges L Y mask).card : ℝ) ≤ (N : ℝ) * cutoffMaxDegree L Y mask := by
    exact_mod_cast (card_maskedSupportEdges_le_card_mul_maxDegree L Y mask).trans
      (Nat.mul_le_mul_right _ hcard)
  calc
    _ ≤ ((N : ℝ) * cutoffMaxDegree L Y mask) / (N : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hedges (by positivity)
    _ = (cutoffMaxDegree L Y mask : ℝ) / N := by field_simp
    _ ≤ _ := normalized_cutoffMaxDegree_le hN hL hLY hY hmask

end
end PaperC.V282.CutoffGraphDegree
