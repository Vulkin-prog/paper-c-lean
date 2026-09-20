import PaperCPrel8.RoughKernelStrongCount
import PaperCPrel8.MicroscopicDeletedSites

/-! # The actual G_theta and its complete complement

A nontrivial rough kernel already guarantees an odd prime above Y. Thus the
original bad-pivot deletion is contained in the stronger kernel deletion.
-/
namespace PaperC.Prel8.RoughKernelGoodSet
open RoughKernelThreshold RoughKernelDeletion RoughKernelStrongCount
open MicroscopicGoodField MicroscopicDeletedSites OddPrimePivot LargeOddKernel
open V282.SaddleParameters V282.SaddleScales V282.PrimeEulerPNT
open Set Filter Topology
noncomputable section
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

def paperGood (M n L E Y T : ℕ) : Finset ℕ :=
  strongGood (goodSites M n L E Y) Y (L+E+1) T

/-- A nontrivial rough kernel certifies the original largest-odd-prime condition. -/
theorem pivot_of_kernel {Y T m : ℕ} (hY : 1 ≤ Y) (hT : 1 ≤ T)
    (h : T < largeOddKernel Y m) : Y < largestOddPrime m := by
  by_contra hn
  have hk := (largeOddKernel_eq_one_iff_hDefective Y m).mpr
    ((largestOddPrime_le_iff hY).mp (Nat.le_of_not_gt hn))
  omega

/-- The actual stronger good set is exactly the deep part of the all-grid kernel set. -/
theorem paperGood_eq (M n L E Y T : ℕ) (hY : 1 ≤ Y) (hT : 1 ≤ T) :
    paperGood M n L E Y T =
      (strongGood (Finset.Icc 1 n) Y (L+E+1) T).filter
        (fun j ↦ ⌈Real.sqrt M⌉₊ ≤ j+1) := by
  ext j
  simp only [paperGood, mem_strongGood, goodSites, Finset.mem_filter]
  constructor
  · rintro ⟨⟨hj,hd,_⟩,hk⟩
    exact ⟨⟨hj,hk⟩,hd⟩
  · rintro ⟨⟨hj,hk⟩,hd⟩
    refine ⟨⟨hj,hd,?_⟩,hk⟩
    intro a
    exact pivot_of_kernel hY hT (hk a)

/-- No second charge for old bad pivots: only shallow sites and small kernels remain. -/
theorem total_card_le (M n L E Y T : ℕ) (hY : 1 ≤ Y) (hT : 1 ≤ T) :
    ((Finset.Icc 1 n) \ paperGood M n L E Y T).card ≤
      ⌈Real.sqrt M⌉₊ + ((Finset.Icc 1 n) \ strongGood (Finset.Icc 1 n) Y (L+E+1) T).card := by
  have hs : (Finset.Icc 1 n) \ paperGood M n L E Y T ⊆
      ((Finset.Icc 1 n).filter (fun j ↦ j+1 < ⌈Real.sqrt M⌉₊)) ∪
        ((Finset.Icc 1 n) \ strongGood (Finset.Icc 1 n) Y (L+E+1) T) := by
    intro j hj
    obtain ⟨hj,hn⟩ := Finset.mem_sdiff.mp hj
    by_cases hd : ⌈Real.sqrt M⌉₊ ≤ j+1
    · apply Finset.mem_union_right
      refine Finset.mem_sdiff.mpr ⟨hj, ?_⟩
      intro hk
      apply hn
      rw [paperGood_eq M n L E Y T hY hT]
      exact Finset.mem_filter.mpr ⟨hk,hd⟩
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hj,by omega⟩)
  exact (Finset.card_le_card hs).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (shallow_card_le M n) _))

/-- Literal total-deletion estimate with the stronger threshold, under the original PNT input. -/
theorem total_count (hPNT : PrimeNumberTheoremRemainder)
    (beta theta epsilon : ℝ) (hbeta : 0 < beta) (htheta : 0 ≤ theta) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ n L E : ℕ,
      M ≤ 2*(n+(L+E+1)) → L+E+1 ≤ n → (L+E+1:ℝ) ≤ beta*Real.log M →
      (((Finset.Icc 1 n) \ paperGood M n L E
        ⌊Real.exp (saddleCutoff 1 (Real.log M))⌋₊ ⌊threshold theta (Real.log M)⌋₊).card : ℝ) ≤
      (⌈Real.sqrt M⌉₊ : ℝ) + n * Real.exp
        (-saddleCutoff 1 (Real.log M) + (theta+epsilon)*saddleNu 1 (Real.log M)) := by
  obtain ⟨Mc,hc⟩ := added_count hPNT beta theta epsilon hbeta htheta hepsilon
  have hl : Tendsto (fun M : ℕ ↦ Real.log M) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨Mh,hh⟩ := eventually_atTop.mp (hl.eventually (eventually_ge_atTop (saddleThreshold 1)))
  refine ⟨max Mc Mh, ?_⟩
  intro M hM n L E hp hq hb
  have hH := hh M (by omega)
  have hY : 1 ≤ ⌊Real.exp (saddleCutoff 1 (Real.log M))⌋₊ :=
    (Nat.one_le_floor_iff _).mpr (Real.one_le_exp (saddleCutoff_pos (by norm_num) hH).le)
  have hT : 1 ≤ ⌊threshold theta (Real.log M)⌋₊ := by
    apply (Nat.one_le_floor_iff _).mpr
    apply Real.one_le_exp
    have hu := (saddleParameter_spec (by norm_num : (0:ℝ)<1) hH).1
    have hHp := (saddleThreshold_pos (by norm_num : (0:ℝ)<1)).trans_le hH
    exact div_nonneg (mul_nonneg htheta hHp.le) (by linarith [saddleParameterBase_ge_two])
  have hfinite := total_card_le M n L E _ _ hY hT
  have hcast : (((Finset.Icc 1 n) \ paperGood M n L E
      ⌊Real.exp (saddleCutoff 1 (Real.log M))⌋₊ ⌊threshold theta (Real.log M)⌋₊).card : ℝ) ≤
      (⌈Real.sqrt M⌉₊ : ℝ) + (((Finset.Icc 1 n) \ strongGood (Finset.Icc 1 n)
        ⌊Real.exp (saddleCutoff 1 (Real.log M))⌋₊ (L+E+1) ⌊threshold theta (Real.log M)⌋₊).card : ℝ) := by
    exact_mod_cast hfinite
  exact hcast.trans (add_le_add (le_refl _) (hc M (by omega) n (L+E+1) hp hq (by exact_mod_cast hb) _ (fun _ h ↦ h)))

end
end PaperC.Prel8.RoughKernelGoodSet
