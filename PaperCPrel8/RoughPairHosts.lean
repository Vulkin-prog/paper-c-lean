import PaperCPrel8.RoughKernelCloudBound
import PaperCPrel8.RoughKernelReciprocal

/-! # Single-target CRT hosting count for the rough pair layer -/
namespace PaperC.Prel8.RoughPairHosts
open Finset RoughKernelCRT LargeOddKernel
noncomputable section
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

def targets (X Q Y m : ℕ) : Finset ℕ :=
  (Icc 1 X).filter (fun y ↦ ∀ p ∈ largeOddPrimeSupport Y m,
    ∃ b : Fin (Q+1), p ∣ y+b.val)

/-- The one-block CRT loss is two overall, not a factor for each rough prime. -/
theorem targets_count (X Q Y m : ℕ) (hm : 0<m) (hmX : m≤X) :
    ((targets X Q Y m).card:ℝ)≤
      2*(X:ℝ)*(Q+1)^ArithmeticFunction.cardDistinctFactors (largeOddKernel Y m)/(largeOddKernel Y m:ℝ) := by
  let S := largeOddPrimeSupport Y m
  let modulus := fun p : S ↦ p.val
  have hp (p : S) : (modulus p).Prime := (prime_and_large_of_mem_largeOddPrimeSupport p.property).1
  have he : (∏ p : S, modulus p)=largeOddKernel Y m :=
    (prod_subtype S (fun _ ↦ Iff.rfl) (fun p : ℕ ↦ p)).symm
  have heR : (∏ p : S, (modulus p:ℝ))=(largeOddKernel Y m:ℝ) := by exact_mod_cast he
  have hr : (largeOddKernel Y m:ℝ)≤X := by exact_mod_cast (largeOddKernel_le hm).trans hmX
  have hr0 : (0:ℝ)<largeOddKernel Y m := by exact_mod_cast Nat.pos_of_ne_zero (largeOddKernel_ne_zero Y m)
  have hc (a : S → Fin (Q+1)) :
      ((solutions X univ modulus (fun p ↦ (a p).val)).card:ℝ)≤2*(X:ℝ)/(largeOddKernel Y m:ℝ) := by
    have h := solutions_count X univ modulus (fun p ↦ (a p).val) hp Subtype.val_injective
    rw [heR] at h
    apply h.trans
    apply (le_div_iff₀ hr0).mpr
    field_simp
    linarith
  have hsub : targets X Q Y m ⊆ (univ : Finset (S → Fin (Q+1))).biUnion
      (fun a ↦ solutions X univ modulus (fun p ↦ (a p).val)) := by
    intro y hy
    obtain ⟨hy,hh⟩ := mem_filter.mp hy
    have hh' : ∀ p : S, ∃ b : Fin (Q+1), p.val ∣ y+b.val := fun p ↦ hh p.val p.property
    choose a ha using hh'
    exact mem_biUnion.mpr ⟨a,mem_univ _,(mem_solutions _ _ _ _ _).mpr ⟨hy,fun p _ ↦ ha p⟩⟩
  have hh : ((targets X Q Y m).card:ℝ)≤
      ∑ a : S → Fin (Q+1), ((solutions X univ modulus (fun p ↦ (a p).val)).card:ℝ) := by
    exact_mod_cast (card_le_card hsub).trans card_biUnion_le
  apply hh.trans
  apply (sum_le_sum (fun a _ ↦ hc a)).trans_eq
  simp only [sum_const,card_univ,Fintype.card_fun,Fintype.card_fin,Fintype.card_coe,nsmul_eq_mul,
    Nat.cast_pow,Nat.cast_add,Nat.cast_one]
  rw [show S.card=ArithmeticFunction.cardDistinctFactors (largeOddKernel Y m) from
    (cardDistinctFactors_largeOddKernel Y m).symm]
  ring

def hostedPairs (n Q Y : ℕ) : Finset (ℕ×ℕ) :=
  ((Icc 1 n)×ˢ(Icc 1 n)).filter (fun z ↦ ∃ a : Fin (Q+1),
    1<largeOddKernel Y (z.1+a.val) ∧
      ∀ p ∈ largeOddPrimeSupport Y (z.1+a.val), ∃ b : Fin (Q+1), p ∣ z.2+b.val)

/-- Count the source occurrence as (vertex,offset), with at most Q+1 offsets. -/
theorem hosted_pairs_count (n Q Y X : ℕ) (hX : n+Q≤X) :
    ((hostedPairs n Q Y).card:ℝ)≤
      2*(Q+1)*(X:ℝ)*∑ m∈(Icc 1 X).filter (fun m ↦ 1<largeOddKernel Y m),
        (Q+1)^ArithmeticFunction.cardDistinctFactors (largeOddKernel Y m)/(largeOddKernel Y m:ℝ) := by
  let S := (Icc 1 X).filter (fun m ↦ 1<largeOddKernel Y m)
  let F := fun m ↦ (univ : Finset (Fin (Q+1))).biUnion
    (fun a ↦ (targets X Q Y m).image (fun y ↦ (m-a.val,y)))
  have hs : hostedPairs n Q Y ⊆ S.biUnion F := by
    intro z hz
    obtain ⟨hgrid,a,ha,hh⟩ := mem_filter.mp hz
    obtain ⟨hx,hy⟩ := mem_product.mp hgrid
    have hx' := mem_Icc.mp hx
    have hy' := mem_Icc.mp hy
    have ha' := a.isLt
    refine mem_biUnion.mpr ⟨z.1+a.val,mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,by omega⟩,ha⟩,?_⟩
    refine mem_biUnion.mpr ⟨a,mem_univ _,mem_image.mpr ⟨z.2,?_,by simp⟩⟩
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hy'.1,by omega⟩,hh⟩
  have hc (m : ℕ) : (F m).card≤(Q+1)*(targets X Q Y m).card := by
    apply card_biUnion_le.trans
    calc
      _ ≤ ∑ a : Fin (Q+1), (targets X Q Y m).card := sum_le_sum (fun a _ ↦ card_image_le)
      _ = _ := by simp
  have hh : ((hostedPairs n Q Y).card:ℝ)≤∑ m∈S, (Q+1:ℝ)*(targets X Q Y m).card := by
    exact_mod_cast (card_le_card hs).trans (card_biUnion_le.trans (sum_le_sum (fun m _ ↦ hc m)))
  apply hh.trans
  calc
    _ ≤ ∑ m∈S, (Q+1:ℝ)*(2*(X:ℝ)*(Q+1)^ArithmeticFunction.cardDistinctFactors (largeOddKernel Y m)/(largeOddKernel Y m:ℝ)) := by
      apply sum_le_sum
      intro m hm
      have hm' := mem_Icc.mp (mem_filter.mp hm).1
      exact mul_le_mul_of_nonneg_left (targets_count X Q Y m (by omega) hm'.2) (by positivity)
    _ = _ := by rw [mul_sum]; apply sum_congr rfl; intro m hm; ring

end
end PaperC.Prel8.RoughPairHosts
