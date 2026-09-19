import PaperCPrel8.AffineDictionarySample

/-! # Exact one- and two-word probabilities under actual affine sampling -/
namespace PaperC.Prel8.AffineDictionaryInclusion
open PaperC PaperC.SectionThirteenFiniteBound
open PaperC.Prel8.AffineDictionarySample PaperC.Prel8.DictionaryAverage
open scoped BigOperators
noncomputable section
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- The probability that a uniformly selected surjection kills a word. -/
def kernelFrequency (B r : ℕ) (u : Word B) : ℝ :=
  finiteUniformAverage (fun A : Surjection B r => if A.val u=0 then 1 else 0)

/-- Invertible linear coordinates preserve the uniform full-rank sample. -/
theorem kernelFrequency_equiv {B r : ℕ} (e : Word B ≃ₗ[F₂] Word B) (u : Word B) :
    kernelFrequency B r (e u)=kernelFrequency B r u := by
  unfold kernelFrequency finiteUniformAverage
  congr 1
  exact (precompose e).sum_comp (fun A : Surjection B r => if A.val u=0 then (1:ℝ) else 0)

/-- All nonzero words have the same actual kernel probability. -/
theorem kernelFrequency_nonzero {B r : ℕ} (u v : Word B) (hu : u ≠ 0) (hv : v ≠ 0) :
    kernelFrequency B r u=kernelFrequency B r v := by
  obtain ⟨e,he⟩ := exists_equiv_nonzero u v hu hv
  rw [← he]
  exact (kernelFrequency_equiv e u).symm

theorem kernelFrequency_zero {B r : ℕ} (hr : r ≤ B) : kernelFrequency B r 0=1 := by
  letI : Nonempty (Surjection B r) := surjection_nonempty hr
  simp only [kernelFrequency,map_zero,ite_true,environment_const]

/-- Double counting the real kernels gives their fixed fibre size. -/
theorem sum_kernelFrequency {B r : ℕ} (hr : r ≤ B) :
    (∑ u : Word B, kernelFrequency B r u)=(2:ℝ)^(B-r) := by
  letI : Nonempty (Surjection B r) := surjection_nonempty hr
  have hc (A : Surjection B r) : (∑ u : Word B, if A.val u=0 then (1:ℝ) else 0)=(2:ℝ)^(B-r) := by
    have h := congrArg (fun n : ℕ => (n:ℝ)) (card_dictionary (A,0))
    simpa [dictionary,Nat.cast_pow,Nat.cast_ofNat,← Finset.sum_filter] using h
  unfold kernelFrequency finiteUniformAverage
  rw [← Finset.sum_div,Finset.sum_comm]
  simp_rw [hc]
  exact environment_const _

/-- The exact kernel probability, including rank zero and full rank. -/
theorem kernelFrequency_eq {B r : ℕ} (hB : 1 ≤ B) (hr : r ≤ B) (u : Word B) (hu : u ≠ 0) :
    kernelFrequency B r u=((2:ℝ)^(B-r)-1)/((2:ℝ)^B-1) := by
  have hQ : (1:ℝ)<(2:ℝ)^B := one_lt_pow₀ (by norm_num) (by omega)
  have hsum := sum_kernelFrequency hr
  have hpoint (v : Word B) : kernelFrequency B r v=
      if v=0 then 1 else kernelFrequency B r u := by
    by_cases hv : v=0
    · subst v; simp [kernelFrequency_zero hr]
    · rw [ite_eq_right hv]; exact kernelFrequency_nonzero v u hv hu
  rw [Finset.sum_congr rfl (fun v _ => hpoint v)] at hsum
  have hc : Fintype.card (Word B)=2^B := by simp [Word,Fintype.card_fun,ZMod.card]
  have hh : (∑ v : Word B, if v=0 then (1:ℝ) else kernelFrequency B r u)=
      1+((2:ℝ)^B-1)*kernelFrequency B r u := by
    have hz : (Finset.univ.filter (fun v : Word B => v=0))={0} := by ext v; simp
    have hn : (Finset.univ.filter (fun v : Word B => ¬v=0))=Finset.univ.erase 0 := by ext v; simp [ne_comm]
    rw [Finset.sum_ite,hz,hn]
    simp [hc,Nat.cast_sub (Nat.one_le_pow B 2 (by decide)),mul_comm]
  rw [hh] at hsum
  apply (eq_div_iff (by linarith : (2:ℝ)^B-1 ≠ 0)).mpr
  nlinarith

/-- Uniform matrices and independent uniform offsets define the actual dictionary mean. -/
def affineAverage (B r : ℕ) (f : Finset (Word B) → ℝ) : ℝ :=
  finiteUniformAverage (fun s : Sample B r => f (dictionary s))

/-- Summing the independent offset leaves only equality of the two linear images. -/
theorem pair_probability_kernel (B r : ℕ) (u v : Word B) :
    affineAverage B r (fun W => if u ∈ W ∧ v ∈ W then 1 else 0)=
      kernelFrequency B r (u-v)/(2:ℝ)^r := by
  have hb (A : Surjection B r) :
      (∑ b : Word r, if A.val u=b ∧ A.val v=b then (1:ℝ) else 0)=
        if A.val (u-v)=0 then 1 else 0 := by
    simp only [map_sub,sub_eq_zero]
    by_cases h : A.val u=A.val v
    · simp [h]
    · have hf (b : Word r) : ¬(A.val u=b ∧ A.val v=b) := fun hh => h (hh.1.trans hh.2.symm)
      simp [hf,h]
  unfold affineAverage kernelFrequency finiteUniformAverage
  simp_rw [mem_dictionary]
  rw [Fintype.sum_prod_type]
  simp_rw [hb]
  simp only [Fintype.card_prod,Nat.cast_mul,Fintype.card_fun,Fintype.card_fin,ZMod.card,Nat.cast_pow,Nat.cast_ofNat]
  ring

end
end PaperC.Prel8.AffineDictionaryInclusion
