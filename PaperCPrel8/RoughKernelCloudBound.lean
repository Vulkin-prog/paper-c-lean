import PaperCPrel8.UniformGridFibres
import PaperCPrel8.RoughKernelExponent
import PaperCPrel8.RoughKernelRegularity
import PaperCPrel8.RoughKernelDeletion

/-! # The multi-source union bound for a fixed-size uniform target cloud -/
namespace PaperC.Prel8.RoughKernelCloudBound
open Finset LargeOddKernel RoughKernelAllocation RoughKernelExponent RoughKernelRegularity
open UniformGridFibres RoughKernelDeletion ArratiaGoldsteinGordonInput
noncomputable section
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- Finite union bound, with a covering implication rather than an event equality. -/
theorem probability_cover {Ω ι : Type*} [Fintype Ω] [Fintype ι] (mu : FinitePMF Ω)
    (P : Ω → Prop) (E : ι → Ω → Prop) (hcover : ∀ w, P w → ∃ i, E i w) :
    eventProbability mu P ≤ ∑ i, eventProbability mu (E i) := by
  classical
  unfold eventProbability
  rw [sum_comm]
  apply sum_le_sum
  intro w _
  by_cases hp : P w
  · obtain ⟨i,hi⟩ := hcover w hp
    rw [ite_eq_left hp]
    have h := single_le_sum (f := fun i ↦ if E i w then mu.prob w else 0)
      (fun j _ ↦ by split_ifs <;> first | exact mu.nonneg w | exact le_rfl) (mem_univ i)
    simpa only [ite_eq_left hi] using h
  · rw [ite_eq_right hp]
    exact sum_nonneg (fun i _ ↦ by split_ifs <;> first | exact mu.nonneg w | exact le_rfl)

/-- A fixed-source allocation bound with any larger weight z. -/
theorem hosting_le (n h Q Y m : ℕ) (hn : 0<n) (hr : largeOddKernel Y m ≤ 2*n)
    (T z : ℝ) (hT : 0<T) (hz : 1≤z) (hbase : 3*(h:ℝ)*(Q+1) ≤ z)
    (hzY : z<Y) (hTr : T≤(largeOddKernel Y m:ℝ)) :
    eventProbability (gridLaw n h hn) (fun J ↦ ∀ p ∈ largeOddPrimeSupport Y m,
      ∃ b : Fin h, ∃ a : Fin (Q+1), p ∣ J.val b+a.val) ≤ T^(-1+Real.log z/Real.log Y) := by
  apply (rough_allocation_probability n h Q Y m hn hr).trans
  apply le_trans _ (kernel_weight_le Y m T z hT hz hzY hTr)
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact pow_le_pow_left₀ (by positivity) hbase _

def HostedAt {k : ℕ} (Q Y : ℕ) (J : Fin k → ℕ) (i : Fin k) (a : Fin (Q+1)) : Prop :=
  ∀ p ∈ largeOddPrimeSupport Y (J i+a.val), ∃ l : Fin k, l≠i ∧ ∃ b : Fin (Q+1), p ∣ J l+b.val

/-- Expose one index, apply CRT to the remaining independent indices, then average. -/
theorem occurrence_probability_le (n h Q Y : ℕ) (hn : 0<n) (hQ : Q≤n)
    (T z : ℝ) (hT : 0<T) (hz : 1≤z) (hbase : 3*(h:ℝ)*(Q+1) ≤ z) (hzY : z<Y)
    (i : Fin (h+1)) (a : Fin (Q+1)) :
    eventProbability (gridLaw n (h+1) hn)
      (fun J ↦ T≤(largeOddKernel Y (J.val i+a.val):ℝ) ∧ HostedAt Q Y J.val i a) ≤
      T^(-1+Real.log z/Real.log Y) := by
  let R := fun j (K : Fin h → ℕ) ↦ T≤(largeOddKernel Y (j+a.val):ℝ) ∧
    ∀ p ∈ largeOddPrimeSupport Y (j+a.val), ∃ b : Fin h, ∃ d : Fin (Q+1), p ∣ K b+d.val
  apply probability_le_of_fibres n h hn i
    (fun J ↦ T≤(largeOddKernel Y (J i+a.val):ℝ) ∧ HostedAt Q Y J i a) R _
  · intro j _ J _ hJ hj
    refine ⟨by simpa only [hj] using hJ.1,?_⟩
    intro p hp
    have hp' : p ∈ largeOddPrimeSupport Y (J i+a.val) := by simpa only [hj] using hp
    obtain ⟨l,hli,b,hdiv⟩ := hJ.2 p hp'
    obtain ⟨t,ht⟩ := Fin.exists_succAbove_eq hli
    exact ⟨t,b,by simpa only [ht] using hdiv⟩
  · intro j hj
    by_cases hTr : T≤(largeOddKernel Y (j+a.val):ℝ)
    · have hr : largeOddKernel Y (j+a.val) ≤ 2*n := by
        apply (largeOddKernel_le (by have := (mem_Icc.mp hj).1; omega)).trans
        have := (mem_Icc.mp hj).2
        have := a.isLt
        omega
      have hb := hosting_le n h Q Y (j+a.val) hn hr T z hT hz hbase hzY hTr
      rw [probability_eq n h hn (fun J ↦ ∀ p ∈ largeOddPrimeSupport Y (j+a.val),
        ∃ b : Fin h, ∃ d : Fin (Q+1), p ∣ J b+d.val)] at hb
      have hc := (div_le_iff₀ (pow_pos (by exact_mod_cast hn : (0:ℝ)<n) h)).mp hb
      rw [mul_comm] at hc
      convert hc using 2
      congr 2
      ext J
      simp [R,hTr]
    · simp only [R,hTr,false_and,filter_false,card_empty,Nat.cast_zero]
      positivity

/-- Uniform weight version for all cloud sizes below a later cutoff. -/
theorem regularity_probability_le_weight (n h Q Y : ℕ) (hn : 0<n) (hQn : Q≤n) (hQY : Q<Y)
    (T z : ℝ) (hT : 0<T) (hz : 1≤z) (hbase : 3*(h:ℝ)*(Q+1)≤z) (hzY : z<Y) :
    eventProbability (gridLaw n (h+1) hn)
      (fun J ↦ (∀ i : Fin (h+1), ∀ a : Fin (Q+1), T≤(largeOddKernel Y (J.val i+a.val):ℝ)) ∧
        ¬Regular Q Y J.val) ≤
      ((h+1:ℕ):ℝ)*(Q+1)*T^(-1+Real.log z/Real.log Y) := by
  have hc := probability_cover (gridLaw n (h+1) hn)
    (fun J ↦ (∀ i : Fin (h+1), ∀ a : Fin (Q+1), T≤(largeOddKernel Y (J.val i+a.val):ℝ)) ∧ ¬Regular Q Y J.val)
    (fun (b : Fin (h+1) × Fin (Q+1)) J ↦
      T≤(largeOddKernel Y (J.val b.1+b.2.val):ℝ) ∧ HostedAt Q Y J.val b.1 b.2)
    (fun J hJ ↦ by
      obtain ⟨i,a,ha⟩ := failure_hosted Q Y J.val hQY hJ.2
      exact ⟨(i,a),hJ.1 i a,ha⟩)
  apply hc.trans
  apply (sum_le_sum (fun b _ ↦ occurrence_probability_le n h Q Y hn hQn T z hT hz hbase hzY b.1 b.2)).trans_eq
  simp [Fintype.card_prod,mul_assoc]

/-- G.2's full fixed-size bad-cloud probability, including all source occurrences. -/
theorem regularity_probability_le (n h Q Y : ℕ) (hn : 0<n) (hQn : Q≤n) (hQY : Q<Y)
    (T : ℝ) (hT : 0<T) (hzY : 3*((h+1:ℕ):ℝ)*(Q+1)<Y) :
    eventProbability (gridLaw n (h+1) hn)
      (fun J ↦ (∀ i : Fin (h+1), ∀ a : Fin (Q+1), T≤(largeOddKernel Y (J.val i+a.val):ℝ)) ∧
        ¬Regular Q Y J.val) ≤
      ((h+1:ℕ):ℝ)*(Q+1)*T^(-1+Real.log (3*((h+1:ℕ):ℝ)*(Q+1))/Real.log Y) := by
  let z : ℝ := 3*((h+1:ℕ):ℝ)*(Q+1)
  have hz : 1≤z := by dsimp [z]; push_cast; nlinarith [(Nat.cast_nonneg h : (0:ℝ)≤h),(Nat.cast_nonneg Q : (0:ℝ)≤Q)]
  have hbase : 3*(h:ℝ)*(Q+1)≤z := by dsimp [z]; push_cast; nlinarith [(Nat.cast_nonneg Q : (0:ℝ)≤Q)]
  have hc := probability_cover (gridLaw n (h+1) hn)
    (fun J ↦ (∀ i : Fin (h+1), ∀ a : Fin (Q+1), T≤(largeOddKernel Y (J.val i+a.val):ℝ)) ∧ ¬Regular Q Y J.val)
    (fun (b : Fin (h+1) × Fin (Q+1)) J ↦
      T≤(largeOddKernel Y (J.val b.1+b.2.val):ℝ) ∧ HostedAt Q Y J.val b.1 b.2)
    (fun J hJ ↦ by
      obtain ⟨i,a,ha⟩ := failure_hosted Q Y J.val hQY hJ.2
      exact ⟨(i,a),hJ.1 i a,ha⟩)
  apply hc.trans
  apply (sum_le_sum (fun b _ ↦ occurrence_probability_le n h Q Y hn hQn T z hT hz hbase hzY b.1 b.2)).trans_eq
  simp [z,Fintype.card_prod,mul_assoc]

/-- Literal membership in the stronger good set discharges the kernel-threshold predicates. -/
theorem strong_good_probability_le (n h Q Y : ℕ) (hn : 0<n) (hQn : Q≤n) (hQY : Q<Y)
    (G : Finset ℕ) (T : ℝ) (hT : 0<T) (hzY : 3*((h+1:ℕ):ℝ)*(Q+1)<Y) :
    eventProbability (gridLaw n (h+1) hn)
      (fun J ↦ (∀ i, J.val i ∈ strongGood G Y Q ⌊T⌋₊) ∧ ¬Regular Q Y J.val) ≤
      ((h+1:ℕ):ℝ)*(Q+1)*T^(-1+Real.log (3*((h+1:ℕ):ℝ)*(Q+1))/Real.log Y) := by
  have hcover := probability_cover (gridLaw n (h+1) hn)
    (fun J ↦ (∀ i, J.val i ∈ strongGood G Y Q ⌊T⌋₊) ∧ ¬Regular Q Y J.val)
    (fun (_ : Unit) J ↦ (∀ i : Fin (h+1), ∀ a : Fin (Q+1), T≤(largeOddKernel Y (J.val i+a.val):ℝ)) ∧ ¬Regular Q Y J.val)
    (fun J hJ ↦ ⟨(),(fun i a ↦ ((mem_strongGood_floor G Y Q _ T hT.le).mp (hJ.1 i)).2 a |>.le),hJ.2⟩)
  simp only [Fintype.sum_unique] at hcover
  exact hcover.trans (regularity_probability_le n h Q Y hn hQn hQY T hT hzY)

end
end PaperC.Prel8.RoughKernelCloudBound
