import PaperCPrel8.PoissonCloudMixture

/-! # Regularity of an actual Poisson-size uniform grid cloud

This constructs and bounds the ordered spatial cloud. Its identification with
the existing full signed/excess target is a separate remaining step.
-/
namespace PaperC.Prel8.PoissonRegularCloud
open Finset LargeOddKernel RoughKernelAllocation RoughKernelRegularity RoughKernelCloudBound
open UniformGridFibres RoughKernelDeletion ArratiaGoldsteinGordonInput PoissonCloudMixture
open scoped NNReal
noncomputable section
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- Two-event covering inequality on the actual finite probability space. -/
theorem probability_two_cover {Ω : Type*} [Fintype Ω] (mu : FinitePMF Ω)
    (P A B : Ω → Prop) (h : ∀ w, P w → A w ∨ B w) :
    eventProbability mu P ≤ eventProbability mu A+eventProbability mu B := by
  have hc := probability_cover mu P (fun b : Bool ↦ if b then A else B)
    (fun w hw ↦ by rcases h w hw with ha | hb; exact ⟨true,ha⟩; exact ⟨false,hb⟩)
  simpa [add_comm] using hc

/-- Exact uniform-coordinate fractions give the expected bad-site union bound. -/
theorem deleted_probability_le (n h : ℕ) (hn : 0<n) (G : Finset ℕ) :
    eventProbability (gridLaw n (h+1) hn) (fun J ↦ ∃ i, J.val i ∉ G) ≤
      ((h+1:ℕ):ℝ)*(((Icc 1 n) \ G).card:ℝ)/n := by
  have hc := probability_cover (gridLaw n (h+1) hn) (fun J ↦ ∃ i, J.val i ∉ G)
    (fun i J ↦ J.val i ∉ G) (fun _ h ↦ h)
  apply hc.trans
  apply (sum_le_sum (fun i _ ↦ coordinate_deleted_le n h hn i G)).trans_eq
  simp [mul_div_assoc]

/-- Full failure at fixed size: bad sites plus the all-source CRT regularity cost. -/
theorem fixed_cloud_failure_le (n h Q Y : ℕ) (hn : 0<n) (hQn : Q≤n) (hQY : Q<Y)
    (G : Finset ℕ) (T z : ℝ) (hT : 0<T) (hz : 1≤z) (hbase : 3*(h:ℝ)*(Q+1)≤z) (hzY : z<Y)
    (hgood : ∀ j∈G, ∀ a : Fin (Q+1), T≤(largeOddKernel Y (j+a.val):ℝ)) :
    eventProbability (gridLaw n (h+1) hn)
      (fun J ↦ ¬((∀ i, J.val i ∈ G) ∧ Regular Q Y J.val)) ≤
      ((h+1:ℕ):ℝ)*(((Icc 1 n) \ G).card:ℝ)/n+
      ((h+1:ℕ):ℝ)*(Q+1)*T^(-1+Real.log z/Real.log Y) := by
  have hc := probability_two_cover (gridLaw n (h+1) hn)
    (fun J ↦ ¬((∀ i, J.val i ∈ G) ∧ Regular Q Y J.val))
    (fun J ↦ ∃ i, J.val i ∉ G)
    (fun J ↦ (∀ i, J.val i ∈ G) ∧ ¬Regular Q Y J.val)
    (fun J hJ ↦ by
      by_cases hg : ∀ i, J.val i ∈ G
      · exact Or.inr ⟨hg,fun hr ↦ hJ ⟨hg,hr⟩⟩
      · exact Or.inl (not_forall.mp hg))
  have hg := probability_cover (gridLaw n (h+1) hn)
    (fun J ↦ (∀ i, J.val i ∈ G) ∧ ¬Regular Q Y J.val)
    (fun (_ : Unit) J ↦ (∀ i : Fin (h+1), ∀ a : Fin (Q+1), T≤(largeOddKernel Y (J.val i+a.val):ℝ)) ∧ ¬Regular Q Y J.val)
    (fun J hJ ↦ ⟨(),(fun i a ↦ hgood _ (hJ.1 i) a),hJ.2⟩)
  simp only [Fintype.sum_unique] at hg
  exact hc.trans (add_le_add (deleted_probability_le n h hn G)
    (hg.trans (regularity_probability_le_weight n h Q Y hn hQn hQY T z hT hz hbase hzY)))

/-- An actual normalized random-size ordered cloud with iid uniform grid positions. -/
abbrev Cloud (n : ℕ) := Σ k : ℕ, grid n k

def badCloud (n Q Y K : ℕ) (G : Finset ℕ) (s : Cloud n) : Prop :=
  K<s.1 ∨ ¬((∀ i, s.2.val i ∈ G) ∧ Regular Q Y s.2.val)

/-- Finite, explicit regular-cloud estimate after averaging the count, including its actual Poisson tail. -/
theorem poisson_failure_le (n Q Y K : ℕ) (hn : 0<n) (hK : 1≤K) (hQn : Q≤n) (hQY : Q<Y)
    (rate : ℝ≥0) (hsize : 2*(rate:ℝ)≤K) (G : Finset ℕ) (T : ℝ) (hT : 0<T)
    (hzY : 3*(K:ℝ)*(Q+1)<Y)
    (hgood : ∀ j∈G, ∀ a : Fin (Q+1), T≤(largeOddKernel Y (j+a.val):ℝ)) :
    probability rate (fun k ↦ gridLaw n k hn) (badCloud n Q Y K G) ≤
      (rate:ℝ)*(((Icc 1 n) \ G).card:ℝ)/n+
      (K:ℝ)*(Q+1)*T^(-1+Real.log (3*(K:ℝ)*(Q+1))/Real.log Y)+
      Real.exp (-((2*Real.log 2-1)*(rate:ℝ))) := by
  let z : ℝ := 3*(K:ℝ)*(Q+1)
  have hz : 1≤z := by
    have hk : (1:ℝ)≤K := by exact_mod_cast hK
    dsimp [z]
    nlinarith [(Nat.cast_nonneg Q : (0:ℝ)≤Q)]
  have hb := probability_le_affine_cutoff rate (fun k ↦ gridLaw n k hn) (badCloud n Q Y K G) K
    ((((Icc 1 n) \ G).card:ℝ)/n) ((K:ℝ)*(Q+1)*T^(-1+Real.log z/Real.log Y))
    (by positivity) (by positivity) (fun k hk ↦ by
      cases k with
      | zero => simp [badCloud,Regular,eventProbability]; positivity
      | succ h =>
        have he : eventProbability (gridLaw n (h+1) hn) (fun w ↦ badCloud n Q Y K G ⟨h+1,w⟩) =
            eventProbability (gridLaw n (h+1) hn) (fun J ↦ ¬((∀ i, J.val i ∈ G) ∧ Regular Q Y J.val)) := by
          congr 1
          funext w
          simp [badCloud,show ¬K<h+1 by omega]
        rw [he]
        have hbase : 3*(h:ℝ)*(Q+1)≤z := by
          have hle : (h:ℝ)≤K := by exact_mod_cast (show h≤K by omega)
          dsimp [z]
          nlinarith [(Nat.cast_nonneg Q : (0:ℝ)≤Q)]
        have hf := fixed_cloud_failure_le n h Q Y hn hQn hQY G T z hT hz hbase hzY hgood
        have hle : ((h+1:ℕ):ℝ)≤K := by exact_mod_cast hk
        have hw := mul_le_mul_of_nonneg_right hle (show 0≤(Q+1:ℝ)*T^(-1+Real.log z/Real.log Y) by positivity)
        calc
          _ ≤ _ := hf
          _ ≤ _ := by simp only [div_eq_mul_inv] at hw ⊢; nlinarith only [hw])
  have ht := PoissonCloudTail.doubled_tail_le rate K hsize
  dsimp only [z] at hb
  calc
    _ ≤ _ := hb
    _ ≤ _ := by simp only [div_eq_mul_inv]; nlinarith only [ht]

/-- Application to the literal stronger good set and the ceiling 2*Lambda. -/
theorem stronger_poisson_failure_le (n Q Y : ℕ) (hn : 0<n) (hQn : Q≤n) (hQY : Q<Y)
    (rate : ℝ≥0) (hrate : 1≤(rate:ℝ)) (G : Finset ℕ) (T : ℝ) (hT : 0<T)
    (hzY : 3*(⌈2*(rate:ℝ)⌉₊:ℝ)*(Q+1)<Y) :
    probability rate (fun k ↦ gridLaw n k hn)
      (badCloud n Q Y ⌈2*(rate:ℝ)⌉₊ (strongGood G Y Q ⌊T⌋₊)) ≤
      (rate:ℝ)*(((Icc 1 n) \ strongGood G Y Q ⌊T⌋₊).card:ℝ)/n+
      (⌈2*(rate:ℝ)⌉₊:ℝ)*(Q+1)*T^(-1+Real.log (3*(⌈2*(rate:ℝ)⌉₊:ℝ)*(Q+1))/Real.log Y)+
      Real.exp (-((2*Real.log 2-1)*(rate:ℝ))) := by
  have hc := Nat.le_ceil (2*(rate:ℝ))
  have hk : 1≤⌈2*(rate:ℝ)⌉₊ := by exact_mod_cast (show (1:ℝ)≤(⌈2*(rate:ℝ)⌉₊:ℝ) by linarith)
  exact poisson_failure_le n Q Y _ hn hk hQn hQY rate hc _ T hT hzY
    (fun j hj a ↦ ((mem_strongGood_floor G Y Q j T hT.le).mp hj).2 a |>.le)

end
end PaperC.Prel8.PoissonRegularCloud
