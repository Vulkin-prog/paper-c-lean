import PaperCV282.SignedExactMarks
import PaperCV282.DictionaryMarginalCap

/-!
# Uniform prescriptions on an actual finite union of marked values

A row is an integer in the set itself, so shared values are counted once.
Odd primes are private in the enclosing short interval and hence in the union.
-/
namespace PaperC.V282.ExactMarkedValueProbability

open Affine ConditionalStartProbability ConditionalDependencyGraph ConditionalAGGInstantiation
open ArratiaGoldsteinGordonInput PrescribedValues WindowValues DefectivePredicate

noncomputable section

/-- Every selected value has a genuine private prime in the common cylinder. -/
theorem selected_values_private_primes {C Y x B : ℕ} (hx : 2 ≤ x)
    (hcut : x-1+B ≤ C+1) (hY : B ≤ Y) (S : Finset ℕ)
    (hS : ∀ n ∈ S, x-1 ≤ n ∧ n < x-1+B)
    (hgood : ∀ n ∈ S, ¬HDefective Y n) :
    ∀ n : S, ∃ p : PrimeUpTo C, Y < p.val.val ∧ parityVec n.val p.val.val = 1 ∧
      ∀ m : S, m ≠ n → parityVec m.val p.val.val = 0 := by
  intro n
  have hn := hS n.val n.property
  let i : Fin B := ⟨n.val-(x-1),by omega⟩
  have hv : vertex x B i = n.val := by dsimp [vertex,i]; omega
  obtain ⟨p,hpY,hdiag,hoff⟩ := private_prime_of_not_defective hx hcut hY i (by rw [hv];exact hgood _ n.property)
  refine ⟨p,hpY,by rwa [hv] at hdiag,?_⟩
  intro m hmn
  have hm := hS m.val m.property
  let j : Fin B := ⟨m.val-(x-1),by omega⟩
  have hvj : vertex x B j = m.val := by dsimp [vertex,j]; omega
  have hji : j ≠ i := by
    intro heq
    apply hmn
    apply Subtype.ext
    rw [← hv,← hvj,heq]
  simpa only [hvj] using hoff j hji

/-- The actual conditional probability of any assignment on the union is exactly uniform. -/
theorem conditioned_selected_values_probability {C Y x B : ℕ} (hx : 2 ≤ x)
    (hcut : x-1+B ≤ C+1) (hY : B ≤ Y) (S : Finset ℕ)
    (hS : ∀ n ∈ S, x-1 ≤ n ∧ n < x-1+B)
    (hgood : ∀ n ∈ S, ¬HDefective Y n) (b : S → F₂) (sigma : SmallSample C Y) :
    eventProbability (largeUniformPMF C Y) (fun eta =>
      ∀ n : S, valueBit (assemble C Y sigma eta) n.val = b n) = 1/(2 : ℝ)^S.card := by
  classical
  letI instSolutionFintype : Fintype (Solution (largeValueSystem C Y (fun n : S => n.val))
      (conditionedValueRhs C Y (fun n : S => n.val) b sigma)) := probabilitySolutionFintype _ _
  have hprivate : ∀ n : S, ∃ eta : LargeSample C Y,
      largeValueSystem C Y (fun n : S => n.val) eta = Pi.single n 1 := by
    intro n
    obtain ⟨p,hpY,hdiag,hoff⟩ := selected_values_private_primes hx hcut hY S hS hgood n
    refine ⟨Pi.single (⟨p,hpY⟩ : LargePrimeCoordinate C Y) 1,?_⟩
    change valueSystem C (fun n : S => n.val)
      (extendLarge C Y (Pi.single (⟨p,hpY⟩ : LargePrimeCoordinate C Y) 1)) = _
    rw [extendLarge_prime_basis]
    exact valueSystem_prime_basis C _ n p hdiag hoff
  have hprob := conditioned_value_probability_eq_baseline C Y (fun n : S => n.val) b sigma hprivate
  have hbridge : finiteUniformProbability (fun eta : LargeSample C Y =>
      ∀ n : S, valueBit (assemble C Y sigma eta) n.val = b n) =
      uniformSolutionProbability (largeValueSystem C Y (fun n : S => n.val))
        (conditionedValueRhs C Y (fun n : S => n.val) b sigma) := by
    unfold finiteUniformProbability uniformSolutionProbability
    rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card]
    congr 1
    apply congrArg (fun k : ℕ => (k : ℚ))
    exact Fintype.card_congr (Equiv.subtypeEquivRight fun eta : LargeSample C Y =>
      (valueSystem_eq_iff C (fun n : S => n.val) b (assemble C Y sigma eta)).symm.trans
        (assemble_solves_values_iff C Y (fun n : S => n.val) b sigma eta))
  rw [eventProbability_largeUniformPMF_eq,hbridge,hprob]
  simp only [Fintype.card_coe,Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_ofNat]

end
end PaperC.V282.ExactMarkedValueProbability
