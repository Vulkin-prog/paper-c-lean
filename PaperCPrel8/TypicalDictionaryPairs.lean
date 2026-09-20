import PaperCPrel8.DictionaryArithmeticCollision
import PaperCPrel8.DictionaryAverage
import PaperCV282.RelationProfileRestriction
import PaperCV282.DictionaryFieldSecondCost

/-! # Averaging the actual separated-pair ledger before bounding its nullity -/
namespace PaperC.Prel8.TypicalDictionaryPairs
open PaperC.Affine PaperC.Prel8.DictionaryArithmeticCollision PaperC.Prel8.DictionaryAverage
open PaperC.V282.RandomDictionary PaperC.V282.RandomDictionaryOverlap
open PaperC.V282.DictionaryMarginalCap PaperC.V282.DictionaryPairCosts
open PaperC.V282.TwoWindowParity PaperC.V282.RelationProfileRestriction
open scoped BigOperators
noncomputable section

/-- Each actual pair costs a baseline 2a^2 plus ap times its full relation excess. -/
theorem averaged_pair_le_excess (M x y L m : ℕ) (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hm : 1 ≤ m) (hmb : m ≤ 2^(L+1)) :
    dictionaryAverage (L+1) m (fun W => dictionaryJointProbability M x y (L+1) W) ≤
      2*((m:ℝ)/(2:ℝ)^(L+1))^2+
      ((m:ℝ)/(2:ℝ)^(L+1))*((1:ℝ)/(2:ℝ)^(L+1))*
        ((2:ℝ)^relationRho (twoValueSystem M x y L)-1) := by
  have h := averaged_dictionary_joint_le M x y (L+1) m (by omega) hm hmb
  rw [jointValueSystem_eq_twoValueSystem hx hy] at h
  have hmR : (1:ℝ)≤m := by exact_mod_cast hm
  have hap : ((m:ℝ)/(2:ℝ)^(L+1))*((1:ℝ)/(2:ℝ)^(L+1)) ≤
      ((m:ℝ)/(2:ℝ)^(L+1))^2 := by
    have hdiv : (1:ℝ)/(2:ℝ)^(L+1) ≤ (m:ℝ)/(2:ℝ)^(L+1) :=
      div_le_div_of_nonneg_right hmR (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hdiv (show 0 ≤ (m:ℝ)/(2:ℝ)^(L+1) by positivity)]
  have he : ((m:ℝ)/(2:ℝ)^(L+1))*((2:ℝ)^relationRho (twoValueSystem M x y L)/(2:ℝ)^(L+1)) =
      ((m:ℝ)/(2:ℝ)^(L+1))*((1:ℝ)/(2:ℝ)^(L+1))*((2:ℝ)^relationRho (twoValueSystem M x y L)-1)+
      ((m:ℝ)/(2:ℝ)^(L+1))*((1:ℝ)/(2:ℝ)^(L+1)) := by ring
  rw [he] at h
  linarith

/-- Sum on the literal pair mask; deleted or extra pairs can be included later. -/
theorem averaged_pairMass_le (M L m : ℕ) (S : Finset (ℕ × ℕ))
    (hpos : ∀ xy ∈ S, 1 ≤ xy.1 ∧ 1 ≤ xy.2) (hm : 1 ≤ m) (hmb : m ≤ 2^(L+1)) :
    dictionaryAverage (L+1) m (fun W => dictionaryPairMass M L W S) ≤
      2*((m:ℝ)/(2:ℝ)^(L+1))^2*S.card+
      ((m:ℝ)/(2:ℝ)^(L+1))*((1:ℝ)/(2:ℝ)^(L+1))*(valueWeightMass M L S:ℝ) := by
  unfold dictionaryPairMass
  rw [dictionaryAverage_finset_sum]
  calc
    _ ≤ ∑ xy ∈ S, (2*((m:ℝ)/(2:ℝ)^(L+1))^2+
        ((m:ℝ)/(2:ℝ)^(L+1))*((1:ℝ)/(2:ℝ)^(L+1))*
          ((2:ℝ)^relationRho (twoValueSystem M xy.1 xy.2 L)-1)) :=
      Finset.sum_le_sum (fun xy hxy => averaged_pair_le_excess M xy.1 xy.2 L m
        (hpos xy hxy).1 (hpos xy hxy).2 hm hmb)
    _ = _ := by
      simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,← Finset.mul_sum,
        valueWeightMass,Nat.cast_sum,two_pow_sub_one_cast]
      ring

end
end PaperC.Prel8.TypicalDictionaryPairs
