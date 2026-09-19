import PaperCPrel8.MicroscopicDeletedSites
import PaperCPrel8.PivotRankinExpandedBand
import PaperCPrel8.DirectedFootprintAsymptotics

/-! # Actual bad-support counts in the microscopic deletion budget

A bad support contains a small odd pivot at one of its actual vertices.
Counting each displacement separately reduces this to the proved pivot population.
The logarithmic support factor is absorbed uniformly at the second saddle scale.
-/
namespace PaperC.Prel8.MicroscopicBadPivotCount
open PaperC.Prel8.MicroscopicDeletedSites PaperC.Prel8.OddPrimePivot
open PaperC.Prel8.PivotRankinExpandedBand PaperC.Prel8.DirectedFootprintAsymptotics
open PaperC.V282.SaddleParameters PaperC.V282.SaddleScales PaperC.V282.PrimeEulerPNT
open Set Filter Topology
noncomputable section
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- At a fixed displacement, translation injects bad boundaries into actual pivot values. -/
theorem bad_displacement_card_le (n Q Y : ℕ) (a : Fin (Q+1)) :
    ((Finset.Icc 1 n).filter (fun j => largestOddPrime (j+a.val) ≤ Y)).card ≤
      (pivotValues (n+Q) Y).card := by
  apply Finset.card_le_card_of_injOn (fun j => j+a.val)
  · intro j hj
    obtain ⟨hj,hp⟩ := Finset.mem_filter.mp hj
    have hj := Finset.mem_Icc.mp hj
    have ha := a.isLt
    change j+a.val ∈ pivotValues (n+Q) Y
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega,by omega⟩,hp⟩
  · intro j _ k _ h
    exact Nat.add_right_cancel h

/-- Finite bad-support count, with the maximal support size and ambient ceiling explicit. -/
theorem badPivotSites_card_le (n L E Y : ℕ) :
    (badPivotSites n L E Y).card ≤
      (L+E+2) * (pivotValues (n+(L+E+1)) Y).card := by
  let f := fun a : Fin (L+E+2) => (Finset.Icc 1 n).filter
    (fun j => largestOddPrime (j+a.val) ≤ Y)
  have he : badPivotSites n L E Y = Finset.univ.biUnion f := by
    ext j
    simp [badPivotSites,f]
  rw [he]
  calc
    _ ≤ ∑ a : Fin (L+E+2), (f a).card := Finset.card_biUnion_le
    _ ≤ ∑ _a : Fin (L+E+2), (pivotValues (n+(L+E+1)) Y).card := by
      apply Finset.sum_le_sum
      intro a _
      exact bad_displacement_card_le n (L+E+1) Y a
    _ = _ := by simp

/-- Actual pivot population at the hard saddle, uniform in every nearby ceiling. -/
theorem hard_pivot_count_eventually (hPNT : PrimeNumberTheoremRemainder)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ X : ℕ, M ≤ 2*X →
      ((pivotValues X ⌊Real.exp (saddleCutoff 1 (Real.log M))⌋₊).card : ℝ) ≤
        X * Real.exp (-saddleCutoff 1 (Real.log M)+epsilon*saddleNu 1 (Real.log M)) := by
  obtain ⟨Mc,hc⟩ := expanded_band_count hPNT epsilon hepsilon
  have hl : Tendsto (fun M : ℕ => Real.log M) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨Md,hd⟩ := eventually_atTop.mp (hl.eventually (eventually_ge_atTop (saddleThreshold 1)))
  refine ⟨max Mc Md, ?_⟩
  intro M hM X hX
  have he := saddleCutoff_equation (by norm_num : (0:ℝ)<1) (hd M (by omega))
  simp only [one_mul] at he
  have hv := saddleCutoff_pos (by norm_num : (0:ℝ)<1) (hd M (by omega))
  have h := hc M (by omega) X hX (saddleCutoff 1 (Real.log M)) (by linarith) (by linarith)
  simpa only [← he] using h

/-- The actual bad-pivot support count has exponent `-V+epsilon*nu`. -/
theorem badPivotSites_hard_bound (hPNT : PrimeNumberTheoremRemainder)
    (beta epsilon : ℝ) (hbeta : 0 < beta) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ n L E : ℕ,
      M ≤ 2*(n+(L+E+1)) → L+E+1 ≤ n → (L+E+1:ℝ) ≤ beta*Real.log M →
      ((badPivotSites n L E ⌊Real.exp (saddleCutoff 1 (Real.log M))⌋₊).card : ℝ) ≤
        n * Real.exp (-saddleCutoff 1 (Real.log M)+epsilon*saddleNu 1 (Real.log M)) := by
  obtain ⟨Mc,hc⟩ := hard_pivot_count_eventually hPNT (epsilon/2) (by positivity)
  obtain ⟨Ma,ha⟩ := logarithmic_support_absorption beta (epsilon/2) hbeta (by positivity)
  refine ⟨max Mc Ma, ?_⟩
  intro M hM n L E hpop hQn hQ
  let Q := L+E+1
  let V := saddleCutoff 1 (Real.log M)
  let nu := saddleNu 1 (Real.log M)
  have hr := hc M (by omega) (n+Q) hpop
  have hp := ha M (by omega) Q (by exact_mod_cast hQ)
  have hpoly : 2*(Q+1:ℝ) ≤ Real.exp ((epsilon/2)*nu) := by
    have hq : (0:ℝ) ≤ Q := Nat.cast_nonneg Q
    dsimp [nu]
    nlinarith
  have hpop' : ((n+Q:ℕ):ℝ) ≤ 2*n := by exact_mod_cast (show n+Q ≤ 2*n by omega)
  have hraw : ((badPivotSites n L E ⌊Real.exp V⌋₊).card:ℝ) ≤
      (Q+1:ℝ)*(pivotValues (n+Q) ⌊Real.exp V⌋₊).card := by
    exact_mod_cast badPivotSites_card_le n L E ⌊Real.exp V⌋₊
  calc
    _ ≤ _ := hraw
    _ ≤ (Q+1:ℝ)*((n+Q:ℕ)*Real.exp (-V+(epsilon/2)*nu)) := by gcongr
    _ ≤ (Q+1:ℝ)*((2*n)*Real.exp (-V+(epsilon/2)*nu)) := by gcongr
    _ = n*(2*(Q+1:ℝ))*Real.exp (-V+(epsilon/2)*nu) := by ring
    _ ≤ n*Real.exp ((epsilon/2)*nu)*Real.exp (-V+(epsilon/2)*nu) := by gcongr
    _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring

/-- The information budget absorbs the conditional bad-support intensity. -/
theorem information_budget_absorption {lambda a V nu c epsilon : ℝ}
    (hlambda : 0 < lambda) (ha : 0 < a)
    (hbudget : Real.log lambda - Real.log a ≤ V-c*nu) :
    lambda * Real.exp (-V+epsilon*nu) / a ≤ Real.exp (-(c-epsilon)*nu) := by
  calc
    _ = Real.exp (Real.log lambda-Real.log a-V+epsilon*nu) := by
      simp only [Real.exp_add, Real.exp_sub, Real.exp_log hlambda, Real.exp_log ha, Real.exp_neg]
      ring
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

/-- The exact bad-support cardinality is eliminated from the conditional deletion bound. -/
theorem conditional_deletion_hard_bound
    (betaMin betaMax beta epsilon : ℝ)
    (hbetaMin : 0 < betaMin) (hband : betaMin < betaMax)
    (hbeta : 0 < beta) (hepsilon : 0 < epsilon)
    (hLS : PaperC.V282.LaishramUniformInput.UniformPrimeDivisorStatement)
    (hShorey : PaperC.V282.PostQuadraticLiterature.ShoreySquareProductStatement)
    (hPNT : PrimeNumberTheoremRemainder)
    (hNR : PaperC.PellInput.NicolasRobinDivisorLogBoundStatement) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ n L E : ℕ,
      betaMin*Real.log M ≤ (L+1:ℝ) → (L+1:ℝ) ≤ betaMax*Real.log M →
      n ≤ M → M ≤ 2*(n+(L+E+1)) → L+E+1 ≤ n → (L+E+1:ℝ) ≤ beta*Real.log M →
      ∀ A : Set PaperC.InfiniteRademacher.InfiniteSample,
      0 < PaperC.InfiniteRademacher.infiniteRademacherMeasure.real A →
      PaperC.InfiniteRademacher.infiniteRademacherMeasure.real
        (A ∩ PaperC.Prel8.IndependentScalarTail.hitEvent L
          (deletedStarts M n L E ⌊Real.exp (saddleCutoff 1 (Real.log M))⌋₊)) /
        PaperC.InfiniteRademacher.infiniteRademacherMeasure.real A ≤
      (((⌈Real.sqrt M⌉₊:ℝ) + n*Real.exp (-saddleCutoff 1 (Real.log M)+epsilon*saddleNu 1 (Real.log M))) /
        (2:ℝ)^L + 2*Real.exp (-(betaMin*Real.log 2/8)*(Real.log M/Real.log (Real.log M)))) /
        PaperC.InfiniteRademacher.infiniteRademacherMeasure.real A := by
  obtain ⟨Md,hd⟩ := actual_deleted_bound_eventually betaMin betaMax hbetaMin hband hLS hShorey hPNT hNR
  obtain ⟨Mb,hb⟩ := badPivotSites_hard_bound hPNT beta epsilon hbeta hepsilon
  refine ⟨max Md Mb, ?_⟩
  intro M hM n L E hlo hhi hn hpop hQn hQ A hA
  have hdel := hd M (by omega) L hlo hhi n E
    ⌊Real.exp (saddleCutoff 1 (Real.log M))⌋₊ hn A hA
  have hbad := hb M (by omega) n L E hpop hQn hQ
  apply hdel.trans
  apply div_le_div_of_nonneg_right _ hA.le
  apply add_le_add _ le_rfl
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact add_le_add le_rfl hbad

end
end PaperC.Prel8.MicroscopicBadPivotCount
