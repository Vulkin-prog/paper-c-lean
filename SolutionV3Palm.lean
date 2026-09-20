import SolutionV3Microscopic
import PaperCPrel8.ArithmeticPalmCompletion
import PaperCPrel8.PrimeCumulantObstruction
import PaperCPrel8.RegularTargetCompletion
namespace PaperCV3Audit
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators NNReal ENNReal
local instance (P : Prop) : Decidable P := Classical.propDecidable P
local instance : MeasurableSpace F₂ := ⊤
namespace Palm
open Analysis Boundary Microscopic
/-- Small-prime assignments in a fixed finite cylinder. -/
abbrev SmallSample (C Y : ℕ) := {p : PrimeUpTo C // p.1.1 ≤ Y} → F₂
def traceEvent (C Y : ℕ) (A : SmallSample C Y → Prop) : Set InfiniteSample :=
  {omega | A (fun p => restrictToFinite C omega p.1)}
def roughPrimes (Y n : ℕ) : Finset ℕ :=
  ((n.factorization.mapRange (fun e : ℕ => e%2) (by simp)).support).filter (fun p => Y<p)
/-- Each raw occurrence has a prime private to it among all planted occurrences. -/
def Regular {k : ℕ} (Q Y : ℕ) (J : Fin k → ℕ) : Prop :=
  ∀ i : Fin k, ∀ a : Fin (Q+1), ∃ p ∈ roughPrimes Y (J i+a.val),
    ∀ l : Fin k, ∀ b : Fin (Q+1), l≠i ∨ b≠a → ¬ p ∣ J l+b.val
def enumerated {k : ℕ} (sites : Finset ℕ) (labels : Fin k → MarkIndex sites) : Config sites :=
  ∑ i, Finsupp.single (labels i) 1
/-- Private-prime regularity includes the cylinder, excess and endpoint conditions. -/
def RegularPlant (sites : Finset ℕ) (C L E Y : ℕ) (z : Config sites) : Prop :=
  ∃ k, ∃ labels : Fin k → MarkIndex sites,
    z=enumerated sites labels ∧
    (∀ i, 2≤(labels i).1.val) ∧ (∀ i, (labels i).2.1≤E) ∧
    (∀ i, (labels i).1.val-1+(L+E+1)≤C) ∧
    Regular (L+E+1) Y (fun i => (labels i).1.val-1)
def presence (sites : Finset ℕ) (L : ℕ) (z : Config sites) : Set InfiniteSample :=
  {omega | ∀ j, z j≠0 → ExactLengthEvent (infiniteValueBit omega) j.1.val (L+j.2.1+1) ∧
    infiniteValueBit omega j.1.val=j.2.2}
def totalRate (sites : Finset ℕ) (L : ℕ) : ℝ≥0 := ⟨(sites.card:ℝ)/2^L,by positivity⟩
def sourceMass {C Y : ℕ} (sites : Finset ℕ) (L : ℕ) (A : SmallSample C Y → Prop) : Config sites → ℝ :=
  conditionalLaw infiniteRademacherMeasure (traceEvent C Y A) (source sites L)
def targetMass (sites : Finset ℕ) (L : ℕ) (z : Config sites) : ℝ := (target sites L).real {z}
def palmVoid {C Y : ℕ} (sites : Finset ℕ) (L : ℕ) (A : SmallSample C Y → Prop) (z : Config sites) : ℝ :=
  (cond (cond infiniteRademacherMeasure (traceEvent C Y A)) (presence sites L z)).real
    {omega | source sites L omega=z}
def voidDeficit {α : Type*} (nu : α → ℝ) (R : α → Prop) (v : α → ℝ) : ℝ :=
  ∑' z, if R z then nu z*max (1-v z) 0 else 0
def fullDeficit {C Y : ℕ} (sites : Finset ℕ) (L E : ℕ) (A : SmallSample C Y → Prop) : ℝ :=
  voidDeficit (targetMass sites L) (RegularPlant sites C L E Y)
    (fun z => Real.exp (totalRate sites L:ℝ)*palmVoid sites L A z)
def totalSize (sites : Finset ℕ) (z : Config sites) : ℕ := z.sum (fun _ n => n)
def boundedRegular (sites : Finset ℕ) (C L E Y K : ℕ) (z : Config sites) : Prop :=
  RegularPlant sites C L E Y z ∧ totalSize sites z≤K
def normalizedVoid {C Y : ℕ} (sites : Finset ℕ) (L : ℕ) (A : SmallSample C Y → Prop) (z : Config sites) : ℝ :=
  palmVoid sites L A z/(1-1/(2:ℝ)^L)^(sites.card-totalSize sites z)
def penalty (sites : Finset ℕ) (L K : ℕ) : ℝ :=
  (K:ℝ)*(1/(2:ℝ)^L)+(sites.card:ℝ)*(1/(2:ℝ)^L)^2/(1-1/(2:ℝ)^L)
def exceptionalMass {α : Type*} (nu : α → ℝ) (R : α → Prop) : ℝ :=
  ∑' z, if R z then 0 else nu z
def hitEvent (L : ℕ) (sites : Finset ℕ) : Set InfiniteSample :=
  {omega | maskedCount L sites omega ≠ 0}
def sourceCylinder (M L : ℕ) (I : ℝ) : ℕ := 2*M+(L+excess M L I+2)
end Palm
namespace Palm
open Analysis Boundary Microscopic
 theorem presence_eq (sites : Finset ℕ) (L : ℕ) :
    presence sites L = PaperC.Prel8.ArithmeticPalmMass.presence sites L := rfl
 theorem regular_eq (sites : Finset ℕ) (C L E Y : ℕ) :
    RegularPlant sites C L E Y = PaperC.Prel8.ArithmeticPalmMass.RegularPlant sites C L E Y := rfl
 theorem sourceMass_eq {C Y : ℕ} (sites : Finset ℕ) (L : ℕ) (A : SmallSample C Y → Prop) :
    sourceMass sites L A = PaperC.Prel8.ArithmeticPalmDeficit.sourceMass sites L A := by
  unfold sourceMass; rw [source_eq]; rfl
 theorem targetMass_eq (sites : Finset ℕ) (L : ℕ) :
    targetMass sites L = PaperC.Prel8.ArithmeticPalmDeficit.targetMass sites L := by
  unfold targetMass; rw [target_eq]; rfl
 theorem palmVoid_eq {C Y : ℕ} (sites : Finset ℕ) (L : ℕ) (A : SmallSample C Y → Prop) :
    palmVoid sites L A = PaperC.Prel8.ArithmeticPalmDeficit.palmVoid sites L A := by
  unfold palmVoid; rw [source_eq]; rfl
 theorem fullDeficit_eq {C Y : ℕ} (sites : Finset ℕ) (L E : ℕ) (A : SmallSample C Y → Prop) :
    fullDeficit sites L E A = PaperC.Prel8.ArithmeticPalmDeficit.fullDeficit sites L E A := by
  unfold fullDeficit; rw [targetMass_eq,regular_eq,palmVoid_eq]; rfl
 theorem normalizedVoid_eq {C Y : ℕ} (sites : Finset ℕ) (L : ℕ) (A : SmallSample C Y → Prop) :
    normalizedVoid sites L A = PaperC.Prel8.ArithmeticPalmNormalization.normalizedVoid sites L A := by
  unfold normalizedVoid; rw [palmVoid_eq]; rfl
 theorem sourceCylinder_eq (M L : ℕ) (I : ℝ) :
    sourceCylinder M L I = PaperC.Prel8.MicroscopicActualGeometry.sourceCylinder M L I := by
  unfold sourceCylinder PaperC.Prel8.MicroscopicActualGeometry.sourceCylinder; rw [excess_eq]
end Palm


namespace Palm
open Analysis Boundary Microscopic
theorem source_target_palm_mass {C L E Y : ℕ} (sites : Finset ℕ) (hL : 1≤L)
    (A : SmallSample C Y → Prop) (hA : 0 < infiniteRademacherMeasure.real (traceEvent C Y A))
    (z : Config sites) (hz : RegularPlant sites C L E Y z) :
    (cond infiniteRademacherMeasure (traceEvent C Y A)).real {w | source sites L w=z} =
    (target sites L).real {z} * (Real.exp (totalRate sites L:ℝ)*
      (cond (cond infiniteRademacherMeasure (traceEvent C Y A)) (presence sites L z)).real
        {w | source sites L w=z}) := by
  rw [source_eq,target_eq]
  exact PaperC.Prel8.ArithmeticPalmMass.source_target_palm_mass sites hL A hA z hz

theorem full_deficit_comparison {C L E Y : ℕ} (sites : Finset ℕ) (hL : 1≤L)
    (A : SmallSample C Y → Prop) (hA : 0 < infiniteRademacherMeasure.real (traceEvent C Y A)) :
    0 ≤ massTV (sourceMass sites L A) (targetMass sites L)-fullDeficit sites L E A ∧
    massTV (sourceMass sites L A) (targetMass sites L)-fullDeficit sites L E A ≤
      (target sites L).real {z | ¬RegularPlant sites C L E Y z} := by
  rw [sourceMass_eq,targetMass_eq,fullDeficit_eq,target_eq]
  exact PaperC.Prel8.ArithmeticPalmDeficit.fullDeficit_comparison sites hL A hA

theorem ordinary_deletion {C L E Y : ℕ} (sites : Finset ℕ) (hL : 1≤L)
    (A : SmallSample C Y → Prop) (hA : 0 < infiniteRademacherMeasure.real (traceEvent C Y A))
    (outside : Set InfiniteSample) (houtside : MeasurableSet outside) :
    (∑' z, if RegularPlant sites C L E Y z then targetMass sites L z*Real.exp (totalRate sites L:ℝ)*
      (palmVoid sites L A z-
        (cond (cond infiniteRademacherMeasure (traceEvent C Y A)) (presence sites L z)).real
          ({w | source sites L w=z} \ outside)) else 0) =
      (cond infiniteRademacherMeasure (traceEvent C Y A)).real
        ({w | RegularPlant sites C L E Y (source sites L w)} ∩ outside) := by
  simp only [targetMass_eq,palmVoid_eq,source_eq]
  exact PaperC.Prel8.ArithmeticPalmDeficit.ordinary_deletion sites hL A hA outside houtside

theorem full_retained_normalized_comparison {C L E Y K : ℕ} {s t : Finset ℕ}
    (hst : s⊆t) (hL : 1≤L) (A : SmallSample C Y → Prop)
    (hA : 0 < infiniteRademacherMeasure.real (traceEvent C Y A)) :
    |massTV (sourceMass t L A) (targetMass t L)-
      voidDeficit (targetMass s L) (boundedRegular s C L E Y K) (normalizedVoid s L A)|≤
      (cond infiniteRademacherMeasure (traceEvent C Y A)).real
        (hitEvent L (t\s))+
      (maskRate L (t\s):ℝ)+
      exceptionalMass (targetMass s L) (boundedRegular s C L E Y K)+penalty s L K := by
  simp only [sourceMass_eq,targetMass_eq,normalizedVoid_eq]
  exact PaperC.Prel8.ArithmeticPalmCompletion.full_retained_normalized_comparison (E := E) (K := K) hst hL A hA

theorem normalized_deficit_eventually
    (hLS : UniformPrimeDivisorStatement) (hShorey : ShoreySquareProductStatement)
    (hPNT : PrimeNumberTheoremRemainder) (hNR : DivisorLogBoundStatement)
    (betaMin betaMax c c' epsilon : ℝ) (hmin : 0<betaMin)
    (hband : betaMin<betaMax) (hc' : 0<c') (hcc : c'<c) (hepsilon : 0<epsilon) :
    ∃ Mzero : ℕ, ∀ M≥Mzero, ∀ L : ℕ, ∀ I : ℝ,
      1≤L → betaMin*Real.log M≤(L+1:ℝ) → (L+1:ℝ)≤betaMax*Real.log M →
      0≤I → 1≤siteRate M L →
      I+Real.log (siteRate M L)≤saddleCutoff 1 (Real.log M)-c*saddleNu 1 (Real.log M) →
      ∀ A : SmallSample (sourceCylinder M L I) (hardCutoff M) → Prop,
      0 < infiniteRademacherMeasure.real (traceEvent (sourceCylinder M L I) (hardCutoff M) A) →
      I = -Real.log (infiniteRademacherMeasure.real
        (traceEvent (sourceCylinder M L I) (hardCutoff M) A)) →
      SteinInput M L I →
      ∀ sites : Finset ℕ, sites⊆interior M L → ∀ E : ℕ,
      voidDeficit (targetMass sites L)
        (boundedRegular sites (sourceCylinder M L I) L E (hardCutoff M) ⌈2*siteRate M L⌉₊)
        (normalizedVoid sites L A)≤
      10*Real.exp (-c'*saddleNu 1 (Real.log M))+4*(M:ℝ)^(-(1/(3:ℝ))+epsilon)+(M:ℝ)^(-(1/(2:ℝ))) := by
  rw [show sourceCylinder = PaperC.Prel8.MicroscopicActualGeometry.sourceCylinder from
    funext fun M => funext fun L => funext fun I => sourceCylinder_eq M L I]
  rw [show Analysis.hardCutoff = PaperC.Prel8.MicroscopicActualGeometry.primeCutoff from
    funext fun M => Analysis.hardCutoff_eq M]
  simp only [stein_eq,targetMass_eq,normalizedVoid_eq,Analysis.saddleCutoff_eq,Analysis.saddleNu_eq]
  exact PaperC.Prel8.ArithmeticPalmCompletion.normalized_deficit_eventually hLS hShorey hPNT hNR betaMin betaMax c c' epsilon hmin hband hc' hcc hepsilon

end Palm

namespace Palm
open Analysis Boundary Microscopic
namespace Cumulants
open Finset
variable {ι : Type*} [DecidableEq ι]
def partitions (S : Finset ι) : Finset (Finset (Finset ι)) :=
  S.powerset.powerset.filter (fun p ↦ (p:Set (Finset ι)).PairwiseDisjoint id ∧
    ∅∉p ∧ p.biUnion id=S)

def properPartitions (S : Finset ι) : Finset (Finset (Finset ι)) :=
  (partitions S).erase {S}

theorem block_subset {S B : Finset ι} {p : Finset (Finset ι)}
    (hp : p∈partitions S) (hB : B∈p) : B⊆S :=
  mem_powerset.mp (mem_powerset.mp (mem_filter.mp hp).1 hB)

theorem block_nonempty {S B : Finset ι} {p : Finset (Finset ι)}
    (hp : p∈partitions S) (hB : B∈p) : B.Nonempty := by
  apply nonempty_iff_ne_empty.mpr
  intro he
  exact (mem_filter.mp hp).2.2.1 (he ▸ hB)

theorem partition_with_full_block {S : Finset ι} {p : Finset (Finset ι)}
    (hp : p∈partitions S) (hS : S∈p) : p={S} := by
  apply eq_singleton_iff_unique_mem.mpr
  refine ⟨hS,?_⟩
  intro B hB
  by_contra hne
  have hd := (mem_filter.mp hp).2.1 hB hS hne
  obtain ⟨x,hx⟩ := block_nonempty hp hB
  exact disjoint_left.mp hd hx (block_subset hp hB hx)

theorem proper_block_ssubset {S B : Finset ι} {p : Finset (Finset ι)}
    (hp : p∈properPartitions S) (hB : B∈p) : B⊂S := by
  obtain ⟨hne,hp⟩ := mem_erase.mp hp
  apply ssubset_iff_subset_ne.mpr
  refine ⟨block_subset hp hB,?_⟩
  intro he
  exact hne (partition_with_full_block hp (he ▸ hB))

theorem singleton_partition {S : Finset ι} (hS : S.Nonempty) : {S}∈partitions S := by
  simp [partitions,Ne.symm hS.ne_empty]

theorem partitions_empty : partitions (∅:Finset ι)={∅} := by
  ext p
  simp only [partitions,mem_filter,mem_powerset,powerset_empty,subset_singleton_iff,mem_singleton]
  constructor
  · rintro ⟨h,hd,he,hu⟩
    rcases h with h|h
    · exact h
    · simp [h] at he
  · rintro rfl
    simp

/-- Triangular finite definition of joint cumulants from a prescribed moment table. -/
def cumulant (moment : Finset ι → ℝ) (S : Finset ι) : ℝ :=
  if S=∅ then 0 else moment S-
    ∑ p : properPartitions S, ∏ B : p.val, cumulant moment B.val
termination_by S.card
decreasing_by exact card_lt_card (proper_block_ssubset p.property B.property)

end Cumulants
/-- The actual finite prime-sign assignment on the witness cylinder. -/
def finiteValue {C : ℕ} (omega : SampleSpace C) (n : ℕ) : F₂ :=
  ∑ p : PrimeUpTo C, omega p * parityVec n p.1
/-- Low exact categories; the unique realized signed excess is selected if present. -/
def lowCategory (C L E j : ℕ) (omega : SampleSpace C) : Option (Fin (E+1)×F₂) :=
  if h : ∃ a : Fin (E+1)×F₂,
    ExactLengthEvent (finiteValue omega) (j+1) (L+a.1.val+1) ∧ finiteValue omega (j+1)=a.2
  then some (Classical.choose h) else none
def categoryIndicator (C L E : ℕ) (G : Finset ℕ)
    (a : G×(Fin (E+1)×F₂)) (omega : SampleSpace C) : ℝ :=
  if lowCategory C L E a.1.val omega=some a.2 then 1 else 0
def uniformMean {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) : ℝ :=
  ∑ omega, (Fintype.card Ω:ℝ)⁻¹*f omega
def centeredMoment {ι Ω : Type*} [Fintype Ω] (X : ι → Ω → ℝ) (S : Finset ι) : ℝ :=
  uniformMean (fun omega => ∏ i∈S, (X i omega-uniformMean (X i)))
def transversals {ι α : Type*} [Fintype ι] [Fintype α] : Finset (Finset (ι×α)) :=
  Finset.univ.powerset.filter (fun S => ∀ i a b, (i,a)∈S → (i,b)∈S → a=b)
/-- G.9 retains all cumulant orders of the actual low-category indicators. -/
def activity (C L E : ℕ) (G : Finset ℕ) : ℝ :=
  ∑ S∈(transversals (ι := G) (α := Fin (E+1)×F₂)).filter (fun S => 2≤S.card),
    (2:ℝ)^(S.card-1)*|Cumulants.cumulant (centeredMoment (categoryIndicator C L E G)) S|
def primeWindow (q : ℕ) : ℕ := 2^(q-1+Nat.log 2 q)
def primeExcess (q : ℕ) : ℕ := excess (primeWindow q) (q-1) 0
def primeCylinder (q : ℕ) : ℕ := primeWindow q+(q-1+primeExcess q+1)
def original (q : ℕ) : Finset ℕ := goodSites (primeWindow q) (q-1) 0
/-- Stronger retention requires every raw vertex to have a sufficiently large rough kernel. -/
def strongerGood (M L : ℕ) (I theta : ℝ) : Finset ℕ :=
  (goodSites M L I).filter (fun j => ∀ a : Fin (L+excess M L I+1+1),
    ⌊Real.exp (theta*Real.log M/saddleParameter 1 (Real.log M))⌋₊ <
      (roughPrimes (hardCutoff M) (j+a.val)).prod id)
def retained (q : ℕ) (theta : ℝ) : Finset ℕ := strongerGood (primeWindow q) (q-1) 0 theta
def obstructionConstant : ℝ := Real.log 2/2*(Real.log 3-1)
end Palm

namespace Palm
open Analysis Boundary Microscopic
 theorem cumulant_eq {ι : Type*} [DecidableEq ι] (m : Finset ι → ℝ) (S : Finset ι) :
    Cumulants.cumulant m S = PaperC.Prel8.FiniteCumulantPartitions.cumulant m S := by
  induction S using Finset.strongInductionOn
  rename_i S ih
  ·
    rw [Cumulants.cumulant,PaperC.Prel8.FiniteCumulantPartitions.cumulant]
    split_ifs
    · rfl
    · congr 1
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.prod_congr rfl
      intro B _
      exact ih B.val (Cumulants.proper_block_ssubset p.property B.property)
 theorem lowCategory_eq (C L E j : ℕ) : lowCategory C L E j =
    PaperC.Prel8.ArithmeticLowCategory.lowCategory C L E j := by
  funext omega
  unfold lowCategory PaperC.Prel8.ArithmeticLowCategory.lowCategory
  split_ifs <;> first | rfl | contradiction
 theorem activity_eq (C L E : ℕ) (G : Finset ℕ) : activity C L E G =
    PaperC.Prel8.CategoricalCumulantBound.activity (PaperC.FinitePMF.uniform (PaperC.SampleSpace C))
      (PaperC.Prel8.ArithmeticLowCategory.retainedCategory C L E G) := by
  unfold activity PaperC.Prel8.CategoricalCumulantBound.activity
  simp only [cumulant_eq]
  have he : categoryIndicator C L E G = PaperC.Prel8.CategoricalMomentExpansion.indicator
      (PaperC.Prel8.ArithmeticLowCategory.retainedCategory C L E G) := by
    funext a omega
    unfold categoryIndicator
    rw [lowCategory_eq]
    rfl
  rw [he]
  unfold PaperC.Prel8.FiniteCumulantEnvelope.jointCumulant
    PaperC.Prel8.FiniteCumulantEnvelope.centeredMoment centeredMoment uniformMean
    PaperC.IndependentThinning.finitePMFExpectation PaperC.FinitePMF.uniform
    transversals PaperC.Prel8.CategoricalTransversals.transversals PaperC.Prel8.CategoricalTransversals.Transversal
  congr 1
  ext S
  simp
 theorem primeExcess_eq (q : ℕ) : primeExcess q = PaperC.Prel8.PrimeWindowGeometry.excess q := by
  unfold primeExcess PaperC.Prel8.PrimeWindowGeometry.excess; rw [excess_eq]; rfl
 theorem primeCylinder_eq (q : ℕ) : primeCylinder q = PaperC.Prel8.PrimeWindowGeometry.cylinder q := by
  unfold primeCylinder PaperC.Prel8.PrimeWindowGeometry.cylinder PaperC.Prel8.PrimeWindowGeometry.support
  rw [primeExcess_eq]; rfl
 theorem original_eq (q : ℕ) : original q = PaperC.Prel8.PrimeRetainedDensity.original q := by
  unfold original PaperC.Prel8.PrimeRetainedDensity.original PaperC.Prel8.StrongerDeletionTheorem.originalGood
  rw [goodSites_eq]; rfl
 theorem strongerGood_eq (M L : ℕ) (I theta : ℝ) : strongerGood M L I theta =
    PaperC.Prel8.StrongerDeletionTheorem.strongerGood M L I theta := by
  unfold strongerGood PaperC.Prel8.StrongerDeletionTheorem.strongerGood
    PaperC.Prel8.RoughKernelGoodSet.paperGood PaperC.Prel8.RoughKernelDeletion.strongGood
    PaperC.Prel8.RoughKernelThreshold.threshold
  rw [goodSites_eq,excess_eq,Analysis.hardCutoff_eq,Analysis.saddleParameter_eq]
  rfl
 theorem retained_eq (q : ℕ) (theta : ℝ) : retained q theta = PaperC.Prel8.PrimeRetainedDensity.retained q theta := by
  unfold retained PaperC.Prel8.PrimeRetainedDensity.retained
  rw [strongerGood_eq]; rfl
end Palm
namespace Palm
open Analysis Boundary Microscopic
/-- G.9: positive normalized lower bound for the original good set, on prime scales. -/
theorem original_cumulant_obstruction (hPNT : PrimeNumberTheoremRemainder)
    {epsilon : ℝ} (hepsilon : 0<epsilon) :
    ∀ᶠ q : ℕ in atTop, q.Prime → obstructionConstant-epsilon ≤
      Real.log (primeWindow q)/(primeWindow q:ℝ)*activity (primeCylinder q) (q-1) (primeExcess q) (original q) := by
  simp only [activity_eq,primeCylinder_eq,primeExcess_eq,original_eq]
  exact PaperC.Prel8.PrimeCumulantObstruction.original_obstruction hPNT hepsilon
/-- G.9: stronger fixed retention leaves the same leading obstruction constant. -/
theorem retained_cumulant_obstruction (hPNT : PrimeNumberTheoremRemainder)
    {theta : ℝ} (htheta : 0≤theta) {epsilon : ℝ} (hepsilon : 0<epsilon) :
    ∀ᶠ q : ℕ in atTop, q.Prime → obstructionConstant-epsilon ≤
      Real.log (primeWindow q)/(primeWindow q:ℝ)*activity (primeCylinder q) (q-1) (primeExcess q) (retained q theta) := by
  simp only [activity_eq,primeCylinder_eq,primeExcess_eq,retained_eq]
  exact PaperC.Prel8.PrimeCumulantObstruction.retained_obstruction hPNT htheta hepsilon
end Palm

namespace Palm
open Analysis Boundary Microscopic
/-- G.3 target regularity uses left-boundary labels, before shifting them to run starts. -/
def regularConfiguration (M L : ℕ) (I theta : ℝ) (z : Config (Finset.Icc 1 (M-L))) : Prop :=
  ∃ k≤⌈2*siteRate M L⌉₊, ∃ labels : Fin k → MarkIndex (Finset.Icc 1 (M-L)),
    z=∑ i, Finsupp.single (labels i) 1 ∧
    (∀ i, (labels i).1.val∈strongerGood M L I theta) ∧
    Regular (L+excess M L I+1) (hardCutoff M) (fun i => (labels i).1.val) ∧
    (∀ i, (labels i).2.1≤excess M L I)
end Palm
namespace Palm
open Analysis Boundary Microscopic
 theorem regularConfiguration_eq (M L : ℕ) (I theta : ℝ) : regularConfiguration M L I theta =
    PaperC.Prel8.RegularTargetSaddle.paperRegular M L I theta := by
  unfold regularConfiguration PaperC.Prel8.RegularTargetSaddle.paperRegular
    PaperC.Prel8.RegularTargetCloud.RegularConfiguration
  rw [excess_eq,Analysis.hardCutoff_eq,strongerGood_eq]
  rfl
end Palm

namespace Palm
open Analysis Boundary Microscopic
theorem stronger_retention_counts (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax theta c : ℝ) (hmin : 0 < betaMin) (hband : betaMin < betaMax)
    (htheta : 0 ≤ theta) (htc : theta < c) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ, ∀ I : ℝ,
      betaMin*Real.log M ≤ (L+1:ℝ) → (L+1:ℝ) ≤ betaMax*Real.log M →
      0 ≤ I → 1 ≤ siteRate M L →
      I+Real.log (siteRate M L) ≤ saddleCutoff 1 (Real.log M)-c*saddleNu 1 (Real.log M) →
      (1/(2:ℝ)^L) * ((goodSites M L I \ strongerGood M L I theta).card : ℝ) ≤
        Real.exp (-((c-theta)/2)*saddleNu 1 (Real.log M)) ∧
      (((Finset.Icc 1 (M-L)) \ strongerGood M L I theta).card : ℝ) ≤
        (⌈Real.sqrt M⌉₊ : ℝ) + M * Real.exp
          (-saddleCutoff 1 (Real.log M)+(theta+1)*saddleNu 1 (Real.log M)) := by
  simp only [saddleCutoff_eq,saddleNu_eq,strongerGood_eq,goodSites_eq]
  exact PaperC.Prel8.StrongerDeletionTheorem.paper_counts hPNT betaMin betaMax theta c hmin hband htheta htc

theorem regular_target_probability (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax c theta : ℝ) (hmin : 0<betaMin) (hband : betaMin<betaMax)
    (htheta : 0<theta) (htc : theta<c) (L : ℕ → ℕ) (I : ℕ → ℝ)
    (hrate : Tendsto (fun M ↦ siteRate M (L M)) atTop atTop)
    (hregime : ∀ᶠ M : ℕ in atTop, betaMin*Real.log M≤(L M+1:ℝ) ∧
      (L M+1:ℝ)≤betaMax*Real.log M ∧ 0≤I M ∧ 1≤siteRate M (L M) ∧
      I M+Real.log (siteRate M (L M))≤saddleCutoff 1 (Real.log M)-c*saddleNu 1 (Real.log M)) :
    Tendsto (fun M ↦ (target (Finset.Icc 1 (M-L M)) (L M)).real
      {z | ¬regularConfiguration M (L M) (I M) theta z}) atTop (𝓝 0) := by
  simp only [saddleCutoff_eq,saddleNu_eq] at hregime
  simp only [regularConfiguration_eq,target_eq]
  exact PaperC.Prel8.RegularTargetCompletion.target_failure_tendsto hPNT betaMin betaMax c theta hmin hband htheta htc L I hrate hregime

end Palm

end
end PaperCV3Audit
