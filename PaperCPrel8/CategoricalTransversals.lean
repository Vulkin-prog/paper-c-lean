import PaperCPrel8.CumulantFamilyEnvelope

/-! # Categorical choices as distinct-site finite subsets -/
namespace PaperC.Prel8.CategoricalTransversals
open Finset CumulantFamilyEnvelope
noncomputable section
variable {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq ι] [DecidableEq α]
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

def Transversal (S : Finset (ι×α)) : Prop :=
  ∀ i a b, (i,a)∈S → (i,b)∈S → a=b

def transversals : Finset (Finset (ι×α)) := univ.powerset.filter Transversal

def graph (f : ι → Option α) : Finset (ι×α) :=
  univ.biUnion (fun i ↦ (f i).toFinset.image (fun a ↦ (i,a)))

theorem mem_graph (f : ι → Option α) (i : ι) (a : α) : (i,a)∈graph f ↔ f i=some a := by
  simp [graph,Option.mem_toFinset,eq_comm]

theorem graph_transversal (f : ι → Option α) : Transversal (graph f) := by
  intro i a b ha hb
  exact Option.some.inj ((mem_graph f i a).mp ha |>.symm.trans ((mem_graph f i b).mp hb))

theorem graph_mem (f : ι → Option α) : graph f∈transversals :=
  mem_filter.mpr ⟨mem_powerset.mpr (subset_univ _),graph_transversal f⟩

def choice (S : Finset (ι×α)) (i : ι) : Option α :=
  if h : ∃ a, (i,a)∈S then some (Classical.choose h) else none

theorem choice_some {S : Finset (ι×α)} (hS : Transversal S) (i : ι) (a : α) :
    choice S i=some a ↔ (i,a)∈S := by
  unfold choice
  split_ifs with h
  · simp only [Option.some.injEq]
    constructor
    · intro he
      simpa only [he] using Classical.choose_spec h
    · intro ha
      exact hS i _ a (Classical.choose_spec h) ha
  · simp only [reduceCtorEq,false_iff]
    exact fun ha ↦ h ⟨a,ha⟩

theorem graph_choice {S : Finset (ι×α)} (hS : Transversal S) : graph (choice S)=S := by
  ext ⟨i,a⟩
  rw [mem_graph,choice_some hS]

theorem graph_injective : Function.Injective (graph : (ι → Option α) → Finset (ι×α)) := by
  intro f g he
  funext i
  cases hf : f i with
  | some a =>
    have h := (mem_graph f i a).mpr hf
    rw [he] at h
    exact ((mem_graph g i a).mp h).symm
  | none =>
    cases hg : g i with
    | none => rfl
    | some a =>
      have h := (mem_graph g i a).mpr hg
      rw [← he] at h
      have hh := (mem_graph f i a).mp h
      simp [hf] at hh

theorem choice_graph (f : ι → Option α) : choice (graph f)=f :=
  graph_injective (graph_choice (graph_transversal f))

theorem transversals_downward : Downward (transversals (ι:=ι) (α:=α)) := by
  intro S hS B hB
  refine mem_filter.mpr ⟨mem_powerset.mpr (subset_univ _),?_⟩
  intro i a b ha hb
  exact (mem_filter.mp hS).2 i a b (hB ha) (hB hb)

theorem empty_mem : (∅:Finset (ι×α))∈transversals := by
  apply mem_filter.mpr
  exact ⟨mem_powerset.mpr (empty_subset _),fun i a b ha _ ↦ False.elim (notMem_empty _ ha)⟩

theorem sum_graph (F : Finset (ι×α) → ℝ) :
    (∑ f : ι → Option α, F (graph f))=∑ S∈transversals, F S := by
  apply sum_bij (fun f _ ↦ graph f)
  · intro f hf
    exact graph_mem f
  · intro f hf g hg he
    exact graph_injective he
  · intro S hS
    exact ⟨choice S,mem_univ _,graph_choice (mem_filter.mp hS).2⟩
  · intro f hf
    rfl

theorem prod_graph (f : ι → Option α) (g : ι×α → ℝ) :
    (∏ a∈graph f, g a)=∏ i, match f i with | none => 1 | some a => g (i,a) := by
  unfold graph
  rw [prod_biUnion]
  · apply prod_congr rfl
    intro i hi
    cases hf : f i <;> simp [hf]
  · intro i hi j hj hne
    apply disjoint_left.mpr
    intro z hz hz'
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hz
    obtain ⟨b,hb,he⟩ := mem_image.mp hz'
    exact hne (Prod.mk.inj he).1.symm

/-- A product of site choices factors into selected blocks and unselected marginal terms. -/
theorem selected_product (f : ι → Option α) (a : ι → ℝ) (b : ι×α → ℝ) :
    (∏ i, match f i with | none => a i | some x => b (i,x))=
      (∏ x∈graph f, b x)*(∏ i, match f i with | none => a i | some _ => 1) := by
  rw [prod_graph,← prod_mul_distrib]
  apply prod_congr rfl
  intro i hi
  cases f i <;> simp

end
end PaperC.Prel8.CategoricalTransversals
