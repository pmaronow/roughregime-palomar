module

public import Mathlib


@[expose] public section
open Set
open scoped BigOperators ENNReal
noncomputable section
namespace RoughRegime.PoissonInterleaving

/-- Named component slots for a fixed vector of point counts. -/
abbrev Slots {ι : Type*} (c : ι → ℕ) := (i : ι) × Fin (c i)

/-- A deterministic initial ordering of all component slots. -/
def slotEquiv {ι : Type*} [Fintype ι] (c : ι → ℕ) :
    Fin (∑ i, c i) ≃ Slots c :=
  (finCongr (by simp : Fintype.card (Slots c) = ∑ i, c i)).symm.trans
    (Fintype.equivFin (Slots c)).symm

/-- There are exactly N! ways of uniformly ordering the named slots. -/
theorem slotEquivCard {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → ℕ) :
    Fintype.card (Fin (∑ i, c i) ≃ Slots c) = (∑ i, c i).factorial := by
  simpa only [Fintype.card_fin] using Fintype.card_equiv (slotEquiv c)

/-- Label-preserving bijections are exactly independent bijections on all
label fibers. This is an actual finite equivalence, including empty fibers. -/
def preservingEquiv {α β ι : Type*} (f : α → ι) (g : β → ι) :
    {e : α ≃ β // ∀ x, g (e x) = f x} ≃
      ((i : ι) → {x : α // f x = i} ≃ {y : β // g y = i}) where
  toFun e i := e.1.subtypeEquiv (fun x => by rw [e.2 x])
  invFun p := ⟨Equiv.ofFiberEquiv p,Equiv.ofFiberEquiv_map p⟩
  left_inv := by intro e; apply Subtype.ext; apply Equiv.ext; intro x; rfl
  right_inv := by
    intro p
    funext i
    apply Equiv.ext
    rintro ⟨x,hx⟩
    cases hx
    rfl

/-- The slots with label i are precisely its c_i named point indices. -/
def slotFiberEquiv {ι : Type*} (c : ι → ℕ) (i : ι) :
    {a : Slots c // a.1 = i} ≃ Fin (c i) where
  toFun a := a.2 ▸ a.1.2
  invFun k := ⟨⟨i,k⟩,rfl⟩
  left_inv := by rintro ⟨⟨j,k⟩,h⟩; cases h; rfl
  right_inv := by intro k; rfl

/-- Multiplicity of a label in an ordered word. -/
def labelCount {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → ℕ)
    (a : Fin (∑ i, c i) → ι) (i : ι) : ℕ :=
  (Finset.univ.filter (fun k => a k = i)).card

/-- A fixed label word has exactly ∏i c_i! uniform slot orderings above it
when its label counts are correct, and none otherwise. -/
theorem labelWordFiberCard {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → ℕ)
    (a : Fin (∑ i, c i) → ι) :
    Fintype.card {e : Fin (∑ i, c i) ≃ Slots c // ∀ k, (e k).1 = a k} =
      if ∀ i, labelCount c a i = c i then ∏ i, (c i).factorial else 0 := by
  classical
  by_cases ha : ∀ i, labelCount c a i = c i
  · rw [ite_eq_left ha]
    let ef (i : ι) : {k : Fin (∑ j, c j) // a k = i} ≃ {s : Slots c // s.1 = i} :=
      (Fintype.equivOfCardEq (by
        rw [Fintype.card_subtype,Fintype.card_congr (slotFiberEquiv c i),Fintype.card_fin]
        exact ha i))
    rw [Fintype.card_congr (preservingEquiv a (fun s : Slots c => s.1)),Fintype.card_pi]
    apply Finset.prod_congr rfl
    intro i _
    rw [Fintype.card_equiv (ef i),Fintype.card_subtype]
    exact congrArg Nat.factorial (ha i)
  · rw [ite_eq_right ha]
    have hnone : IsEmpty {e : Fin (∑ i, c i) ≃ Slots c // ∀ k, (e k).1 = a k} := by
      constructor
      rintro ⟨e,he⟩
      apply ha
      intro i
      have ei := (e.subtypeEquiv (fun k => by rw [he k])).trans (slotFiberEquiv c i)
      simpa only [Fintype.card_subtype,Fintype.card_fin,labelCount] using Fintype.card_congr ei
    exact Fintype.card_eq_zero



/-- Exact counting rewrite for every quantity that depends only on the
component-label word. This is the finite uniform-shuffle identity. -/
theorem sum_by_label_word {ι R : Type*} [Fintype ι] [DecidableEq ι] [AddCommMonoid R]
    (c : ι → ℕ) (f : (Fin (∑ i, c i) → ι) → R) :
    ∑ e : Fin (∑ i, c i) ≃ Slots c, f (fun k => (e k).1) =
      ∑ a : Fin (∑ i, c i) → ι,
        (if ∀ i, labelCount c a i = c i then ∏ i, (c i).factorial else 0) • f a := by
  classical
  rw [← Fintype.sum_fiberwise (fun e : Fin (∑ i, c i) ≃ Slots c => fun k => (e k).1)]
  apply Finset.sum_congr rfl
  intro a _
  have he : Fintype.card {e : Fin (∑ i, c i) ≃ Slots c // (fun k => (e k).1) = a} =
      if ∀ i, labelCount c a i = c i then ∏ i, (c i).factorial else 0 := by
    rw [Fintype.card_congr (Equiv.subtypeEquivRight (fun e => funext_iff))]
    exact labelWordFiberCard c a
  have hpoint (e : {e : Fin (∑ i, c i) ≃ Slots c // (fun k => (e k).1) = a}) :
      f (fun k => (e.1 k).1) = f a := congrArg f e.2
  simp only [hpoint,Finset.sum_const,Finset.card_univ,he]



/-- Actual uniform independent random ordering of the named slots. -/
def uniformOrdering {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → ℕ) :
    PMF (Fin (∑ i, c i) ≃ Slots c) := by
  letI : Nonempty (Fin (∑ i, c i) ≃ Slots c) := ⟨slotEquiv c⟩
  exact PMF.uniformOfFintype _

/-- The actual label-word distribution produced by uniform interleaving. -/
def labelWordLaw {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → ℕ) :
    PMF (Fin (∑ i, c i) → ι) := (uniformOrdering c).map (fun e => fun k => (e k).1)

/-- Conditional on the component counts, every compatible label word has
exact probability ∏c_i!/N!, and incompatible words have probability zero. -/
theorem labelWordLaw_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → ℕ)
    (a : Fin (∑ i, c i) → ι) :
    labelWordLaw c a = if ∀ i, labelCount c a i = c i then
      (∏ i, ((c i).factorial : ℝ≥0∞))/( (∑ i, c i).factorial : ℝ≥0∞) else 0 := by
  classical
  let : Nonempty (Fin (∑ i, c i) ≃ Slots c) := ⟨slotEquiv c⟩
  rw [← PMF.toOuterMeasure_apply_singleton,labelWordLaw,PMF.toOuterMeasure_map_apply,
    uniformOrdering,PMF.toOuterMeasure_uniformOfFintype_apply,slotEquivCard]
  have he : Fintype.card ((fun e : Fin (∑ i, c i) ≃ Slots c => fun k => (e k).1) ⁻¹' {a}) =
      if ∀ i, labelCount c a i = c i then ∏ i, (c i).factorial else 0 := by
    let ee : ((fun e : Fin (∑ i, c i) ≃ Slots c => fun k => (e k).1) ⁻¹' {a}) ≃
        {e : Fin (∑ i, c i) ≃ Slots c // ∀ k, (e k).1 = a k} :=
      Equiv.subtypeEquivRight (fun e => by simp only [Set.mem_preimage,Set.mem_singleton_iff,funext_iff])
    rw [Fintype.card_congr ee,labelWordFiberCard]
  rw [he]
  split_ifs <;> simp

end RoughRegime.PoissonInterleaving
