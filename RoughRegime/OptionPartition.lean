module

public import RoughRegime.PartitionPoisson


@[expose] public section
/-! The finite measurable partition consisting of named disjoint regions
and their actual complement. -/
noncomputable section
open Set MeasureTheory Function
namespace RoughRegime.PartitionPoisson
variable {X ι : Type*} [MeasurableSpace X] [Fintype ι] [DecidableEq ι]

def partitionPiece (s : ι → Set X) : Option ι → Set X
  | none => (⋃ i, s i)ᶜ
  | some i => s i

theorem partitionPiece_measurable (s : ι → Set X) (hm : ∀ i, MeasurableSet (s i)) :
    ∀ i, MeasurableSet (partitionPiece s i)
  | none => (MeasurableSet.iUnion hm).compl
  | some i => hm i

theorem partitionPiece_disjoint (s : ι → Set X) (hd : Pairwise (Disjoint on s)) :
    Pairwise (Disjoint on partitionPiece s) := by
  intro a b hab
  cases a with
  | none =>
    cases b with
    | none => exact False.elim (hab rfl)
    | some b =>
      apply disjoint_left.mpr
      intro x hx hy
      exact hx (mem_iUnion.mpr ⟨b, hy⟩)
  | some a =>
    cases b with
    | none =>
      apply disjoint_left.mpr
      intro x hx hy
      exact hy (mem_iUnion.mpr ⟨a, hx⟩)
    | some b => exact hd (fun he => hab (congrArg some he))

theorem partitionPiece_cover (s : ι → Set X) : (⋃ i, partitionPiece s i) = univ := by
  classical
  ext x
  simp only [mem_univ, iff_true]
  by_cases hx : x ∈ ⋃ i, s i
  · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨some i, hi⟩
  · exact mem_iUnion.mpr ⟨none, hx⟩

end RoughRegime.PartitionPoisson
