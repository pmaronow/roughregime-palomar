module

public import RoughRegime.DyadicIntegral


@[expose] public section
/-! Genuine two-child indexing and measure refinement of the source partitions. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace RoughRegime.Model

theorem dyadicChildCell_bijective (d j : ℕ) (hd : 0 < d) :
    Function.Bijective (fun p : DyadicCell d j × Bool => dyadicChildCell hd p.1 p.2) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · rintro ⟨c, b⟩ ⟨e, q⟩ he
    have hp := congrArg (dyadicParentCell hd) he
    simp only [dyadicParentCell_child] at hp
    subst e
    have hb : b = q := by
      cases b <;> cases q
      · rfl
      · exact False.elim (dyadicChildCell_false_ne_true hd c he)
      · exact False.elim (dyadicChildCell_false_ne_true hd c he.symm)
      · rfl
    exact Prod.ext rfl hb
  · rw [Fintype.card_prod, dyadicCell_card d j hd, Fintype.card_bool,
      dyadicCell_card d (j + 1) hd, pow_succ]

def dyadicChildrenEquiv (d j : ℕ) (hd : 0 < d) : DyadicCell d j × Bool ≃ DyadicCell d (j + 1) :=
  Equiv.ofBijective (fun p => dyadicChildCell hd p.1 p.2) (dyadicChildCell_bijective d j hd)

theorem sum_dyadic_children {d j : ℕ} (hd : 0 < d) (f : DyadicCell d (j + 1) → ℝ) :
    (∑ c : DyadicCell d (j + 1), f c) =
      ∑ c : DyadicCell d j, ∑ b : Bool, f (dyadicChildCell hd c b) := by
  rw [← (dyadicChildrenEquiv d j hd).sum_comp f, Fintype.sum_prod_type]
  rfl

theorem dyadic_partition_children {d j : ℕ} (hd : 0 < d) (c : DyadicCell d j) :
    dyadicPartitionCell (dyadicChildCell hd c false) ∪ dyadicPartitionCell (dyadicChildCell hd c true) =
      dyadicPartitionCell c := by
  apply le_antisymm
  · apply union_subset
    all_goals simpa only [dyadicParentCell_child] using dyadicPartitionCell_refinement hd (dyadicChildCell hd c _)
  · intro x hx
    obtain ⟨⟨e, b⟩, he⟩ := (dyadicChildCell_bijective d j hd).surjective (dyadicSelection d (j + 1) x)
    have hp := dyadicParentCell_selection d j hd x hx.1
    rw [← he, dyadicParentCell_child, hx.2] at hp
    change e = c at hp
    subst e
    have hm : x ∈ dyadicPartitionCell (dyadicChildCell hd c b) := ⟨hx.1, he.symm⟩
    cases b
    · exact Or.inl hm
    · exact Or.inr hm

theorem dyadicCell_measure_children {d j : ℕ} (hd : 0 < d) (c : DyadicCell d j) :
    rectangleVolume (dyadicOrigin c) (dyadicSides c) =
      ENNReal.ofReal (1 / 2 : ℝ) •
        (rectangleVolume (dyadicOrigin (dyadicChildCell hd c false)) (dyadicSides (dyadicChildCell hd c false)) +
        rectangleVolume (dyadicOrigin (dyadicChildCell hd c true)) (dyadicSides (dyadicChildCell hd c true))) := by
  simp only [dyadicRectangle_normalizedVolume hd]
  rw [← dyadic_partition_children hd c,
    Measure.restrict_union (dyadicPartitionCell_pairwiseDisjoint d (j + 1) (dyadicChildCell_false_ne_true hd c))
      (dyadicPartitionCell_measurable _), smul_add, smul_add, smul_smul, smul_smul]
  congr 1 <;> congr 1 <;> rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2), pow_succ]
  all_goals congr 1; ring

end RoughRegime.Model
