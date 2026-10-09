module

public import RoughRegime.GridPairMass
public import RoughRegime.GridRegion


@[expose] public section
/-! Null grid faces and the genuine almost-everywhere geometric partition. -/
noncomputable section
namespace RoughRegime.LatticePriors
open MeasureTheory Set
variable {D N : ℕ}

 theorem gridBlockClosed_ae_eq_open (offset ell : ℝ) (hell : 0 < ell) (b : GridBlock D N) :
    gridBlockClosed offset ell b =ᵐ[volume] gridBlockOpen offset ell b := by
  have hq (q : Fin (D + 1)) : ∀ᵐ x ∂(volume : Measure (Model.Covariate (D + 1))),
      x q ≠ offset + ell * (gridCell b q : ℝ) ∧
      x q ≠ offset + ell * ((gridCell b q : ℝ) + 1) := by
    have hl : ∀ᵐ x ∂(volume : Measure (Model.Covariate (D + 1))),
        x q ≠ offset + ell * (gridCell b q : ℝ) := by
      rw [ae_iff]
      simpa only [not_not] using volume_coordinate_fiber_zero (D + 1) q (offset + ell * (gridCell b q : ℝ))
    have hu : ∀ᵐ x ∂(volume : Measure (Model.Covariate (D + 1))),
        x q ≠ offset + ell * ((gridCell b q : ℝ) + 1) := by
      rw [ae_iff]
      simpa only [not_not] using volume_coordinate_fiber_zero (D + 1) q (offset + ell * ((gridCell b q : ℝ) + 1))
    exact hl.and hu
  filter_upwards [ae_all_iff.mpr hq] with x hx
  apply propext
  constructor
  · intro hclosed
    apply (gridBlockOpen_iff offset ell b hell x).mpr
    intro q
    have hb := gridBlockClosed_coordinate_bounds offset ell b hell x hclosed q
    exact ⟨lt_of_le_of_ne hb.1 (hx q).1.symm, lt_of_le_of_ne hb.2 (hx q).2⟩
  · intro hopen q
    exact ⟨(hopen q).1.le, (hopen q).2.le⟩

 theorem gridBlockClosed_pairwiseAEDisjoint (offset ell : ℝ) (hell : 0 < ell) :
    Pairwise (fun a b : GridBlock D N => AEDisjoint volume
      (gridBlockClosed offset ell a) (gridBlockClosed offset ell b)) := by
  intro a b hab
  exact ((gridBlockOpen_pairwiseDisjoint D N offset ell hell) hab).aedisjoint.congr
    (gridBlockClosed_ae_eq_open offset ell hell a) (gridBlockClosed_ae_eq_open offset ell hell b)

 def gridPairClosed (offset ell : ℝ) (k : GridPair D N) : Set (Model.Covariate (D + 1)) :=
  gridBlockClosed offset ell (k, false) ∪ gridBlockClosed offset ell (k, true)
 def gridPairOpen (offset ell : ℝ) (k : GridPair D N) : Set (Model.Covariate (D + 1)) :=
  gridBlockOpen offset ell (k, false) ∪ gridBlockOpen offset ell (k, true)

 theorem gridPairClosed_ae_eq_open (offset ell : ℝ) (hell : 0 < ell) (k : GridPair D N) :
    gridPairClosed offset ell k =ᵐ[volume] gridPairOpen offset ell k := by
  filter_upwards [gridBlockClosed_ae_eq_open offset ell hell (k, false),
    gridBlockClosed_ae_eq_open offset ell hell (k, true)] with x hf ht
  change (x ∈ gridBlockClosed offset ell (k, false) ∪ gridBlockClosed offset ell (k, true)) = _
  simp only [gridPairOpen, mem_union]
  rw [hf, ht]

 theorem gridPairClosed_pairwiseAEDisjoint (offset ell : ℝ) (hell : 0 < ell) :
    Pairwise (fun a b : GridPair D N => AEDisjoint volume
      (gridPairClosed offset ell a) (gridPairClosed offset ell b)) := by
  intro a b hab
  simp only [gridPairClosed, AEDisjoint.union_left_iff, AEDisjoint.union_right_iff]
  have h (s t : Bool) : (a, s) ≠ (b, t) := fun he => hab (congrArg Prod.fst he)
  exact ⟨⟨gridBlockClosed_pairwiseAEDisjoint offset ell hell (h false false),
    gridBlockClosed_pairwiseAEDisjoint offset ell hell (h true false)⟩,
    ⟨gridBlockClosed_pairwiseAEDisjoint offset ell hell (h false true),
      gridBlockClosed_pairwiseAEDisjoint offset ell hell (h true true)⟩⟩

theorem gridBlockClosed_iff (offset ell : ℝ) (b : GridBlock D N) (hell : 0 < ell)
    (x : Model.Covariate (D + 1)) : x ∈ gridBlockClosed offset ell b ↔
      ∀ q, offset + ell * (gridCell b q : ℝ) ≤ x q ∧ x q ≤ offset + ell * ((gridCell b q : ℝ) + 1) := by
  refine ⟨fun hx q => gridBlockClosed_coordinate_bounds offset ell b hell x hx q, ?_⟩
  intro hx q
  have hh := hx q
  change 0 ≤ ell⁻¹ * (x q - (offset + ell * (gridCell b q : ℝ))) ∧
    ell⁻¹ * (x q - (offset + ell * (gridCell b q : ℝ))) ≤ 1
  refine ⟨mul_nonneg (inv_nonneg.mpr hell.le) (sub_nonneg.mpr hh.1), ?_⟩
  apply (inv_mul_le_iff₀ hell).mpr
  linarith

 theorem gridCell_surjective (c : Fin (D + 1) → Fin (2 * N)) :
    ∃ b : GridBlock D N, ∀ q, gridCell b q = (c q).val := by
  let k : Fin N := ⟨(c 0).val / 2, by have := (c 0).isLt; omega⟩
  let label : Bool := decide ((c 0).val % 2 = 1)
  refine ⟨((k, fun q => c q.succ), label), ?_⟩
  intro q
  cases q using Fin.cases
  · change 2 * ((c 0).val / 2) + (decide ((c 0).val % 2 = 1)).toNat = (c 0).val
    by_cases h : (c 0).val % 2 = 1
    · simp only [h, decide_true, Bool.toNat_true]
      omega
    · simp only [h, decide_false, Bool.toNat_false, add_zero]
      omega
  · rfl

 lemma real_closed_grid_index (m : ℕ) (hm : 0 < m) (y : ℝ) (hy : 0 ≤ y) (hym : y ≤ m) :
    ∃ k : Fin m, (k : ℝ) ≤ y ∧ y ≤ (k : ℝ) + 1 := by
  by_cases hylt : y < m
  · exact ⟨⟨Nat.floor y, (Nat.floor_lt hy).mpr hylt⟩, Nat.floor_le hy, (Nat.lt_floor_add_one y).le⟩
  · have he : y = (m : ℝ) := le_antisymm hym (le_of_not_gt hylt)
    refine ⟨⟨m - 1, by omega⟩, ?_⟩
    have hc : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
    change ((m - 1 : ℕ) : ℝ) ≤ y ∧ y ≤ ((m - 1 : ℕ) : ℝ) + 1
    rw [hc, he]
    constructor <;> linarith

 theorem gridRegion_eq_iUnion_closed (offset ell : ℝ) (hell : 0 < ell) (hN : 0 < N) :
    gridRegion (D + 1) N offset ell = ⋃ b : GridBlock D N, gridBlockClosed offset ell b := by
  classical
  ext x
  constructor
  · intro hx
    let y : Fin (D + 1) → ℝ := fun q => (x q - offset) / ell
    have hy (q) : 0 ≤ y q := div_nonneg (sub_nonneg.mpr (hx q).1) hell.le
    have hym (q) : y q ≤ (2 * N : ℕ) := by
      apply (div_le_iff₀ hell).mpr
      nlinarith [(hx q).2]
    have hi (q) := real_closed_grid_index (2 * N) (by omega) (y q) (hy q) (hym q)
    let c : Fin (D + 1) → Fin (2 * N) := fun q => Classical.choose (hi q)
    have hc (q) : (c q : ℝ) ≤ y q ∧ y q ≤ (c q : ℝ) + 1 := Classical.choose_spec (hi q)
    obtain ⟨b, hb⟩ := gridCell_surjective c
    refine mem_iUnion.mpr ⟨b, (gridBlockClosed_iff offset ell b hell x).mpr ?_⟩
    intro q
    rw [hb q]
    have hlow := (le_div_iff₀ hell).mp (hc q).1
    have hhigh := (div_le_iff₀ hell).mp (hc q).2
    constructor <;> nlinarith
  · intro hx
    obtain ⟨b, hb⟩ := mem_iUnion.mp hx
    intro q
    have hx := gridBlockClosed_coordinate_bounds offset ell b hell x hb q
    have hc : (gridCell b q : ℝ) + 1 ≤ (2 * N : ℕ) := by exact_mod_cast gridCell_lt b q
    have hn := Nat.cast_nonneg (α := ℝ) (gridCell b q)
    constructor <;> nlinarith

 theorem grid_iUnion_closed_ae_eq_open (offset ell : ℝ) (hell : 0 < ell) :
    (⋃ b : GridBlock D N, gridBlockClosed offset ell b) =ᵐ[volume]
      (⋃ b : GridBlock D N, gridBlockOpen offset ell b) := by
  filter_upwards [ae_all_iff.mpr (fun b : GridBlock D N => gridBlockClosed_ae_eq_open offset ell hell b)] with x hx
  simp only [mem_iUnion]
  congr 1
  funext b
  exact hx b

 theorem gridRegion_ae_eq_iUnion_open (offset ell : ℝ) (hell : 0 < ell) :
    gridRegion (D + 1) N offset ell =ᵐ[volume] ⋃ b : GridBlock D N, gridBlockOpen offset ell b := by
  by_cases hN : 0 < N
  · rw [gridRegion_eq_iUnion_closed offset ell hell hN]
    exact grid_iUnion_closed_ae_eq_open offset ell hell
  · have he : N = 0 := by omega
    subst N
    have hnull : (volume : Measure (Model.Covariate (D + 1))) (gridRegion (D + 1) 0 offset ell) = 0 := by
      simpa using gridRegion_volume (D + 1) 0 offset ell hell.le
    have ha : ∀ᵐ x ∂(volume : Measure (Model.Covariate (D + 1))), x ∉ gridRegion (D + 1) 0 offset ell := by
      rw [ae_iff]
      simpa only [not_not, Set.ofPred_mem_eq] using hnull
    filter_upwards [ha] with x hx
    simp [hx, GridBlock, GridPair]

 theorem grid_iUnion_pairClosed (offset ell : ℝ) :
    (⋃ k : GridPair D N, gridPairClosed offset ell k) =
      ⋃ b : GridBlock D N, gridBlockClosed offset ell b := by
  ext x
  simp only [mem_iUnion, gridPairClosed, mem_union]
  constructor
  · rintro ⟨k, hk | hk⟩
    · exact ⟨(k, false), hk⟩
    · exact ⟨(k, true), hk⟩
  · rintro ⟨⟨k, label⟩, hk⟩
    cases label
    · exact ⟨k, Or.inl hk⟩
    · exact ⟨k, Or.inr hk⟩

 theorem gridRegion_ae_eq_iUnion_pairClosed (offset ell : ℝ) (hell : 0 < ell) :
    gridRegion (D + 1) N offset ell =ᵐ[volume] ⋃ k : GridPair D N, gridPairClosed offset ell k := by
  rw [grid_iUnion_pairClosed]
  exact (gridRegion_ae_eq_iUnion_open offset ell hell).trans (grid_iUnion_closed_ae_eq_open offset ell hell).symm

theorem gridBlockOpen_measurable (offset ell : ℝ) (hell : 0 < ell) (b : GridBlock D N) :
    MeasurableSet (gridBlockOpen offset ell b) := by
  have he : gridBlockOpen offset ell b = ⋂ q : Fin (D + 1),
      {x : Model.Covariate (D + 1) | offset + ell * (gridCell b q : ℝ) < x q ∧
        x q < offset + ell * ((gridCell b q : ℝ) + 1)} := by
    ext x
    simp only [mem_iInter, mem_ofPred_eq]
    exact gridBlockOpen_iff offset ell b hell x
  rw [he]
  apply MeasurableSet.iInter
  intro q
  exact (measurableSet_lt measurable_const (PiLp.continuous_apply 2 (fun _ : Fin (D + 1) => ℝ) q).measurable).inter
    (measurableSet_lt (PiLp.continuous_apply 2 (fun _ : Fin (D + 1) => ℝ) q).measurable measurable_const)

 theorem gridPairOpen_measurable (offset ell : ℝ) (hell : 0 < ell) (k : GridPair D N) :
    MeasurableSet (gridPairOpen offset ell k) :=
  (gridBlockOpen_measurable offset ell hell (k, false)).union
    (gridBlockOpen_measurable offset ell hell (k, true))

 theorem gridPairClosed_measurable (offset ell : ℝ) (k : GridPair D N) :
    MeasurableSet (gridPairClosed offset ell k) :=
  (gridBlockClosed_measurable offset ell (k, false)).union (gridBlockClosed_measurable offset ell (k, true))

 theorem gridPairOpen_pairwiseDisjoint (offset ell : ℝ) (hell : 0 < ell) :
    Pairwise (fun a b : GridPair D N => Disjoint (gridPairOpen offset ell a) (gridPairOpen offset ell b)) := by
  intro a b hab
  simp only [gridPairOpen, disjoint_union_left, disjoint_union_right]
  have h (s t : Bool) : (a, s) ≠ (b, t) := fun he => hab (congrArg Prod.fst he)
  exact ⟨⟨gridBlockOpen_pairwiseDisjoint D N offset ell hell (h false false),
    gridBlockOpen_pairwiseDisjoint D N offset ell hell (h true false)⟩,
    ⟨gridBlockOpen_pairwiseDisjoint D N offset ell hell (h false true),
      gridBlockOpen_pairwiseDisjoint D N offset ell hell (h true true)⟩⟩

 theorem grid_iUnion_pairOpen (offset ell : ℝ) :
    (⋃ k : GridPair D N, gridPairOpen offset ell k) = ⋃ b : GridBlock D N, gridBlockOpen offset ell b := by
  ext x
  simp only [mem_iUnion, gridPairOpen, mem_union]
  constructor
  · rintro ⟨k, hk | hk⟩
    · exact ⟨(k, false), hk⟩
    · exact ⟨(k, true), hk⟩
  · rintro ⟨⟨k, label⟩, hk⟩
    cases label
    · exact ⟨k, Or.inl hk⟩
    · exact ⟨k, Or.inr hk⟩

 theorem gridRegion_ae_eq_iUnion_pairOpen (offset ell : ℝ) (hell : 0 < ell) :
    gridRegion (D + 1) N offset ell =ᵐ[volume] ⋃ k : GridPair D N, gridPairOpen offset ell k := by
  rw [grid_iUnion_pairOpen]
  exact gridRegion_ae_eq_iUnion_open offset ell hell

 theorem gridPairClosed_ae_eq_open_of_ac (offset ell : ℝ) (hell : 0 < ell)
    (μ : Measure (Model.Covariate (D + 1))) (hμ : μ ≪ volume) (k : GridPair D N) :
    gridPairClosed offset ell k =ᵐ[μ] gridPairOpen offset ell k :=
  hμ.ae_le (gridPairClosed_ae_eq_open offset ell hell k)

end RoughRegime.LatticePriors
