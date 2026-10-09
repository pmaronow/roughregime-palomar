module

public import RoughRegime.LatticeConstruction


@[expose] public section
/-! The actual even Cartesian block grid and its affine local coordinates. -/
noncomputable section
namespace RoughRegime.LatticePriors
open Set
open scoped ContDiff

 abbrev GridPair (D N : ℕ) := Fin N × (Fin D → Fin (2 * N))
 abbrev GridBlock (D N : ℕ) := GridPair D N × Bool

 def gridCell {D N : ℕ} (b : GridBlock D N) : Fin (D + 1) → ℕ :=
  Fin.cons (2 * b.1.1.val + b.2.toNat) (fun q => (b.1.2 q).val)

 theorem gridCell_injective (D N : ℕ) : Function.Injective (gridCell (D := D) (N := N)) := by
  intro a b hab
  have h0 := congrFun hab 0
  simp only [gridCell, Fin.cons_zero] at h0
  have hl : a.2 = b.2 := by cases ha : a.2 <;> cases hb : b.2 <;> simp_all [Bool.toNat] <;> omega
  have hp : a.1.1 = b.1.1 := by apply Fin.ext; rw [hl] at h0; omega
  have hr : a.1.2 = b.1.2 := by
    funext q
    apply Fin.ext
    have hh := congrFun hab q.succ
    simpa only [gridCell, Fin.cons_succ] using hh
  exact Prod.ext (Prod.ext hp hr) hl

 theorem gridCell_lt {D N : ℕ} (b : GridBlock D N) (q : Fin (D + 1)) : gridCell b q < 2 * N := by
  cases q using Fin.cases
  · simp only [gridCell, Fin.cons_zero]
    have hn := b.1.1.isLt
    cases b.2 <;> simp [Bool.toNat] <;> omega
  · rename_i q
    simpa only [gridCell, Fin.cons_succ] using (b.1.2 q).isLt

 def gridOrigin {D N : ℕ} (offset ell : ℝ) (b : GridBlock D N) : Model.Covariate (D + 1) :=
  WithLp.toLp 2 (fun q => offset + ell * (gridCell b q : ℝ))

 def gridCoords {D N : ℕ} (offset ell : ℝ) (b : GridBlock D N)
    (x : Model.Covariate (D + 1)) : Model.Covariate (D + 1) :=
  ell⁻¹ • (x - gridOrigin offset ell b)

 def gridEmbed {D N : ℕ} (offset ell : ℝ) (b : GridBlock D N)
    (y : Model.Covariate (D + 1)) : Model.Covariate (D + 1) :=
  gridOrigin offset ell b + ell • y

 theorem gridCoords_embed {D N : ℕ} (offset ell : ℝ) (b : GridBlock D N) (hell : ell ≠ 0)
    (y : Model.Covariate (D + 1)) : gridCoords offset ell b (gridEmbed offset ell b y) = y := by
  simp [gridCoords, gridEmbed, smul_smul, inv_mul_cancel₀ hell]
 theorem gridEmbed_coords {D N : ℕ} (offset ell : ℝ) (b : GridBlock D N) (hell : ell ≠ 0)
    (x : Model.Covariate (D + 1)) : gridEmbed offset ell b (gridCoords offset ell b x) = x := by
  simp [gridCoords, gridEmbed, smul_smul, mul_inv_cancel₀ hell]
 theorem gridCoords_smooth {D N : ℕ} (offset ell : ℝ) (b : GridBlock D N) :
    ContDiff ℝ ∞ (gridCoords offset ell b) := by
  unfold gridCoords
  exact (contDiff_id.sub contDiff_const).const_smul (ell⁻¹)
 theorem gridEmbed_smooth {D N : ℕ} (offset ell : ℝ) (b : GridBlock D N) :
    ContDiff ℝ ∞ (gridEmbed offset ell b) := by
  unfold gridEmbed
  exact contDiff_const.add (contDiff_id.const_smul ell)

 def gridBlockOpen {D N : ℕ} (offset ell : ℝ) (b : GridBlock D N) : Set (Model.Covariate (D + 1)) :=
  {x | ∀ q, 0 < gridCoords offset ell b x q ∧ gridCoords offset ell b x q < 1}
 def gridBlockClosed {D N : ℕ} (offset ell : ℝ) (b : GridBlock D N) : Set (Model.Covariate (D + 1)) :=
  {x | ∀ q, 0 ≤ gridCoords offset ell b x q ∧ gridCoords offset ell b x q ≤ 1}

 theorem gridBlockOpen_iff {D N : ℕ} (offset ell : ℝ) (b : GridBlock D N) (hell : 0 < ell)
    (x : Model.Covariate (D + 1)) : x ∈ gridBlockOpen offset ell b ↔
      ∀ q, offset + ell * (gridCell b q : ℝ) < x q ∧ x q < offset + ell * ((gridCell b q : ℝ) + 1) := by
  unfold gridBlockOpen gridCoords gridOrigin
  constructor
  · intro hx q
    have hh := hx q
    change 0 < ell⁻¹ * (x q - (offset + ell * (gridCell b q : ℝ))) ∧
      ell⁻¹ * (x q - (offset + ell * (gridCell b q : ℝ))) < 1 at hh
    have h0 := mul_lt_mul_of_pos_left hh.1 hell
    have h1 := mul_lt_mul_of_pos_left hh.2 hell
    simp only [mul_zero, ← mul_assoc, mul_inv_cancel₀ hell.ne', one_mul, mul_one] at h0 h1
    constructor <;> linarith
  · intro hx q
    have hh := hx q
    change 0 < ell⁻¹ * (x q - (offset + ell * (gridCell b q : ℝ))) ∧
      ell⁻¹ * (x q - (offset + ell * (gridCell b q : ℝ))) < 1
    constructor
    · exact mul_pos (inv_pos.mpr hell) (sub_pos.mpr hh.1)
    · apply (inv_mul_lt_iff₀ hell).mpr
      linarith

 theorem gridBlockOpen_pairwiseDisjoint (D N : ℕ) (offset ell : ℝ) (hell : 0 < ell) :
    Pairwise (fun a b : GridBlock D N => Disjoint (gridBlockOpen offset ell a) (gridBlockOpen offset ell b)) := by
  intro a b hab
  apply Set.disjoint_left.mpr
  intro x hxa hxb
  have ha := (gridBlockOpen_iff offset ell a hell x).mp hxa
  have hb := (gridBlockOpen_iff offset ell b hell x).mp hxb
  apply hab
  apply gridCell_injective D N
  funext q
  by_contra hq
  have hcases : gridCell a q + 1 ≤ gridCell b q ∨ gridCell b q + 1 ≤ gridCell a q := by omega
  rcases hcases with hh | hh
  · have hr : (gridCell a q : ℝ) + 1 ≤ gridCell b q := by exact_mod_cast hh
    nlinarith [(ha q).2, (hb q).1]
  · have hr : (gridCell b q : ℝ) + 1 ≤ gridCell a q := by exact_mod_cast hh
    nlinarith [(hb q).2, (ha q).1]

 theorem gridBlockOpen_subset_cube {D N : ℕ} (offset ell : ℝ) (b : GridBlock D N) (hell : 0 < ell)
    (hoff : 0 ≤ offset) (hsize : offset + ell * (2 * N : ℕ) ≤ 1) :
    gridBlockOpen offset ell b ⊆ Model.cube (D + 1) := by
  intro x hx q
  have hh := (gridBlockOpen_iff offset ell b hell x).mp hx q
  have hc : (gridCell b q : ℝ) + 1 ≤ (2 * N : ℕ) := by exact_mod_cast gridCell_lt b q
  constructor
  · have hcell : 0 ≤ (gridCell b q : ℝ) := Nat.cast_nonneg _
    nlinarith
  · nlinarith

 theorem gridPair_card (D N : ℕ) : Fintype.card (GridPair D N) = N * (2 * N) ^ D := by
  simp [GridPair]
 theorem gridBlock_card (D N : ℕ) : Fintype.card (GridBlock D N) = (2 * N) ^ (D + 1) := by
  simp only [GridBlock, GridPair, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, pow_succ]
  ring

 theorem gridBlockClosed_coordinate_bounds {D N : ℕ} (offset ell : ℝ) (b : GridBlock D N) (hell : 0 < ell)
    (x : Model.Covariate (D + 1)) (hx : x ∈ gridBlockClosed offset ell b) (q : Fin (D + 1)) :
    offset + ell * (gridCell b q : ℝ) ≤ x q ∧ x q ≤ offset + ell * ((gridCell b q : ℝ) + 1) := by
  have hh := hx q
  change 0 ≤ ell⁻¹ * (x q - (offset + ell * (gridCell b q : ℝ))) ∧
    ell⁻¹ * (x q - (offset + ell * (gridCell b q : ℝ))) ≤ 1 at hh
  have h0 := mul_le_mul_of_nonneg_left hh.1 hell.le
  have h1 := mul_le_mul_of_nonneg_left hh.2 hell.le
  simp only [mul_zero, ← mul_assoc, mul_inv_cancel₀ hell.ne', one_mul, mul_one] at h0 h1
  constructor <;> linarith

 theorem gridClosedOpen_unique {D N : ℕ} (offset ell : ℝ) (hell : 0 < ell) (a b : GridBlock D N)
    (x : Model.Covariate (D + 1)) (hxa : x ∈ gridBlockClosed offset ell a) (hxb : x ∈ gridBlockOpen offset ell b) : a = b := by
  apply gridCell_injective D N
  funext q
  have ha := gridBlockClosed_coordinate_bounds offset ell a hell x hxa q
  have hb := (gridBlockOpen_iff offset ell b hell x).mp hxb q
  by_contra hq
  have hcases : gridCell a q + 1 ≤ gridCell b q ∨ gridCell b q + 1 ≤ gridCell a q := by omega
  rcases hcases with hh | hh
  · have hr : (gridCell a q : ℝ) + 1 ≤ gridCell b q := by exact_mod_cast hh
    nlinarith
  · have hr : (gridCell b q : ℝ) + 1 ≤ gridCell a q := by exact_mod_cast hh
    nlinarith

end RoughRegime.LatticePriors
