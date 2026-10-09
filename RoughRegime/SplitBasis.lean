module

public import RoughRegime.RectanglePolynomials
public import RoughRegime.DyadicPartition


@[expose] public section
/-! Bounded polynomial representatives for the actual bisected reference cell. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace RoughRegime.Model

def splitOrigin {d : ℕ} (r : Fin d) (b : Bool) : Covariate d :=
  WithLp.toLp 2 (fun i => if i = r then (b.toNat : ℝ) / 2 else 0)

def splitSides {d : ℕ} (r : Fin d) (i : Fin d) : ℝ := if i = r then 1 / 2 else 1

theorem splitSides_pos {d : ℕ} (r : Fin d) (i : Fin d) : 0 < splitSides r i := by
  unfold splitSides
  split_ifs <;> norm_num

def splitRectangle {d : ℕ} (r : Fin d) (b : Bool) : Set (Covariate d) :=
  rectangle (splitOrigin r b) (splitSides r)

theorem splitRectangle_subset_cube {d : ℕ} (r : Fin d) (b : Bool) :
    splitRectangle r b ⊆ cube d := by
  intro x hx i
  have hh := hx i
  by_cases hi : i = r
  · subst i
    cases b <;> norm_num [splitOrigin, splitSides, Bool.toNat] at hh <;>
      constructor <;> linarith [hh.1, hh.2]
  · simpa [splitRectangle, splitOrigin, splitSides, hi] using hh

theorem splitRectangle_measurable {d : ℕ} (r : Fin d) (b : Bool) :
    MeasurableSet (splitRectangle r b) := rectangle_measurable _ _

theorem splitSides_prod {d : ℕ} (r : Fin d) : (∏ i, splitSides r i) = (1 / 2 : ℝ) := by
  classical
  calc
    _ = splitSides r r := Finset.prod_eq_single r (fun i _ hi => by simp [splitSides, hi]) (by simp)
    _ = _ := by simp [splitSides]

theorem splitRectangle_volume {d : ℕ} (r : Fin d) (b : Bool) :
    volume (splitRectangle r b) = ENNReal.ofReal (1 / 2 : ℝ) := by
  rw [splitRectangle, rectangle_volume,
    ← ENNReal.ofReal_prod_of_nonneg (fun i _ => (splitSides_pos r i).le), splitSides_prod]

theorem splitRectangle_normalizedVolume {d : ℕ} (r : Fin d) (b : Bool) :
    rectangleVolume (splitOrigin r b) (splitSides r) =
      ENNReal.ofReal (2 : ℝ) • (cubeVolume d).restrict (splitRectangle r b) := by
  rw [rectangleVolume, splitSides_prod]
  norm_num only [one_div_div]
  rw [cubeVolume, Measure.restrict_restrict (splitRectangle_measurable r b),
    inter_eq_left.mpr (splitRectangle_subset_cube r b)]
  rfl

abbrev SplitIndex (d k : ℕ) := Bool × Fin (Module.finrank ℝ (polynomialLpSpace d k))

instance (d k : ℕ) : Fintype (SplitIndex d k) := by unfold SplitIndex; infer_instance

def splitBasisFunction {d : ℕ} (k : ℕ) (r : Fin d) (i : SplitIndex d k)
    (x : Covariate d) : ℝ :=
  (splitRectangle r i.1).indicator (fun x => Real.sqrt 2 *
    polynomialEvaluation (basisPolynomial d k i.2)
      (rectangleCoords (splitOrigin r i.1) (splitSides r) x)) x

theorem splitBasisFunction_measurable {d : ℕ} (k : ℕ) (r : Fin d) (i : SplitIndex d k) :
    Measurable (splitBasisFunction k r i) :=
  ((continuous_const.mul ((polynomialEvaluation_continuous _).comp
    (rectangleCoords_continuous _ _))).measurable).indicator (splitRectangle_measurable _ _)

theorem splitBasisFunction_uniform_bound {d : ℕ} (k : ℕ) (r : Fin d) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ i x, |splitBasisFunction k r i x| ≤ B := by
  obtain ⟨B, hB, hb⟩ := rectangleBasis_uniform_bound (d := d) k
  refine ⟨1 + Real.sqrt 2 * B, ?_, ?_⟩
  · exact le_add_of_nonneg_right (mul_nonneg (Real.sqrt_nonneg _) (by linarith))
  · intro i x
    by_cases hx : x ∈ splitRectangle r i.1
    · rw [splitBasisFunction, indicator_of_mem hx, abs_mul,
        abs_of_nonneg (Real.sqrt_nonneg _)]
      have hi := hb (splitOrigin r i.1) (splitSides r) (splitSides_pos r) i.2 x hx
      nlinarith [Real.sqrt_nonneg (2 : ℝ)]
    · rw [splitBasisFunction, indicator_of_notMem hx]
      simp only [abs_zero]
      positivity

theorem splitBasisFunction_memLp {d : ℕ} (k : ℕ) (r : Fin d) (i : SplitIndex d k) :
    MemLp (splitBasisFunction k r i) 2 (cubeVolume d) := by
  obtain ⟨B, _, hB⟩ := splitBasisFunction_uniform_bound k r
  apply MemLp.of_bound (splitBasisFunction_measurable k r i).aestronglyMeasurable B
  exact Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hB i x)

def splitBasisLp {d : ℕ} (k : ℕ) (r : Fin d) (i : SplitIndex d k) : Lp ℝ 2 (cubeVolume d) :=
  (splitBasisFunction_memLp k r i).toLp (splitBasisFunction k r i)

end RoughRegime.Model
