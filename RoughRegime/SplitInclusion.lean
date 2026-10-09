module

public import RoughRegime.SplitOrthonormal
public import RoughRegime.PolynomialExpansion
public import RoughRegime.HilbertInclusion


@[expose] public section
/-! Actual parent polynomial spaces are contained in the two-child space. -/
noncomputable section
open MeasureTheory Set MvPolynomial
open scoped BigOperators ENNReal
namespace RoughRegime.Model

theorem splitRectangle_union {d : ℕ} (r : Fin d) :
    splitRectangle r false ∪ splitRectangle r true = cube d := by
  apply le_antisymm
  · exact union_subset (splitRectangle_subset_cube r false) (splitRectangle_subset_cube r true)
  · intro x hx
    by_cases hr : x r ≤ 1 / 2
    · left
      intro i
      by_cases hi : i = r
      · subst i
        simpa [splitOrigin, splitSides, Bool.toNat] using (show x r ∈ Icc 0 (1 / 2) from ⟨(hx r).1, hr⟩)
      · simpa [splitOrigin, splitSides, hi] using hx i
    · right
      intro i
      by_cases hi : i = r
      · subst i
        norm_num [splitOrigin, splitSides, Bool.toNat]
        exact
          (show x r ∈ Icc (1 / 2) 1 from ⟨(lt_of_not_ge hr).le, (hx r).2⟩)
      · simpa [splitOrigin, splitSides, hi] using hx i

def splitLpSpace {d : ℕ} (k : ℕ) (r : Fin d) : Submodule ℝ (Lp ℝ 2 (cubeVolume d)) :=
  Submodule.span ℝ (range (splitBasisLp k r))

theorem polynomialToLp_mem_splitSpace {d k : ℕ} (r : Fin d)
    (p : MvPolynomial (Fin d) ℝ) (hp : p.totalDegree ≤ k) :
    polynomialToLp d p ∈ splitLpSpace k r := by
  classical
  have hex (b : Bool) := basisPolynomial_evaluation_expansion
    (rectangleEmbedPolynomial (splitOrigin r b) (splitSides r) p)
    ((rectangleEmbedPolynomial_degree _ _ p).trans hp)
  choose c hc using hex
  let a : SplitIndex d k → ℝ := fun i => c i.1 i.2 / Real.sqrt 2
  apply (Submodule.mem_span_range_iff_exists_fun ℝ).mpr
  refine ⟨a, Lp.ext ?_⟩
  have hsum := Lp.coeFn_finsetSum Finset.univ (fun i => a i • splitBasisLp k r i)
  have hsmul : ∀ᵐ x ∂cubeVolume d, ∀ i : SplitIndex d k,
      (a i • splitBasisLp k r i : Lp ℝ 2 (cubeVolume d)) x =
        a i * splitBasisFunction k r i x := by
    apply ae_all_iff.mpr
    intro i
    filter_upwards [Lp.coeFn_smul (a i) (splitBasisLp k r i), splitBasisLp_ae k r i] with x hs hb
    simpa [hs, hb]
  have hnull : cubeVolume d (splitRectangle r false ∩ splitRectangle r true) = 0 := by
    apply le_antisymm _ bot_le
    exact (Measure.restrict_le_self _).trans_eq (splitRectangle_inter_volume_zero r (by decide))
  have hnot : ∀ᵐ x ∂cubeVolume d, x ∉ splitRectangle r false ∩ splitRectangle r true := by
    apply ae_iff.mpr
    simpa only [not_not, ofPred_mem_eq] using hnull
  filter_upwards [hsum, hsmul, polynomialToLp_ae p,
    ae_restrict_mem (measurableSet_cube d), hnot] with x hsum hs hpval hcube hnot
  rw [hsum, hpval]
  simp only [Finset.sum_apply]
  simp_rw [hs]
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  have hhalf (b : Bool) (hx : x ∈ splitRectangle r b) :
      (∑ i, a (b, i) * splitBasisFunction k r (b, i) x) = polynomialEvaluation p x := by
    simp only [a, splitBasisFunction, indicator_of_mem hx]
    have hsqrt : Real.sqrt (2 : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
    have hcancel (i) : c b i / Real.sqrt 2 *
        (Real.sqrt 2 * polynomialEvaluation (basisPolynomial d k i)
          (rectangleCoords (splitOrigin r b) (splitSides r) x)) =
        c b i * polynomialEvaluation (basisPolynomial d k i)
          (rectangleCoords (splitOrigin r b) (splitSides r) x) := by
      field_simp
    simp_rw [hcancel]
    rw [← hc b, rectangleEmbedPolynomial_eval,
      rectangleEmbed_coords _ _ (fun i => (splitSides_pos r i).ne')]
  have hzero (b : Bool) (hx : x ∉ splitRectangle r b) :
      (∑ i, a (b, i) * splitBasisFunction k r (b, i) x) = 0 := by
    simp [splitBasisFunction, hx]
  have hu : x ∈ splitRectangle r false ∪ splitRectangle r true := by
    rw [splitRectangle_union]
    exact hcube
  rcases hu with hf | ht
  · rw [hzero true (fun ht => hnot ⟨hf, ht⟩), hhalf false hf, zero_add]
  · rw [hhalf true ht, hzero false (fun hf => hnot ⟨hf, ht⟩), add_zero]

theorem polynomialLpSpace_le_splitLpSpace {d : ℕ} (r : Fin d) {k l : ℕ} (hkl : k ≤ l) :
    polynomialLpSpace d k ≤ splitLpSpace l r := by
  intro f hf
  obtain ⟨p, hp, rfl⟩ := hf
  exact polynomialToLp_mem_splitSpace r p ((polynomialSpace_degree p hp).trans hkl)

theorem splitLpSpace_finrank {d : ℕ} (k : ℕ) (r : Fin d) :
    Module.finrank ℝ (splitLpSpace k r) = 2 * (d + k).choose d := by
  rw [splitLpSpace, finrank_span_eq_card (splitBasisLp_orthonormal k r).linearIndependent]
  simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin, polynomialLpSpace_finrank]

end RoughRegime.Model
