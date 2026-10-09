module

public import RoughRegime.ProductBaselines


@[expose] public section
/-! Literal bounded real response spaces for the product applications.  The
Rademacher baselines are actual pushforward probability laws on these spaces. -/
noncomputable section
open MeasureTheory Set ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology
namespace RoughRegime.Applications.Products

abbrev BoundedResponse := Set.Icc (-1 : ℝ) 1
abbrev PairResponse := BoundedResponse × BoundedResponse

def signPoint (b : Bool) : BoundedResponse :=
  ⟨sign b, abs_le.mp (le_of_eq (sign_abs b))⟩

def pairPoint (b : Bool × Bool) : PairResponse := (signPoint b.1, signPoint b.2)

def boundedPairBaseline : ProbabilityMeasure PairResponse :=
  ProbabilityMeasure.map pairBaseline pairPoint

def boundedDiagonalBaseline : ProbabilityMeasure BoundedResponse :=
  ProbabilityMeasure.map diagonalBaseline signPoint

def firstResponse (z : PairResponse) : ℝ := z.1.1
def secondResponse (z : PairResponse) : ℝ := z.2.1

theorem firstResponse_measurable : Measurable firstResponse :=
  measurable_subtype_coe.comp measurable_fst

theorem secondResponse_measurable : Measurable secondResponse :=
  measurable_subtype_coe.comp measurable_snd

theorem response_bound (z : BoundedResponse) : |(z : ℝ)| ≤ 1 := abs_le.mpr z.property

theorem firstResponse_bound (z : PairResponse) : |firstResponse z| ≤ 1 := response_bound z.1

theorem secondResponse_bound (z : PairResponse) : |secondResponse z| ≤ 1 := response_bound z.2

theorem boundedPairBaseline_integral (f : PairResponse → ℝ) (hf : Measurable f) :
    (∫ z, f z ∂(boundedPairBaseline : Measure PairResponse)) =
      (f (pairPoint (false,false)) + f (pairPoint (false,true)) +
        f (pairPoint (true,false)) + f (pairPoint (true,true))) / 4 := by
  change (∫ z, f z ∂(pairBaseline : Measure (Bool × Bool)).map pairPoint) = _
  rw [integral_map (measurable_of_countable pairPoint).aemeasurable hf.aestronglyMeasurable,
    pairBaseline_integral]

theorem boundedDiagonalBaseline_integral (f : BoundedResponse → ℝ) (hf : Measurable f) :
    (∫ z, f z ∂(boundedDiagonalBaseline : Measure BoundedResponse)) =
      (f (signPoint false) + f (signPoint true)) / 2 := by
  change (∫ z, f z ∂(diagonalBaseline : Measure Bool).map signPoint) = _
  rw [integral_map (measurable_of_countable signPoint).aemeasurable hf.aestronglyMeasurable,
    diagonalBaseline_integral]

theorem boundedPairBaseline_finite_support :
    ∃ s : Finset PairResponse, (boundedPairBaseline : Measure PairResponse) (s : Set PairResponse) = 1 := by
  classical
  refine ⟨Finset.univ.image pairPoint, ?_⟩
  change (pairBaseline : Measure (Bool × Bool)).map pairPoint (↑(Finset.univ.image pairPoint)) = 1
  rw [Measure.map_apply (measurable_of_countable pairPoint) (Finset.measurableSet _)]
  have hs : pairPoint ⁻¹' (↑(Finset.univ.image pairPoint) : Set PairResponse) = univ := by
    ext i
    simp
  rw [hs, measure_univ]

theorem boundedDiagonalBaseline_finite_support :
    ∃ s : Finset BoundedResponse,
      (boundedDiagonalBaseline : Measure BoundedResponse) (s : Set BoundedResponse) = 1 := by
  classical
  refine ⟨Finset.univ.image signPoint, ?_⟩
  change (diagonalBaseline : Measure Bool).map signPoint (↑(Finset.univ.image signPoint)) = 1
  rw [Measure.map_apply (measurable_of_countable signPoint) (Finset.measurableSet _)]
  have hs : signPoint ⁻¹' (↑(Finset.univ.image signPoint) : Set BoundedResponse) = univ := by
    ext i
    cases i <;> simp
  rw [hs, measure_univ]

theorem bounded_pair_baseline_nondegenerate (A : Model.Parameters)
    (F : Model.Observables PairResponse A) (hD : F.D = fun _ => 1)
    (hU : F.U = firstResponse) (hV : F.V = secondResponse)
    (hlo : max A.δ A.gminus < 1) (hhi : 1 < A.gplus) :
    Model.Nondegenerate A F boundedPairBaseline := by
  have hw : Model.baselineW A F boundedPairBaseline = 1 := by
    unfold Model.baselineW
    rw [hD, integral_const, probReal_univ]
    simp
  have hau : (∫ z, F.U z ∂(boundedPairBaseline : Measure PairResponse)) = 0 := by
    rw [hU, boundedPairBaseline_integral _ firstResponse_measurable]
    norm_num [firstResponse, pairPoint, signPoint, sign]
  have hbv : (∫ z, F.V z ∂(boundedPairBaseline : Measure PairResponse)) = 0 := by
    rw [hV, boundedPairBaseline_integral _ secondResponse_measurable]
    norm_num [secondResponse, pairPoint, signPoint, sign]
  have ha : Model.baselineA A F boundedPairBaseline = 0 := by
    rw [Model.baselineA, hau, hw]; norm_num
  have hb : Model.baselineB A F boundedPairBaseline = 0 := by
    rw [Model.baselineB, hbv, hw]; norm_num
  refine ⟨boundedPairBaseline_finite_support, by simpa only [hw] using hlo,
    by simpa only [hw] using hhi, by simpa only [ha, abs_zero] using A.hH,
    by simpa only [hb, abs_zero] using A.hH, ?_⟩
  dsimp only
  rw [ha, hb]
  simp only [zero_mul, sub_zero]
  rw [hU, hV]
  rw [boundedPairBaseline_integral _ (firstResponse_measurable.pow_const 2),
    boundedPairBaseline_integral _ (secondResponse_measurable.pow_const 2),
    boundedPairBaseline_integral (fun z => firstResponse z * secondResponse z)
      (firstResponse_measurable.mul secondResponse_measurable)]
  left
  norm_num [firstResponse, secondResponse, pairPoint, signPoint, sign]

theorem bounded_diagonal_baseline_nondegenerate (A : Model.Parameters)
    (F : Model.Observables BoundedResponse A) (hD : F.D = fun _ => 1)
    (hU : F.U = Subtype.val) (hV : F.V = Subtype.val)
    (hlo : max A.δ A.gminus < 1) (hhi : 1 < A.gplus) (hab : A.α = A.β) :
    Model.Nondegenerate A F boundedDiagonalBaseline := by
  have hw : Model.baselineW A F boundedDiagonalBaseline = 1 := by
    unfold Model.baselineW
    rw [hD, integral_const, probReal_univ]
    simp
  have hm : (∫ z : BoundedResponse, (z : ℝ) ∂(boundedDiagonalBaseline : Measure BoundedResponse)) = 0 := by
    rw [boundedDiagonalBaseline_integral _ measurable_subtype_coe]
    norm_num [signPoint, sign]
  have ha : Model.baselineA A F boundedDiagonalBaseline = 0 := by
    rw [Model.baselineA, hU, hm, hw]; norm_num
  have hb : Model.baselineB A F boundedDiagonalBaseline = 0 := by
    rw [Model.baselineB, hV, hm, hw]; norm_num
  refine ⟨boundedDiagonalBaseline_finite_support, by simpa only [hw] using hlo,
    by simpa only [hw] using hhi, by simpa only [ha, abs_zero] using A.hH,
    by simpa only [hb, abs_zero] using A.hH, ?_⟩
  dsimp only
  right
  refine ⟨by rw [hU, hV], hab, ?_⟩
  rw [ha, hU]
  simp only [zero_mul, sub_zero]
  rw [boundedDiagonalBaseline_integral _ (measurable_subtype_coe.pow_const 2)]
  norm_num [signPoint, sign]

/-- Root-n hardness on the entire class of bounded real pairs, not merely
on the four-point baseline support. -/
theorem bounded_pair_class_parametric_lower (A : Model.Parameters)
    (F : Model.Observables PairResponse A) (hD : F.D = fun _ => 1)
    (hU : F.U = firstResponse) (hV : F.V = secondResponse)
    (hlo : max A.δ A.gminus < 1) (hhi : 1 < A.gplus) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal (c * (n : ℝ) ^ (-(1 / 2 : ℝ))) ≤
        Model.minimaxRMSE n (Model.target A F) (modelClass A F.U F.V) := by
  obtain ⟨c, hc, n0, _, hn⟩ := Model.main_parametric_lower A F boundedPairBaseline
    (bounded_pair_baseline_nondegenerate A F hD hU hV hlo hhi) 1 zero_lt_one
  refine ⟨c, hc, eventually_atTop.2 ⟨n0, ?_⟩⟩
  apply hn
  rw [modelClass_eq_generic A F hD ((le_max_left _ _).trans hlo.le)]
  exact Model.localClass_subset A F boundedPairBaseline 1

theorem bounded_diagonal_class_parametric_lower (A : Model.Parameters)
    (F : Model.Observables BoundedResponse A) (hD : F.D = fun _ => 1)
    (hU : F.U = Subtype.val) (hV : F.V = Subtype.val)
    (hlo : max A.δ A.gminus < 1) (hhi : 1 < A.gplus) (hab : A.α = A.β) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal (c * (n : ℝ) ^ (-(1 / 2 : ℝ))) ≤
        Model.minimaxRMSE n (Model.target A F) (modelClass A F.U F.V) := by
  obtain ⟨c, hc, n0, _, hn⟩ := Model.main_parametric_lower A F boundedDiagonalBaseline
    (bounded_diagonal_baseline_nondegenerate A F hD hU hV hlo hhi hab) 1 zero_lt_one
  refine ⟨c, hc, eventually_atTop.2 ⟨n0, ?_⟩⟩
  apply hn
  rw [modelClass_eq_generic A F hD ((le_max_left _ _).trans hlo.le)]
  exact Model.localClass_subset A F boundedDiagonalBaseline 1

end RoughRegime.Applications.Products
