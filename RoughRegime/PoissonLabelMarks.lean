module

public import RoughRegime.PoissonLabeling


@[expose] public section
/-! Exact removal of mark-score factors from labeling norms. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace RoughRegime.PoissonMeasure

set_option backward.isDefEq.respectTransparency false

variable {W X Z : Type*} [MeasurableSpace W] [MeasurableSpace X] [MeasurableSpace Z]
variable (prior : Measure W) (μ : Measure X) (κ : Measure Z)
variable [IsProbabilityMeasure prior] [IsProbabilityMeasure μ] [IsProbabilityMeasure κ]

omit [MeasurableSpace X] [MeasurableSpace Z] [IsProbabilityMeasure prior] in
/-- The mark-score tensor is constant in the mixing parameter. -/
theorem labeledMixture_mark_factor (v : W → ℝ) (e : Fin 3 → W → X → ℝ)
    (s : Fin 3 → Z → ℝ) (k : ℕ) (labels : Fin k → Fin 3) (ys : Fin k → X × Z) :
    labeledMixture prior v (fun l w y => e l w y.1 * s l y.2) k labels ys =
      labeledMixture prior v e k labels (fun i => (ys i).1) * ∏ i, s (labels i) (ys i).2 := by
  unfold labeledMixture
  have he : (fun w => v w * labeledTensor (fun l w y => e l w y.1 * s l y.2) k labels w ys) =
      fun w => (v w * labeledTensor e k labels w (fun i => (ys i).1)) *
        ∏ i, s (labels i) (ys i).2 := by
    funext w
    simp [labeledTensor, Finset.prod_mul_distrib, mul_assoc]
  rw [he, integral_mul_const]

omit [IsProbabilityMeasure prior] in
/-- The labeling norm separates exactly into its spatial norm and mark second
moments. In particular, continuous marks and finite marks use the same theorem. -/
theorem labeledNormSquared_mark_factor (v : W → ℝ) (e : Fin 3 → W → X → ℝ)
    (s : Fin 3 → Z → ℝ) (k : ℕ) (labels : Fin k → Fin 3) :
    labeledNormSquared prior (μ.prod κ) v (fun l w y => e l w y.1 * s l y.2) k labels =
      labeledNormSquared prior μ v e k labels *
        ∏ i, (∫ z, s (labels i) z ^ 2 ∂κ) := by
  let E := MeasurableEquiv.arrowProdEquivProdArrow X Z (Fin k)
  have hp := measurePreserving_arrowProdEquivProdArrow X Z (Fin k)
    (fun _ => μ) (fun _ => κ)
  let F := fun q : (Fin k → X) × (Fin k → Z) =>
    labeledMixture prior v e k labels q.1 ^ 2 * (∏ i, s (labels i) (q.2 i)) ^ 2
  unfold labeledNormSquared
  simp_rw [labeledMixture_mark_factor, mul_pow]
  have he : (∫ ys : Fin k → X × Z,
      labeledMixture prior v e k labels (fun i => (ys i).1) ^ 2 *
        (∏ i, s (labels i) (ys i).2) ^ 2 ∂Measure.pi (fun _ => μ.prod κ)) =
      ∫ q, F q ∂(Measure.pi (fun _ : Fin k => μ)).prod (Measure.pi (fun _ : Fin k => κ)) := by
    simpa [F, E, MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow] using
      hp.integral_comp' F
  rw [he, integral_prod_mul
    (fun xs : Fin k → X => labeledMixture prior v e k labels xs ^ 2)
    (fun zs : Fin k → Z => (∏ i, s (labels i) (zs i)) ^ 2)]
  congr 1
  have hpow : (fun zs : Fin k → Z => (∏ i, s (labels i) (zs i)) ^ 2) =
      fun zs => ∏ i, s (labels i) (zs i) ^ 2 := by
    funext zs
    exact (Finset.prod_pow Finset.univ 2 (fun i : Fin k => s (labels i) (zs i))).symm
  rw [hpow,
    integral_fin_nat_prod_eq_prod (μ := fun _ : Fin k => κ) (fun i z => s (labels i) z ^ 2)]

omit [IsProbabilityMeasure prior] in
/-- Uniform bounded mark scores cost at most `S^(2k)` in a labeling norm. -/
theorem labeledNormSquared_mark_le (v : W → ℝ) (e : Fin 3 → W → X → ℝ)
    (s : Fin 3 → Z → ℝ) (S : ℝ) (_hS : 0 ≤ S)
    (hs : ∀ l z, |s l z| ≤ S) (k : ℕ) (labels : Fin k → Fin 3) :
    labeledNormSquared prior (μ.prod κ) v (fun l w y => e l w y.1 * s l y.2) k labels ≤
      S ^ (2 * k) * labeledNormSquared prior μ v e k labels := by
  rw [labeledNormSquared_mark_factor prior μ κ]
  have hb (i : Fin k) : (∫ z, s (labels i) z ^ 2 ∂κ) ≤ S ^ 2 := by
    have h := norm_integral_le_of_norm_le_const (μ := κ)
      (f := fun z => s (labels i) z ^ 2) (C := S ^ 2)
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_pow]
        nlinarith [hs (labels i) z, abs_nonneg (s (labels i) z)])
    have hz : 0 ≤ ∫ z, s (labels i) z ^ 2 ∂κ := integral_nonneg fun _ => sq_nonneg _
    simpa [Real.norm_eq_abs, abs_of_nonneg hz] using h
  have hprod : (∏ i, ∫ z, s (labels i) z ^ 2 ∂κ) ≤ S ^ (2 * k) := by
    have h := Finset.prod_le_prod₀ (s := Finset.univ)
      (f := fun i : Fin k => ∫ z, s (labels i) z ^ 2 ∂κ) (g := fun _ => S ^ 2)
      (fun _ _ => integral_nonneg fun _ => sq_nonneg _) (fun i _ => hb i)
    simpa [← pow_mul] using h
  have hnorm : 0 ≤ labeledNormSquared prior μ v e k labels := integral_nonneg fun _ => sq_nonneg _
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hprod hnorm

/-- Equation (5.9), with arbitrary continuous spatial and prior measures and
arbitrary bounded marks. All label tensors and score costs are derived. -/
theorem marked_tensorNormSquared_labelings_le (v : W → ℝ)
    (e : Fin 3 → W → X → ℝ) (s : Fin 3 → Z → ℝ)
    (hv : Measurable v) (he : ∀ l, Measurable (Function.uncurry (e l)))
    (hs : ∀ l, Measurable (s l)) (V C S : ℝ) (hV : 0 ≤ V) (hC : 0 ≤ C) (hS : 0 ≤ S)
    (hbv : ∀ w, |v w| ≤ V) (hbe : ∀ l w x, |e l w x| ≤ C)
    (hbs : ∀ l z, |s l z| ≤ S) (k : ℕ) :
    tensorNormSquared prior (μ.prod κ) v (fun w y => ∑ l : Fin 3, e l w y.1 * s l y.2) k ≤
      (3 * S ^ 2) ^ k * ∑ labels : Fin k → Fin 3, labeledNormSquared prior μ v e k labels := by
  let obs := fun l w (y : X × Z) => e l w y.1 * s l y.2
  have hm (l : Fin 3) : Measurable (Function.uncurry (obs l)) :=
    ((he l).comp (measurable_fst.prodMk measurable_snd.fst)).mul
      ((hs l).comp measurable_snd.snd)
  have hb (l : Fin 3) (w : W) (y : X × Z) : |obs l w y| ≤ C * S := by
    dsimp [obs]
    rw [abs_mul]
    exact mul_le_mul (hbe l w y.1) (hbs l y.2) (abs_nonneg _) hC
  have hcs := tensorNormSquared_labelings_le prior (μ.prod κ) v obs hv hm V (C * S)
    hV (by positivity) hbv hb k
  have hsum : (∑ labels : Fin k → Fin 3, labeledNormSquared prior (μ.prod κ) v obs k labels) ≤
      S ^ (2 * k) * ∑ labels : Fin k → Fin 3, labeledNormSquared prior μ v e k labels := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro labels _
    exact labeledNormSquared_mark_le prior μ κ v e s S hS hbs k labels
  have h := hcs.trans (mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ (3 : ℝ) ^ k))
  have hp : (3 : ℝ) ^ k * S ^ (2 * k) = (3 * S ^ 2) ^ k := by
    rw [mul_pow, pow_mul]
  calc
    _ ≤ (3 : ℝ) ^ k * (S ^ (2 * k) * ∑ labels : Fin k → Fin 3,
        labeledNormSquared prior μ v e k labels) := h
    _ = _ := by rw [← mul_assoc, hp]

end RoughRegime.PoissonMeasure
