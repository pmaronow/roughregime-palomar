module

public import RoughRegime.PoissonUniformComparison


@[expose] public section
/-! Actual products of independent pair experiments and the maximum Gamma
norm appearing in the full Poisson comparison. -/
noncomputable section
open MeasureTheory
open scoped BigOperators NNReal
namespace RoughRegime.PoissonMeasure
set_option backward.isDefEq.respectTransparency false

 def finiteMaximum {p : ℕ} [NeZero p] (g : Fin p → ℝ) : ℝ :=
   Finset.univ.sup' Finset.univ_nonempty g

 theorem le_finiteMaximum {p : ℕ} [NeZero p] (g : Fin p → ℝ) (i : Fin p) : g i ≤ finiteMaximum g :=
   Finset.le_sup' g (Finset.mem_univ i)

 theorem finiteMaximum_nonneg {p : ℕ} [NeZero p] (g : Fin p → ℝ) (hg : ∀ i, 0 ≤ g i) :
    0 ≤ finiteMaximum g := by
  obtain ⟨i⟩ := (inferInstance : Nonempty (Fin p))
  exact (hg i).trans (le_finiteMaximum g i)

 theorem finiteMaximum_le_sum {p : ℕ} [NeZero p] (g : Fin p → ℝ) (hg : ∀ i, 0 ≤ g i) :
    finiteMaximum g ≤ ∑ i, g i := by
  apply Finset.sup'_le
  intro i _
  exact Finset.single_le_sum (fun j _ => hg j) (Finset.mem_univ i)

 theorem finiteMaximum_series_summable {p : ℕ} [NeZero p] (g : Fin p → ℕ → ℝ)
    (hg : ∀ i j, 0 ≤ g i j) (z : ℝ) (hz : 0 ≤ z)
    (hs : ∀ i, Summable (fun j => z ^ j / j.factorial * g i j)) :
    Summable (fun j => z ^ j / j.factorial * finiteMaximum (fun i => g i j)) := by
  have hupper (j : ℕ) : z ^ j / j.factorial * finiteMaximum (fun i => g i j) ≤
      ∑ i, z ^ j / j.factorial * g i j := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (finiteMaximum_le_sum _ (fun i => hg i j)) (by positivity)
  have hfinite (t : Finset (Fin p)) : Summable (fun j => ∑ i ∈ t, z ^ j / j.factorial * g i j) := by
    induction t using Finset.induction_on with
    | empty => simp
    | @insert i t hi ih =>
      simpa only [Finset.sum_insert hi] using (hs i).add ih
  have hsum : Summable (fun j => ∑ i, z ^ j / j.factorial * g i j) := by
    simpa using hfinite Finset.univ
  exact Summable.of_nonneg_of_le (fun j =>
    mul_nonneg (by positivity) (finiteMaximum_nonneg _ (fun i => hg i j))) hupper hsum

variable {H X Z : Type*} [MeasurableSpace H] [MeasurableSpace X] [MeasurableSpace Z]
variable {p : ℕ} [NeZero p] (ν : Fin p → Measure H) (μ : Measure X) (κ : Measure Z)
variable [∀ i, IsProbabilityMeasure (ν i)] [IsProbabilityMeasure μ] [IsProbabilityMeasure κ]

 def AffinePhaseField.pairGammaMaximum (F : Fin p → AffinePhaseField H X)
    (Au Av : ℝ) (M j : ℕ) : ℝ := finiteMaximum fun i => (F i).gammaNorm (ν i) μ Au Av M j

 theorem AffinePhaseField.pair_product_hellinger_uniform (F : Fin p → AffinePhaseField H X)
    (hm : ∀ i, (F i).IsMeasurable) (Au Av C S : ℝ) (hAu : 0 ≤ Au) (hAu1 : Au ≤ 1)
    (hAv : 0 ≤ Av) (hAv1 : Av ≤ 1) (hC : 0 ≤ C) (hS : 0 ≤ S) (hb : ∀ i, (F i).Bounded C)
    (s : Fin 3 → Z → ℝ) (hs : ∀ l, Measurable (s l)) (hbs : ∀ l z, |s l z| ≤ S)
    (hzero : ∀ i q, (∫ y, (F i).markedFactor Au Av s q y ∂μ.prod κ) = 0)
    (c : ℝ) (hc : 0 < c) (hlow : ∀ i q y, c ≤ 1 + (F i).markedFactor Au Av s q y)
    (M : ℕ) (rate : ℝ≥0) (R : ℝ) (hRate : (rate : ℝ) ≤ R) :
    let K := comparisonConstant C S c R
    let L := fun i => (F i).poissonLaw (ν i) μ κ (hm i) Au Av C S hAu hAu1 hAv hAv1 hC hS (hb i)
      s hs hbs (hzero i) c hc (hlow i) M rate true
    let Rlaw := fun i => (F i).poissonLaw (ν i) μ κ (hm i) Au Av C S hAu hAu1 hAv hAv1 hC hS (hb i)
      s hs hbs (hzero i) c hc (hlow i) M rate false
    GeneralTesting.hellingerSquared (LowerMeasure.productDensityLaw L) (LowerMeasure.productDensityLaw Rlaw) ≤
      K * p * (rate : ℝ) ^ 2 * (∑' j, if M ≤ j then
        (K * (rate : ℝ)) ^ j / j.factorial * AffinePhaseField.pairGammaMaximum ν μ F Au Av M j else 0) +
      K * p * (rate : ℝ) ^ 4 * Au ^ 2 * Av ^ 2 * (Au ^ 2 + Av ^ 2) ^ 2 *
        ((K * (rate : ℝ)) ^ M / M.factorial) := by
  let K := comparisonConstant C S c R
  have hK : 0 ≤ K := le_trans zero_le_one (comparisonConstant_bounds C S c R hc).1
  let L := fun i => (F i).poissonLaw (ν i) μ κ (hm i) Au Av C S hAu hAu1 hAv hAv1 hC hS (hb i)
    s hs hbs (hzero i) c hc (hlow i) M rate true
  let Rlaw := fun i => (F i).poissonLaw (ν i) μ κ (hm i) Au Av C S hAu hAu1 hAv hAv1 hC hS (hb i)
    s hs hbs (hzero i) c hc (hlow i) M rate false
  let T := ∑' j : ℕ, if M ≤ j then (K * (rate : ℝ)) ^ j / j.factorial *
    AffinePhaseField.pairGammaMaximum ν μ F Au Av M j else 0
  let D := K * (rate : ℝ) ^ 4 * Au ^ 2 * Av ^ 2 * (Au ^ 2 + Av ^ 2) ^ 2 *
    ((K * (rate : ℝ)) ^ M / M.factorial)
  have hseries := PoissonSeriesBounds.summable_cutoff _
    (finiteMaximum_series_summable (fun i j => (F i).gammaNorm (ν i) μ Au Av M j)
      (fun i => (F i).gammaNorm_nonneg (ν i) μ Au Av M) (K * rate) (by positivity)
      (fun i => (F i).gammaSeries_summable (ν i) μ Au Av C hAu hAv hC (hb i) M (K * rate) (by positivity))) M
  have hHi (i : Fin p) : GeneralTesting.hellingerSquared (L i) (Rlaw i) ≤ K * (rate : ℝ) ^ 2 * T + D := by
    have hi := (F i).poisson_hellinger_uniform (ν i) μ κ (hm i) Au Av C S hAu hAu1 hAv hAv1 hC hS
      (hb i) s hs hbs (hzero i) c hc (hlow i) M rate R hRate
    have hseriesi := PoissonSeriesBounds.summable_cutoff _
      ((F i).gammaSeries_summable (ν i) μ Au Av C hAu hAv hC (hb i) M (K * rate) (by positivity)) M
    have hT : (∑' j : ℕ, if M ≤ j then (K * (rate : ℝ)) ^ j / j.factorial *
        (F i).gammaNorm (ν i) μ Au Av M j else 0) ≤ T := hseriesi.tsum_le_tsum (fun j => by
      split_ifs
      · exact mul_le_mul_of_nonneg_left
          (le_finiteMaximum (fun i => (F i).gammaNorm (ν i) μ Au Av M j) i) (by positivity)
      · exact le_rfl) hseries
    have hhead : K * (rate : ℝ) ^ 2 * (∑' j : ℕ, if M ≤ j then
        (K * (rate : ℝ)) ^ j / j.factorial * (F i).gammaNorm (ν i) μ Au Av M j else 0) ≤
        K * (rate : ℝ) ^ 2 * T :=
      mul_le_mul_of_nonneg_left hT (by positivity)
    exact hi.trans (add_le_add hhead (le_refl D))
  have hh := (LowerMeasure.hellinger_product_le L Rlaw).trans (Finset.sum_le_sum (fun i _ => hHi i))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
  convert hh using 1
  dsimp [T, D, K]
  ring

end RoughRegime.PoissonMeasure
