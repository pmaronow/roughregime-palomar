module

public import RoughRegime.UpperTuning


@[expose] public section
/-! Explicit measurable distinct-sample polynomial estimators in the actual
iid product experiment, with their independence and mean laws derived. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace RoughRegime.IIDPolynomialEstimator
open RoughRegime.Upper RoughRegime.UpperTuning
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Evaluate the known finite statistic at the i-th observed sample. -/
def sampleStatistics {n p : ℕ} (z : Ω → Fin p → ℝ)
    (i : Fin n) (xs : Fin n → Ω) : Fin p → ℝ := z (xs i)

theorem sampleStatistics_measurable {n p : ℕ} (z : Ω → Fin p → ℝ)
    (hz : Measurable z) (i : Fin n) : Measurable (sampleStatistics z i) :=
  hz.comp (measurable_pi_apply i)

theorem sampleStatistics_independent (P : Measure Ω) [IsProbabilityMeasure P]
    {n p : ℕ} (z : Ω → Fin p → ℝ) (hz : Measurable z) :
    iIndepFun (sampleStatistics (n := n) z) (Measure.pi (fun _ : Fin n => P)) :=
  iIndepFun_pi (fun _ => hz.aemeasurable)

theorem sampleStatistics_identDistrib (P : Measure Ω) [IsProbabilityMeasure P]
    {n p : ℕ} (z : Ω → Fin p → ℝ) (hz : Measurable z) (i j : Fin n) :
    IdentDistrib (sampleStatistics z i) (sampleStatistics z j)
      (Measure.pi (fun _ : Fin n => P)) (Measure.pi (fun _ : Fin n => P)) := by
  refine ⟨(sampleStatistics_measurable z hz i).aemeasurable,
    (sampleStatistics_measurable z hz j).aemeasurable,?_⟩
  unfold sampleStatistics
  have hi := (measurePreserving_eval (fun _ : Fin n => P) i).map_eq
  have hj := (measurePreserving_eval (fun _ : Fin n => P) j).map_eq
  calc
    _ = Measure.map z (Measure.map (fun xs : Fin n → Ω => xs i) (Measure.pi (fun _ : Fin n => P))) :=
      (Measure.map_map hz (measurable_pi_apply i)).symm
    _ = P.map z := congrArg (Measure.map z) hi
    _ = Measure.map z (Measure.map (fun xs : Fin n → Ω => xs j) (Measure.pi (fun _ : Fin n => P))) :=
      congrArg (Measure.map z) hj.symm
    _ = _ := Measure.map_map hz (measurable_pi_apply j)

theorem sampleStatistics_integral (P : Measure Ω) [IsProbabilityMeasure P]
    {n p : ℕ} (z : Ω → Fin p → ℝ) (hz : Measurable z) (i : Fin n) (k : Fin p) :
    (∫ xs, sampleStatistics z i xs k ∂Measure.pi (fun _ : Fin n => P)) = ∫ ω, z ω k ∂P :=
  by
    have hi := (measurePreserving_eval (fun _ : Fin n => P) i).map_eq
    symm
    calc
      _ = ∫ ω, z ω k ∂Measure.map (fun xs : Fin n → Ω => xs i) (Measure.pi (fun _ : Fin n => P)) :=
        congrArg (fun μ : Measure Ω => ∫ ω, z ω k ∂μ) hi.symm
      _ = _ := integral_map (measurable_pi_apply i).aemeasurable
        (((measurable_pi_apply k).comp hz).aestronglyMeasurable)

/-- The genuine polynomial estimator on the observed sample, with no
unknown population center in its definition. -/
def sampleLift {n p : ℕ} (F : MvPolynomial (Fin p) ℝ) (z : Ω → Fin p → ℝ)
    (xs : Fin n → Ω) : ℝ := polynomialLift F (sampleStatistics z) xs

theorem monomialLift_measurable {A : Type*} [MeasurableSpace A] {n p q : ℕ}
    (σ : Fin q → Fin p) (X : Fin n → A → Fin p → ℝ) (hX : ∀ i, Measurable (X i)) :
    Measurable (monomialLift σ X) := by
  classical
  unfold monomialLift
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro e _
  apply Finset.measurable_prod
  intro i _
  exact (measurable_pi_apply (σ i)).comp (hX (e i))

theorem polynomialLift_measurable {A : Type*} [MeasurableSpace A] {n p : ℕ}
    (F : MvPolynomial (Fin p) ℝ) (X : Fin n → A → Fin p → ℝ) (hX : ∀ i, Measurable (X i)) :
    Measurable (polynomialLift F X) := by
  classical
  unfold polynomialLift
  apply Finset.measurable_sum
  intro α _
  exact (monomialLift_measurable (exponentCoordinates α) X hX).const_mul _

theorem sampleLift_measurable {n p : ℕ} (F : MvPolynomial (Fin p) ℝ)
    (z : Ω → Fin p → ℝ) (hz : Measurable z) : Measurable (sampleLift (n := n) F z) :=
  polynomialLift_measurable F _ (sampleStatistics_measurable z hz)

/-- Exact expectation of the actual iid sample lift. -/
theorem sampleLift_mean (P : Measure Ω) [IsProbabilityMeasure P] {n p : ℕ}
    (F : MvPolynomial (Fin p) ℝ) (z : Ω → Fin p → ℝ) (hz : Measurable z)
    (hdeg : F.totalDegree ≤ n) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ ω k, |z ω k| ≤ M) :
    (∫ xs, sampleLift F z xs ∂Measure.pi (fun _ : Fin n => P)) =
      MvPolynomial.eval (fun k => ∫ ω, z ω k ∂P) F := by
  apply polynomialLift_unbiased _ F _ hdeg (sampleStatistics_independent P z hz)
    (sampleStatistics_measurable z hz) M hM (fun _ ω k => hb (ω _) k)
  exact sampleStatistics_integral P z hz

theorem sampleLift_memLp (P : Measure Ω) [IsProbabilityMeasure P] {n p : ℕ}
    (F : MvPolynomial (Fin p) ℝ) (z : Ω → Fin p → ℝ) (hz : Measurable z)
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ ω k, |z ω k| ≤ M) :
    MemLp (sampleLift (n := n) F z) 2 (Measure.pi (fun _ : Fin n => P)) :=
  polynomialLift_memLp _ F _ (sampleStatistics_measurable z hz) M hM
    (fun i xs k => hb (xs i) k)

/-- Full Lemma 8 on the actual iid sample of a known cell statistic.
Independence, equal laws and coordinate expectations are proved from the
product experiment rather than assumed. -/
theorem sampleLift_variance_cells (P : Measure Ω) [IsProbabilityMeasure P]
    {n K p R : ℕ} (hK : 0 < K) (hR : 0 < R) (h2R : 2 * R ≤ n)
    (F : Fin K → MvPolynomial (Fin p) ℝ) (hdeg : ∀ c, (F c).totalDegree ≤ R)
    (z : Ω → Fin (K * p) → ℝ) (hz : Measurable z)
    (cell : Ω → Fin K) (hc : Measurable cell)
    (C0 h s0 : ℝ) (hC0 : 1 ≤ C0) (hh : 0 < h) (hh1 : h ≤ 1) (hs0 : 0 < s0)
    (hcomplex : ∀ c y, ‖y - (fun j =>
      (RoughRegime.PolynomialCells.cellProjection c (fun k => ∫ ω, z ω k ∂P) j : ℂ))‖ < 1 / C0 →
      ‖MvPolynomial.eval y (RoughRegime.ComplexDerivativeBridge.complexify (F c))‖ ≤ C0)
    (hgrad : ∀ c, ‖(WithLp.toLp 2 (fun j => fderiv ℝ (fun y => MvPolynomial.eval y (F c))
      (RoughRegime.PolynomialCells.cellProjection c (fun k => ∫ ω, z ω k ∂P)) (Pi.single j 1)) :
        EuclideanSpace ℝ (Fin p))‖ ≤ C0 * h ^ s0)
    (hZ : ∀ ω c, ‖(WithLp.toLp 2 (RoughRegime.PolynomialCells.cellProjection c (z ω)) :
      EuclideanSpace ℝ (Fin p))‖ ≤ C0 * K * RoughRegime.LiftVariance.cellIndicator cell c ω)
    (hprob : ∀ c, P.real {ω | cell ω = c} ≤ C0 / K) :
    variance (sampleLift (RoughRegime.PolynomialCells.cellMomentPolynomial F) z)
      (Measure.pi (fun _ : Fin n => P)) ≤
        RoughRegime.LiftVariance.varianceConstant C0 * h ^ (2 * s0) / n +
          (1 / (n : ℝ)) * ∑ j ∈ Finset.range (R - 1),
            RoughRegime.LiftVariance.varianceConstant C0 ^ (j + 2) * ((j + 2).factorial : ℝ) *
              (K / (n : ℝ)) ^ (j + 1) := by
  have hcell : iIndepFun (fun i : Fin n => fun xs : Fin n → Ω => cell (xs i))
      (Measure.pi (fun _ : Fin n => P)) := iIndepFun_pi (fun _ => hc.aemeasurable)
  have hmcell (i : Fin n) : Measurable (fun xs : Fin n → Ω => cell (xs i)) :=
    hc.comp (measurable_pi_apply i)
  have hprob' (i : Fin n) (c : Fin K) :
      (Measure.pi (fun _ : Fin n => P)).real {xs | cell (xs i) = c} ≤ C0 / K := by
    have hs : MeasurableSet {ω | cell ω = c} := hc (measurableSet_singleton c)
    have hp := (measurePreserving_eval (fun _ : Fin n => P) i).measure_preimage hs.nullMeasurableSet
    have hp' : Measure.pi (fun _ : Fin n => P) {xs | cell (xs i) = c} = P {ω | cell ω = c} := hp
    change (Measure.pi (fun _ : Fin n => P) {xs | cell (xs i) = c}).toReal ≤ _
    rw [hp']
    exact hprob c
  exact (RoughRegime.LiftVariance.variance_polynomial_cell_lift_paper
    (Measure.pi (fun _ : Fin n => P)) hK hR h2R F hdeg (sampleStatistics z)
    (sampleStatistics_independent P z hz) (sampleStatistics_measurable z hz)
    (sampleStatistics_identDistrib P z hz) (fun k => ∫ ω, z ω k ∂P)
    (sampleStatistics_integral P z hz) _ hcell hmcell C0 h s0 hC0 hh hh1 hs0
    hcomplex hgrad (fun i xs c => hZ (xs i) c) hprob').1

end RoughRegime.IIDPolynomialEstimator
