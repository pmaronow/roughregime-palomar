module

public import RoughRegime.ModelIncrementSize
public import RoughRegime.DesignFiniteStatistics


@[expose] public section
/-! The complete literal cell part of source Lemma 6: known finite observable,
true mean, projection increment, and a common class constant for every bound. -/
noncomputable section
open MeasureTheory MvPolynomial
namespace RoughRegime.Model
universe u
open RoughRegime.ProjectionFrame RoughRegime.ComplexDerivativeBridge RoughRegime.KernelExpressions
open RoughRegime.Upper RoughRegime.ProjectionIncrementComplex

 def localDesignStatistic (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) {j : ℕ} (c : DyadicCell A.d j) :
    Observation A Z → EuclideanSpace ℝ (Fin (localMomentDimension A)) :=
  fun o => designFinReindex (localChildDimension A) (dyadicDesignStatistic A F (holderOrder A.β) c o)

 theorem localDesignStatistic_measurable (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) {j : ℕ} (c : DyadicCell A.d j) : Measurable (localDesignStatistic A F c) :=
  (designFinReindex (localChildDimension A)).continuous.measurable.comp
    (dyadicDesignStatistic_measurable A F (holderOrder A.β) c)

 theorem localDesignStatistic_mean (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (P : ProbabilityMeasure (Observation A Z)) {j : ℕ} (c : DyadicCell A.d j) :
    (fun i => (∫ o, localDesignStatistic A F c o ∂(P : Measure (Observation A Z))) i) =
      dyadicDesignMean A F P (holderOrder A.β) c := by
  have he : (∫ o, localDesignStatistic A F c o ∂(P : Measure (Observation A Z))) =
      designFinReindex (localChildDimension A)
        (∫ o, dyadicDesignStatistic A F (holderOrder A.β) c o ∂(P : Measure (Observation A Z))) := by
    exact (designFinReindex (localChildDimension A)).toLinearIsometry.integral_comp_comm _
  rw [he]
  rfl

 theorem localDesignStatistic_norm_bound (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) {j : ℕ} (c : DyadicCell A.d j) (o : Observation A Z) :
    ‖localDesignStatistic A F c o‖ ≤ dyadicDesignConstant A (holderOrder A.β) * (2 : ℝ) ^ j *
      (dyadicPartitionCell c).indicator (fun _ => (1 : ℝ)) o.1 := by
  change ‖designFinReindex _ _‖ ≤ _
  rw [(designFinReindex _).norm_map]
  exact dyadicDesignStatistic_norm_bound A F _ c o

/-- Every cell conclusion of source Lemma 6 uses one constant independent of the
response type, model, level, cell and truncation order. The known observable and
polynomial are explicit; the mean, size and spectral facts come from the model. -/
theorem uniform_model_local_lemma (A : Parameters) (hαβ : A.α ≤ A.β) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (Z : Type u) [MeasurableSpace Z] (F : Observables Z A)
      (P : ProbabilityMeasure (Observation A Z)) (W : ModelWitness A F P)
      (j : ℕ) (c : DyadicCell A.d j),
      let x := dyadicDesignMean A F P (holderOrder A.β) c
      let r := dyadicSplitAxis A.d j (lt_of_lt_of_le Nat.zero_lt_one A.hd)
      let h := (2 : ℝ) ^ (-(j : ℝ) / A.d)
      Measurable (localDesignStatistic A F c) ∧
      (fun i => (∫ o, localDesignStatistic A F c o ∂(P : Measure (Observation A Z))) i) = x ∧
      W.localProjectionIncrement c = localIncrementFunction A r x ∧
      (∀ o, ‖localDesignStatistic A F c o‖ ≤ C * (2 : ℝ) ^ j *
        (dyadicPartitionCell c).indicator (fun _ => (1 : ℝ)) o.1) ∧
      (P : Measure (Observation A Z)).real (Prod.fst ⁻¹' dyadicPartitionCell c) ≤ C / (2 : ℝ) ^ j ∧
      ‖W.localProjectionIncrement c‖ ≤ C * h ^ (A.α + A.β) ∧
      ∀ m : ℕ,
        let q := localIncrementPolynomial A hαβ r m
        q.totalDegree ≤ m + A.nu + 2 ∧
        ‖W.localProjectionIncrement c - MvPolynomial.eval x q‖ ≤
          C * h ^ (A.α + A.β) * ((m + 1 : ℕ) : ℝ) ^ A.nu * intervalRho A.gminus A.gplus ^ m ∧
        (∀ t : Fin (localMomentDimension A) → ℂ,
          ‖t - realParametersCLM (localMomentDimension A) x‖ < 1 / C →
          ‖MvPolynomial.eval t (complexify q)‖ ≤ C) ∧
        ‖polynomialGradient q x‖ ≤ C * h ^ min (min A.α A.β) 1 := by
  obtain ⟨Cp, hCp, hp⟩ := uniform_model_local_polynomials.{u} A hαβ
  obtain ⟨Cs, hCs, hs⟩ := uniform_model_increment_size.{u} A hαβ
  let Co := dyadicDesignConstant A (holderOrder A.β)
  let C := max Cp (max Cs Co)
  have hpC : Cp ≤ C := le_max_left _ _
  have hsC : Cs ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hoC : Co ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  have hC : 1 ≤ C := hCp.trans hpC
  have hrad : 1 / C ≤ 1 / Cp := one_div_le_one_div_of_le (zero_lt_one.trans_le hCp) hpC
  refine ⟨C, hC, ?_⟩
  intro Z _ F P W j c
  dsimp only
  refine ⟨localDesignStatistic_measurable A F c, localDesignStatistic_mean A F P c,
    W.localProjectionIncrement_eq c, ?_, ?_, ?_, ?_⟩
  · intro o
    apply (localDesignStatistic_norm_bound A F c o).trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hoC (by positivity))
      (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
  · exact (dyadicDesign_cell_probability A F P W (holderOrder A.β) c).trans
      (div_le_div_of_nonneg_right hoC (by positivity))
  · exact (hs Z F P W j c).trans (mul_le_mul_of_nonneg_right hsC (by positivity))
  · intro m
    obtain ⟨hdeg, herr, hcomplex, hgrad⟩ := hp Z F P W j c m
    refine ⟨hdeg, ?_, ?_, ?_⟩
    · apply herr.trans
      have hρ := (RoughRegime.Upper.intervalRho_pos A.gminus A.gplus A.hgminus A.hgplus).le
      gcongr
    · intro t ht
      exact (hcomplex t (ht.trans_le hrad)).trans hpC
    · exact hgrad.trans (mul_le_mul_of_nonneg_right hpC (by positivity))

end RoughRegime.Model
