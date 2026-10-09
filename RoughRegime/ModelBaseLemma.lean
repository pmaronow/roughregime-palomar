module

public import RoughRegime.BaseDesign
public import RoughRegime.UniformBaseApproximation


@[expose] public section
/-! The literal source Lemma 6 base term, with a common class-only constant. -/
noncomputable section
open MeasureTheory MvPolynomial
namespace RoughRegime.Model
universe u
open RoughRegime.HilbertGram RoughRegime.Upper RoughRegime.ProjectionIncrementComplex
open RoughRegime.KernelExpressions RoughRegime.ComplexDerivativeBridge

 def baseIncrementPolynomial (A : Parameters) (m : ℕ) :
    MvPolynomial (Fin (designMomentDimension (baseDimension A.d (holderOrder A.β)))) ℝ :=
  packedInversePolynomial (baseDimension A.d (holderOrder A.β)) A.gminus A.gplus m

 theorem baseIncrementPolynomial_degree (A : Parameters) (m : ℕ) :
    (baseIncrementPolynomial A m).totalDegree ≤ m + 2 :=
  packedInversePolynomial_degree _ _ _ m

/-- The base observable and its `m+2` polynomial depend only on the class. Their
true approximation error, complex bound, gradient and observable bound use one
constant, quantified before every response space, probability law and model. -/
theorem uniform_model_base_lemma (A : Parameters) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (Z : Type u) [MeasurableSpace Z] (F : Observables Z A)
      (P : ProbabilityMeasure (Observation A Z)) (W : ModelWitness A F P),
      let x := baseDesignMean A F P (holderOrder A.β)
      Measurable (baseDesignStatistic A F (holderOrder A.β)) ∧
      (fun i => (∫ o, baseDesignStatistic A F (holderOrder A.β) o ∂(P : Measure (Observation A Z))) i) = x ∧
      (∀ o, ‖baseDesignStatistic A F (holderOrder A.β) o‖ ≤
        C * (cube A.d).indicator (fun _ => (1 : ℝ)) o.1) ∧
      (P : Measure (Observation A Z)).real (Prod.fst ⁻¹' cube A.d) ≤ C ∧
      ∀ m,
        let q := baseIncrementPolynomial A m
        q.totalDegree ≤ m + 2 ∧
        ‖W.levelProjectionTarget (holderOrder A.β) 0 - MvPolynomial.eval x q‖ ≤
          C * intervalRho A.gminus A.gplus ^ m ∧
        (∀ t, ‖t - realParametersCLM (designMomentDimension (baseDimension A.d (holderOrder A.β))) x‖ < 1 / C →
          ‖MvPolynomial.eval t (complexify q)‖ ≤ C) ∧
        ‖polynomialGradient q x‖ ≤ C := by
  let n := baseDimension A.d (holderOrder A.β)
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (baseDimension_pos A.d (holderOrder A.β))
  obtain ⟨Cp, hCp, hdegree, hcomplex, htrue⟩ := uniform_packed_base_approximation.{0}
    n A.gminus A.gplus (A.H * A.gplus) (Real.sqrt A.gplus * A.H) A.hgminus A.hgplus
    (mul_nonneg (Real.sqrt_nonneg _) A.hH.le)
  let C := max Cp (baseDesignConstant A (holderOrder A.β))
  have hpC : Cp ≤ C := le_max_left _ _
  have hoC : baseDesignConstant A (holderOrder A.β) ≤ C := le_max_right _ _
  have hC : 1 ≤ C := hCp.trans hpC
  have hrad : 1 / C ≤ 1 / Cp := one_div_le_one_div_of_le (zero_lt_one.trans_le hCp) hpC
  refine ⟨C, hC, ?_⟩
  intro Z _ F P W
  dsimp only
  refine ⟨baseDesignStatistic_measurable A F _, rfl, ?_, ?_, ?_⟩
  · intro o
    exact (baseDesignStatistic_norm_bound A F _ o).trans
      (mul_le_mul_of_nonneg_right hoC (Set.indicator_nonneg (fun _ _ => zero_le_one) _))
  · exact (measureReal_le_one (μ := (P : Measure (Observation A Z))) (s := Prod.fst ⁻¹' cube A.d)).trans hC
  · intro m
    have hx := baseDesignMean_mem A F P W (holderOrder A.β)
    obtain ⟨herr, hgrad⟩ := htrue (Lp ℝ 2 (W.cellDesignMeasure (dyadicBaseCell A.d)))
      _ hx (W.weightedParentBasis (holderOrder A.β) (dyadicBaseCell A.d))
      (W.weightedParentBasis_linearIndependent _ _) (baseDesignMean_gram A F P W _)
      (W.cellALp (dyadicBaseCell A.d)) (W.cellBLp (dyadicBaseCell A.d))
      (baseDesignMean_first A F P W _) (baseDesignMean_second A F P W _)
      W.base_response_norms.1 W.base_response_norms.2 m
    change ‖W.cellProjectionTarget (holderOrder A.β) (dyadicBaseCell A.d) -
      MvPolynomial.eval _ (baseIncrementPolynomial A m)‖ ≤ _ at herr
    rw [← W.base_level_projection] at herr
    refine ⟨baseIncrementPolynomial_degree A m, ?_, ?_, ?_⟩
    · exact herr.trans (mul_le_mul_of_nonneg_right hpC
        (pow_nonneg (intervalRho_pos A.gminus A.gplus A.hgminus A.hgplus).le m))
    · intro t ht
      exact (hcomplex t ⟨_, hx, ht.trans_le hrad⟩ m).trans hpC
    · exact hgrad.trans hpC

end RoughRegime.Model
