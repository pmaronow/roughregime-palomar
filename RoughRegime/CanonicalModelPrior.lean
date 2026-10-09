module

public import RoughRegime.SourceNondegenerate
public import RoughRegime.SpatialInteraction
public import RoughRegime.CanonicalPriorTargets


@[expose] public section
/-! The actual model target integrand has local C4 regularity and a nonzero
mixed coefficient, derived from the original nondegeneracy score branches.
Its Taylor and variance constants work uniformly over every canonical grid. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ContDiff BigOperators
namespace RoughRegime.LatticePriors.SourceModelFamily
open RoughRegime.SpatialAffine
set_option backward.isDefEq.respectTransparency false
variable {A0 : Model.Parameters} {D : ℕ} {Z : Type*} [MeasurableSpace Z]
    {O : Model.Observables Z (A0.withDimension D)} {π : ProbabilityMeasure Z}

 def integrand (F : SourceModelFamily A0 D O π) : ℝ×ℝ→ℝ :=
   fun uv => affineIntegrand (A0.withDimension D) O π F.scores uv.1 uv.2

 theorem baseline_positive (F : SourceModelFamily A0 D O π) :
     0 < Model.baselineW (A0.withDimension D) O π :=
   A0.hδ.trans (lt_of_le_of_lt (le_max_left _ _) F.nondegenerate.2.1)

 theorem integrand_measurable (F : SourceModelFamily A0 D O π) : Measurable F.integrand :=
   affineIntegrand_measurable (A0.withDimension D) O π F.scores

 theorem integrand_smoothAt (F : SourceModelFamily A0 D O π) : ContDiffAt ℝ ∞ F.integrand 0 :=
   (affineIntegrand_smooth (A0.withDimension D) O π F.scores).contDiffAt
     ((denominatorDomain_open (A0.withDimension D) O π F.scores).mem_nhds
       (denominatorDomain_zero (A0.withDimension D) O π F.scores F.baseline_positive.ne'))

 theorem integrand_C4 (F : SourceModelFamily A0 D O π) : ContDiffAt ℝ 4 F.integrand 0 :=
   F.integrand_smoothAt.of_le (by simp)

 theorem integrand_mixed_nonzero (F : SourceModelFamily A0 D O π) :
     OddTaylor.mixedDerivative F.integrand 0 ≠ 0 := by
   rw [OddTaylor.mixedDerivative_eq_reverse_scalar_deriv F.integrand
     (F.integrand_smoothAt.of_le (by simp))]
   rcases F.score_case with hpos | hdiag
   · exact affineIntegrand_interaction_nonzero (A0.withDimension D) O π F.scores
       F.baseline_positive.ne' hpos.1 hpos.2.1 hpos.2.2.1 hpos.2.2.2
   · exact affineIntegrand_interaction_nonzero_diagonal (A0.withDimension D) O π F.scores
       F.baseline_positive.ne' hdiag.1 hdiag.2.2.1 hdiag.2.2.2

 theorem target_eq_responseFunctional (F : SourceModelFamily A0 D O π)
     {N : ℕ} {ι : Type*} [Fintype ι] (G : CanonicalFrame D N ι)
     (hsmall : (G.Au+G.Av)/F.rminus*F.scores.C ≤ 1/4)
     (hrminus : G.rminus=F.rminus) (z : GridPair D N→PairState ι) :
     Model.target (A0.withDimension D) O
       (law F.scores (G.field z) (by simpa only [CanonicalFrame.field,hrminus] using hsmall)).probabilityMeasure =
       G.responseFunctional F.integrand z := by
   exact model_target_integral (A0.withDimension D) O π F.scores (G.field z) _ F.baseline_positive

 theorem uniform_response_prior_taylor (F : SourceModelFamily A0 D O π) :
     ∃ epsilon>0,∃ C≥0,∃ B≥0,
       (∀ u v:ℝ,|u| ≤ epsilon→|v| ≤ epsilon→|F.integrand (u,v)-F.integrand 0| ≤ B) ∧
       ∀ {d N : ℕ} {ι : Type*} [Fintype ι] (G : CanonicalFrame d N ι)
         (nu : Measure (ι→ℤ)) [IsProbabilityMeasure nu],
       G.Au/G.rminus ≤ epsilon→G.Av/G.rminus ≤ epsilon→
       |G.priorMeanDifference F.integrand nu-OddTaylor.mixedDerivative F.integrand 0*
         G.priorMeanDifference (fun x=>x.1*x.2) nu| ≤
       (G.ell*(2*N:ℕ))^(d+1)*
         (C*G.rplus*(G.Au/G.rminus)*(G.Av/G.rminus)*
           ((G.Au/G.rminus)^2+(G.Av/G.rminus)^2)) :=
   CanonicalFrame.uniform_response_prior_taylor F.integrand F.integrand_measurable F.integrand_C4

 theorem model_prior_mean_difference_eq (F : SourceModelFamily A0 D O π)
     {N : ℕ} {ι : Type*} [Fintype ι] (G : CanonicalFrame D N ι)
     (hsmall : (G.Au+G.Av)/F.rminus*F.scores.C ≤ 1/4)
     (hrminus : G.rminus=F.rminus) (nu : Measure (ι→ℤ)) :
     ((∫ z,Model.target (A0.withDimension D) O
         (law F.scores (G.field z) (by simpa only [CanonicalFrame.field,hrminus] using hsmall)).probabilityMeasure
       ∂globalBlockPrior nu G.M true)-
       (∫ z,Model.target (A0.withDimension D) O
         (law F.scores (G.field z) (by simpa only [CanonicalFrame.field,hrminus] using hsmall)).probabilityMeasure
       ∂globalBlockPrior nu G.M false))=G.priorMeanDifference F.integrand nu := by
   unfold CanonicalFrame.priorMeanDifference
   congr 1 <;> apply integral_congr_ae <;> filter_upwards with z
   · exact F.target_eq_responseFunctional G hsmall hrminus z
   · exact F.target_eq_responseFunctional G hsmall hrminus z


 def actualTarget (F : SourceModelFamily A0 D O π) {N : ℕ} {ι : Type*} [Fintype ι]
     (G : CanonicalFrame D N ι) (hsmall : (G.Au+G.Av)/G.rminus*F.scores.C ≤ 1/4)
     (z : GridPair D N→PairState ι) : ℝ :=
   Model.target (A0.withDimension D) O
     (law F.scores (G.field z) (by simpa only [CanonicalFrame.field] using hsmall)).probabilityMeasure

 theorem actualTarget_eq_responseFunctional (F : SourceModelFamily A0 D O π)
     {N : ℕ} {ι : Type*} [Fintype ι] (G : CanonicalFrame D N ι)
     (hsmall : (G.Au+G.Av)/G.rminus*F.scores.C ≤ 1/4) :
     F.actualTarget G hsmall=G.responseFunctional F.integrand := by
   funext z
   exact model_target_integral (A0.withDimension D) O π F.scores (G.field z) _ F.baseline_positive

 theorem actualTarget_prior_memLp (F : SourceModelFamily A0 D O π)
     {N : ℕ} {ι : Type*} [Fintype ι] (G : CanonicalFrame D N ι)
     (hsmall : (G.Au+G.Av)/G.rminus*F.scores.C ≤ 1/4)
     (B : ℝ)
     (hbound : ∀ u v:ℝ,|u|≤G.Au/G.rminus→|v|≤G.Av/G.rminus→
       |F.integrand (u,v)-F.integrand 0|≤B)
     (nu : Measure (ι→ℤ)) [IsProbabilityMeasure nu] (positive : Bool) :
     MemLp (F.actualTarget G hsmall) 2 (globalBlockPrior nu G.M positive) := by
   rw [F.actualTarget_eq_responseFunctional G hsmall]
   exact G.global_response_prior_memLp F.integrand F.integrand_measurable B hbound nu positive

 theorem actualTarget_prior_variance_grid (F : SourceModelFamily A0 D O π)
     {N : ℕ} {ι : Type*} [Fintype ι] (G : CanonicalFrame D N ι)
     (hN : 0<N) (hsmall : (G.Au+G.Av)/G.rminus*F.scores.C ≤ 1/4)
     (B : ℝ) (hB : 0≤B)
     (hbound : ∀ u v:ℝ,|u|≤G.Au/G.rminus→|v|≤G.Av/G.rminus→
       |F.integrand (u,v)-F.integrand 0|≤B)
     (nu : Measure (ι→ℤ)) [IsProbabilityMeasure nu] (positive : Bool) :
     variance (F.actualTarget G hsmall) (globalBlockPrior nu G.M positive) ≤
       4*(G.rplus*B)^2/((2*N:ℕ):ℝ)^(D+1) := by
   rw [F.actualTarget_eq_responseFunctional G hsmall]
   exact G.global_response_prior_variance_grid hN F.integrand F.integrand_measurable B hB hbound nu positive

 theorem uniform_actualTarget_prior_taylor (F : SourceModelFamily A0 D O π) :
     ∃ epsilon>0,∃ C≥0,∃ B≥0,
       (∀ u v:ℝ,|u|≤epsilon→|v|≤epsilon→|F.integrand (u,v)-F.integrand 0|≤B) ∧
       ∀ {N : ℕ} {ι : Type*} [Fintype ι] (G : CanonicalFrame D N ι)
         (hsmall : (G.Au+G.Av)/G.rminus*F.scores.C≤1/4)
         (nu : Measure (ι→ℤ)) [IsProbabilityMeasure nu],
       G.Au/G.rminus≤epsilon→G.Av/G.rminus≤epsilon→
       |((∫ z,F.actualTarget G hsmall z ∂globalBlockPrior nu G.M true)-
          (∫ z,F.actualTarget G hsmall z ∂globalBlockPrior nu G.M false))-
          OddTaylor.mixedDerivative F.integrand 0*G.priorMeanDifference (fun x=>x.1*x.2) nu|≤
       (G.ell*(2*N:ℕ))^(D+1)*
         (C*G.rplus*(G.Au/G.rminus)*(G.Av/G.rminus)*
           ((G.Au/G.rminus)^2+(G.Av/G.rminus)^2)) := by
   obtain ⟨epsilon,he,C,hC,B,hB,hbound,hTaylor⟩ := F.uniform_response_prior_taylor
   refine ⟨epsilon,he,C,hC,B,hB,hbound,?_⟩
   intro N ι _ G hsmall nu _ hAu hAv
   rw [F.actualTarget_eq_responseFunctional G hsmall]
   exact hTaylor G nu hAu hAv

end RoughRegime.LatticePriors.SourceModelFamily
