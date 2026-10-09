module

public import RoughRegime.ProductDeterminationLower
public import RoughRegime.ProductDerivedSmoothLower
public import RoughRegime.ProductVarianceSmoothHardness


@[expose] public section
noncomputable section
open MeasureTheory Set ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology
namespace RoughRegime.Applications.Products

 theorem smooth_determination_rough_lowerBracket (A : Model.Parameters) (hM : 1≤A.M0)
    (hlo : max A.δ A.gminus<1) (hhi : 1<A.gplus) (hab : A.α=A.β) (hrough : A.theta<1/2)
    (vmin:ℝ)(hv:0<vmin)(hv1:vmin<1) :
    Model.LowerBracket (determinationTarget A) (positiveVarianceClass A vmin ∩ Model.smoothDensityClass A.d BoundedResponse) A.bracketParameters := by
  let K:=1/vmin
  have hK : 0≤K := by dsimp [K];positivity
  let h:=determinationPilot A
  have hm : ∀P : ProbabilityMeasure (Model.Observation A BoundedResponse),
      ∀j:Fin 2,(∫o,h j o ∂(P:Measure _))∈Icc (-1:ℝ) 1 := by
    intro P j
    exact abs_le.mp (bounded_mean_abs P (h j) 1 (determinationPilot_bound A j))
  have htarget : ∀P∈(positiveVarianceClass A vmin ∩ Model.smoothDensityClass A.d BoundedResponse),determinationTarget A P∈Icc (0:ℝ) K := by
    intro P hP
    have hvar : 0<responseVariance A P:=hv.trans_le hP.1.2
    refine ⟨div_nonneg (explainedTarget_range A P).1 hvar.le,?_⟩
    exact (div_le_div_of_nonneg_right (explainedTarget_range A P).2 hvar.le).trans
      (one_div_le_one_div_of_le hv hP.1.2)
  apply Model.pilot_rough_lowerBracket A.bracketParameters hrough
    (determinationTarget A) (quadraticTarget A) (fun _=>positiveVarianceClass A vmin ∩ Model.smoothDensityClass A.d BoundedResponse)
    (positiveVarianceClass A vmin ∩ Model.smoothDensityClass A.d BoundedResponse) (Eventually.of_forall fun _=>subset_rfl) h
    (determinationPilot_measurable A)
    (fun P j=>Applications.bounded_memLp (P:Measure _) (h j) (determinationPilot_measurable A j) 1 (determinationPilot_bound A j))
    unitMomentLo unitMomentHi (fun _=>by norm_num [unitMomentLo,unitMomentHi]) hm
    0 K hK (determinationPhi K) (2+3*K) 2 (by positivity)
  · exact determinationPhi_lipschitz K hK
  · apply Eventually.of_forall
    intro n
    refine ⟨htarget,?_,?_⟩
    · intro P hP
      rw [projIcc_of_mem hK (htarget P hP)]
      change quadraticTarget A P=determinationTarget A P*
        (responseSecondMoment A P-(responseMean A P)^2)+(responseMean A P)^2
      rw [←responseVariance_identity,determinationTarget,
        div_mul_cancel₀ _ (hv.trans_le hP.1.2).ne',explainedTarget_identity]
      ring
    · intro P _
      have hb:=bounded_vectorPilot_variance P h (determinationPilot_measurable A) 1 (determinationPilot_bound A)
      norm_num at hb ⊢
      exact hb.trans (by norm_num)
  · exact smooth_quadratic_positiveVariance_rough_hardness A hM hlo hhi hab hrough vmin hv hv1
  · exact Model.rough_lowerBracket_squared_sample_tendsto A.bracketParameters hrough

 theorem smooth_determination_bracket (A : Model.Parameters) (hM : 1≤A.M0)
    (hlo : max A.δ A.gminus<1) (hhi : 1<A.gplus) (hab : A.α=A.β)
    (vmin:ℝ)(hv:0<vmin)(hv1:vmin<1) :
    Model.Bracket (determinationTarget A) (positiveVarianceClass A vmin ∩ Model.smoothDensityClass A.d BoundedResponse) A.bracketParameters (A.nu:ℝ) := by
  refine ⟨?_,Model.upperBracket_mono_class _ _ _ Set.inter_subset_left
    (determination_upperBracket A hM ((le_max_left _ _).trans hlo.le) vmin hv hv1.le)⟩
  by_cases hrough : A.theta<1/2
  · exact smooth_determination_rough_lowerBracket A hM hlo hhi hab hrough vmin hv hv1
  · exact parametric_lowerBracket A _ _ (le_of_not_gt hrough)
      (smooth_determination_parametric_lower A hab ((le_max_right _ _).trans hlo.le) hhi.le vmin hv1.le)

end RoughRegime.Applications.Products
