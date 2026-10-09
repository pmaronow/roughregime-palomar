module

public import RoughRegime.ApplicationOverlapAffine
public import RoughRegime.SourceFamilyFixedScores


@[expose] public section
/-! Actual prescribed-score source families for the independent and
correlated diagonal overlap constructions. -/
noncomputable section
open MeasureTheory Set
namespace RoughRegime.Applications.Overlap
open RoughRegime.SpatialAffine RoughRegime.LatticePriors
set_option backward.isDefEq.respectTransparency false

 theorem baselineA_half (A : Model.Parameters) (O : Model.Observables Response A)
    (hD : O.D=fun _=>1) (hU : O.U=treatment) (c : ℝ) (hc : |c|≤1/4) :
    Model.baselineA A O (baseline c hc)=1/2 := by
  rw [Model.baselineA,hU,(baseline_moments c hc).1,baselineW_one A O hD]
  norm_num
 theorem baselineB_half (A : Model.Parameters) (O : Model.Observables Response A)
    (hD : O.D=fun _=>1) (hV : O.V=outcome) (c : ℝ) (hc : |c|≤1/4) :
    Model.baselineB A O (baseline c hc)=1/2 := by
  rw [Model.baselineB,hV,(baseline_moments c hc).2.1,baselineW_one A O hD]
  norm_num
 theorem independent_score_case (A : Model.Parameters) (hM : 1≤A.M0) :
    residualMomentU A (numeratorObservables A hM) (baseline 0 (by norm_num)) (scores 0 (by norm_num)) true=1 ∧
    residualMomentU A (numeratorObservables A hM) (baseline 0 (by norm_num)) (scores 0 (by norm_num)) false=0 ∧
    residualMomentV A (numeratorObservables A hM) (baseline 0 (by norm_num)) (scores 0 (by norm_num)) true=0 ∧
    residualMomentV A (numeratorObservables A hM) (baseline 0 (by norm_num)) (scores 0 (by norm_num)) false=1 := by
  have ha := baselineA_half A (numeratorObservables A hM) rfl rfl 0 (by norm_num)
  have hb := baselineB_half A (numeratorObservables A hM) rfl rfl 0 (by norm_num)
  simp only [residualMomentU,residualMomentV]
  rw [ha,hb]
  simp only [Bool.false_eq_true,ite_false,ite_true,numeratorObservables,Products.covarianceObservables,scores,mul_one]
  change (∫ z,(treatment z-1/2)*scoreU 0 z ∂(baseline 0 (by norm_num):Measure Response))=1 ∧
    (∫ z,(treatment z-1/2)*scoreV 0 z ∂(baseline 0 (by norm_num):Measure Response))=0 ∧
    (∫ z,(outcome z-1/2)*scoreU 0 z ∂(baseline 0 (by norm_num):Measure Response))=0 ∧
    (∫ z,(outcome z-1/2)*scoreV 0 z ∂(baseline 0 (by norm_num):Measure Response))=1
  rw [baseline_integral 0 (by norm_num) (fun z=>(treatment z-1/2)*scoreU 0 z) ((treatment_measurable.sub_const _).mul (scoreU_measurable _)),
    baseline_integral 0 (by norm_num) (fun z=>(treatment z-1/2)*scoreV 0 z) ((treatment_measurable.sub_const _).mul (scoreV_measurable _)),
    baseline_integral 0 (by norm_num) (fun z=>(outcome z-1/2)*scoreU 0 z) ((outcome_measurable.sub_const _).mul (scoreU_measurable _)),
    baseline_integral 0 (by norm_num) (fun z=>(outcome z-1/2)*scoreV 0 z) ((outcome_measurable.sub_const _).mul (scoreV_measurable _))]
  norm_num [binaryPoint,treatment,outcome,MAR.armIndicator,MAR.bitOutcome,scoreU,scoreV,signA,signY,RoughRegime.Lower.sign]

 theorem diagonal_score_case (A : Model.Parameters) (hM : 1≤A.M0) :
    residualMomentU (diagonalParameters A) (denominatorObservables A hM)
      (baseline (1/4) (by norm_num)) diagonalScores true=1 := by
  have ha := baselineA_half (diagonalParameters A) (denominatorObservables A hM) rfl rfl (1/4) (by norm_num)
  simp only [residualMomentU]
  rw [ha]
  simp only [ite_true,denominatorObservables,Products.covarianceObservables,diagonalScores,mul_one]
  change (∫ z,(treatment z-1/2)*scoreU (1/4) z ∂(baseline (1/4) (by norm_num):Measure Response))=1
  rw [baseline_integral (1/4) (by norm_num) (fun z=>(treatment z-1/2)*scoreU (1/4) z) ((treatment_measurable.sub_const _).mul (scoreU_measurable _))]
  norm_num [binaryPoint,treatment,outcome,MAR.armIndicator,MAR.bitOutcome,scoreU,signA,signY,RoughRegime.Lower.sign]

 theorem exists_independent_family (A0 : Model.Parameters) (D : ℕ) (hM : 1≤A0.M0)
    (hlo : max A0.δ A0.gminus<1) (hhi : 1<A0.gplus) (hH : 1/2<A0.H) :
    ∃ F : SourceModelFamily A0 D (numeratorObservables (A0.withDimension D) hM) (baseline 0 (by norm_num)),
      F.AllWeightsLocalized ∧ F.scores=scores 0 (by norm_num) := by
  exact source_model_family_fixed_scores A0 D _ _
    (independent_baseline_nondegenerate _ _ rfl rfl rfl hlo hhi hH) _
    (Or.inl (independent_score_case _ hM))

 theorem exists_diagonal_family (A0 : Model.Parameters) (D : ℕ) (hM : 1≤A0.M0)
    (hlo : max A0.δ A0.gminus<1) (hhi : 1<A0.gplus) (hH : 1/2<A0.H) :
    ∃ F : SourceModelFamily (diagonalParameters A0) D (denominatorObservables (A0.withDimension D) hM)
      (baseline (1/4) (by norm_num)), F.AllWeightsLocalized ∧ F.scores=diagonalScores := by
  exact source_model_family_fixed_scores (diagonalParameters A0) D _ _
    (diagonal_baseline_nondegenerate _ _ rfl rfl rfl hlo hhi hH rfl) _
    (Or.inr ⟨rfl,rfl,rfl,diagonal_score_case _ hM⟩)

end RoughRegime.Applications.Overlap
