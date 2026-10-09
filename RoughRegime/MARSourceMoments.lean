module

public import RoughRegime.SourceModelWeights
public import RoughRegime.MARBaseline


@[expose] public section
/-! The exact affine MAR response moments forced by the normalized residual
scores. Their identities use actual integrals and exclude the diagonal branch. -/
noncomputable section
open MeasureTheory Set
namespace RoughRegime.Applications.MAR
open RoughRegime.SpatialAffine RoughRegime.LatticePriors
set_option backward.isDefEq.respectTransparency false

theorem source_scores_positive (A0 : Model.Parameters) (D : ℕ) (hM : 1 ≤ A0.M0)
    (F : SourceModelFamily A0 D (observables (A0.withDimension D) hM) baseline) :
    residualMomentU (A0.withDimension D) (observables (A0.withDimension D) hM) baseline F.scores true=1 ∧
    residualMomentU (A0.withDimension D) (observables (A0.withDimension D) hM) baseline F.scores false=0 ∧
    residualMomentV (A0.withDimension D) (observables (A0.withDimension D) hM) baseline F.scores true=0 ∧
    residualMomentV (A0.withDimension D) (observables (A0.withDimension D) hM) baseline F.scores false=1 := by
  rcases F.score_case with hp | hd
  · exact hp
  · have h := congrFun hd.1 missingPoint
    norm_num [observables,missingPoint,observedOutcome] at h

theorem affineMean_observed (A : Model.Parameters) (hM : 1 ≤ A.M0)
    (S : Scores (baseline : Measure Response))
    (hu : residualMomentU A (observables A hM) baseline S true=1)
    (hv : residualMomentU A (observables A hM) baseline S false=0) (u v : ℝ) :
    affineMean baseline S observed u v = (1-u)/2 := by
  have h := affineMean_U A (observables A hM) baseline S
    (by rw [(baseline_ratios A hM).1]; norm_num) u v
  rw [(baseline_ratios A hM).2.1,hu,hv] at h
  have hone : affineMean baseline S (fun _=>1) u v=1 := by
    simp [affineMean,S.meanU,S.meanV]
  change affineMean baseline S (fun _=>1) u v=2*affineMean baseline S observed u v+1*u+0*v at h
  rw [hone] at h
  linarith

theorem affineMean_observedOutcome (A : Model.Parameters) (hM : 1 ≤ A.M0)
    (S : Scores (baseline : Measure Response))
    (hu : residualMomentU A (observables A hM) baseline S true=1)
    (hv : residualMomentU A (observables A hM) baseline S false=0)
    (hvu : residualMomentV A (observables A hM) baseline S true=0)
    (hvv : residualMomentV A (observables A hM) baseline S false=1) (u v : ℝ) :
    affineMean baseline S observedOutcome u v = (1-u)/4+v := by
  have h := affineMean_V A (observables A hM) baseline S
    (by rw [(baseline_ratios A hM).1]; norm_num) u v
  rw [(baseline_ratios A hM).2.2,hvu,hvv] at h
  change affineMean baseline S observedOutcome u v = (1/2)*affineMean baseline S observed u v+0*u+1*v at h
  rw [affineMean_observed A hM S hu hv] at h
  linarith

theorem source_response_moments (A : Model.Parameters) (hM : 1 ≤ A.M0)
    (S : Scores (baseline : Measure Response))
    (hp : residualMomentU A (observables A hM) baseline S true=1 ∧
      residualMomentU A (observables A hM) baseline S false=0 ∧
      residualMomentV A (observables A hM) baseline S true=0 ∧
      residualMomentV A (observables A hM) baseline S false=1)
    (F : Field (Model.cubeVolume A.d)) (x : Model.Covariate A.d) :
    responseMoment S F observed x = (1-F.u x)/2 ∧
      responseMoment S F observedOutcome x = (1-F.u x)/4+F.v x := by
  constructor
  · rw [bounded_responseMoment_eq_affineMean A baseline S F observed observed_measurable 1 zero_le_one
      (fun z=>by simpa only [abs_of_nonneg (observed_range z).1] using (observed_range z).2),
      affineMean_observed A hM S hp.1 hp.2.1]
  · rw [bounded_responseMoment_eq_affineMean A baseline S F observedOutcome observedOutcome_measurable 1 zero_le_one
      (fun z=>by simpa only [abs_of_nonneg (observedOutcome_range z).1] using (observedOutcome_range z).2),
      affineMean_observedOutcome A hM S hp.1 hp.2.1 hp.2.2.1 hp.2.2.2]

end RoughRegime.Applications.MAR
