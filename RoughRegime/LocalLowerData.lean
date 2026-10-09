module

public import RoughRegime.ScoreCovariance
public import RoughRegime.SampleMeanBound
public import RoughRegime.SourceFamilyFixedScores


@[expose] public section
/-! Standalone data for Proposition15: arbitrary finite response baseline,
its prescribed bounded scores, and any density interval straddling one.
The enclosing model radius is constructed, rather than assumed. -/
noncomputable section
open MeasureTheory Set
namespace RoughRegime.LocalLower

structure ResponseData (Z:Type*) [MeasurableSpace Z] where
  D : Z→ℝ
  U : Z→ℝ
  V : Z→ℝ
  W : Z→ℝ
  lam : ℝ
  lam_ne : lam≠0
  M0 : ℝ
  M0_pos : 0<M0
  measurableD : Measurable D
  measurableU : Measurable U
  measurableV : Measurable V
  measurableW : Measurable W
  boundD : ∀z,0≤D z ∧ D z≤M0
  boundU : ∀z,|U z|≤M0
  boundV : ∀z,|V z|≤M0
  boundW : ∃C:ℝ,0≤C ∧ ∀z,|W z|≤C

namespace ResponseData
variable {Z:Type*}[MeasurableSpace Z](O:ResponseData Z) (π:ProbabilityMeasure Z)
 def w0 : ℝ:=∫z,O.D z ∂(π:Measure Z)
 def a0 : ℝ:=(∫z,O.U z ∂(π:Measure Z))/O.w0 π
 def b0 : ℝ:=(∫z,O.V z ∂(π:Measure Z))/O.w0 π
 def rU : Z→ℝ:=fun z=>O.U z-O.a0 π*O.D z
 def rV : Z→ℝ:=fun z=>O.V z-O.b0 π*O.D z

 def parameters (D:ℕ) (α β rminus rplus:ℝ) (hα:0<α) (hβ:0<β)
     (hrminus:0<rminus) (hrmin1:rminus<1) (hrplus:1<rplus) (hw:0<O.w0 π) : Model.Parameters where
  d:=D+1
  α:=α
  β:=β
  H:=1+|O.a0 π|+|O.b0 π|
  δ:=O.w0 π/2
  gminus:=O.w0 π*rminus
  gplus:=O.w0 π*rplus
  M0:=O.M0
  hd:=Nat.succ_pos _
  hα:=hα
  hβ:=hβ
  hH:=by positivity
  hδ:=by positivity
  hgminus:=by positivity
  hgplus:=mul_lt_mul_of_pos_left (hrmin1.trans hrplus) hw
  hM0:=O.M0_pos

 def observables (A:Model.Parameters) (hM:O.M0≤A.M0) : Model.Observables Z A where
  D:=O.D
  U:=O.U
  V:=O.V
  W:=O.W
  lam:=O.lam
  hlam:=O.lam_ne
  measurableD:=O.measurableD
  measurableU:=O.measurableU
  measurableV:=O.measurableV
  measurableW:=O.measurableW
  boundD z:=⟨(O.boundD z).1,(O.boundD z).2.trans hM⟩
  boundU z:=(O.boundU z).trans hM
  boundV z:=(O.boundV z).trans hM
  boundW:=O.boundW

 def scoreIdentity (S:SpatialAffine.Scores (π:Measure Z)) (α β:ℝ) : Prop :=
  ((∫z,O.rU π z*S.su z ∂(π:Measure Z))=1 ∧
   (∫z,O.rU π z*S.sv z ∂(π:Measure Z))=0 ∧
   (∫z,O.rV π z*S.su z ∂(π:Measure Z))=0 ∧
   (∫z,O.rV π z*S.sv z ∂(π:Measure Z))=1) ∨
  (O.U=O.V ∧ α=β ∧ S.su=S.sv ∧ (∫z,O.rU π z*S.su z ∂(π:Measure Z))=1)

 theorem residual_memLp (which:Bool) : MemLp (if which then O.rU π else O.rV π) 2 (π:Measure Z) := by
  have hD : MemLp O.D 2 (π:Measure Z):=Applications.bounded_memLp _ _ O.measurableD O.M0
    (fun z=>by rw [abs_of_nonneg (O.boundD z).1];exact (O.boundD z).2)
  cases which
  · exact (Applications.bounded_memLp _ _ O.measurableV O.M0 O.boundV).sub (hD.const_mul _)
  · exact (Applications.bounded_memLp _ _ O.measurableU O.M0 O.boundU).sub (hD.const_mul _)

 theorem prescribed_scores_nondegenerate (D:ℕ) (α β rminus rplus:ℝ) (hα:0<α) (hβ:0<β)
     (hrminus:0<rminus) (hrmin1:rminus<1) (hrplus:1<rplus) (hw:0<O.w0 π)
     (hfinite:∃s:Finset Z,(π:Measure Z) (s:Set Z)=1)
     (S:SpatialAffine.Scores (π:Measure Z)) (hS:O.scoreIdentity π S α β) :
     let A:=O.parameters π D α β rminus rplus hα hβ hrminus hrmin1 hrplus hw
     Model.Nondegenerate A (O.observables A le_rfl) π := by
  dsimp only
  let A:=O.parameters π D α β rminus rplus hα hβ hrminus hrmin1 hrplus hw
  let F:=O.observables A le_rfl
  have ha : Model.baselineA A F π=O.a0 π:=rfl
  have hb : Model.baselineB A F π=O.b0 π:=rfl
  have hw' : Model.baselineW A F π=O.w0 π:=rfl
  have hru:=O.residual_memLp π true
  have hrv:=O.residual_memLp π false
  refine ⟨hfinite,?_,?_,?_,?_,?_⟩
  · rw [hw']
    change max (O.w0 π/2) (O.w0 π*rminus)<O.w0 π
    exact max_lt (by linarith) (by nlinarith)
  · rw [hw']
    change O.w0 π<O.w0 π*rplus
    nlinarith
  · rw [ha]
    change |O.a0 π|<1+|O.a0 π|+|O.b0 π|
    linarith [abs_nonneg (O.b0 π)]
  · rw [hb]
    change |O.b0 π|<1+|O.a0 π|+|O.b0 π|
    linarith [abs_nonneg (O.a0 π)]
  · change (0<(∫z,(O.rU π z)^2 ∂(π:Measure Z)) ∧
        0<(∫z,(O.rU π z)^2 ∂(π:Measure Z))*(∫z,(O.rV π z)^2 ∂(π:Measure Z))-
          (∫z,O.rU π z*O.rV π z ∂(π:Measure Z))^2) ∨
      (O.U=O.V ∧ α=β ∧ 0<∫z,(O.rU π z)^2 ∂(π:Measure Z))
    rcases hS with hpos|hdiag
    · exact Or.inl (MeasureScores.covariance_positive_of_dual_scores (π:Measure Z) _ _ S.su S.sv hru hrv
        (Applications.bounded_memLp _ _ S.measurableU S.C S.boundU)
        (Applications.bounded_memLp _ _ S.measurableV S.C S.boundV) hpos.1 hpos.2.1 hpos.2.2.1 hpos.2.2.2)
    · exact Or.inr ⟨hdiag.1,hdiag.2.1,
        MeasureScores.square_integral_pos_of_score (π:Measure Z) _ S.su hru hdiag.2.2.2⟩

 theorem exists_prescribed_score_family (D:ℕ)(α β rminus rplus:ℝ)(hα:0<α)(hβ:0<β)
     (hrminus:0<rminus)(hrmin1:rminus<1)(hrplus:1<rplus)(hw:0<O.w0 π)
     (hfinite:∃s:Finset Z,(π:Measure Z) (s:Set Z)=1)
     (S:SpatialAffine.Scores (π:Measure Z))(hS:O.scoreIdentity π S α β) :
     let A:=O.parameters π D α β rminus rplus hα hβ hrminus hrmin1 hrplus hw
     let Obs:=O.observables (A.withDimension D) le_rfl
     ∃F:LatticePriors.SourceModelFamily A D Obs π,F.AllWeightsLocalized ∧ F.scores=S ∧
       F.rminus=rminus ∧ F.rplus=rplus := by
  dsimp only
  let A:=O.parameters π D α β rminus rplus hα hβ hrminus hrmin1 hrplus hw
  let Obs:=O.observables (A.withDimension D) le_rfl
  have hnd : Model.Nondegenerate (A.withDimension D) Obs π :=
    O.prescribed_scores_nondegenerate π D α β rminus rplus hα hβ hrminus hrmin1 hrplus hw hfinite S hS
  have hscores : (SpatialAffine.residualMomentU (A.withDimension D) Obs π S true=1 ∧
      SpatialAffine.residualMomentU (A.withDimension D) Obs π S false=0 ∧
      SpatialAffine.residualMomentV (A.withDimension D) Obs π S true=0 ∧
      SpatialAffine.residualMomentV (A.withDimension D) Obs π S false=1) ∨
    (Obs.U=Obs.V ∧ A.α=A.β ∧ S.su=S.sv ∧
      SpatialAffine.residualMomentU (A.withDimension D) Obs π S true=1) := hS
  obtain ⟨F,hF,hscore⟩:=LatticePriors.source_model_family_fixed_scores A D Obs π hnd S hscores
  refine ⟨F,hF,hscore,?_,?_⟩
  · change (O.w0 π*rminus)/O.w0 π=rminus
    field_simp [hw.ne']
  · change (O.w0 π*rplus)/O.w0 π=rplus
    field_simp [hw.ne']

end ResponseData
end RoughRegime.LocalLower
