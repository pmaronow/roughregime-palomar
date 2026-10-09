module

public import RoughRegime.SpatialModel


@[expose] public section
/-! The true spatial affine moments and regression ratios implied by the
paper's residual score identities. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace RoughRegime.SpatialAffine
set_option backward.isDefEq.respectTransparency false

variable (A : Model.Parameters) {Z : Type*} [MeasurableSpace Z]
  (O : Model.Observables Z A) (π : ProbabilityMeasure Z) (S : Scores (π : Measure Z))

 def denominatorDomain : Set (ℝ×ℝ) := {p | affineMean π S O.D p.1 p.2 ≠ 0}

 theorem affineMean_smooth (f : Z → ℝ) : ContDiff ℝ ∞ (fun p : ℝ×ℝ => affineMean π S f p.1 p.2) := by
   unfold affineMean
   fun_prop

 theorem denominatorDomain_open : IsOpen (denominatorDomain A O π S) := by
   exact isOpen_ne.preimage (affineMean_smooth π S O.D).continuous

 theorem denominatorDomain_zero (hbase : Model.baselineW A O π ≠ 0) :
     (0 : ℝ×ℝ) ∈ denominatorDomain A O π S := by
   simpa [denominatorDomain,affineMean,Model.baselineW] using hbase

 theorem affineIntegrand_smooth : ContDiffOn ℝ ∞ (fun p : ℝ×ℝ => affineIntegrand A O π S p.1 p.2)
     (denominatorDomain A O π S) := by
   unfold affineIntegrand
   exact (affineMean_smooth π S O.W).contDiffOn.add
     (contDiffOn_const.mul (((affineMean_smooth π S O.U).contDiffOn.mul
       (affineMean_smooth π S O.V).contDiffOn).div (affineMean_smooth π S O.D).contDiffOn (fun _ hp => hp)))

 theorem affineMean_residual (f : Z → ℝ) (hf : Measurable f) (C : ℝ) (hC : 0 ≤ C)
     (hfb : ∀ z, |f z| ≤ C) (a cu cv : ℝ)
     (hmean : (∫ z, f z ∂(π : Measure Z)) = a*Model.baselineW A O π)
     (hru : (∫ z, (f z-a*O.D z)*S.su z ∂(π : Measure Z)) = cu)
     (hrv : (∫ z, (f z-a*O.D z)*S.sv z ∂(π : Measure Z)) = cv) (u v : ℝ) :
     affineMean π S f u v = a*affineMean π S O.D u v + cu*u+cv*v := by
   have hDb (z : Z) : |O.D z| ≤ A.M0 := by rw [abs_of_nonneg (O.boundD z).1]; exact (O.boundD z).2
   have hDu := AffineResponseLower.bounded_score_product_integrable (π : Measure Z) O.D S.su O.measurableD
     S.measurableU A.M0 S.C A.hM0.le S.nonnegativeC hDb S.boundU
   have hDv := AffineResponseLower.bounded_score_product_integrable (π : Measure Z) O.D S.sv O.measurableD
     S.measurableV A.M0 S.C A.hM0.le S.nonnegativeC hDb S.boundV
   have hfu := AffineResponseLower.bounded_score_product_integrable (π : Measure Z) f S.su hf
     S.measurableU C S.C hC S.nonnegativeC hfb S.boundU
   have hfv := AffineResponseLower.bounded_score_product_integrable (π : Measure Z) f S.sv hf
     S.measurableV C S.C hC S.nonnegativeC hfb S.boundV
   rw [AffineResponseLower.residual_score_integral (π : Measure Z) f O.D S.su a hfu hDu] at hru
   rw [AffineResponseLower.residual_score_integral (π : Measure Z) f O.D S.sv a hfv hDv] at hrv
   have heu : (∫ z, f z*S.su z ∂(π : Measure Z)) = a*(∫ z, O.D z*S.su z ∂(π : Measure Z))+cu := by linarith
   have hev : (∫ z, f z*S.sv z ∂(π : Measure Z)) = a*(∫ z, O.D z*S.sv z ∂(π : Measure Z))+cv := by linarith
   unfold affineMean
   rw [hmean,heu,hev]
   unfold Model.baselineW
   ring

 theorem baseline_meanU (hbase : Model.baselineW A O π ≠ 0) :
     (∫ z, O.U z ∂(π : Measure Z)) = Model.baselineA A O π*Model.baselineW A O π := by
   unfold Model.baselineA
   field_simp

 theorem baseline_meanV (hbase : Model.baselineW A O π ≠ 0) :
     (∫ z, O.V z ∂(π : Measure Z)) = Model.baselineB A O π*Model.baselineW A O π := by
   unfold Model.baselineB
   field_simp

 def residualMomentU (which : Bool) : ℝ :=
   ∫ z, (O.U z-Model.baselineA A O π*O.D z)*(if which then S.su z else S.sv z) ∂(π : Measure Z)
 def residualMomentV (which : Bool) : ℝ :=
   ∫ z, (O.V z-Model.baselineB A O π*O.D z)*(if which then S.su z else S.sv z) ∂(π : Measure Z)

 theorem affineMean_U (hbase : Model.baselineW A O π ≠ 0) (u v : ℝ) :
     affineMean π S O.U u v = Model.baselineA A O π*affineMean π S O.D u v +
       residualMomentU A O π S true*u+residualMomentU A O π S false*v := by
   exact affineMean_residual A O π S O.U O.measurableU A.M0 A.hM0.le O.boundU
     (Model.baselineA A O π) _ _ (baseline_meanU A O π hbase) rfl rfl u v

 theorem affineMean_V (hbase : Model.baselineW A O π ≠ 0) (u v : ℝ) :
     affineMean π S O.V u v = Model.baselineB A O π*affineMean π S O.D u v +
       residualMomentV A O π S true*u+residualMomentV A O π S false*v := by
   exact affineMean_residual A O π S O.V O.measurableV A.M0 A.hM0.le O.boundV
     (Model.baselineB A O π) _ _ (baseline_meanV A O π hbase) rfl rfl u v

 def regressionChangeU (p : ℝ×ℝ) : ℝ :=
   (residualMomentU A O π S true*p.1+residualMomentU A O π S false*p.2)/affineMean π S O.D p.1 p.2
 def regressionChangeV (p : ℝ×ℝ) : ℝ :=
   (residualMomentV A O π S true*p.1+residualMomentV A O π S false*p.2)/affineMean π S O.D p.1 p.2

 theorem regressionChangeU_smooth : ContDiffOn ℝ ∞ (regressionChangeU A O π S) (denominatorDomain A O π S) := by
   unfold regressionChangeU
   exact ((contDiffOn_const.mul contDiffOn_fst).add (contDiffOn_const.mul contDiffOn_snd)).div
     (affineMean_smooth π S O.D).contDiffOn (fun _ hp => hp)
 theorem regressionChangeV_smooth : ContDiffOn ℝ ∞ (regressionChangeV A O π S) (denominatorDomain A O π S) := by
   unfold regressionChangeV
   exact ((contDiffOn_const.mul contDiffOn_fst).add (contDiffOn_const.mul contDiffOn_snd)).div
     (affineMean_smooth π S O.D).contDiffOn (fun _ hp => hp)

 theorem regressionChangeU_zero_axis (hz : residualMomentU A O π S false=0) (v : ℝ) :
     regressionChangeU A O π S (0,v)=0 := by simp [regressionChangeU,hz]
 theorem regressionChangeV_zero_axis (hz : residualMomentV A O π S true=0) (u : ℝ) :
     regressionChangeV A O π S (u,0)=0 := by simp [regressionChangeV,hz]

 theorem responseRatio_U (F : Field (Model.cubeVolume A.d)) (hbase : Model.baselineW A O π ≠ 0)
     (x : Model.Covariate A.d) (hw : responseMoment S F O.D x ≠ 0) :
     responseMoment S F O.U x/responseMoment S F O.D x =
       Model.baselineA A O π+regressionChangeU A O π S (F.u x,F.v x) := by
   have hDb (z : Z) : |O.D z| ≤ A.M0 := by rw [abs_of_nonneg (O.boundD z).1]; exact (O.boundD z).2
   rw [bounded_responseMoment_eq_affineMean A π S F O.D O.measurableD A.M0 A.hM0.le hDb x] at hw ⊢
   rw [bounded_responseMoment_eq_affineMean A π S F O.U O.measurableU A.M0 A.hM0.le O.boundU x,
     affineMean_U A O π S hbase]
   unfold regressionChangeU
   field_simp
   ring

 theorem responseRatio_V (F : Field (Model.cubeVolume A.d)) (hbase : Model.baselineW A O π ≠ 0)
     (x : Model.Covariate A.d) (hw : responseMoment S F O.D x ≠ 0) :
     responseMoment S F O.V x/responseMoment S F O.D x =
       Model.baselineB A O π+regressionChangeV A O π S (F.u x,F.v x) := by
   have hDb (z : Z) : |O.D z| ≤ A.M0 := by rw [abs_of_nonneg (O.boundD z).1]; exact (O.boundD z).2
   rw [bounded_responseMoment_eq_affineMean A π S F O.D O.measurableD A.M0 A.hM0.le hDb x] at hw ⊢
   rw [bounded_responseMoment_eq_affineMean A π S F O.V O.measurableV A.M0 A.hM0.le O.boundV x,
     affineMean_V A O π S hbase]
   unfold regressionChangeV
   field_simp
   ring

end RoughRegime.SpatialAffine
