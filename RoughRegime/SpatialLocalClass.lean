module

public import RoughRegime.SpatialScores
public import RoughRegime.HolderAffine


@[expose] public section
/-! Model localization derived from actual density margins, spatial affine
moments, and the smooth perturbations of the baseline regression ratios. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace RoughRegime.SpatialAffine
set_option backward.isDefEq.respectTransparency false

variable (A : Model.Parameters) {Z : Type*} [MeasurableSpace Z]
  (O : Model.Observables Z A) (π : ProbabilityMeasure Z) (S : Scores (π : Measure Z))
  (F : Field (Model.cubeVolume A.d)) (hsmall : F.epsilon*S.C ≤ 1/4)

 theorem responseMoment_baseline_bound (f : Z → ℝ) (hf : Measurable f) (C : ℝ) (hC : 0 ≤ C)
     (hfb : ∀ z, |f z| ≤ C) (x : Model.Covariate A.d) :
     |responseMoment S F f x-(∫ z, f z ∂(π : Measure Z))| ≤ 2*F.epsilon*C*S.C := by
   rw [bounded_responseMoment_eq_affineMean A π S F f hf C hC hfb x]
   unfold affineMean
   have hbu : |∫ z, f z*S.su z ∂(π : Measure Z)| ≤ C*S.C := by
     have he := norm_integral_le_of_norm_le_const (μ := (π : Measure Z))
       (Filter.Eventually.of_forall fun z => show ‖f z*S.su z‖ ≤ C*S.C from by
         rw [Real.norm_eq_abs,abs_mul]
         exact mul_le_mul (hfb z) (S.boundU z) (abs_nonneg _) hC)
     simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using he
   have hbv : |∫ z, f z*S.sv z ∂(π : Measure Z)| ≤ C*S.C := by
     have he := norm_integral_le_of_norm_le_const (μ := (π : Measure Z))
       (Filter.Eventually.of_forall fun z => show ‖f z*S.sv z‖ ≤ C*S.C from by
         rw [Real.norm_eq_abs,abs_mul]
         exact mul_le_mul (hfb z) (S.boundV z) (abs_nonneg _) hC)
     simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using he
   have hu := mul_le_mul (F.boundU x) hbu (abs_nonneg _) F.nonnegativeEpsilon
   have hv := mul_le_mul (F.boundV x) hbv (abs_nonneg _) F.nonnegativeEpsilon
   calc
     _ = |F.u x*(∫ z, f z*S.su z ∂(π : Measure Z))+F.v x*(∫ z, f z*S.sv z ∂(π : Measure Z))| := by congr 1; ring
     _ ≤ _ := abs_add_le _ _
     _ ≤ _ := by rw [abs_mul,abs_mul]; nlinarith

 theorem responseMoment_w_baseline_bound (x : Model.Covariate A.d) :
     |responseMoment S F O.D x-Model.baselineW A O π| ≤ 2*F.epsilon*A.M0*S.C := by
   exact responseMoment_baseline_bound A π S F O.D O.measurableD A.M0 A.hM0.le
     (fun z => by rw [abs_of_nonneg (O.boundD z).1]; exact (O.boundD z).2) x

 include hsmall in
 theorem regressionChangeU_bound (hbase : 0 < Model.baselineW A O π) (x : Model.Covariate A.d) :
     |regressionChangeU A O π S (F.u x,F.v x)| ≤
       F.epsilon*(|residualMomentU A O π S true|+|residualMomentU A O π S false|)/(Model.baselineW A O π/2) := by
   have hDb (z : Z) : |O.D z| ≤ A.M0 := by rw [abs_of_nonneg (O.boundD z).1]; exact (O.boundD z).2
   have hd := responseMoment_D_lower A O π S F hsmall hbase x
   rw [bounded_responseMoment_eq_affineMean A π S F O.D O.measurableD A.M0 A.hM0.le hDb x] at hd
   have hw : 0 < affineMean π S O.D (F.u x) (F.v x) := (by linarith : 0 < Model.baselineW A O π/2).trans_le hd
   unfold regressionChangeU
   rw [abs_div,abs_of_pos hw]
   apply div_le_div₀ (mul_nonneg F.nonnegativeEpsilon (add_nonneg (abs_nonneg _) (abs_nonneg _)))
     (show |residualMomentU A O π S true*F.u x+residualMomentU A O π S false*F.v x| ≤
       F.epsilon*(|residualMomentU A O π S true|+|residualMomentU A O π S false|) from by
       apply (abs_add_le _ _).trans
       rw [abs_mul,abs_mul]
       have hu := mul_le_mul_of_nonneg_left (F.boundU x) (abs_nonneg (residualMomentU A O π S true))
       have hv := mul_le_mul_of_nonneg_left (F.boundV x) (abs_nonneg (residualMomentU A O π S false))
       nlinarith)
     (by linarith) hd

 include hsmall in
 theorem regressionChangeV_bound (hbase : 0 < Model.baselineW A O π) (x : Model.Covariate A.d) :
     |regressionChangeV A O π S (F.u x,F.v x)| ≤
       F.epsilon*(|residualMomentV A O π S true|+|residualMomentV A O π S false|)/(Model.baselineW A O π/2) := by
   have hDb (z : Z) : |O.D z| ≤ A.M0 := by rw [abs_of_nonneg (O.boundD z).1]; exact (O.boundD z).2
   have hd := responseMoment_D_lower A O π S F hsmall hbase x
   rw [bounded_responseMoment_eq_affineMean A π S F O.D O.measurableD A.M0 A.hM0.le hDb x] at hd
   have hw : 0 < affineMean π S O.D (F.u x) (F.v x) := (by linarith : 0 < Model.baselineW A O π/2).trans_le hd
   unfold regressionChangeV
   rw [abs_div,abs_of_pos hw]
   apply div_le_div₀ (mul_nonneg F.nonnegativeEpsilon (add_nonneg (abs_nonneg _) (abs_nonneg _)))
     (show |residualMomentV A O π S true*F.u x+residualMomentV A O π S false*F.v x| ≤
       F.epsilon*(|residualMomentV A O π S true|+|residualMomentV A O π S false|) from by
       apply (abs_add_le _ _).trans
       rw [abs_mul,abs_mul]
       have hu := mul_le_mul_of_nonneg_left (F.boundU x) (abs_nonneg (residualMomentV A O π S true))
       have hv := mul_le_mul_of_nonneg_left (F.boundV x) (abs_nonneg (residualMomentV A O π S false))
       nlinarith)
     (by linarith) hd

 theorem law_localClass_from_source_bounds
     (hbase : 0 < Model.baselineW A O π) (rminus rplus delta : ℝ)
     (hrplus : 0 ≤ rplus) (hdelta : 0 ≤ delta)
     (hp : ∀ x, rminus+delta ≤ F.p x ∧ F.p x ≤ rplus-delta)
     (hinterval : A.gminus ≤ Model.baselineW A O π*rminus ∧ Model.baselineW A O π*rplus ≤ A.gplus)
     (hoverlap : 2*F.epsilon*A.M0*S.C ≤ Model.baselineW A O π-A.δ)
     (hmargin : (2*F.epsilon*A.M0*S.C)*rplus ≤ Model.baselineW A O π*delta)
     (ha0 : |Model.baselineA A O π| ≤ A.H) (hb0 : |Model.baselineB A O π| ≤ A.H)
     (hKa : ContDiff ℝ ∞ (fun x => regressionChangeU A O π S (F.u x,F.v x)))
     (hKb : ContDiff ℝ ∞ (fun x => regressionChangeV A O π S (F.u x,F.v x)))
     (ha : Model.holderNorm (fun x => regressionChangeU A O π S (F.u x,F.v x)) A.α ≤
       ENNReal.ofReal (A.H-|Model.baselineA A O π|))
     (hb : Model.holderNorm (fun x => regressionChangeV A O π S (F.u x,F.v x)) A.β ≤
       ENNReal.ofReal (A.H-|Model.baselineB A O π|))
     (r : ℝ) (hwr : 2*F.epsilon*A.M0*S.C ≤ r)
     (har : F.epsilon*(|residualMomentU A O π S true|+|residualMomentU A O π S false|)/(Model.baselineW A O π/2) ≤ r)
     (hbr : F.epsilon*(|residualMomentV A O π S true|+|residualMomentV A O π S false|)/(Model.baselineW A O π/2) ≤ r) :
     (law S F hsmall).probabilityMeasure ∈ Model.localClass A O π r := by
   have he0 := F.nonnegativeEpsilon
   have hsC := S.nonnegativeC
   have hM0 := A.hM0
   have hwb (x : Model.Covariate A.d) := responseMoment_w_baseline_bound A O π S F x
   have hw (x : Model.Covariate A.d) : A.δ ≤ responseMoment S F O.D x := by
     have he := (abs_le.mp (hwb x)).1
     linarith
   have hwd (x : Model.Covariate A.d) : responseMoment S F O.D x ≠ 0 := ne_of_gt (A.hδ.trans_le (hw x))
   have ha' : (fun x => responseMoment S F O.U x/responseMoment S F O.D x) ∈ Model.holderBall A.α A.H := by
     have he := Model.holderNorm_const_add_le _ hKa (Model.baselineA A O π) A.α
       (A.H-|Model.baselineA A O π|) A.hα (by linarith) ha
     have hfun : (fun x => responseMoment S F O.U x/responseMoment S F O.D x) =
         fun x => Model.baselineA A O π+regressionChangeU A O π S (F.u x,F.v x) := by
       funext x
       exact responseRatio_U A O π S F hbase.ne' x (hwd x)
     change Model.holderNorm _ A.α ≤ _
     rw [hfun]
     convert he using 1 <;> congr 1 <;> ring
   have hb' : (fun x => responseMoment S F O.V x/responseMoment S F O.D x) ∈ Model.holderBall A.β A.H := by
     have he := Model.holderNorm_const_add_le _ hKb (Model.baselineB A O π) A.β
       (A.H-|Model.baselineB A O π|) A.hβ (by linarith) hb
     have hfun : (fun x => responseMoment S F O.V x/responseMoment S F O.D x) =
         fun x => Model.baselineB A O π+regressionChangeV A O π S (F.u x,F.v x) := by
       funext x
       exact responseRatio_V A O π S F hbase.ne' x (hwd x)
     change Model.holderNorm _ A.β ≤ _
     rw [hfun]
     convert he using 1 <;> congr 1 <;> ring
   have hg (x : Model.Covariate A.d) : A.gminus ≤ responseMoment S F O.D x*F.p x ∧
       responseMoment S F O.D x*F.p x ≤ A.gplus := by
     have hp0 := (F.densityBounds x).1
     have hptop : F.p x ≤ rplus := (hp x).2.trans (by linarith)
     have hvar : |(responseMoment S F O.D x-Model.baselineW A O π)*F.p x| ≤
         (2*F.epsilon*A.M0*S.C)*rplus := by
       rw [abs_mul,abs_of_nonneg hp0]
       exact mul_le_mul (hwb x) hptop hp0 (by positivity)
     have hlo := (abs_le.mp hvar).1
     have hhi := (abs_le.mp hvar).2
     have hlow := mul_le_mul_of_nonneg_left (hp x).1 hbase.le
     have hupp := mul_le_mul_of_nonneg_left (hp x).2 hbase.le
     constructor <;> nlinarith [hinterval.1,hinterval.2]
   apply law_mem_localClass A O π S F hsmall hw ha' hb' hg r
   intro x
   refine ⟨(hwb x).trans hwr,?_,?_⟩
   · rw [responseRatio_U A O π S F hbase.ne' x (hwd x)]
     simpa only [add_sub_cancel_left] using (regressionChangeU_bound A O π S F hsmall hbase x).trans har
   · rw [responseRatio_V A O π S F hbase.ne' x (hwd x)]
     simpa only [add_sub_cancel_left] using (regressionChangeV_bound A O π S F hsmall hbase x).trans hbr

end RoughRegime.SpatialAffine
