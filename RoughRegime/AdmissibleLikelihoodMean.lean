module

public import RoughRegime.AdmissiblePhaseComparison


@[expose] public section
/-! Original point-likelihood normalization and positivity, without any
smallness assumption on the global amplitude bound. -/
noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace RoughRegime.PoissonMeasure.AdmissiblePhasePair
set_option backward.isDefEq.respectTransparency false
variable {H X Z:Type*}[MeasurableSpace H][MeasurableSpace X][MeasurableSpace Z]
    {μ:Measure X}[IsProbabilityMeasure μ]{π:Measure Z}[IsProbabilityMeasure π]
    {lo hi barp C0:ℝ}(A:AdmissiblePhasePair (H:=H) μ lo hi barp C0)

 def signedCoefficientU (Au:ℝ)(q:PhaseParameter H)(x:X) : ℝ:=
  Lower.sign q.2.1*Au*A.field.hu q.1.1 x/barp
 def signedCoefficientV (Av:ℝ)(q:PhaseParameter H)(x:X) : ℝ:=
  Lower.sign q.2.2*Av*A.field.hv q.1.1 x/barp

 theorem likelihood_split (S:SpatialAffine.Scores π)(Au Av:ℝ)(q:PhaseParameter H)(o:X×Z)
    (hbarp:barp≠0) : A.likelihood S Au Av q o=
      A.field.designDensity barp q.1 o.1/barp+
        A.signedCoefficientU Au q o.1*S.su o.2+A.signedCoefficientV Av q o.1*S.sv o.2 := by
  simp only [likelihood,AffinePhaseField.markedFactor,AffinePhaseField.scale,AffinePhaseField.feature,
    AffinePhaseField.unsigned,phaseScores,Fin.sum_univ_three]
  simp only [Fin.isValue,ite_true,ite_false,show (1:Fin 3)≠0 by decide,
    show (2:Fin 3)≠0 by decide,show (2:Fin 3)≠1 by decide,
    show (0:Fin 3)≠1 by decide,show (0:Fin 3)≠2 by decide,show (1:Fin 3)≠2 by decide]
  unfold AffinePhaseField.designDensity signedCoefficientU signedCoefficientV
  field_simp [hbarp]
  ring

 theorem likelihood_integrable_and_mean (S:SpatialAffine.Scores π)
    (hlo:0<lo)(hhi:0≤hi)(hbarp:0<barp)(hC0:0≤C0)(Au Av:ℝ)(q:PhaseParameter H) :
    Integrable (A.likelihood S Au Av q) (μ.prod π) ∧ (∫o,A.likelihood S Au Av q o ∂μ.prod π)=1 := by
  let p:=fun x=>A.field.designDensity barp q.1 x/barp
  let u:=A.signedCoefficientU Au q
  let v:=A.signedCoefficientV Av q
  have hpM : Measurable (A.field.designDensity barp q.1):=
    A.designDensity_measurable.comp (measurable_const.prodMk measurable_id)
  have hpI : Integrable p μ:=Integrable.of_bound (hpM.div_const barp).aestronglyMeasurable
    (hi/barp) (ae_of_all _ (fun x=>by
      rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg ((hlo.trans_le (A.densityBounds q.1 x).1).le) hbarp.le)]
      exact div_le_div_of_nonneg_right (A.densityBounds q.1 x).2 hbarp.le))
  have hraw:=A.field_bounded hlo hhi hbarp.le hC0
  have hmu : Measurable (A.field.hu q.1.1):=A.measurable.hu.comp (measurable_const.prodMk measurable_id)
  have hmv : Measurable (A.field.hv q.1.1):=A.measurable.hv.comp (measurable_const.prodMk measurable_id)
  have huI : Integrable u μ :=
    ((Integrable.of_bound hmu.aestronglyMeasurable (rawBound lo hi barp C0)
      (ae_of_all _ (fun x=>by simpa only [Real.norm_eq_abs] using hraw.hu q.1.1 x))).const_mul
      (Lower.sign q.2.1*Au)).div_const barp
  have hvI : Integrable v μ :=
    ((Integrable.of_bound hmv.aestronglyMeasurable (rawBound lo hi barp C0)
      (ae_of_all _ (fun x=>by simpa only [Real.norm_eq_abs] using hraw.hv q.1.1 x))).const_mul
      (Lower.sign q.2.2*Av)).div_const barp
  have hsu : Integrable S.su π :=Integrable.of_bound S.measurableU.aestronglyMeasurable S.C
    (ae_of_all _ (fun z=>by simpa only [Real.norm_eq_abs] using S.boundU z))
  have hsv : Integrable S.sv π :=Integrable.of_bound S.measurableV.aestronglyMeasurable S.C
    (ae_of_all _ (fun z=>by simpa only [Real.norm_eq_abs] using S.boundV z))
  have hpP : Integrable (fun o:X×Z=>p o.1) (μ.prod π) := by
    simpa only [mul_one] using hpI.mul_prod (integrable_const (1:ℝ))
  have huP:=huI.mul_prod hsu
  have hvP:=hvI.mul_prod hsv
  have he : A.likelihood S Au Av q=fun o:X×Z=>p o.1+u o.1*S.su o.2+v o.1*S.sv o.2 := by
    funext o;exact A.likelihood_split S Au Av q o hbarp.ne'
  refine ⟨by rw [he];exact (hpP.add huP).add hvP,?_⟩
  rw [he,integral_add (f:=fun o:X×Z=>p o.1+u o.1*S.su o.2) (g:=fun o:X×Z=>v o.1*S.sv o.2)
    (hpP.add huP) hvP,integral_add (f:=fun o:X×Z=>p o.1) (g:=fun o:X×Z=>u o.1*S.su o.2) hpP huP,
    integral_prod_mul,integral_prod_mul,S.meanU,S.meanV,mul_zero,mul_zero,add_zero,add_zero]
  have heP : (∫o:X×Z,p o.1 ∂μ.prod π)=∫x,p x ∂μ := by
    simpa only [mul_one,integral_const,probReal_univ,one_smul] using integral_prod_mul (μ:=μ) (ν:=π) p (fun _=> (1:ℝ))
  rw [heP]
  dsimp only [p]
  rw [integral_div,A.constantMass,div_self hbarp.ne']

 theorem likelihood_integral_without_smallness (S:SpatialAffine.Scores π)
    (hlo:0<lo)(hhi:0≤hi)(hbarp:0<barp)(hC0:0≤C0)(Au Av:ℝ)(q:PhaseParameter H) :
    (∫o,A.likelihood S Au Av q o ∂μ.prod π)=1 :=
  (A.likelihood_integrable_and_mean S hlo hhi hbarp hC0 Au Av q).2

 theorem markedFactor_integral_zero_without_smallness (S:SpatialAffine.Scores π)
    (hlo:0<lo)(hhi:0≤hi)(hbarp:0<barp)(hC0:0≤C0)(Au Av:ℝ)(q:PhaseParameter H) :
    (∫o,(A.field.scale (1/barp)).markedFactor Au Av (phaseScores S) q o ∂μ.prod π)=0 := by
  have hh:=A.likelihood_integrable_and_mean S hlo hhi hbarp hC0 Au Av q
  have heq : (A.field.scale (1/barp)).markedFactor Au Av (phaseScores S) q=
      fun o=>A.likelihood S Au Av q o-1 := by funext o;unfold likelihood;ring
  rw [heq,integral_sub hh.1 (integrable_const 1),hh.2]
  simp

 theorem likelihood_factor (S:SpatialAffine.Scores π)(Au Av:ℝ)(q:PhaseParameter H)(o:X×Z)
    (hlo:0<lo)(hbarp:0<barp) : A.likelihood S Au Av q o=
      (A.field.designDensity barp q.1 o.1/barp)*
        (1+Lower.sign q.2.1*A.unsignedProfileU Au q.1 o.1*S.su o.2+
          Lower.sign q.2.2*A.unsignedProfileV Av q.1 o.1*S.sv o.2) := by
  rw [A.likelihood_split S Au Av q o hbarp.ne']
  have hp : A.field.designDensity barp q.1 o.1≠0 := (hlo.trans_le (A.densityBounds q.1 o.1).1).ne'
  unfold unsignedProfileU unsignedProfileV signedCoefficientU signedCoefficientV
  field_simp [hbarp.ne',hp]

 theorem likelihood_lower_pointwise (S:SpatialAffine.Scores π)(Au Av:ℝ)
    (hlo:0<lo)(hbarp:0<barp)
    (hpoint:∀(q:H×ℝ)(x:X)(z:Z),|A.unsignedProfileU Au q x*S.su z|+
      |A.unsignedProfileV Av q x*S.sv z|≤1/2)
    (q:PhaseParameter H)(o:X×Z) : lo/(2*barp)≤A.likelihood S Au Av q o := by
  have hsign (s:Bool) : |Lower.sign s|=1 := by cases s <;> simp [Lower.sign]
  have hs : |Lower.sign q.2.1*A.unsignedProfileU Au q.1 o.1*S.su o.2+
      Lower.sign q.2.2*A.unsignedProfileV Av q.1 o.1*S.sv o.2|≤1/2 := by
    apply (abs_add_le _ _).trans
    simpa only [mul_assoc,abs_mul,hsign,one_mul] using hpoint q.1 o.1 o.2
  have hr : (1/2:ℝ)≤1+Lower.sign q.2.1*A.unsignedProfileU Au q.1 o.1*S.su o.2+
      Lower.sign q.2.2*A.unsignedProfileV Av q.1 o.1*S.sv o.2 := by
    linarith [(abs_le.mp hs).1]
  have hp : lo/barp≤A.field.designDensity barp q.1 o.1/barp :=
    div_le_div_of_nonneg_right (A.densityBounds q.1 o.1).1 hbarp.le
  rw [A.likelihood_factor S Au Av q o hlo hbarp]
  calc
    _=(lo/barp)*(1/2) := by ring
    _≤_ := mul_le_mul hp hr (by norm_num) (div_nonneg ((hlo.trans_le (A.densityBounds q.1 o.1).1).le) hbarp.le)

end RoughRegime.PoissonMeasure.AdmissiblePhasePair
